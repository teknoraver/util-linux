/* mu -- summarize memory usage

   Copyright (C) 2025
   Author(s): Xiaofei Du <xiaofeidu@meta.com>, Matteo Croce <teknoraver@meta.com>
   This program is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program.  If not, see <https://www.gnu.org/licenses/>.  */

/*
#include "system.h"
#include "argmatch.h"
#include "argv-iter.h"
#include "assure.h"
#include "di-set.h"
#include "exclude.h"
#include "fprintftime.h"
#include "human.h"
#include "mountlist.h"
#include "quote.h"
#include "stat-size.h"
#include "stat-time.h"
#include "stdio--.h"
#include "xfts.h"
#include "xstrtol.h"
#include "xstrtol-error.h"
*/

#include <config.h>
#include <getopt.h>
#include <sys/types.h>

#include <stdbool.h>
#include <stdint.h>
#include <limits.h>
#include <error.h>

#include <fcntl.h>
#include <linux/mman.h>
#include <sys/stat.h>
#include <sys/syscall.h>
#include <unistd.h>

#include "c.h"
#include "nls.h"
#include "strutils.h"
#include "closestream.h"

extern bool fts_debug;

/* The official name of this program (e.g., no 'g' prefix).  */
#define PROGRAM_NAME "mu"

#if DU_DEBUG
#define FTS_CROSS_CHECK(Fts) fts_cross_check (Fts)
#else
#define FTS_CROSS_CHECK(Fts)
#endif

#define LONGEST_HUMAN_READABLE \
  ((2 * sizeof (uintmax_t) * CHAR_BIT * 146 / 485 + 1) * (MB_LEN_MAX + 1) \
   - MB_LEN_MAX + 1 + 3)

#define SAME_SIZE(a, b)	(ARRAY_SIZE(a) == ARRAY_SIZE(b))

/* A set of dev/ino pairs to help identify files and directories
   whose sizes have already been counted.  */
static struct di_set *di_files;

/* A set containing a dev/ino pair for each local mount point directory.  */
static struct di_set *di_mnt;

/* Keep track of the preceding "level" (depth in hierarchy)
   from one call of process_file to the next.  */
static size_t prev_level;

struct muinfo {
	uintmax_t cache_size;
	uintmax_t dirty_size;
	uintmax_t writeback_size;
	uintmax_t evicted_size;
	uintmax_t recently_evicted_size;
	struct timespec tmax;
};

static int
cachestat(int fd, struct cachestat_range *cstat_range, struct cachestat *cstat, unsigned int flags)
{
	return syscall(__NR_cachestat, fd, cstat_range, cstat, flags);
}

static inline void muinfo_init(struct muinfo *mui)
{
	mui->cache_size = 0;
	mui->dirty_size = 0;
	mui->writeback_size = 0;
	mui->evicted_size = 0;
	mui->recently_evicted_size = 0;
	mui->tmax.tv_sec = (time_t)LLONG_MIN;
	mui->tmax.tv_nsec = -1;
}

static inline void muinfo_add(struct muinfo *first, const struct muinfo *second)
{
	uintmax_t sum = first->cache_size + second->cache_size;
	first->cache_size = first->cache_size <= sum ? sum : UINTMAX_MAX;

	sum = first->dirty_size + second->dirty_size;
	first->dirty_size = first->dirty_size <= sum ? sum : UINTMAX_MAX;

	sum = first->writeback_size + second->writeback_size;
	first->writeback_size = first->writeback_size <= sum ? sum : UINTMAX_MAX;

	sum = first->evicted_size + second->evicted_size;
	first->evicted_size = first->evicted_size <= sum ? sum : UINTMAX_MAX;

	sum = first->recently_evicted_size + second->recently_evicted_size;
	first->recently_evicted_size = first->recently_evicted_size <= sum ? sum : UINTMAX_MAX;

	if (cmp_timespec(&first->tmax, &second->tmax, <))
		first->tmax = second->tmax;
}

struct mulevel {
	struct muinfo ent;
	struct muinfo subdir;
};

/* If true, display counts for all files, not just directories.  */
static bool opt_all = false;

/* If true, count each hard link of files with multiple links.  */
static bool opt_count_all = false;

/* If true, hash all files to look for hard links.  */
static bool hash_all;

/* If true, output the NUL byte instead of a newline at the end of each line. */
static bool opt_nul_terminate_output = false;

/* If true, print a grand total at the end.  */
static bool print_grand_total = false;

/* If nonzero, do not add sizes of subdirectories.  */
static bool opt_separate_dirs = false;

/* Show the total for each directory (and file if --all) that is at
   most MAX_DEPTH levels down from the root of the hierarchy.  The root
   is at level 0, so 'mu --max-depth=0' is equivalent to 'mu -s'.  */
static size_t max_depth = SIZE_MAX;

/* Only output entries with at least this SIZE if positive,
   or at most if negative.  See --threshold option.  */
static intmax_t opt_threshold = 0;

/* Human-readable options for output.  */
static int human_readable;
static int human_output_opts;

/* If true, print most recently modified date, using the specified format.  */
static bool opt_time = false;

/* Type of time to display. controlled by --time.  */

enum time_type {
	time_mtime,		/* default */
	time_ctime,
	time_atime
};

static enum time_type time_type = time_mtime;

/* User specified date / time style */
static char const *time_style = NULL;

/* Format used to display date / time. Controlled by --time-style */
static char const *time_format = NULL;

/* The units to use when printing sizes.  */
static uintmax_t output_block_size;

#if 0
/* File name patterns to exclude.  */
static struct exclude *exclude;
#endif

static struct muinfo tot_mui;

#define IS_DIR_TYPE(Type)	\
  ((Type) == FTS_DP		\
   || (Type) == FTS_DNR)

/* For long options that have no equivalent short option, use a
   non-character as a pseudo short option, starting with CHAR_MAX + 1.  */
enum {
	EXCLUDE_OPTION = CHAR_MAX + 1,
	FILES0_FROM_OPTION,
	HUMAN_SI_OPTION,
	FTS_DEBUG,
	TIME_OPTION,
	TIME_STYLE_OPTION,
};

static struct option const long_options[] = {
	{"all", no_argument, NULL, 'a'},
	{"block-size", required_argument, NULL, 'B'},
	{"bytes", no_argument, NULL, 'b'},
	{"count-links", no_argument, NULL, 'l'},
	/* {"-debug", no_argument, NULL, FTS_DEBUG}, */
	{"dereference", no_argument, NULL, 'L'},
	{"dereference-args", no_argument, NULL, 'D'},
	{"exclude", required_argument, NULL, EXCLUDE_OPTION},
	{"exclude-from", required_argument, NULL, 'X'},
	{"files0-from", required_argument, NULL, FILES0_FROM_OPTION},
	{"human-readable", no_argument, NULL, 'h'},
	{"si", no_argument, NULL, HUMAN_SI_OPTION},
	{"max-depth", required_argument, NULL, 'd'},
	{"null", no_argument, NULL, '0'},
	{"no-dereference", no_argument, NULL, 'P'},
	{"one-file-system", no_argument, NULL, 'x'},
	{"separate-dirs", no_argument, NULL, 'S'},
	{"summarize", no_argument, NULL, 's'},
	{"total", no_argument, NULL, 'c'},
	{"threshold", required_argument, NULL, 't'},
	{"time", optional_argument, NULL, TIME_OPTION},
	{"time-style", required_argument, NULL, TIME_STYLE_OPTION},
	{"format", required_argument, NULL, 'f'},
	{"help", no_argument, NULL, CHAR_MIN - 2},
	{"version", no_argument, NULL, CHAR_MIN - 3},
	{NULL, 0, NULL, 0}
};

static char const *const time_args[] = {
	"atime", "access", "use", "ctime", "status"
};

static enum time_type const time_types[] = {
	time_atime, time_atime, time_atime, time_ctime, time_ctime
};

static_assert(SAME_SIZE(time_args, time_types));

/* 'full-iso' uses full ISO-style dates and times.  'long-iso' uses longer
   ISO-style timestamps, though shorter than 'full-iso'.  'iso' uses shorter
   ISO-style timestamps.  */
enum time_style {
	full_iso_time_style,	/* --time-style=full-iso */
	long_iso_time_style,	/* --time-style=long-iso */
	iso_time_style		/* --time-style=iso */
};

static char const *const time_style_args[] = {
	"full-iso", "long-iso", "iso"
};

static enum time_style const time_style_types[] = {
	full_iso_time_style, long_iso_time_style, iso_time_style
};

static_assert(SAME_SIZE(time_style_args, time_style_types));

static void usage(int status)
{
	if (status != EXIT_SUCCESS) {
		fputs(_("Try '" PROGRAM_NAME " --help' for more information.\n"), stderr);
	} else {
		puts(_("\
Usage: " PROGRAM_NAME " [OPTION]... [FILE]...\n\
  or:  " PROGRAM_NAME " [OPTION]... --files0-from=F"));
		fputs(_("\
Summarize memory usage of the set of FILEs, recursively for directories.\n\
"), stdout);

		puts(_("\n\
Mandatory arguments to long options are mandatory for short options too."));

		fputs(_("\
  -0, --null            end each output line with NUL, not newline\n\
  -a, --all             write counts for all files, not just directories\n\
"), stdout);
		fputs(_("\
  -B, --block-size=SIZE  scale sizes by SIZE before printing them; e.g.,\n\
                           '-BM' prints sizes in units of 1,048,576 bytes;\n\
                           see SIZE format below\n\
  -b, --bytes           equivalent to '--block-size=1'\n\
  -c, --total           produce a grand total\n\
  -D, --dereference-args  dereference only symlinks that are listed on the\n\
                          command line\n\
  -d, --max-depth=N     print the total for a directory (or file, with --all)\n\
                          only if it is N or fewer levels below the command\n\
                          line argument;  --max-depth=0 is the same as\n\
                          --summarize\n\
"), stdout);
		fputs(_("\
      --files0-from=F   summarize device usage of the\n\
                          NUL-terminated file names specified in file F;\n\
                          if F is -, then read names from standard input\n\
  -f, --format=FORMAT   use the specified FORMAT for output instead of the\n\
                          default; Only cached bytes are printed by default\n\
  -H                    equivalent to --dereference-args (-D)\n\
  -h, --human-readable  print sizes in human readable format (e.g., 1K 234M 2G)\
\n\
"), stdout);
		fputs(_("\
  -k                    like --block-size=1K\n\
  -L, --dereference     dereference all symbolic links\n\
  -l, --count-links     count sizes many times if hard linked\n\
  -m                    like --block-size=1M\n\
"), stdout);
		fputs(_("\
  -P, --no-dereference  don't follow any symbolic links (this is the default)\n\
  -S, --separate-dirs   for directories do not include size of subdirectories\n\
      --si              like -h, but use powers of 1000 not 1024\n\
  -s, --summarize       display only a total for each argument\n\
"), stdout);
		fputs(_("\
  -t, --threshold=SIZE  exclude entries smaller than SIZE if positive,\n\
                          or entries greater than SIZE if negative\n\
      --time            show time of the last modification of any file in the\n\
                          directory, or any of its subdirectories\n\
      --time=WORD       show time as WORD instead of modification time:\n\
                          atime, access, use, ctime or status\n\
      --time-style=STYLE  show times using STYLE, which can be:\n\
                            full-iso, long-iso, iso, or +FORMAT;\n\
                            FORMAT is interpreted like in 'date'\n\
"), stdout);
		fputs(_("\
  -X, --exclude-from=FILE  exclude files that match any pattern in FILE\n\
      --exclude=PATTERN    exclude files that match PATTERN\n\
  -x, --one-file-system    skip directories on different file systems\n\
"), stdout);
		puts("      --help        display this help and exit");
		puts("      --version     output version information and exit");
		fputs(_("\n\
The valid format sequences are:\n\
\n\
  %c   memory cached in the page cache\n\
  %d   dirty memory (have been modified and not yet written back\n\
         to persistent storage)\n\
  %w   memory currently being written back\n\
  %e   memory were once resident in the cache but has since been forced out\n\
  %r   memory that has been forced out in the recent past. In this case, the\n\
         'recent past' is defined by the memory that has been evicted since\n\
         the memory in question was forced out\n\
"), stdout);
		puts(_("\n\
Display values are in units of the first available SIZE from --block-size,\n\
and the " PROGRAM_NAME "_BLOCK_SIZE, BLOCK_SIZE and BLOCKSIZE environment variables.\n\
Otherwise, units default to 1024 bytes (or 512 if POSIXLY_CORRECT is set)."));
		puts(_("\n\
The SIZE argument is an integer and optional unit (example: 10K is 10*1024).\n\
Units are K,M,G,T,P,E,Z,Y,R,Q (powers of 1024) or KB,MB,... (powers of 1000).\n\
Binary prefixes can be used, too: KiB=K, MiB=M, and so on."));
	}
	exit(status);
}

/* TODO: remove and use xalloc() in the allocators */
static void xalloc_die(void)
{
	err(EXIT_FAILURE, _("ENOMEM"));
}

/* Try to insert the INO/DEV pair into DI_SET.
   Return true if the pair is successfully inserted,
   false if the pair was already there.  */
static bool hash_ins(struct di_set *di_set, ino_t ino, dev_t dev)
{
	int inserted = di_set_insert(di_set, dev, ino);
	if (inserted < 0)
		xalloc_die();
	return inserted;
}

/* FIXME: this code is nearly identical to code in date.c  */
/* Display the date and time in WHEN according to the format specified
   in FORMAT.  */

static void show_date(char const *format, struct timespec when)
{
	struct tm tm;

	if (localtime_r(&when.tv_sec, &tm)) {
		char fmt[64];
		strftime(fmt, sizeof(fmt), format, &tm);
		fputs(fmt, stdout);
	} else
		fprintf(stderr, "time %ld is out of range\n", when.tv_sec);
}

/* Print N_BYTES.  Convert it to a readable value before printing.  */

static void print_only_size(uintmax_t n_bytes)
{
	char *str;

	if (n_bytes == UINTMAX_MAX) {
		fputs(_("Infinity"), stdout);
		return;
	}

	str = size_to_human_string(SIZE_SUFFIX_1LETTER, output_block_size);
	if (!str)
		return; // ENOMEM?

	fputs(str, stdout);
	free(str);
}

static void mu_print_stat(const struct muinfo *pmui, char m)
{
	switch (m) {
	case 'c':
		print_only_size(pmui->cache_size);
		break;
	case 'd':
		print_only_size(pmui->dirty_size);
		break;
	case 'w':
		print_only_size(pmui->writeback_size);
		break;
	case 'e':
		print_only_size(pmui->evicted_size);
		break;
	case 'r':
		print_only_size(pmui->recently_evicted_size);
		break;
	default:
		putchar('?');
		break;
	}
}

static void mu_print_size(const struct muinfo *pmui, char const *string, char const *format)
{
	if (format) {
		for (char const *b = format; *b; ++b) {
			if (*b == '%') {
				b += 1;
				char fmt_char = *b;
				switch (fmt_char) {
				case '\0':
					--b;
					/* fallthrough */
				case '%':
					putchar('%');
					break;
				default:
					mu_print_stat(pmui, *b);
					break;
				}
			} else {
				putchar(*b);
			}
		}
	} else {
		/* Only print cache size by default if no format is provided */
		print_only_size(pmui->cache_size);
	}

	if (opt_time) {
		putchar('\t');
		show_date(time_format, pmui->tmax);
	}
	printf("\t%s%c", string, opt_nul_terminate_output ? '\0' : '\n');
	fflush(stdout);
}

/* Fill the di_mnt set with local mount point dev/ino pairs.  */

static void fill_mount_table(void)
{
	struct mount_entry *mnt_ent = read_file_system_list(false);
	while (mnt_ent) {
		struct mount_entry *mnt_free;
		if (!mnt_ent->me_remote && !mnt_ent->me_dummy) {
			struct stat buf;
			if (!stat(mnt_ent->me_mountdir, &buf))
				hash_ins(di_mnt, buf.st_ino, buf.st_dev);
			else {
				/* Ignore stat failure.  False positives are too common.
				   E.g., "Permission denied" on /run/user/<name>/gvfs.  */
			}
		}

		mnt_free = mnt_ent;
		mnt_ent = mnt_ent->me_next;
		free_mount_entry(mnt_free);
	}
}

/* This function checks whether any of the directories in the cycle that
   fts detected is a mount point.  */

static bool mount_point_in_fts_cycle(FTSENT const *ent)
{
	FTSENT const *cycle_ent = ent->fts_cycle;

	if (!di_mnt) {
		/* Initialize the set of dev,inode pairs.  */
		di_mnt = di_set_alloc();
		if (!di_mnt)
			xalloc_die();

		fill_mount_table();
	}

	while (ent && ent != cycle_ent) {
		if (di_set_lookup(di_mnt, ent->fts_statp->st_dev, ent->fts_statp->st_ino) > 0) {
			return true;
		}
		ent = ent->fts_parent;
	}

	return false;
}

/* Return the nanosecond component of *ST's access time.  */
static long int
get_stat_atime_ns (struct stat const *st)
{
	return st->st_atim.tv_nsec;
}

/* Return the nanosecond component of *ST's status change time.  */
static long int
get_stat_ctime_ns (struct stat const *st)
{
	return st->st_ctim.tv_nsec;
}

/* Return the nanosecond component of *ST's data modification time.  */
static long int
get_stat_mtime_ns (struct stat const *st)
{
	return st->st_mtim.tv_nsec;
}

/* Return *ST's access time.  */
static struct timespec
get_stat_atime (struct stat const *st)
{
	return (struct timespec) {
		.tv_sec = st->st_atime,
		.tv_nsec = get_stat_atime_ns(st),
	};
}

/* Return *ST's status change time.  */
static struct timespec
get_stat_ctime (struct stat const *st)
{
	return (struct timespec) {
		.tv_sec = st->st_ctime,
		.tv_nsec = get_stat_ctime_ns(st),
	};
}

/* Return *ST's data modification time.  */
static struct timespec
get_stat_mtime (struct stat const *st)
{
	return (struct timespec) {
		.tv_sec = st->st_mtime,
		.tv_nsec = get_stat_mtime_ns(st),
	};
}

static bool
get_file_cachestat(const FTSENT *ent, const struct stat *sb, enum time_type tt, struct muinfo *mui)
{
	bool ret;
	const char *filename = ent->fts_path;
	int fd = -1;

	muinfo_init(mui);

	/* skip calling cachestat for symlinks */
	if (ent->fts_info == FTS_SL) {
		goto out_time;
	}

	fd = open(filename, O_RDONLY, 0400);
	if (fd == -1) {
		/* UNIX domain socket file */
		if (errno == ENXIO) {
			goto out_time;
		}

		/* file does not exist */
		if (access(filename, F_OK)) {
			goto out_time;
		}

		return false;
	}

	struct cachestat cs;
	struct cachestat_range cs_range = { 0, sb->st_size };
	if (cachestat(fd, &cs_range, &cs, 0)) {
		ret = false;
		goto out;
	}

	long pagesize = sysconf(_SC_PAGESIZE);
	mui->cache_size = cs.nr_cache * pagesize;
	mui->dirty_size = cs.nr_dirty * pagesize;
	mui->writeback_size = cs.nr_writeback * pagesize;
	mui->evicted_size = cs.nr_evicted * pagesize;
	mui->recently_evicted_size = cs.nr_recently_evicted * pagesize;

 out_time:
	mui->tmax = (tt == time_mtime ? get_stat_mtime(sb)
		     : tt == time_atime ? get_stat_atime(sb)
		     : get_stat_ctime(sb));

	ret = true;

 out:
	if (fd != -1) {
		close(fd);
	}

	return ret;
}

/* This function is called once for every file system object that fts
   encounters.  fts does a depth-first traversal.  This function knows
   that and accumulates per-directory totals based on changes in
   the depth of the current entry.  It returns true on success.  */

static bool process_file(FTS *fts, FTSENT *ent, char const *format)
{
	bool ok = true;

	struct muinfo mui;
	struct muinfo mui_to_print;

	size_t level;
	static size_t n_alloc;
	/* First element of the structure contains:
	   The sum of the sizes of all entries in the single directory
	   at the corresponding level.  Although this does include the sizes
	   corresponding to each subdirectory, it does not include the size of
	   any file in a subdirectory. Also corresponding last modified date.
	   Second element of the structure contains:
	   The sum of the sizes of all entries in the hierarchy at or below the
	   directory at the specified level.  */

	static struct mulevel *mulvl;

	char const *file = ent->fts_path;
	const struct stat *sb = ent->fts_statp;
	int info = ent->fts_info;

	if (info == FTS_DNR) {
		/* An error occurred, but the size is known, so count it.  */
		// TODO: restore quoting?
		error(0, ent->fts_errno, _("cannot read directory %s"), file);
		ok = false;
	} else if (info != FTS_DP) {
#if 0
		bool excluded = excluded_file_name(exclude, file);
		if (!excluded) {
			/* Make the stat buffer *SB valid, or fail noisily.  */

			if (info == FTS_NSOK) {
				fts_set(fts, ent, FTS_AGAIN);
				MAYBE_UNUSED FTSENT const *e = fts_read(fts);
				assert(e == ent);
				info = ent->fts_info;
			}

			if (info == FTS_NS || info == FTS_SLNONE) {
				// TODO: restore quoting?
				error(0, ent->fts_errno, _("cannot access %s"), file);
				return false;
			}

			/* The --one-file-system (-x) option cannot exclude anything
			   specified on the command-line.  By definition, it can exclude
			   a file or directory only when its device number is different
			   from that of its just-processed parent directory, and mu does
			   not process the parent of a command-line argument.  */
			if (fts->fts_options & FTS_XDEV
			    && FTS_ROOTLEVEL < ent->fts_level && fts->fts_dev != sb->st_dev)
				excluded = true;
		}

		if (excluded
		    || (!opt_count_all && (hash_all || (!S_ISDIR(sb->st_mode) && 1 < sb->st_nlink))
			&& !hash_ins(di_files, sb->st_ino, sb->st_dev))) {
			/* If ignoring a directory in preorder, skip its children.
			   Ignore the next fts_read output too, as it's a postorder
			   visit to the same directory.  */
			if (info == FTS_D) {
				fts_set(fts, ent, FTS_SKIP);
				MAYBE_UNUSED FTSENT const *e = fts_read(fts);
				assert(e == ent);
			}

			return true;
		}
#endif

		switch (info) {
		case FTS_D:
			return true;

		case FTS_ERR:
			/* An error occurred, but the size is known, so count it.  */
			// TODO: restore quoting?
			error(0, ent->fts_errno, "%s", file);
			ok = false;
			break;

		case FTS_DC:
			/* If not following symlinks and not a (bind) mount point.  */
			if (cycle_warning_required(fts, ent)
			    && !mount_point_in_fts_cycle(ent)) {
				emit_cycle_warning(file);
				return false;
			}
			return true;
		}
	}

	if (!get_file_cachestat(ent, sb, time_type, &mui)) {
		error(EXIT_FAILURE, errno, "getting file cache stat for %s failed", ent->fts_path);
	}

	level = ent->fts_level;
	mui_to_print = mui;

	if (n_alloc == 0) {
		n_alloc = level + 10;
		mulvl = xcalloc(n_alloc, sizeof *mulvl);
	} else {
		if (level == prev_level) {
			/* This is usually the most common case.  Do nothing.  */
		} else if (level > prev_level) {
			/* Descending the hierarchy.
			   Clear the accumulators for *all* levels between prev_level
			   and the current one.  The depth may change dramatically,
			   e.g., from 1 to 10.  */

			if (n_alloc <= level) {
				mulvl = xnrealloc(mulvl, level, 2 * sizeof *mulvl);
				n_alloc = level * 2;
			}

			for (size_t i = prev_level + 1; i <= level; i++) {
				muinfo_init(&mulvl[i].ent);
				muinfo_init(&mulvl[i].subdir);
			}
		} else {	/* level < prev_level */
			/* Ascending the hierarchy.
			   Process a directory only after all entries in that
			   directory have been processed.  When the depth decreases,
			   propagate sums from the children (prev_level) to the parent.
			   Here, the current level is always one smaller than the
			   previous one.  */
			assert(level == prev_level - 1);

			muinfo_add(&mui_to_print, &mulvl[prev_level].ent);
			if (!opt_separate_dirs)
				muinfo_add(&mui_to_print, &mulvl[prev_level].subdir);
			muinfo_add(&mulvl[level].subdir, &mulvl[prev_level].ent);
			muinfo_add(&mulvl[level].subdir, &mulvl[prev_level].subdir);
		}
	}

	prev_level = level;

	/* Let the size of a directory entry contribute to the total for the
	   containing directory, unless --separate-dirs (-S) is specified.  */
	if (!(opt_separate_dirs && IS_DIR_TYPE(info)))
		muinfo_add(&mulvl[level].ent, &mui);

	/* Even if this directory is unreadable or we can't chdir into it,
	   do let its size contribute to the total. */
	muinfo_add(&tot_mui, &mui);

	if ((IS_DIR_TYPE(info) && level <= max_depth)
	    || (opt_all && level <= max_depth)
	    || level == 0) {
		/* Print or elide this entry according to the --threshold option.  */
		uintmax_t v = mui_to_print.cache_size;
		if (opt_threshold < 0 ? v <= -opt_threshold : v >= opt_threshold) {
			mu_print_size(&mui_to_print, file, format);
		}
	}

	return ok;
}

/* Recursively print the sizes of the directories (and, if selected, files)
   named in FILES, the last entry of which is null.
   BIT_FLAGS controls how fts works.
   Return true if successful.  */

static bool mu_files(char **files, int bit_flags, char const *format)
{
	bool ok = true;

	if (*files) {
		FTS *fts = xfts_open(files, bit_flags, NULL);

		while (true) {
			FTSENT *ent;

			ent = fts_read(fts);
			if (ent == NULL) {
				if (errno != 0) {
					// TODO: restore quoting?
					error(0, errno, _("fts_read failed: %s"), fts->fts_path);
					ok = false;
				}

				/* When exiting this loop early, be careful to reset the
				   global, prev_level, used in process_file.  Otherwise, its
				   (level == prev_level - 1) assertion could fail.  */
				prev_level = 0;
				break;
			}
			FTS_CROSS_CHECK(fts);

			ok &= process_file(fts, ent, format);
		}

		if (fts_close(fts) != 0) {
			error(0, errno, _("fts_close failed"));
			ok = false;
		}
	}

	return ok;
}

int main(int argc, char **argv)
{
	char *cwd_only[2];
	bool max_depth_specified = false;
	bool ok = true;
	char *files_from = NULL;

	/* Bit flags that control how fts works.  */
	int bit_flags = FTS_NOSTAT;

	/* Select one of the three FTS_ options that control if/when
	   to follow a symlink.  */
	int symlink_deref_bits = FTS_PHYSICAL;

	/* If true, display only a total for each argument. */
	bool opt_summarize_only = false;

	cwd_only[0] = ".";
	cwd_only[1] = NULL;

	setlocale(LC_ALL, "");
	bindtextdomain(PACKAGE, LOCALEDIR);
	textdomain(PACKAGE);

	close_stdout_atexit();

#if 0
	exclude = new_exclude();
#endif

	/* TODO
	human_options(getenv("MU_BLOCK_SIZE"), &human_output_opts, &output_block_size);
	*/

	muinfo_init(&tot_mui);

	char *format = NULL;

	while (true) {
		int oi = -1;
		int c = getopt_long(argc, argv, "0abd:cf:hHklmst:xB:DLPSX:",
				    long_options, &oi);
		if (c == -1)
			break;

		switch (c) {
#if DU_DEBUG
		case FTS_DEBUG:
			fts_debug = true;
			break;
#endif

		case '0':
			opt_nul_terminate_output = true;
			break;

		case 'a':
			opt_all = true;
			break;

		case 'b':
			human_readable = 0;
			break;

		case 'c':
			print_grand_total = true;
			break;

		case 'f':
			format = optarg;
			break;

		case 'h':
			human_readable = 1;
			human_output_opts = SIZE_SUFFIX_1LETTER;
			output_block_size = 1;
			break;

		case HUMAN_SI_OPTION:
			human_readable = 1;
			human_output_opts = SIZE_DECIMAL_2DIGITS;
			output_block_size = 1;
			break;

		case 'k':
			// TODO: implement K
			human_readable = 1;
			human_output_opts = SIZE_SUFFIX_1LETTER;
			output_block_size = 1024;
			break;

		case 'd':	/* --max-depth=N */
			max_depth_specified = true;
			max_depth = strtoimax(optarg, NULL, 0);
			break;

		case 'm':
			human_output_opts = 0;
			output_block_size = 1024 * 1024;
			break;

		case 'l':
			opt_count_all = true;
			break;

		case 's':
			opt_summarize_only = true;
			break;

		case 't':
			opt_threshold = strtoimax(optarg, NULL, 0);
#if 0
			{
				enum strtol_error e;
				e = xstrtoimax(optarg, NULL, 0, &opt_threshold, "kKmMGTPEZYRQ0");
				if (e != LONGINT_OK)
					xstrtol_fatal(e, oi, c, long_options, optarg);
				if (opt_threshold == 0 && *optarg == '-') {
					/* Do not allow -0, as this wouldn't make sense anyway.  */
					error(EXIT_FAILURE, 0,
					      _("invalid --threshold argument '-0'"));
				}
			}
#endif
			break;

		case 'x':
			bit_flags |= FTS_XDEV;
			break;

		case 'B':
			{
				/* TODO
				enum strtol_error e = human_options(optarg, &human_output_opts,
								    &output_block_size);
				if (e != LONGINT_OK)
					xstrtol_fatal(e, oi, c, long_options, optarg);
				*/
			}
			break;

		case 'H':	/* NOTE: before 2008-12, -H was equivalent to --si.  */
		case 'D':
			symlink_deref_bits = FTS_COMFOLLOW | FTS_PHYSICAL;
			break;

		case 'L':	/* --dereference */
			symlink_deref_bits = FTS_LOGICAL;
			break;

		case 'P':	/* --no-dereference */
			symlink_deref_bits = FTS_PHYSICAL;
			break;

		case 'S':
			opt_separate_dirs = true;
			break;

		case 'X':
#if 0
			if (add_exclude_file(add_exclude, exclude, optarg, EXCLUDE_WILDCARDS, '\n')) {
				// TODO: restore quoting?
				error(0, errno, "%s", optarg);
				ok = false;
			}
#endif
			error(0, 0, _("option -X is not implemented"));
			exit(EXIT_FAILURE);
			break;

		case FILES0_FROM_OPTION:
#if 0
			files_from = optarg;
#endif
			error(0, 0, _("option --files0-from is not implemented"));
			exit(EXIT_FAILURE);
			break;

		case EXCLUDE_OPTION:
#if 0
			add_exclude(exclude, optarg, EXCLUDE_WILDCARDS);
#endif
			error(0, 0, _("option --exclude is not implemented"));
			exit(EXIT_FAILURE);
			break;

		case TIME_OPTION:
			opt_time = true;
			for (unsigned long i = 0; i < ARRAY_SIZE(time_args); i++)
				if (streq(optarg, time_args[i])) {
					time_type = time_types[i];
					break;
				}
			break;

		case TIME_STYLE_OPTION:
			time_style = optarg;
			break;

		case CHAR_MIN - 2:
			/* fallthrough */
		case CHAR_MIN - 3:
			exit (EXIT_SUCCESS);
			break;

		default:
			ok = false;
		}
	}

	if (!ok)
		usage(EXIT_FAILURE);

	if (opt_all && opt_summarize_only) {
		error(0, 0, _("cannot both summarize and show all entries"));
		usage(EXIT_FAILURE);
	}

	if (opt_summarize_only && max_depth_specified && max_depth == 0) {
		error(0, 0, _("warning: summarizing is the same as using --max-depth=0"));
	}

	if (opt_summarize_only && max_depth_specified && max_depth != 0) {
		error(0, 0, _("warning: summarizing conflicts with --max-depth=%td"), max_depth);
		usage(EXIT_FAILURE);
	}

	if (opt_summarize_only)
		max_depth = 0;

	/* Process time style if printing last times.  */
	if (opt_time) {
		if (!time_style) {
			time_style = getenv("TIME_STYLE");

			/* Ignore TIMESTYLE="locale", for compatibility with ls.  */
			if (!time_style || streq(time_style, "locale"))
				time_style = "long-iso";
			else if (*time_style == '+') {
				/* Ignore anything after a newline, for compatibility
				   with ls.  */
				char *p = strchr(time_style, '\n');
				if (p)
					*p = '\0';
			} else {
				/* Ignore "posix-" prefix, for compatibility with ls.  */
				static char const posix_prefix[] = "posix-";
				static const size_t prefix_len = sizeof posix_prefix - 1;
				while (strncmp(time_style, posix_prefix, prefix_len) == 0)
					time_style += prefix_len;
			}
		}

		if (*time_style == '+')
			time_format = time_style + 1;
		else {
			enum time_style time_style = long_iso_time_style;
			for (unsigned long i = 0; i < ARRAY_SIZE(time_style_args); i++)
				if (streq(optarg, time_style_args[i])) {
					time_style = time_style_types[i];
					break;
				}
			switch (time_style) {
			case full_iso_time_style:
				time_format = "%Y-%m-%d %H:%M:%S.%N %z";
				break;

			case long_iso_time_style:
				time_format = "%Y-%m-%d %H:%M";
				break;

			case iso_time_style:
				time_format = "%Y-%m-%d";
				break;
			}
		}
	}

#if 0
	struct argv_iterator *ai;
	if (files_from) {
		/* When using --files0-from=F, you may not specify any files
		   on the command-line.  */
		if (optind < argc) {
			// TODO: restore quoting?
			error(0, 0, _("extra operand %s"), argv[optind]);
			fprintf(stderr, "%s\n",
				_("file operands cannot be combined with --files0-from"));
			usage(EXIT_FAILURE);
		}

		if (!(streq(files_from, "-") || freopen(files_from, "r", stdin)))
			// TODO: restore quoting?
			error(EXIT_FAILURE, errno, _("cannot open %s for reading"),
			      files_from);

		ai = argv_iter_init_stream(stdin);

		/* It's not easy here to count the arguments, so assume the
		   worst.  */
		hash_all = true;
	} else {
		char **files = (optind < argc ? argv + optind : cwd_only);
		ai = argv_iter_init_argv(files);

		/* Hash all dev,ino pairs if there are multiple arguments, or if
		   following non-command-line symlinks, because in either case a
		   file with just one hard link might be seen more than once.  */
		hash_all = (optind + 1 < argc || symlink_deref_bits == FTS_LOGICAL);
	}

	if (!ai)
		xalloc_die();
#endif

	/* Initialize the set of dev,inode pairs.  */
	di_files = di_set_alloc();
	if (!di_files)
		xalloc_die();

	/* If not hashing everything, process_file won't find cycles on its
	   own, so ask fts_read to check for them accurately.  */
	if (opt_count_all || !hash_all)
		bit_flags |= FTS_TIGHT_CYCLE_CHECK;

	bit_flags |= symlink_deref_bits;
	static char *temp_argv[] = { NULL, NULL };

#if 0
	while (true) {
		bool skip_file = false;
		enum argv_iter_err ai_err;
		char *file_name = argv_iter(ai, &ai_err);
		if (!file_name) {
			switch (ai_err) {
			case AI_ERR_EOF:
				goto argv_iter_done;
			case AI_ERR_READ:
				// TODO: restore quoting?
				error(0, errno, _("%s: read error"), files_from);
				ok = false;
				goto argv_iter_done;
			case AI_ERR_MEM:
				xalloc_die();
			case AI_ERR_OK:
			default:
				assert(!"unexpected error code from argv_iter");
			}
		}
		if (files_from && streq(files_from, "-") && streq(file_name, "-")) {
			/* Give a better diagnostic in an unusual case:
			   printf - | du --files0-from=- */
			// TODO: restore quoting?
			error(0, 0, _("when reading file names from stdin, "
				      "no file name of %s allowed"), file_name);
			skip_file = true;
		}

		/* Report and skip any empty file names before invoking fts.
		   This works around a glitch in fts, which fails immediately
		   (without looking at the other file names) when given an empty
		   file name.  */
		if (!file_name[0]) {
			/* Diagnose a zero-length file name.  When it's one
			   among many, knowing the record number may help.
			   FIXME: currently print the record number only with
			   --files0-from=FILE.  Maybe do it for argv, too?  */
			if (files_from == NULL) {
				error(0, 0, "%s", _("invalid zero-length file name"));
			} else {
				/* Using the standard 'filename:line-number:' prefix here is
				   not totally appropriate, since NUL is the separator, not NL,
				   but it might be better than nothing.  */
				size_t file_number = argv_iter_n_args(ai);
				// TODO: restore quoting?
				error(0, 0, "%s:%td: %s", files_from,
				      file_number, _("invalid zero-length file name"));
			}
			skip_file = true;
		}

		if (skip_file)
			ok = false;
		else {
			temp_argv[0] = file_name;
			ok &= mu_files(temp_argv, bit_flags, format);
		}
	}
 argv_iter_done:

	argv_iter_free(ai);
#endif

	for (int i = optind; i < argc; i++) {
		temp_argv[0] = argv[i];
		ok &= mu_files(temp_argv, bit_flags, format);
	}

	di_set_free(di_files);
	if (di_mnt)
		di_set_free(di_mnt);

	// TODO: restore quoting?
	if (files_from && (ferror(stdin) || fclose(stdin) != 0) && ok)
		error(EXIT_FAILURE, 0, _("error reading %s"), files_from);

	if (print_grand_total) {
		mu_print_size(&tot_mui, _("total"), format);
	}

	return ok ? EXIT_SUCCESS : EXIT_FAILURE;
}
