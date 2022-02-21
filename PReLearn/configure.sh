#!/bin/sh
debug=no
logging=unknown
check=unknown
die () {
  echo "*** 'configure' error: $*" 1>&2
  exit 1
}
usage () {
cat <<EOF
usage: configure.sh [ <option> ... ]

where <option> is one of the following

-h | --help     print this command line option summary
-g | --debug    compile with debugging support
-c | --check    compile with assertion checking support (default for '-g')
-l | --logging  compile with logging support (default for '-g')
EOF
}
while [ $# -gt 0 ]
do
  case $1 in
    -h|--help) usage; exit 0;;
    -g|--debug) debug=yes;;
    -c|--check) check=yes;;
    -l|--logging) logging=yes;;
    *) die "invalid option '$1' (try '-h')";;
  esac
  shift
done
rm -f makefile
CC=gcc
CFLAGS="-Wall"
[ $check = unknown ] && check=$debug
[ $logging = unknown ] && logging=$debug
if [ $debug = yes ]
then
  CFLAGS="$CFLAGS -g3"
else
  CFLAGS="$CFLAGS -O3"
fi
[ $check = no ] && CFLAGS="$CFLAGS -DNDEBUG"
[ $logging = yes ] && CFLAGS="$CFLAGS -DLOG"
[ $logging = no ] && CFLAGS="$CFLAGS -DNLOG"
echo "$CC $CFLAGS"
sed -e "s,@CC@,$CC," -e "s,@CFLAGS@,$CFLAGS," makefile.in > makefile
