#!/bin/sh
TMPFILE="${2}.tmp"
grep -n 'in <a' $1 | sort -k 2 -t ':' | uniq -f 1 > "$TMPFILE"
grep -nv 'in <a' $1 >> "$TMPFILE"
sort -n -k 1 -t ':' "$TMPFILE" | cut -f2- -d ':' >> "$2"
rm "$TMPFILE"
