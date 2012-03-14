#!/bin/bash

grep -n 'in <a' $1 | sort -k 2 -t ':' | uniq -f 1 > $2.tmp
grep -nv 'in <a' $1 >> $2.tmp
sort -n -k 1 -t ':' $2.tmp | cut -f2- -d ':' >> $2
rm $2.tmp
