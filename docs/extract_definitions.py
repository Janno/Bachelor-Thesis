#!/usr/bin/python

import re
from sys import stdin, argv

T = stdin.read()

module = argv[1]
target = argv[2]

for (D, T, N) in re.findall('((Definition|Inductive|Record|Fixpoint)\s+(\S+).*?:=.*?\.)', T, re.S):
    f = file('%s/%s_%s' % (target, module, N), 'w')
    f.write(D)
    f.close()
    #print N, '(%s)' % T
    #print D 

