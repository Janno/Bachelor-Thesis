#!/usr/bin/python

import re
from sys import stdin, argv

text = stdin.read()

module = argv[1]
target = argv[2]

for (D, T, N) in re.findall('((Definition|Inductive|Record|Fixpoint)\s+([^:\s]+).*?:=.*?\.)', text, re.S):
    f = file('%s/%s_%s' % (target, module, N), 'w')
    f.write(D)
    f.close()
    #print N, '(%s)' % T
    #print D 

for (D, H, T, N, S, E) in re.findall('(((Lemma)\s+(\S+).*?:(.*?)\.)\s+Proof\..*?(Qed|Defined)\.)', text, re.S):
    f = file('%s/%s_%s' % (target, module, N), 'w')
    f.write(D)
    f.close()
    f = file('%s/%s_%s_head' % (target, module, N), 'w')
    f.write(H)
    f.close()
    #print N, '(%s)' % T
    #print D 
