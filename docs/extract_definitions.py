#!/usr/bin/python

import re
from sys import stdin, argv

text1 = stdin.read()
text = re.sub(r'\(\*(.+?)\*\)',r'',text1, flags=re.S + re.I)

module = argv[1]
target = argv[2]

for (D, T, N) in re.findall('((Function|Definition|Inductive|Record|Fixpoint)\s+([^:\s]+).*?:=.*?\.)[^+(12]', text, re.S):
    f = file('%s/%s_%s' % (target, module, N), 'w')
    f.write(D)
    f.close()

for (D, H, T, N, S, E) in re.findall('(((Lemma)\s+([^:\s]+).*?:(.*?)\.)\s*Proof\..*?(Qed|Defined)\.)[^+(12]', text, re.S):
    f = file('%s/%s_%s' % (target, module, N), 'w')
    f.write(D)
    f.close()
    f = file('%s/%s_%s_head' % (target, module, N), 'w')
    f.write(H)
    f.close()

for (D, _, N, T) in re.findall('((Variable)\s+([^:\s]+)\s*?:(.+?)\.)[^+]', text, re.S):
    f = file('%s/%s_%s' % (target, module, N), 'w')
    f.write(D)
    f.close()
