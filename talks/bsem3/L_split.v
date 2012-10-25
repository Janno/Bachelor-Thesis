Lemma L_split X x y z w:
    w \in L^(z |: X) x y ->
    w \in L^X x y \/
    exists w1, exists w2,
        w = w1 ++ w2 /\
        size w2 < size w /\
        w1 \in L^X x z /\
        w2 \in L^(z |: X) z y
