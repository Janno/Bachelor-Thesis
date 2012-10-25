  Lemma L_split k' i j a w:
      let k := k_ord k' in
      (a::w) \in L^k'.+1 i j ->
      (a::w) \in L^k' i j \/
      exists w1, exists w2,
      a::w = w1 ++ w2 /\
      w1 != [::] /\
      w1 \in L^k' i (enum_val k) /\
      w2 \in L^k'.+1 (enum_val k) j.
