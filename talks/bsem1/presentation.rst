.. header::
    **###Title###**

.. footer::
    **###Section###**
    

Constructive Formalization of Regular Languages
==================================================
Jan-Oliver Kaiser
--------------------------------------------

.. raw:: pdf

    Spacer 0, 50

.. class:: centered

Advisors: Christian Doczkal, Gert Smolka

.. class:: centered

Supervisor: Gert Smolka


.. raw:: pdf

    PageBreak 34Page

--------
Contents
--------

#. Motivation
#. Quick Recap
#. Previous work
#. Our development
#. Roadmap


.. raw:: pdf

    PageBreak 34Page

----------
Motivation
----------

We want to develop an elegant formalization of regular languages in Coq based on finite automata. 

There are several reasons for choosing this topic and our specific approach:

* Strong interest in formalizations in this area.
* Few formalizations of regular languages in Coq, most of them very long or incomplete.
* Most formalizations avoid finite automata in favor of regular expressions. 
  Regular expressions (with Brzozowski derivatives) lead to more complex but also more performant algorithms.

.. raw:: pdf

    PageBreak normalPage

-----------
Quick Recap
-----------

We use extended **regular expressions** (regexp):

:math:`r,s \, ::= \, \emptyset \, | \, \varepsilon \, | \, a \, | \, r s \, | \, r + s \, | \, r & s \, | \, r^{\ast} \, | \, \neg r`

* :math:`\mathcal{L}(\emptyset) := \{\}`
* :math:`\mathcal{L}(\varepsilon) := \{ \varepsilon \}`
* :math:`\mathcal{L}(a) := \{ a \}`
* :math:`\mathcal{L}(r s) := \mathcal{L}(r) \cdot \mathcal{L}(s)`
* :math:`\mathcal{L}(r + s) := \mathcal{L}(r) \cup \mathcal{L}(s)`
* :math:`\mathcal{L}(r & s) := \mathcal{L}(r) \cap \mathcal{L}(s)`
* :math:`\mathcal{L}(r^{\ast}) := \mathcal{L}(r)^{\ast}`
* :math:`\mathcal{L}(\neg r) := \overline{\mathcal{L}(r)}`

.. raw:: pdf

    PageBreak normalPage

**Derivatives of Regular Expressions** (1964), *Janusz Brzozowski*:

* der a :math:`\emptyset` = :math:`\emptyset`
* der a :math:`\varepsilon` = :math:`\emptyset`
* der a b = if a = b then :math:`\varepsilon \,` else :math:`\emptyset`
* der a (r s) = if :math:`\delta(r) \,` then (der a s) + ((der a r) s)  else (der a r) s 
  
  with :math:`\delta(r) \, = \, true \, \Leftrightarrow \, \varepsilon \, \in \, \mathcal{L}(r)`. (easily decidable by recursion on r)

  ...


.. raw:: pdf

    Spacer 0, 10

**Theorem 1**: :math:`w \, \in \, \mathcal{L}(r) \,` if and only if the derivative of r with respect to :math:`w_1 .. \, w_{|w|}\,` accepts :math:`\varepsilon`.

.. raw:: pdf
    
    Spacer 0, 10

**Theorem 2**: The set of derivatives of r is *closed under derivation* and *finite* up to similarity.

.. raw:: pdf

    PageBreak normalPage

Regular languages are also exactly those languages accepted by **finite automata** (FA).

Our definition of FA over an alphabet :math:`\Sigma \,`:

* The finite set of states Q
* The initial state :math:`s_0 \in \,` Q
* The (decidable) transition relation :math:`\Delta \, \in \,` (Q, :math:`\Sigma`, Q) 
  
  Deterministic FA: :math:`\Delta \,` is functional and **total**.
   
* The set of finite states F, F :math:`\subseteq \,` Q

.. raw:: pdf

    Spacer 0, 10

Let A be a FA:

:math:`\mathcal{L}(A) :=`

:math:`\{ w \, | \, \exists \, s_1, \, .. \, , \, s_{|w|} \, \in \, Q \, s.t. \, (\forall \, i : \, 0 \, < \, i \, \leq \, n \, \rightarrow \, (s_{i-1}, w_i, s_i) \, \in \, \Delta_A) \, \wedge \, s_{|w|} \in \, F_A \, \}`


.. raw:: pdf

    PageBreak halfPage

Finally, regular languages are also characterized by the Myhill-Nerode theorem (MH).

First, we define an  equivalence relation on L (MH relation):

:math:`x \, R_{L} \, y \, := \, \forall z, \, x \cdot z \, \in \, L \, \Leftrightarrow \, y \cdot z \, \in \, L` 

.. raw:: pdf

    Spacer 0, 10

**Myhill-Nerode theorem**: L is regular if and only if :math:`R_{L}` divides L into a finite number of equivalence classes.

.. raw:: pdf

    PageBreak normalPage


-------------
Previous work
-------------

* **The first constructive formalization of MH**.
  
    Based on FA. 
  
    Implemented in Nuprl.

    Focus on clear formalization. 

    Close to what we want to do.

  (*Constable, Jackson, Naumov, Uribe*, 1997)

.. raw:: pdf

    Spacer 0, 10

* Decision procedure for regexp equivalence.

    Based on Brzozowski derivatives.

    Only soundness proof, *no proof of termination or completeness*.

    Implemented in Isabelle. 

    Focus on simplicity, small regexps.

  (*Krauss, Nipkow*, 2011)
  

.. raw:: pdf

    PageBreak

* Decision procedure for regexp equivalence.
    
    Based on FA, matrices.

    Implemented in Coq.

    Focus on performance. Outperforms every other solution so far.

  (*Braibant, Pous*, 2011)


.. raw:: pdf

    Spacer 0, 10

* **Decision Procedure for regexp equivalence**.
    
    Based on Brzozowski derivatives.
    
    Implemented in Coq.

    Proof of termination given.

    Introduces the notion of *inductively finite sets*.

  (*Coquand, Siles*, 2011)

.. raw:: pdf

    PageBreak normalPage

* **First formalization of MH based on regexp**. 

    Based on Brzozowski derivatives.

    Implemented in Isabelle.

    The first formalization of MH in Isabelle.

  (*Wu, Zhang, Urban*, 2011)

.. raw:: pdf

    Spacer 0, 10

* Decision Procedure for regexp equivalence.

    Based on Brzozowski derivatives.

    Implemented in Coq.

    Translation of the work done by Krauss and Nipkow to Coq.

    Adds proof of termination.
  
  (*Moreira, Pereira, de Sousa*, 2011)


.. raw:: pdf

    PageBreak halfPage

---------------
Our Development
---------------

* We want to focus on elegance, not performance. 
* Our main goals are MH and the decidability of regexp equivalence.
* We use finite automata.
  
  They are not at all impractical. (Partly thanks to Ssreflect's finType)

.. raw:: pdf

    PageBreak normalPage

.. class:: bigtext

**Quick examples**

.. code-block:: Haskell

    Record dfa : Type :=
      dfaI {
        dfa_state :> finType;
        dfa_s0: dfa_state;
        dfa_fin: pred dfa_state;
        dfa_step: dfa_state -> char -> dfa_state
      }.

    Fixpoint dfa_accept A (x: A) w :=
    match w with
      | [::] => dfa_fin A x
      | a::w => dfa_accept A (dfa_step A x a) w
    end.

.. code-block:: Haskell

    Record nfa : Type :=
      nfaI {
        nfa_state :> finType;
        nfa_s0: nfa_state;
        nfa_fin: pred nfa_state;
        nfa_step: nfa_state -> char -> pred nfa_state
      }.

    Fixpoint nfa_accept A (x: A) w :=
    match w with
      | [::] => nfa_fin A x
      | a::w => existsb y, (nfa_step A x a y) && nfa_accept A y w
    end.

.. raw:: pdf
    
    PageBreak 34Page

50% of **NFA** :math:`\Rightarrow` **DFA** (powerset construction)

.. code-block:: Haskell

    Lemma nfa_to_dfa_correct2 (X: nfa_to_dfa) w:
      dfa_accept nfa_to_dfa X w -> existsb x, (x \in X) && nfa_accept A x w.
    Proof. elim: w X => [| a w IHw] X.
      by [].
    move/IHw => /existsP [] y /andP [].
    rewrite /dfa_step /nfa_to_dfa /= cover_imset.
    move/bigcupP => [] x H0 H1 H2.
    apply/existsP. exists x. rewrite H0 andTb.
    apply/existsP. exists y. move: H1. rewrite in_set => ->.
    exact: H2.
    Qed.


.. raw:: pdf

    PageBreak halfPage

-------
Roadmap
-------

.. raw:: pdf
    
    Spacer 0, 10


#. regexp :math:`\Rightarrow\,` FA: closure of FA under :math:`\cdot`, :math:`\cup`, :math:`\cap`, :math:`\ast`, :math:`\neg`. (**Done**)

   
#. Emptiness test on FA. (:math:`\mathcal{L}(A) = \emptyset \,`)
#. Dedicedability of regexp equivalence:

    :math:`\mathcal{L}(r) = \mathcal{L}(s)`
    :math:`\Leftrightarrow`
    :math:`\mathcal{L}(\mathcal{A}(r) \cap \overline{\mathcal{A}(s)}) = \emptyset \, \wedge`
    :math:`\mathcal{L}(\overline{\mathcal{A}(r)} \cap \mathcal{A}(s)) = \emptyset`
#. FA :math:`\Rightarrow\,` regexp.

.. raw:: pdf
    
    PageBreak 34Page

5. Finally, we want to prove the Myhill-Nerode theorem.

   Constable et al. establish a direct equivalence between MH and FA.

   This requires proof of:

   - FA induce an equivalence relation on words
   - This relation is invariant under extension.
   - This relation is a refinement of the MH relation.
   - A finite number of equivalence classes under the MH relation 
     induce a set of states for a FA which accepts exactly the union of these equivalence classes.

.. raw:: pdf
    
    PageBreak halfPage

.. class:: end

Thank you for your attention.

.. raw:: pdf

    PageBreak normalPage

.. class:: bigtext

    **References**
::

     Constructively formalizing automata theory (1997)

      Robert L. Constable, Paul B. Jackson, Pavel Naumov, Juan C. Uribe


     Proof Pearl: Regular Expression Equivalence and Relation Algebra (2011)

      Alexander Krauss, Tobias Nipkow


     Deciding Kleene Algebras in Coq (2011)

      Thomas Braibant, Damien Pous


     A Decision Procedure for Regular Expression Equivalence in Type Theory (2011)

      Thierry Coquand, Vincent Siles


     A Formalisation of the Myhill-Nerode Theorem based on Regular Expressions (Proof Pearl) (2011)

      Chunhan Wu, Xingyuan Zhang, Christian Urban


     Deciding Regular Expressions (In-)Equivalence in Coq (2011)
      
      Nelma Moreira, David Pereira, Simão Melo de Sousa



.. raw:: pdf

    PageBreak halfPage

---------------
Extras
---------------

.. raw:: pdf

    PageBreak normalPage

With **Theorem 2**, we can formulate a system of equations:

.. raw:: pdf
    
    Spacer 0, 25

:math:`r_0 = \sum^{n}_{i=0} \, a_{0, i} \, r_{0,i}`

.. raw:: pdf
    
    Spacer 0, 25

:math:`r_1 = \sum^{n}_{i=0} \, a_{1, i} \, r_{1,i}`

.. raw:: pdf
    
    Spacer 0, 20

...

.. raw:: pdf
    
    Spacer 0, 20

:math:`r_n = \sum^{n}_{i=0} \, a_{n, i} \, r_{n,i}`

.. raw:: pdf
    
    Spacer 0, 25

where 

  :math:`r_{j, i} = \emptyset \, \vee \, r_{j,i} = r_i`,

  :math:`\{r_k | 0 < k \leq n \}\,` is the set of derivatives of :math:`r_0`

and 

  :math:`r_j = ... \, + \, a_{j,i} \, r_i \, + ... \,  \Leftrightarrow \, der \, r_j \, a_{j, i} \, = \, r_i`.
