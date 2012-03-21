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

There are several reasons for chosing this topic and our specific approach:

* Strong interest in formalizations in this area.
* Few formalizations of regular languages in Coq, most of them very long or incomplete.
* Most formalizations avoid finite automata in favor of regular expressions.
* It's fun.

.. raw:: pdf

    PageBreak 34Page

-----------
Quick Recap
-----------

The regular languages over an alphabet :math:`\Sigma\,` can be defined recursively:

* :math:`\emptyset \, \in \, RL_{\Sigma}`
* :math:`a \, \in \, \Sigma \, \rightarrow \, \{a\} \, \in \, RL_{\Sigma}`
* :math:`A,B \, \in \, RL_{\Sigma} \, \rightarrow \, A \, \cup \, B \, \in \, RL_{\Sigma}`
* :math:`A,B \, \in \, RL_{\Sigma} \, \rightarrow \, A \, \bullet \, B \, \in \, RL_{\Sigma}`
* :math:`A \, \in \, RL_{\Sigma} \, \rightarrow \, A^{\ast} \, \in \, RL_{\Sigma}`

.. raw:: pdf

    PageBreak 34Page

Additionally, regular languages are also exactly those languages accepted by **finite automata**.

One possible definition of FA over an alphabet :math:`\Sigma \,` is:

* a finite set of states Q
* an initial state :math:`s_0 \in \,` Q
* a transition relation :math:`\Delta \, \in \,` (Q, :math:`\Sigma`, Q)
* a set of finite states F, F :math:`\sqsubseteq \,` Q

.. raw:: pdf

    Spacer 0, 10

Let A be a FA.

:math:`\mathcal{L}(A) := \{ w \, | \, \exists s_1, \, ... \, s_{|w|} \, \in \, Q \, s.t. \, \forall \, i : \, 0 \, < \, i \, \leq \, n \, \rightarrow \, (s_{i-1}, w_i, s_i) \, \in \, \Delta \}`

.. raw:: pdf

    PageBreak 34Page

They can also be defined using **regular expressions** which are usually converted to FA for matching:

* :math:`\emptyset \, \in \, regexp_{\Sigma}, \, \mathcal{L}(\emptyset) := \{\}`
* :math:`\varepsilon \, \in \, regexp_{\Sigma}, \, \mathcal{L}(\varepsilon) := \{ \varepsilon \}`
* :math:`a \, \in \, \Sigma \, \rightarrow \, a \in \, regexp_{\Sigma}, \, \mathcal{L}(a) := \{ a \}`
* :math:`r,s \, \in \, RL_{\Sigma} \, \rightarrow \, (r + s) \in \, regexp_{\Sigma}, \, \mathcal{L}(r + s) := \mathcal{L}(r) \cup \mathcal{L}(s)`
* :math:`r,s \, \in \, RL_{\Sigma} \, \rightarrow \, (r s) \in \, regexp_{\Sigma}, \, \mathcal{L}(r \bullet s) := \mathcal{L}(r) \bullet \mathcal{L}(s)`
* :math:`r \, \in \, RL_{\Sigma} \, \rightarrow \, r^{\ast} \in \, regexp_{\Sigma}, \, \mathcal{L}(r^{\ast}) := \mathcal{L}(r)^{\ast}`

.. raw:: pdf

    PageBreak normalPage

Brzozowski showed that matching words against regular expressions can be done without converting them to FA. (1964, Derivatives of Regular Expressions)


* der a :math:`\emptyset` = :math:`\emptyset`
* der a :math:`\varepsilon` = :math:`\emptyset`
* der a b = if a = b then :math:`\varepsilon` else :math:`\emptyset`
* der a (r + s) = (der a r) + (der a s)
* der a (r s) = if :math:`\delta(r) \,` then (der a s) + ((der a r) s)  else (der a r) s 
* der a (r*) = (der a r) r*

with :math:`\delta(r) \, = \, true \, \Leftrightarrow \, \varepsilon \, \in \, \mathcal{L}(r)`.

.. raw:: pdf

    Spacer 0, 10

:math:`w \, \in \, \mathcal{L}(r) \,` if and only if the derivative of r with respect to :math:`w_1 .. \, w_{|w|}` accepts :math:`\varepsilon`.


.. raw:: pdf

    PageBreak halfPage

Finally, regular languages are also characterized by the Myhill-Nerode theorem.

* First, we define a binary relation on L:

  :math:`R_{L} x y := \neg \exists z, \, x \bullet z \, \in \, L \, \oplus \, y \bullet z \, \in \, L` 

.. raw:: pdf

    Spacer 0, 10

* L is regular if and only if :math:`R_{L}` divides L into a finite number of equivalence classes.

.. raw:: pdf

    PageBreak normalPage


-------------
Previous work
-------------

* Constructively formalizing automata theory (2000)

  *Robert L. Constable, Paul B. Jackson, Pavel Naumov, Juan C. Uribe*

  **PA**: Nuprl

  The first constructive formalization of MH.

  Based on **FA**.

.. raw:: pdf

    Spacer 0, 10

* Proof Pearl: Regular Expression Equivalence and Relation Algebra (2011)

  *Alexander Krauss, Tobias Nipkow*
  
  **PA**: Isabelle

  Based on **derivatives of regexps**. No proof of termination.

.. raw:: pdf

    PageBreak

* Deciding Kleene Algebras in Coq (2011)

  *Thomas Braibant, Damien Pous*

  **PA**: Coq

  Based on **FA**, matrices. Focus on performance.

.. raw:: pdf

    Spacer 0, 10

* A Decision Procedure for Regular Expression Equivalence in Type Theory (2011)

  *Thierry Coquand, Vincent Siles*

  **PA**: Coq

  Based on **derivatives of regexps**.

.. raw:: pdf

    PageBreak

* A Formalisation of the Myhill-Nerode Theorem
  based on Regular Expressions (Proof Pearl) (2011)

  *Chunhan Wu, Xingyuan Zhang, Christian Urban*

  **PA**: Isabelle

  The first proof of MH based on **derivatives of regexps**.

.. raw:: pdf

    Spacer 0, 10

* Deciding Regular Expressions (In-)Equivalence in Coq (2011)
  
  Nelma Moreira, David Pereira, Simão Melo de Sousa

  **PA**: Coq

  Based on Krauss, Nipkow. Proof of termination.



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

    PageBreak halfPage

.. class:: bigtext

**Ssreflect**

* Excellent support for all things boolean.
* Finite types with all necessary operations and closure properties. 
  
  (very useful for alphabets, FA states, etc.)
* Lots and lots of useful lemmas and functions.


.. raw:: pdf

    PageBreak 34Page

.. class:: bigtext

**Finite automata**

.. raw:: pdf
    
    Spacer 0, 10

DFA and NFA without e-transitions.

* DFA to prove closure under :math:`\cup`, :math:`\cap`, and :math:`\neg`.
* NFA to prove closure under :math:`\bullet\,` and :math:`\ast`.

.. raw:: pdf
    
    Spacer 0, 20

Also proven: 
NFA :math:`\Leftrightarrow\,` DFA.

.. raw:: pdf
    
    Spacer 0, 20

This gives us:
regexp :math:`\Rightarrow\,` FA.    

.. raw:: pdf

    PageBreak


-------
Roadmap
-------

.. raw:: pdf
    
    Spacer 0, 10


#. Emptiness test on FA (:math:`\emptyset(A) := \mathcal{L}(A) = \emptyset \,`)
#. FA :math:`\Rightarrow\,` regexp
#. Dedicedability of regexp equivalence using regexp :math:`\Rightarrow` FA, (2) and (1):

    :math:`\mathcal{L}(r) = \mathcal{L}(s)`
    
    :math:`\Leftrightarrow`

    :math:`\emptyset(\mathcal{A}(r) \cap \overline{\mathcal{A}(s)}) \wedge`
    :math:`\emptyset(\overline{\mathcal{A}(r)} \cap \mathcal{A}(s))`

.. raw:: pdf
    
    PageBreak halfPage

4. Finally, we want to prove the MH theorem

.. raw:: pdf
    
    Spacer 0, 20

With this we'll have an extensive formalization of regular languages including regular expressions, FA and MH and all corresponding equivalences.

