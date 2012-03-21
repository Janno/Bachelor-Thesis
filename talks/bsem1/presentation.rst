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

    PageBreak halfPage

--------
Contents
--------


#. Motivation
#. Previous work
#. Our development
#. Roadmap

.. raw:: pdf

    PageBreak halfPage

----------
Motivation
----------

* Strong interest in formalizations in this area.
* No complete and elegant formalization of regular languages in Coq.
* Recent formalizations avoid FA in favor of partial derivatives.

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

  Based on **partial derivatives of RE**. No proof of termination.

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

  Based on **partial derivatives of RE**.

.. raw:: pdf

    PageBreak

* A Formalisation of the Myhill-Nerode Theorem
  based on Regular Expressions (Proof Pearl) (2011)

  *Chunhan Wu, Xingyuan Zhang, Christian Urban*

  **PA**: Isabelle

  The first proof of MH based on **partial derivatives of RE**.

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
* Our main goals are MH and the decidability of RE equivalence.
* We use FA.
  
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
RE :math:`\Rightarrow\,` FA.    

.. raw:: pdf

    PageBreak


-------
Roadmap
-------

.. raw:: pdf
    
    Spacer 0, 10


#. Emptiness test on FA (:math:`\emptyset(A) := \mathcal{L}(A) = \emptyset \,`)
#. FA :math:`\Rightarrow\,` RE
#. Dedicedability of RE equivalence using RE :math:`\Rightarrow` FA, (2) and (1):

    :math:`\mathcal{L}(r) = \mathcal{L}(s)`
    
    :math:`\Leftrightarrow`

    :math:`\emptyset(\mathcal{A}(r) \cap \overline{\mathcal{A}(s)}) \wedge`
    :math:`\emptyset(\overline{\mathcal{A}(r)} \cap \mathcal{A}(s))`

.. raw:: pdf
    
    PageBreak halfPage

4. Finally, we want to prove the MH theorem

.. raw:: pdf
    
    Spacer 0, 20

With this we'll have a complete formalization of regular languages including RE, FA and MH and all corresponding equivalences.

