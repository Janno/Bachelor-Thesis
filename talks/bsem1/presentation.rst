.. header::
    **###Title###**

.. footer::
    **###Section###**
    

Constructive Formalization of Regular Languages
==================================================

--------------------------------------------
Jan-Oliver Kaiser
--------------------------------------------

.. raw:: pdf

    Spacer 0, 50

.. class:: centered

Advisors: Christian Doczkal, Gert Smolka

.. class:: centered

Supervisor: Gert Smolka


.. raw:: pdf

    PageBreak normalPage

=============
Contents
=============


#. Motivation
#. Previous work
#. Roadmap

.. raw:: pdf

    PageBreak 

==========
Motivation
==========

* Interest in formalizations growing stronger
* No complete and elegant formalization of regular languages in Coq
* Recent formalizations avoid FA in favor of partial derivatives

.. raw:: pdf

    PageBreak 


=============
Previous work
=============

* Constructively formalizing automata theory (2000)

  *Robert L. Constable, Paul B. Jackson, Pavel Naumov, Juan C. Uribe*

  **PA**: Nuprl

  The first constructive formalization of MH.

  Based on **FA**.

.. raw:: pdf

    Spacer 0, 10

* Proof Pearl: Regular Expression Equivalence and Relation Algebra

  *Alexander Krauss, Tobias Nipkow*
  
  **PA**: Isabelle

  Based on **partial derivatives of RE**.

.. raw:: pdf

    Spacer 0, 10

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

    Spacer 0, 10

* A Formalisation of the Myhill-Nerode Theorem
  based on Regular Expressions (Proof Pearl) (2011)

  *Chunhan Wu, Xingyuan Zhang, Christian Urban*

  **PA**: Isabelle

  The first proof of MH based on **partial derivatives of RE**.




