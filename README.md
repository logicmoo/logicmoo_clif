# logicmoo_base

Knowledge Base Maintenance System


````
?- ensure_loaded(library(logicmoo/logicmoo_base)).

:- file_begin(pfc).
spouse(X,Y) ==> spouse(Y,X).
gender(P,male) <==> male(P).
gender(P,female) <==> female(P).

````

# Defining new General Inference rules

````

?- ensure_loaded(library(logicmoo/logicmoo_user)).

:- file_begin(kif).

parent(X,Y),female(X) <=> mother(X,Y).
parent(X,Y),parent(Y,Z) => grandparent(X,Z).
grandparent(X,Y),male(X) <=> grandfather(X,Y).
grandparent(X,Y),female(X) <=> grandmother(X,Y).
mother(Ma,Kid),parent(Kid,GrandKid)
      =>grandmother(Ma,GrandKid).
grandparent(X,Y),female(X) <=> grandmother(X,Y).
parent(X,Y),male(X) <=> father(X,Y).
mother(Ma,X),mother(Ma,Y),{X\==Y}
     =>sibling(X,Y).

````

examples:  https://github.com/logicmoo/PrologMUD/tree/master/pack/logicmoo_base/t/examples/fol

# First Order Logic (FOL) declarations in Prolog source code. 


Despite Prolog's logic heritage it does not qualify as a full general-purpose theorem-proving system. There are three main reasons: (1) Prolog is a programming language and not an inference engine so if we used the unification algorithm of Prolog for FOL, it is unsound,  (2) Prolog's unbounded depth-first search strategy is inefficient when it is doing complete search, and (3) Prolog's inference system is not complete for non-Horn clauses. Nevertheless, Prolog is quite interesting from a theorem-proving standpoint because of its very high inference rate as compared to conventional theorem-proving programs. 

Logicmoo use of the Prolog Technology Theorem Prover (PTTP) was to overcome the deficiencies while retaining as fully as possible the high performance of well-engineered Prolog systems.

The Prolog Technology Theorem Prover (PTTP) is an extension of Prolog that is complete for the full first order predicate calculus (Stickel, 1988).   
It is invoked whenever the facts and rule are described in NNF or CNF put into the knowledge base.  And optionally for Horn clauses built by other modules.
However, when the rules are in Prenix Normal Form (PNF) (thus have quantifiers) they are converted to NNF, SNF and finally CNF and handed back over to PTTP.
Also a formula whose leading quantifier is existential, the formula obtained by removing that quantifier via Closed Skolemization may be generated. 

kif_add/1: the file has a rule or fact, in the form of a predicate of FOPC (First Order Predicate Calculus).  The LogicMOO invokes the PTTP compiler (discussed later) to assert the form to the knowledge base. The
knowledge base represents the user''s beliefs. Thus, asserting the logical form to the knowledge base amounts to applying the Declarative rule and the Distributivity rule (Axiom B2).

kif_ask/1: the user types in a question, in the form of a predicate of FOPC (First Order Predicate Calculus). The PTTP inference system is then invoked to attempt to  prove the predicate, 
using the axioms and facts of the knowledge base. This amounts toassuming that the user''s beliefs are closed under logical consequence, i.e., the Closure rule (Axiom B1) is implicitly applied over and over.

LogicMOO, because of PTTP, is unlike all other theorem provers today  (Perhaps except SNARK and maybe CYC) 
Here is how:: If the proof succeeds, LogicMOO answers ``yes'', and prints out the predicate, instantiating all variables. If there are multiple answers, then it prints all of them. 
If the proof fails, LogicMOO invokes PTTP to prove the negation of the queried predicate.  If that NEGATED proof succeeds, then LogicMOO answers ``no''; otherwise, LogicMOO answers ``cannot tell, not enough information''.

LogicMOO, therefore, has the capability for reasoning about negation, being able to distinguish between real negation (``P is false'') from negation by failure (``P is not provable'').
This allows the system to distinguish beliefs that are provably false from beliefs that cannot be proven because of insufficient information. 
This is an important feature that overcomes the supposed limitations of Prolog.   For example, without this added capability, if a user were to
ask whether LogicMOO believes that John intended to let the cat out, then LogicMOO would answer ``no''. 
This answer is misleading because LogicMOO would also answer ``no'' if it were asked if John did not intend to let the cat out.  This is why the system automaically Re-asks the negation.

Sadly all theorem provers since PTTP (include theorem provers said to be based on it) have been simplified to to no longer do this simple analysis.  The reason? According to classically trained
logicians horn clauses *cannot* start with a negated literals.   So to not offend them (entirely)  PTTP can store "( ~a :- ~b )" as "( not_a :- not_b )" 
If we obeyed the classical limitations set forth upon Horn clauses to only being "positive" that would remove the unique ability for LogicMOO to deduce the difference between false and unknown. 
We are no longer restricted to CWA and the limitations imposed by modern theorem provers and sematic web tools.  I must assume the reason programmers made these sacrifices is they can still solve problems like circuit verifcation without disrupting the post 1980s maintsteam thinking.

Since LogicMOO can infer the limits it's theoretical knowledge, so it can help guide the user to understand what types of knowledge it is missing.  That also provides a portal through which
other modules (e.g., a plan recognition system or a modules for NL reference resolution) can enter information. When such modules are not available, the user may simulate this capacity. ("ask the user")

is_entailed_u/1: Detects if an Horn Clause (or fact) is holograpically existing. Example: assert a=>b. this will result in the following two clauses:   is_entailed_u(( ~a :- ~b )) and   is_entailed_u((  b :- a ) ).


# Backward-Chaining Rules
## PFC
Pfc includes a special kind of backward chaining rule which is used to generate all possible solutions to a goal that is sought in the process of forward chaining.     

# Forward chaining macros
It is well known that sound and complete reasoning systems can be built using either exclusive backward chaining or exclusive forward chaining. Thus, this is not a theoretical problem. It is also well understood how to ``implement'' forward reasoning using an exclusively backward chaining system and vice versa. Thus, this need not be a practical problem. In fact, many of the logic-based languages developed for AI applications allow one to build systems with both forward and backward chaining rules.
There are, however, some interesting and important issues which need to be addresses in order to provide the Prolog programmer with a practical, efficient, and well integrated facility for forward chaining.

This module uses such a facility, written by Tim Finin called PFC, which he has implemented in standard Prolog. The PFC system is a package that provides a forward reasoning capability to be used together with conventional Prolog programs. The PFC inference rules are Prolog terms which are asserted as facts into the regular Prolog database.

The PFC system package provides a forward reasoning capability to be used together with conventional Prolog programs. The PFC inference rules are Prolog terms which are asserted as clauses into the regular Prolog database. When new facts or forward reasoning rules are added to the Prolog database (via a special predicate pfc_add/1, forward reasoning is triggered and additional facts that can be deduced via the application of the forward chaining rules are also added to the database. A simple justification-based truth-maintenance system is provided as well as simple predicates to explore the resulting proof trees.   Additionally this module provides the user with various methods for trying out new techniques of backwards chaining without rewriting their code.

The =logicmoo_base= module allows one to use optimal First Order Logic declarations in Prolog code.
During *development*, these declarations log informative information when values don't match
expectations.  A typical development environment converts this into a helpful
stack trace which assists in locating the programing error.


````

You may have noticed that Logicmoo defines {}/1 as an escape construct for bypassing the FOL's salient body goals. 

% this means that both P and Q can't be true.
disjoint(P,Q), {current_predciate(_,P),current_predciate(_,Q)}
  ==>
  (P ==> not(Q)),
  (Q ==> not(P)).

````


As exemplified above, this is the same control construct that is used in grammar rules for bypassing the expansion of rule body goals when a rule is converted into a clause. 
Both control constructs can be combined in order to call a goal from a grammar rule body, while bypassing at the same time the Prolog compiler. Consider the following example:


# S-Expr reader utilities

The abiliity to use CLIF/KIF/CycL Etc


Source code available and pull requests accepted on GitHub:
https://github.com/logicmoo/PrologMUD/tree/master/pack/logicmoo_base


# Some TODOs

Document this pack!
Write tests
Untangle the 'pack' install deps
Still in progress (Moving predicates over here from logicmoo_base)


[BSD 2-Clause License](LICENSE.md)

Copyright (c) 2017, 
Douglas Miles <logicmoo@gmail.com> and logicmoo
All rights reserved.

# Not _obligated_ to maintain a git fork just to contribute

Dislike having tons of forks that are several commits behind the main git repo?

Be old school - Please ask to be added to logicmoo and Contribute directly !
Still, we wont stop you from doing it the Fork+PullRequest method




