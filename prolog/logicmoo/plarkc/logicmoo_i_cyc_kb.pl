/* 
% ===================================================================
% File 'logicmoo_i_cyc_kb.pl'
% Purpose: Emulation of OpenCyc for SWI-Prolog
% Maintainer: Douglas Miles
% Contact: $Author: dmiles $@users.sourceforge.net ;
% Version: 'interface.pl' 1.0.0
% Revision:  $Revision: 1.9 $
% Revised At:   $Date: 2002/06/27 14:13:20 $
% ===================================================================
% File used as storage place for all predicates which make us more like Cyc
% special module hooks into the logicmoo engine allow
% syntax to be recocogized via our CycL/KIF handlers 
%
% Dec 13, 2035
% Douglas Miles
*/

% File: /opt/PrologMUD/pack/logicmoo_base/prolog/logicmoo/plarkc/logicmoo_i_cyc_kb.pl
:- module(logicmoo_i_cyc_kb,[          
          is_better_backchained/1,
          addCycL/1,
          addCycL0/1,
          addCycL1/1,
          cycl_to_mpred/2,
          as_cycl/2,
          is_better_backchained/1,
          rtEscapeFunction/1
          
          ]).
:- set_module(class(development)).

% ===================================================================
% OPERATOR PRECEDANCE
% ===================================================================

:- op(500,fx,'~').
:- op(1050,xfx,('==>')).
:- op(1050,xfx,'<==>').
:- op(1050,xfx,('<-')).
:- op(1100,fx,('==>')).
:- op(1150,xfx,('::::')).
:- 
 system:((
 op(1199,fx,('==>')), 
 op(1190,xfx,('::::')),
 op(1180,xfx,('==>')),
 op(1170,xfx,'<==>'),  
 op(1160,xfx,('<-')),
 op(1150,xfx,'=>'),
 op(1140,xfx,'<='),
 op(1130,xfx,'<=>'), 
 op(600,yfx,'&'), 
 op(600,yfx,'v'),
 op(350,xfx,'xor'),
 op(300,fx,'~'))).

is_simple_gaf(V):-not(compound(V)),!.
is_simple_gaf(V):-needs_canoncalization(V),!,fail.
is_simple_gaf(V):-functor(V,F,A),member(F/A,[isa/2,genls/2,argQuotedIsa/3,afterAdding/2,afterRemoving/2]),!.
is_simple_gaf(V):-needs_indexing(V),!,fail.
is_simple_gaf(_).

needs_indexing(V):-compound(V),arg(_,V,A),not(is_simple_arg(A)),!,fail.

is_simple_arg(A):-not(compound(A)),!.
is_simple_arg(A):-functor(A,Simple,_),rtEscapeFunction(Simple).

% :- dynamic(vtUnreifiableFunction/1).
'rtEscapeFunction'('TINYKB-ASSERTION').
'rtEscapeFunction'('uQuoteFn').
'rtEscapeFunction'(X):- clause_b('rtUnreifiableFunction'(X)).

needs_canoncalization(CycL):-is_ftVar(CycL),!,fail.
needs_canoncalization(CycL):-functor(CycL,F,_),isa_db(F,'rtSentenceOperator').
needs_canoncalization(CycL):-needs_indexing(CycL).

is_better_backchained(CycL):-is_ftVar(CycL),!,fail.
is_better_backchained(CycL):-functor(CycL,F,_),isa_db(F,'rtSentenceOperator').
is_better_backchained(V):-unnumbervars(V,FOO),(((each_subterm(FOO,SubTerm),nonvar(SubTerm),isa_db(SubTerm,rtAvoidForwardChain)))),!.


as_cycl(VP,VE):-subst(VP,('-'),(~),V0),subst(V0,('v'),(or),V1),subst(V1,('exists'),(thereExists),V2),subst(V2,('&'),(and),VE),!.

kif_to_boxlog_ex(I,O):- if_defined(kif_to_boxlog(I,M)),if_defined(boxlog_to_pfc(M,O)).

:- dynamic(addTiny_added/1).
addCycL(V):-addTiny_added(V),!.
addCycL(V):-into_mpred_form_locally(V,M),V\=@=M,!,addCycL(M),!.
addCycL(V):-defunctionalize('implies',V,VE),V\=@=VE,!,addCycL(VE).
addCycL(V):-cyc_to_clif(V,VE),V\=@=VE,!,addCycL(VE).
addCycL(V):-is_simple_gaf(V),!,addCycL0(V),!.
addCycL(V):-kif_to_boxlog_ex(V,VP),V\=@=VP,!,as_cycl(VP,VE),show_call(tiny_kb,addCycL0(VE)).
addCycL(V):-addCycL0(V),!.

addCycL0(V):-addCycL1(V).

addCycL1(V):-into_mpred_form_locally(V,M),V\=@=M,!,addCycL0(M),!.
addCycL1(V):-cyc_to_clif(V,VE),V\=@=VE,!,addCycL0(VE).
addCycL1((TRUE=>V)):-is_true(TRUE),addCycL0(V),!.
addCycL1(<=(V , TRUE)):-is_true(TRUE),addCycL0(V),!.
addCycL1((V :- TRUE)):-is_true(TRUE),addCycL0(V),!.
addCycL1((V :- A)):- show_call(tiny_kb,addCycL0((A => V))).
addCycL1((A => (V1 , V2))):-not(is_ftVar(V1)),!,show_call(tiny_kb,addCycL0((A => V1))) , show_call(tiny_kb,addCycL0((A => V2))).
addCycL1((V1 , V2)):-!,addCycL0(V1),addCycL0(V2),!.
addCycL1([V1 | V2]):-!,addCycL0(V1),addCycL0(V2),!.
addCycL1(V):-addTiny_added(V),!.
addCycL1(V):-asserta(addTiny_added(V)),unnumbervars(V,VE),
  % must(nop(remQueuedTinyKB(VE))),
  ain(VE).


sent_to_conseq(CycLIn,Consequent):- into_mpred_form_locally(CycLIn,CycL), ignore((tiny_support(CycL,_MT,CALL),retract(CALL))),must(cycl_to_mpred(CycL,Consequent)),!.


cycl_to_mpred(V,CP):-into_mpred_form_locally(V,M),V\=@=M,!,cycl_to_mpred(M,CP),!.
cycl_to_mpred(V,CP):-cyc_to_clif(V,VE),V\=@=VE,!,cycl_to_mpred(VE,CP).
cycl_to_mpred(V,CP):-is_simple_gaf(V),!,cycl_to_mpred0(V,CP),!.
cycl_to_mpred(V,CP):-defunctionalize('implies',V,VE),V\=@=VE,!,cycl_to_mpred(VE,CP).
cycl_to_mpred(V,CP):-kif_to_boxlog_ex(V,VP),V\=@=VP,!,as_cycl(VP,VE),show_call(tiny_kb,cycl_to_mpred0(VE,CP)).
cycl_to_mpred(V,CP):-cycl_to_mpred0(V,CP),!.

cycl_to_mpred0(V,CP):-into_mpred_form_locally(V,M),V\=@=M,!,cycl_to_mpred0(M,CP),!.
cycl_to_mpred0(V,CP):-cyc_to_clif(V,VE),V\=@=VE,!,cycl_to_mpred0(VE,CP).
cycl_to_mpred0((TRUE => V),CP):-is_true(TRUE),cycl_to_mpred0(V,CP),!.
cycl_to_mpred0((V <=> TRUE),CP):-is_true(TRUE),cycl_to_mpred0(V,CP),!.
cycl_to_mpred0((V :- TRUE),CP):-is_true(TRUE),cycl_to_mpred0(V,CP),!.
cycl_to_mpred0((V :- A),CP):- show_call(tiny_kb,cycl_to_mpred0((A => V),CP)).
cycl_to_mpred0((A => (V1 , V2)),CP):-not(is_ftVar(V1)),!,cycl_to_mpred0((A=> (V1/consistent(V2))),V1P),
   cycl_to_mpred0((A=> (V2/consistent(V1))),V2P) ,!,conjoin(V1P,V2P,CP).
cycl_to_mpred0((V1 , V2),CP):-!,cycl_to_mpred0(V1,V1P),cycl_to_mpred0(V2,V2P),!,conjoin(V1P,V2P,CP).
cycl_to_mpred0([V1 | V2],CP):-!,cycl_to_mpred0(V1,V1P),cycl_to_mpred0(V2,V2P),!,conjoin(V1P,V2P,CP).
cycl_to_mpred0(V,V).

%  cycl_to_mpred( (grandparent('$VAR'('G'),'$VAR'('C')) => thereExists('$VAR'('P'), and(parent('$VAR'('G'),'$VAR'('P')),parent('$VAR'('P'),'$VAR'('C'))))),O).


/*
:- multifile(t/3).
:- multifile(t/4).
:- multifile(t/5).
:- multifile(t/6).
:- multifile(t/7).
:- multifile(t/8).
*/
into_mpred_form_locally(V,V):- current_prolog_flag(logicmoo_load_state,making_renames),!.
into_mpred_form_locally(V,R):- into_mpred_form(V,R),!. 

freeze_u(V,G):- freeze(V,call_u(G)).

:- kb_shared(rtLogicalConnective/1).

as_compound(G):- compound(G),!.
as_compound(G):- rtLogicalConnective(F),connective_arity(F,A),functor(G,F,A).
as_compound(G):- between(2,11,A),functor(G,t,A).

connective_arity(equiv,2):-!.
connective_arity(implies,2):-!.
connective_arity(not,1):-!.
connective_arity(_,A):-between(2,11,A).


tAsserted(ist(MT,P)):- !, istAsserted(P,MT).
tAsserted(P):- as_compound(P),asserted_id(P,_).

istAsserted(P,MT):- kb7166:assertion_content(ist,MT,P,_).
istAsserted(P,MT):- as_compound(P),istAsserted0(P,MT).

istAsserted0(P,MT):- istAsserted0(P,ID),assertion_mt(ID,MT).


asserted_id(P,ID):- P=..[F,F1|ARGS],append(ARGS,[ID],ARGSID),
   (F==t -> (AP=..[assertion_content,F1|ARGSID],freeze_u(F1,\+ rtLogicalConnective(F1)));
            AP=..[assertion_content,F,F1|ARGSID]),!,
   call(kb7166:AP).



:- ain(tAsserted(isa(F,rtLogicalConnective))==>rtLogicalConnective(F)).

:- ain(rtArgsVerbatum(tAsserted)).

:- ain((tAsserted(isa(MT,mtCycInternalAnthropacity))==> mtUndressedMt(MT))).

:- ain((mtUndressedMt(iEnglishParaphraseMt))).

cyc_ain(P):-ainz(P,(kb7166,ax)).

fix_head(HEAD,FHEAD):- fully_expand(HEAD,FHEAD).
  
% ?- assertion_content(isa,X,Y,O),assertion_mt(O,MT).
/*

 forall(
 ((current_predicate(assertion_content/N),NN is N-2,
   functor(P,assertion_content,N),
   arg(1,P,F),arg(N,P,ID))),
   forall(no_repeats(F,(P,assertion_mt(ID,MT), mtUndressedMt(MT))),
    ((cyc_ain(cycPredUndressed(F,NN)))))).

 
 
 forall(
 ((current_predicate(assertion_content/N),NN is N-2,
   functor(P,assertion_content,N),
   arg(1,P,F),arg(N,P,ID))),
   forall(no_repeats(F-MT,(P, \+ cycPredUndressed(F,NN), assertion_mt(ID,MT), \+ mtUndressedMt(MT))),
    ((cyc_ain(cycPredDressed(F,NN)))))).

:- forall(
 ((current_predicate(assertion_content/N),
   functor(P,assertion_content,N),P=..[assertion_content,F|PARGS],
   functor(PP,assertion_content,N),PP=..[assertion_content,F|FARGS],
   append(ARGS,[ID],PARGS),
   assertion_mt(ID,MT))),
   forall(no_repeats(F-MT,(P,assertion_mt(ID,MT))),
    (writeq(cycPredArity(F,N,MT)),nl))).

    ((atom(F) -> HEAD=..[F|ARGS]; HEAD=..[ac,F|ARGS]),
  fix_head(HEAD,FHEAD),
    dmsg((FHEAD :- PP))))).

*/

:- fixup_exports.

