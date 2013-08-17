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



into_mpred_form_locally(V,V):- current_prolog_flag(logicmoo_load_state,making_renames),!.
into_mpred_form_locally(V,R):- into_mpred_form(V,R),!. 

freeze_u(V,G):- freeze(V,call_u(G)).

:- kb_shared(rtLogicalConnective/1).

get_LogicalConnective(F):- call_u(rtLogicalConnective(F)).

as_compound(G):- compound(G),!.
as_compound(G):- get_LogicalConnective(F),connective_arity(F,A),functor(G,F,A).
as_compound(G):- between(2,11,A),functor(G,t,A).

connective_arity(F,A):- connective_arity0(F,A).
connective_arity(_,A):- between(2,11,A).
connective_arity0(equiv,2):-!.
connective_arity0(implies,2):-!.
connective_arity0(not,1):-!.

inner_connective(F) :- get_LogicalConnective(F), \+ connective_arity0(F,_).

tAsserted(ist(MT,P)):- !, istAsserted(MT,P).
tAsserted(P):- 
   asserted_id(P,_).

ist(MT,P):- istAsserted(MT,P).

istAsserted(MT,P):- kb7166:assertion_content(ist,MT,P,_).
%istAsserted(P,MT):- as_compound(P),istAsserted0(P,MT).
istAsserted(MT,P):- asserted_id(P,ID),assertion_mt(ID,MT).

% Y=verbSemTrans(xIndicateTheWord,X,xTransitiveThatClauseFrame,and(isa('ACTION',eventInformationTransferEvent),informationOrigin('ACTION','SUBJECT'),infoTransferred('ACTION','CLAUSE'))),rtrace(kif_to_boxlog(Y,BL)).


asserted_id(P,ID):- compound(P), P=..[F,F1|ARGS],append(ARGS,[ID],ARGSID),
   (F==t -> (AP=..[assertion_content,F1|ARGSID],nop(freeze_u(F1,\+ get_LogicalConnective(F1))));
            AP=..[assertion_content,F,F1|ARGSID]),!,
   call(kb7166:AP),
   varnamify(ID),
   guardify(ID).
asserted_id(PO,ID):- var(PO),
   % current_predicate(assertion_content/N),
   between(3,13,N2),N is 16-N2,
   current_predicate(assertion_content/N),
   functor(AP,assertion_content,N),
   AP=..[assertion_content,F|PARGS],
   append(ARGS,[ID],PARGS),
   call(kb7166:AP),
   ((
    varnamify(ID),
    ((atom(F) -> P=..[F|ARGS]; P=..[t,F|ARGS])),
    litterally_guard(ID,P,PO))).


litterally_guard(ID,I,O):- assertion_variable_guard(ID,Guard),!,must_det(and_conj_to_list(Guard,ListE)),exclude(skip_guard,ListE,List),
   add_guard_list(I,List,O),!.
litterally_guard(_,IO,IO).

add_guard_list(IO,[],IO):-!.
add_guard_list(I,[List],List=>I):-!.
add_guard_list(I,List,AList=>I):- AList=..[and|List].

guardify(ID):- assertion_variable_guard(ID,Guard),!,must_det(and_conj_to_list(Guard,List)),
  must_maplist(maybe_add_guard,List).
guardify(_).

skip_guard('quotedIsa'(_,EXPR)):-EXPR='ftExpression'.

maybe_add_guard(G):- skip_guard(G),!.
maybe_add_guard(G):- term_variables(G,Vars),maplist(maybe_add_guard_2(G),Vars).
maybe_add_guard_2(G,Var):-add_dom(Var,G).

and_conj_to_list(C,[C]):- var(C),!.
and_conj_to_list([],[]):- !.
and_conj_to_list(C,C):- \+ compound(C),!.
and_conj_to_list(AND,List):- AND=..[and|List],!.
and_conj_to_list(C,[C]).

varnamify(ID):- assertion_varnames(ID,NAMES),!,ID=..[_|VARS],maplist(varnamify,VARS,NAMES).
varnamify(_).
varnamify(Var,String):- string_to_atom(String,Atom),nb_current('$variable_names',Was),!,b_setval('$variable_names',[Atom=Var|Was]),
 name_variable(Var,Atom).

badz:- asserted_id(t(P,A,zzzz),ID),dmsg(badz(asserted_id(t(P,A,zzzz),ID))),fail.
badz:- asserted_id(t(P,zzzz,B),ID),dmsg(asserted_id(t(P,zzzz,B),ID)),fail.
badz:- asserted_id(t(zzzz,A,B),ID),dmsg(asserted_id(t(zzzz,A,B),ID)),fail.

asserted_boxlog:- asserted_boxlog(BoxLog),nl,nl,maplist(wdmsg,BoxLog),nl,nl,fail.

/*


X = 

  defunctionalize(implies(isa(YEAR, tClazzCalendarYear), temporallyFinishedBy(YEAR, uU(iTimeOf_SecondFn, 59, uU(iTimeOf_MinuteFn, 59, uU(iTimeOf_HourFn, 23, uU(iTimeOf_DayFn, 31, uU(iTimeOf_MonthFn, vDecember, YEAR))))))),O)


rtrace(kif_to_boxlog(
 sourceSchemaObjectID(SOURCE, SCHEMA, uU(uSourceSchemaObjectFn, SOURCE, SCHEMA, ID), ID),BL))

rtrace(kif_to_boxlog(
 sourceSchemaObjectID(SOURCE, SCHEMA, THING, uU(uSourceSchemaObjectIDFn, SOURCE, SCHEMA, THING)),BL)).

X = or(holdsIn(YEAR, isa(PERSON, nartR(tClazzCitizenFn, iGroup_UnitedStatesOfAmerica))), holdsIn(YEAR, isa(PERSON, nartR(mobTaxResidentsFn, iGroup_Canada))), holdsIn(YEAR, isa(PERSON, nartR(mobTaxResidentsFn, iMexico))), holdsIn(YEAR, isa(PERSON, nartR(mobTaxResidentsFn, iGroup_UnitedStatesOfAmerica))), forbiddenToDoWrt(iCW_USIncomeTax, SUPPORTER, claimsAsDependent(YEAR, SUPPORTER, SUPPORTEE))),
  rtrace(kif_to_boxlog(X,BL)).

*/

% asserted_boxlog(BoxLog):- asserted_id(P,ID),atomic(ID),dmsg(asserted_id(P,ID)),once(kif_to_boxlog(P,BoxLog)).
asserted_boxlog(BoxLog):- asserted_id(P,ID),compound(ID),dmsg(asserted_id(P,ID)),once(kif_to_boxlog(P,BoxLog)).

:- ain(tAsserted(isa(F,rtLogicalConnective))==>rtLogicalConnective(F)).

:- ain(rtArgsVerbatum(tAsserted)).

:- ain((tAsserted(isa(MT,mtCycInternalAnthropacity))==> mtUndressedMt(MT))).

:- ain((mtUndressedMt(iEnglishParaphraseMt))).

cyc_ain(P):- mpred_ainz(P,(kb7166,ax)),writeq(P),nl.

fix_head(HEAD,FHEAD):- fully_expand(HEAD,FHEAD).

pred_in_mt(F,A,MT,Type):- no_repeats(pred_in_mt0(F,A,MT,Type)).

pred_in_mt0(F,A,MT0,Type0):-
  pred_in_mt1(_QQ,F,A,MT0,Type0).

pred_in_mt1(QQ,F,A,MT0,Type0):- 
  asserted_id(QQ,ID),
  assertion_mt(ID,MT),
  append_dir(ID,fact,Type),  
  preds_fa_s(Type,Type0,MT,QQ,F,A,MT0).

append_dir(ID,I,O):- assertion_forward(ID),!,append_dir0(f,I,O).
append_dir(ID,I,O):- assertion_backward(ID),!,append_dir0(b,I,O).
append_dir(ID,I,O):- assertion_code(ID),!,append_dir0(c,I,O).
append_dir(_, I,O):- append_dir0(u,I,O).

append_dir0(C,fact,C):-!.
append_dir0(C,I,O):- O=..[C,I].


preds_fa_s(_Type,_Type0,_MT,QQ,_,_,_MT0):- \+ compound(QQ),!,fail.
preds_fa_s(Type,Type0,_,ist(MT,QQ),F0,A0,MT0):- !,preds_fa_s(Type,Type0,MT,QQ,F0,A0,MT0).
preds_fa_s(Type,Type0,MT,not(Q),F0,A0,MT0):- !,preds_fa_s(not(Type),Type0,MT,Q,F0,A0,MT0).
preds_fa_s(Type,Type0,MT,knows(A,Q),F0,A0,MT0):- !, preds_fa_s(knows(Type),Type0,modal(A,MT),Q,F0,A0,MT0).
preds_fa_s(Type,Type0,MT,implies(P,Q),F0,A0,MT0):- !, (preds_fa_s(antec(Type),Type0,MT,P,F0,A0,MT0); preds_fa_s(consq(Type),Type0,MT,Q,F0,A0,MT0)).
preds_fa_s(Type,Type0,MT,QQ,F0,A0,MT0):- 
   functor(QQ,F,A),
   ((get_LogicalConnective(F),append_dir0(F,Type,FType))
      -> (arg(_,QQ,Arg),preds_fa_s(FType,Type0,MT,Arg,F0,A0,MT0)) ;
       (F0=F,A0=A,MT=MT0,Type=Type0)).

scyc:- forall(pred_in_mt(F,A,MT,Type), cyc_ain(cycPredMtType(F,A,MT,Type))).

% ?- assertion_content(isa,X,Y,O),assertion_mt(O,MT).
/*

:- forall(
 ((% current_predicate(assertion_content/N),
   between(3,13,N),
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

