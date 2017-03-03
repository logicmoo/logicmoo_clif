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
%:- module(tiny_kb,['TINYKB-ASSERTION'/5, 'TINYKB-ASSERTION'/6]).
% File: /opt/PrologMUD/pack/logicmoo_base/prolog/logicmoo/plarkc/logicmoo_i_cyc_kb.pl
/*
:- module(logicmoo_i_cyc_kb,
          [

           logicmoo_i_cyc_xform/0,
            addCycL/1,
            addCycL0/1,
            addCycL1/1,
            addTinyCycL/1,
            addTiny_added/1,
            as_cycl/2,
          is_better_backchained/1,
          is_simple_arg/1,
          is_simple_gaf/1,
          isa_db/2,
          ist_tiny/2,
        cycLToMpred/2,
        cycLToMpred0/2,
            loadTinyKB/0,
            ltkb1/0,
            ltkb1_complete/0,
          call_el_stub/3,

            system:mwkb1/0,
            needs_canoncalization/1,
            needs_indexing/1,
            
            print_assertion/3,
            sent_to_conseq/2,
            mtDressedMt/1,
            rtEscapeFunction/1,
            mtUndressedMt/1,
            tinyAssertion/3,
            tinyAssertion0/3,
            tinyKB/1,
            tinyKB/3,
            tinyKB1/1,
            tinyKB2/1,
            tinyKB_All/3,
            tinyKB_wstr/1,
            tiny_support/3,
            wkb0/0,
            wkb01/0,
            wkb02/0,
            wkb2/0,
            wkbe/0,
   %finish_asserts/0,
   
   %make_el_stub/4,
   %cyc_to_mpred_idiom/2,

   
          ]).
*/         

:- use_module(library('filestreams')).

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

:- dynamic(tinyKB9/1).
:- multifile(tinyKB9/1).


:- dynamic(cwtdl_failed/1).

cwtdl(Goal,DL,TL):- cwc,
  quietly((ignore((nortrace,
   (show_failure(why,catch(call_with_time_limit(TL,(((call_with_depth_limit(Goal,DL,DLE),DLE\==depth_limit_exceeded)))),E,(dmsg(E:cwtdl(Goal,DL,TL)),fail)))
     ->true;
    assert(cwtdl_failed(Goal))))))).

:- baseKB:meta_predicate((cwtdl(0,+,+),transfer_predicate(?,0,0),transTiny(?,0))).


%:- in_cmt(doall((filematch(logicmoo('plarkc/mpred_cyc_kb_tinykb.pl'),F),source_file(X,F),predicate_property(X,static),X\='$pldoc'(_G8428,_G8429,_G8430,_G8431),listing(X)))).


transfer_predicate(C,If,Q):-doall((clause(C,true,Ref),If,Q,on_x_log_throw(erase(Ref)))).
transTiny(Template,If):-transfer_predicate(tinyK8(Template),If,once(ain(Template))).


reallyLoadTiny:- transTiny(tCol(X),ground(X)).
reallyLoadTiny:- transTiny(arity(X,Y),ground((X,Y))).
reallyLoadTiny:- transTiny(genls(X,Y),((X\=ftAtomicTerm,ground((X,Y))))).
reallyLoadTiny:- mpred_trace.
reallyLoadTiny:- transTiny(genls(X,Y),((ground((X,Y))))).
%TODO_VERIFY_STILL_UNNEEDED :- retract_all((ftClosedAtomicTerm(A) :- ftAtomicTerm(A))).
%TODO_VERIFY_STILL_UNNEEDED :- mpred_withdraw(genls(ftAtomicTerm,ftClosedAtomicTerm)).
reallyLoadTiny:- transTiny(genlMt(X,Y),writeq((X,Y))).
reallyLoadTiny:- transTiny(ttExpressionType(X),ground(X)).

%TODO_VERIFY_STILL_UNNEEDED :-mpred_withdraw(genls(ftAtomicTerm,ftClosedAtomicTerm)).

%TODO_VERIFY_STILL_UNNEEDED :-retract_all((ftClosedAtomicTerm(A) :- ftAtomicTerm(A))).
reallyLoadTiny:- mpred_notrace.


:- if(false).
:- doall(reallyLoadTiny).
:- endif.


%TODO FIX :-ain((((cycl(X),{must(cyc_to_clif(X,Y))}) ==> clif(Y)))).

:- ain((((cycl('$VAR'('X')),{must(cyc_to_clif('$VAR'('X'),'$VAR'('Y')))}) ==> clif('$VAR'('Y'))))).
% ?-listing(cycl).

%TODO FIX :- must(isa(iExplorer2,tHominid)).
%TODO FIX :- must(tHominid(iExplorer2)).

% tHominid(iExplorer2).



:- multifile(t/3).
:- multifile(t/4).
:- multifile(t/5).
:- multifile(t/6).
:- multifile(t/7).
:- multifile(t/8).

% extra_tcol(Mt,A,ID):- isTT(Mt,t(genls,A,Other),ID),atom(Other),Other\=A,'Thing'\=Other.
% extra_tcol(Mt,A,ID):- isTT(Mt,t(genls,Other,A),ID),atom(Other),Other\=A,'Thing'\=Other.


% :- kb_shared((  argGenl/3,argIsa/3,argQuotedIsa/3)).

:- dynamic((
  
        % argGenl/3,argIsa/3,argQuotedIsa/3,

        addTiny_added/1,
        baseKB:cycPrepending/2,
        baseKB:cyc_to_plarkc/2,
        lmcache:isCycUnavailable_known/1,
        baseKB:mpred_to_cyc/2)).

:- volatile(lmcache:isCycAvailable_known/0).

isa_db(I,C):-clause(isa(I,C),true).

:- dynamic((exactlyAssertedEL/4,exactlyAssertedEL/5,exactlyAssertedEL/6,exactlyAssertedEL/7)).
:- dynamic((exactlyAssertedEL_next/4,exactlyAssertedEL_next/5,exactlyAssertedEL_next/6,exactlyAssertedEL_next/7)).
:- dynamic((exactlyAssertedEL_first/4,exactlyAssertedEL_first/5,exactlyAssertedEL_first/6,exactlyAssertedEL_first/7)).
:- dynamic(assertedTinyKB_implies_first/4).
:- dynamic(assertedTinyKB_not_first/3).
:- dynamic((exactlyAssertedEL_first/5,exactlyAssertedEL_with_vars/5,exactlyAssertedEL_with_vars/6,assertedTinyKB_implies_Already/4)).

:- set_prolog_flag(lm_expanders,true).

:- dynamic(tinyKB0/1).


tinyKB_wstr(P):-mtUndressedMt(MT),tinyKB(P,MT,_).
tinyKB_wstr(ist(MT,P)):-mtDressedMt(MT),tinyKB(P,MT,_).


/*
:- dynamic(argIsa/3).
:- kb_shared(argIsa/3).
:- dynamic(argGenl/3).
:- kb_shared(argGenl/3).
:- dynamic(argQuotedIsa/3).
:- kb_shared(argQuotedIsa/3).
isa(I,C):-exactlyAssertedEL(isa,I,C,_,_).
genls(I,C):-exactlyAssertedEL(genls,I,C,_,_).
arity(I,C):-exactlyAssertedEL(arity,I,C,_,_).
argIsa(P,N,C):-exactlyAssertedEL(argIsa,P,N,C,_,_).
argGenl(P,N,C):-exactlyAssertedEL(argGenl,P,N,C,_,_).
argQuotedIsa(P,N,C):-exactlyAssertedEL(argQuotedIsa,P,N,C,_,_).
*/
% queuedTinyKB(CycL,MT):- (mtUndressedMt(MT);mtDressedMt(MT)),(STR=vStrMon;STR=vStrDef),  tinyKB_All(CycL,MT,STR),\+ clause(exactlyAssertedEL(CycL,_,_,_),true).
% queuedTinyKB(CycL):-mtUndressedMt(MT),queuedTinyKB(CycL,MT).
% queuedTinyKB(ist(MT,CycL)):-mtDressedMt(MT),queuedTinyKB(CycL,MT).

tinyKBA(P):-tinyKB_All(P,_MT,_)*->true;find_and_call(tinyKB0(P)).

ist_tiny(MT,P):-tinyKB(P,MT,vStrMon).
ist_tiny(MT,P):-tinyKB(P,MT,vStrDef).

%TODO ADD BACK AFTER OPTIZING
tinyKB(P):- current_prolog_flag(logicmoo_load_state,making_renames),!,tinyKBA(P).
tinyKB(P):- tinyKBA(P).
tinyKB(ist(MT,P)):- (nonvar(MT)->true;mtDressedMt(MT)),!,tinyKB_All(P,MT,_).


tinyKB1(P):- current_prolog_flag(logicmoo_load_state,making_renames),!,tinyKBA(P).
                 
tinyKB1(D):-no_repeats(tinyKB2(D)).
tinyKB2(P):-tinyKBA(P)*->true;tinyKB0(P).
tinyKB2(isa(C1,C3)):-nonvar(C1),!,tinyKBA(isa(C1,C2)),tinyKB2(genls(C2,C3)).
tinyKB2(genls(C1,C3)):-nonvar(C1),tinyKBA(genls(C1,C2)),tinyKB2(genls(C2,C3)).
/*
tinyKB2(genls(C1,C3)):-nonvar(C1),tinyKB0(genls(C1,C2)),tinyKB0(genls(C2,C3)).
tinyKB2(genls(C1,C4)):-nonvar(C1),tinyKB0(genls(C1,C2)),tinyKB0(genls(C2,C3)),tinyKB0(genls(C3,C4)).
tinyKB2(genls(C1,C5)):-nonvar(C1),tinyKB0(genls(C1,C2)),tinyKB0(genls(C2,C3)),tinyKB0(genls(C3,C4)),tinyKB0(genls(C4,C5)).
*/
%TODO ADD BACK AFTER OPTIZING tinyKB(P):-nonvar(P),if_defined(P).

tinyKB(PO,MT,STR):-
  (nonvar(MT)->true;(mtUndressedMt(MT);mtDressedMt(MT))),
  (nonvar(STR)->true;(STR=vStrMon;STR=vStrDef)),
  tinyKB_All(PO,MT,STR).

tinyKB_All(V,MT,STR):- tinyAssertion(V,MT,STR).
tinyKB_All(PO,MT,STR):- current_predicate(_:'TINYKB-ASSERTION'/5),!,
    tiny_kb_ASSERTION(PLISTIn,PROPS),
        once((sexpr_sterm_to_pterm(PLISTIn,P),
               memberchk(amt(MT),PROPS),
               memberchk(str(STR),PROPS), 
              (member(vars(VARS),PROPS)->(nput_variable_names( []),fixvars(P,0,VARS,PO),nput_variable_names( PO));PO=P ))).

loadTinyKB:-forall((tinyKB(C,MT,STR),cyc_to_clif(C,P)),((print_assertion(P,MT,STR),wdmsg(ain(P))))).
% ssveTinyKB:-tinyKB_All(tinyKB(P,MT,STR),tell((print_assertion(P,MT,STR),ain(P)))).

print_assertion(P,MT,STR):- P=..PL,append([exactlyAssertedEL|PL],[MT,STR],PPL),PP=..PPL, portray_clause(current_output,PP,[numbervars(false)]).


mtUndressedMt('iUniversalVocabularyImplementationMt').
mtUndressedMt('iLogicalTruthImplementationMt').
mtUndressedMt('iCoreCycLImplementationMt').
mtUndressedMt('iUniversalVocabularyMt').
mtUndressedMt('iLogicalTruthMt').
mtUndressedMt('iCoreCycLMt').
mtUndressedMt('iBaseKB').

mtDressedMt('iBookkeepingMt').
mtDressedMt('iEnglishParaphraseMt').
mtDressedMt('iTemporaryEnglishParaphraseMt').

into_mpred_form_locally(V,V):- current_prolog_flag(logicmoo_load_state,making_renames),!.
into_mpred_form_locally(V,R):- into_mpred_form(V,R),!. 

call_el_stub(V,MT,STR):-into_mpred_form_locally(V,M),!,M=..ML,((ML=[t|ARGS]-> true; ARGS=ML)),CALL=..[exactlyAssertedEL|ARGS],!,call(CALL,MT,STR).
make_el_stub(V,MT,STR,CALL):-into_mpred_form_locally(V,M),!,M=..ML,((ML=[t|ARGS]-> true; ARGS=ML)),append(ARGS,[MT,STR],CARGS),CALL=..[exactlyAssertedEL|CARGS],!.

tinyAssertion(V,MT,STR):- 
 nonvar(V) -> call_el_stub(V,MT,STR);
  (tinyAssertion0(W,MT,STR),once(into_mpred_form_locally(W,V))).

tinyAssertion0(t(A,B,C,D,E),MT,STR):-exactlyAssertedEL(A,B,C,D,E,MT,STR).
tinyAssertion0(t(A,B,C,D),MT,STR):-exactlyAssertedEL(A,B,C,D,MT,STR).
tinyAssertion0(t(A,B,C),MT,STR):-exactlyAssertedEL(A,B,C,MT,STR).
tinyAssertion0(t(A,B),MT,STR):-exactlyAssertedEL(A,B,MT,STR).


addTinyCycL(CycLIn):- into_mpred_form_locally(CycLIn,CycL),
  ignore((tiny_support(CycL,_MT,CALL),must(retract(CALL)))),!,
  addCycL(CycL),!.



tiny_support(CycLIn,MT,CALL):- compound(CycLIn),!,into_mpred_form_locally(CycLIn,CycL), CycL=..[F|Args], append(Args,[MT,_STR],WMT),CCALL=..[exactlyAssertedEL,F|WMT],!,
  ((clause(CCALL,true), CCALL=CALL) ; clause(CCALL,(CALL,_))).
tiny_support(CycLOut,MT,CALL):- between(4,7,Len),functor(CCALL,exactlyAssertedEL,Len),CCALL=..[exactlyAssertedEL,F|WMT],append(Args,[MT,_STR],WMT),
 CCALL,(atom(F)->CycL=..[F|Args];append_termlist(F,Args,CycL)),((clause(CCALL,true), CCALL=CALL) ; clause(CCALL,(CALL,_))), fully_expand(CycL,CycLOut).


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
needs_canoncalization(CycL):-functor(CycL,F,_),isa_db(F,'SentenceOperator').
needs_canoncalization(CycL):-needs_indexing(CycL).

is_better_backchained(CycL):-is_ftVar(CycL),!,fail.
is_better_backchained(CycL):-functor(CycL,F,_),isa_db(F,'SentenceOperator').
is_better_backchained(V):-unnumbervars(V,FOO),(((each_subterm(FOO,SubTerm),nonvar(SubTerm),isa_db(SubTerm,rtAvoidForwardChain)))),!.


as_cycl(VP,VE):-subst(VP,('-'),(~),V0),subst(V0,('v'),(or),V1),subst(V1,('exists'),(thereExists),V2),subst(V2,('&'),(and),VE),!.


:- dynamic(addTiny_added/1).
addCycL(V):-addTiny_added(V),!.
addCycL(V):-into_mpred_form_locally(V,M),V\=@=M,!,addCycL(M),!.
addCycL(V):-defunctionalize('implies',V,VE),V\=@=VE,!,addCycL(VE).
addCycL(V):-cyc_to_clif(V,VE),V\=@=VE,!,addCycL(VE).
addCycL(V):-is_simple_gaf(V),!,addCycL0(V),!.
addCycL(V):-kif_to_boxlog(V,VB),boxlog_to_pfc(VB,VP),V\=@=VP,!,as_cycl(VP,VE),show_call(why,addCycL0(VE)).
addCycL(V):-addCycL0(V),!.

addCycL0(V):-addCycL1(V).

addCycL1(V):-into_mpred_form_locally(V,M),V\=@=M,!,addCycL0(M),!.
addCycL1(V):-cyc_to_clif(V,VE),V\=@=VE,!,addCycL0(VE).
addCycL1((TRUE=>V)):-is_true(TRUE),addCycL0(V),!.
addCycL1(<=(V , TRUE)):-is_true(TRUE),addCycL0(V),!.
addCycL1((V :- TRUE)):-is_true(TRUE),addCycL0(V),!.
addCycL1((V :- A)):- show_call(why,addCycL0((A => V))).
addCycL1((A => (V1 , V2))):-not(is_ftVar(V1)),!,show_call(why,addCycL0((A => V1))) , show_call(why,addCycL0((A => V2))).
addCycL1((V1 , V2)):-!,addCycL0(V1),addCycL0(V2),!.
addCycL1([V1 | V2]):-!,addCycL0(V1),addCycL0(V2),!.
addCycL1(V):-addTiny_added(V),!.
addCycL1(V):-asserta(addTiny_added(V)),unnumbervars(V,VE),
  % must(nop(remQueuedTinyKB(VE))),
  ain(VE).


sent_to_conseq(CycLIn,Consequent):- into_mpred_form_locally(CycLIn,CycL), ignore((tiny_support(CycL,_MT,CALL),retract(CALL))),must(cycLToMpred(CycL,Consequent)),!.

:- dynamic(addTiny_added/1).

cycLToMpred(V,CP):-into_mpred_form_locally(V,M),V\=@=M,!,cycLToMpred(M,CP),!.
cycLToMpred(V,CP):-cyc_to_clif(V,VE),V\=@=VE,!,cycLToMpred(VE,CP).
cycLToMpred(V,CP):-is_simple_gaf(V),!,cycLToMpred0(V,CP),!.
cycLToMpred(V,CP):-defunctionalize('implies',V,VE),V\=@=VE,!,cycLToMpred(VE,CP).
cycLToMpred(V,CP):-kif_to_boxlog(V,VB),boxlog_to_pfc(VB,VP),V\=@=VP,!,as_cycl(VP,VE),show_call(why,cycLToMpred0(VE,CP)).
cycLToMpred(V,CP):-cycLToMpred0(V,CP),!.

cycLToMpred0(V,CP):-into_mpred_form_locally(V,M),V\=@=M,!,cycLToMpred0(M,CP),!.
cycLToMpred0(V,CP):-cyc_to_clif(V,VE),V\=@=VE,!,cycLToMpred0(VE,CP).
cycLToMpred0((TRUE => V),CP):-is_true(TRUE),cycLToMpred0(V,CP),!.
cycLToMpred0((V <=> TRUE),CP):-is_true(TRUE),cycLToMpred0(V,CP),!.
cycLToMpred0((V :- TRUE),CP):-is_true(TRUE),cycLToMpred0(V,CP),!.
cycLToMpred0((V :- A),CP):- show_call(why,cycLToMpred0((A => V),CP)).
cycLToMpred0((A => (V1 , V2)),CP):-not(is_ftVar(V1)),!,cycLToMpred0((A=> (V1/consistent(V2))),V1P),cycLToMpred0((A=> (V2/consistent(V1))),V2P) ,!,conjoin(V1P,V2P,CP).
cycLToMpred0((V1 , V2),CP):-!,cycLToMpred0(V1,V1P),cycLToMpred0(V2,V2P),!,conjoin(V1P,V2P,CP).
cycLToMpred0([V1 | V2],CP):-!,cycLToMpred0(V1,V1P),cycLToMpred0(V2,V2P),!,conjoin(V1P,V2P,CP).
cycLToMpred0(V,V).

%  cycLToMpred( (grandparent('$VAR'('G'),'$VAR'('C')) => thereExists('$VAR'('P'), and(parent('$VAR'('G'),'$VAR'('P')),parent('$VAR'('P'),'$VAR'('C'))))),O).



% :-onEachLoad(loadTinyAssertions2).

% ============================================
% DBASE to Cyc Predicate Mapping
% ============================================
/*
arity('abbreviationString-PN', 2).

typical_mtvars([_,_]).

% arity 1 person
make_functorskel(Person,1,fskel(Person,t(Person,A),Call,A,[],MtVars,Call2)):-typical_mtvars(MtVars),Call=..[Person,A],Call2=..[Person,A|MtVars]. 
% arity 2 likes
make_functorskel(Likes,2,fskel(Likes,t(Likes,A,B),Call,A,B,MtVars,Call2)):- typical_mtvars(MtVars),Call=..[Likes,A,B],Call2=..[Likes,A,B|MtVars]. 
% arity 3 between
make_functorskel(Between,3,fskel(Between,t(Between,A,B,C),Call,A,[B,C],MtVars,Call2)):- typical_mtvars(MtVars),Call=..[Between,A,B,C],Call2=..[Between,A,B,C|MtVars]. 
% arity 4 xyz
make_functorskel(Xyz,4,fskel(Xyz,t(Xyz,I,X,Y,Z),Call,I,[X,Y,Z],MtVars,Call2)):- typical_mtvars(MtVars),Call=..[Xyz,I,X,Y,Z],Call2=..[Xyz,I,X,Y,Z|MtVars]. 
% arity 5 rxyz
make_functorskel(RXyz,5,fskel(RXyz,t(RXyz,I,R,X,Y,Z),Call,I,[R,X,Y,Z],MtVars,Call2)):-typical_mtvars(MtVars),Call=..[RXyz,I,R,X,Y,Z],Call2=..[RXyz,I,R,X,Y,Z|MtVars]. 
% arity >6 
make_functorskel(F,N,fskel(F,DBASE,Call,I,NList,MtVars,Call2)):-typical_mtvars(MtVars),functor(Call,F,N),Call=..[F,I|NList],DBASE=..[t,F,I|NList],append([F,I|NList],MtVars,CALL2List),Call2=..CALL2List.

*/

% ============================================
% Prolog to Cyc Predicate Mapping
%
%  the following will all do the same things:
%
% :- decl_mpred('BaseKB':isa/2). 
% :- decl_mpred('BaseKB':isa(_,_)). 
% :- decl_mpred(isa(_,_),'BaseKB'). 
% :- decl_mpred('BaseKB',isa,2). 
%
%  Will make calls 
% :- isa(X,Y)
%  Query into #$BaseKB for (#$isa ?X ?Y) 
%
% decl_mpred/N
%
% ============================================

:- dynamic(lmcache:isCycUnavailable_known/1).
:- dynamic(lmcache:isCycAvailable_known/0).

/*
:- was_export(isCycAvailable/0).
isCycAvailable:-lmcache:isCycUnavailable_known(_),!,fail.
isCycAvailable:-lmcache:isCycAvailable_known,!.
isCycAvailable:-checkCycAvailablity,isCycAvailable.

:- was_export(isCycUnavailable/0).
isCycUnavailable:-lmcache:isCycUnavailable_known(_),!.
isCycUnavailable:-lmcache:isCycAvailable_known,!,fail.
isCycUnavailable:-checkCycAvailablity,isCycUnavailable.

:- was_export(checkCycAvailablity/0).
checkCycAvailablity:- (lmcache:isCycAvailable_known;lmcache:isCycUnavailable_known(_)),!.
checkCycAvailablity:- catchv((current_predicate(invokeSubL/2),ignore((invokeSubL("(+ 1 1)",R))),(R==2->assert_if_new(lmcache:isCycAvailable_known);assert_if_new(lmcache:isCycUnavailable_known(R)))),E,assert_if_new(lmcache:isCycUnavailable_known(E))),!.
*/



system:mwkb1:- setup_call_cleanup(tell(tinyKB9_cache),
   forall(tinyKB_wstr(P),((cyc_to_clif(P,SAVE),
     once(must(unnumbervars(SAVE,SAVE2))),
     assert_if_new(tinyKB9(SAVE2)),
   format('~q.~n',[tinyKB9(SAVE)])))),
   told).

ltkb1:- check_clause_counts,
 defaultAssertMt(MT),
 must(logicmoo_i_cyc_kb\==MT),
 with_current_why(mfl(MT, ltkb1, _ ),
 ( MT: must_det_l(( system:mwkb1,forall(find_and_call(tinyKB0(D)), MT:cycAssert(D)))),
         check_clause_counts,
         finish_asserts,
  ltkb1_complete)).


finish_asserts:- call_u(forall(find_and_call(tinyKB8(Fact)),mpred_post(baseKB:Fact,(tinyKB8(Fact),ax)))).

ltkb1_complete:- 
  finish_asserts,
  doall((filematch(logicmoo('plarkc/logicmoo_i_cyc_kb_tinykb.pfc'),F),
  source_file(X,F),
  predicate_property(X,dynamic),retract(X:-_))).


wkb0:- 
  setup_call_cleanup(tell(tinyKB9_cache),
      forall(tinyKB_All(V,MT,STR),format('~q.~n',[tinyKB_All(V,MT,STR)])),
      told).

wkbe:- statistics(cputime,S),
  setup_call_cleanup(tell(foof),
   ignore((el_assertions:el_holds_pred_impl(F),between(2,16,A),
          current_predicate(F/A),functor(P,F,A),forall(P,format('~q.~n',[P])),fail)),told),
   statistics(cputime,E),Total is E - S, writeln(Total).

wkb2:- setup_call_cleanup(tell(tinyKB9_proof_cache),
      ignore(( tinyKB(D,MT,Str),cyc_to_clif(D,KB),format('~N~q.~N',[proof(KB,D,MT,Str)]),fail)),
      told).


:- export(do_renames_cyc_to_clif/3).
do_renames_cyc_to_clif(InTerm,_Info,_Ignored):- InTerm == '$translate_file_steam',!.
do_renames_cyc_to_clif(end_of_file,_Info,end_of_file).
do_renames_cyc_to_clif(InTerm,_Info,OutTerm):-
   cyc_to_clif(InTerm,Mid),
   nb_current('$variable_names',Vs),
   reread_vars(Mid-Vs,re_symbolize,OutTerm),!.



:- ((baseKB:ensure_loaded(logicmoo(plarkc/'logicmoo_i_cyc_kb_preds.pfc')))).
logicmoo_i_cyc_xform:- dmsg("Compiling tinyKB should take under a minute"),
                      gripe_time(60,qcompile(logicmoo(plarkc/'logicmoo_i_cyc_xform.pfc'))).
% :- logicmoo_i_cyc_xform.

:- current_prolog_flag(do_renames,WAS),writeq(current_prolog_flag(do_renames,WAS)),nl.
:- after_boot(dmsg("Dont forget to ?- logicmoo_i_cyc_xform.")).

end_of_file.

%:- trace,(cyc_to_clif("a",_X)).
:- must(predicate_property(tinyKB9(_),number_of_clauses(_))).

:- retractall(tinyKB9(_)).

:- if((predicate_property(tinyKB9(_),number_of_clauses(N)),N==0)).
:- wdmsg("Making tinyKB").
:- must(gripe_time(7.0,system:mwkb1)).
:- wdmsg("Made tinyKB").
:- break.
:- endif.

%:- set_prolog_flag(alt_term_expansion,do_nothing).
%:- set_prolog_flag(alt_goal_expansion,do_nothing).
%:- rtrace.
%:- set_prolog_flag(alt_term_expansion,false).
%:- set_prolog_flag(alt_goal_expansion,false).
%:- notrace.
%:- break.

:- fixup_exports.

