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
:- module(logicmoo_i_cyc_kb,[
          logicmoo_i_cyc_xform/0,
          is_better_backchained/1,
          addCycL/1,
          cycl_to_mpred/2,
          as_cycl/2,
          is_better_backchained/1
          
          ]).
/*
:- module(logicmoo_i_cyc_kb,
          [

         addCycL/1,
         addCycL0/1,
         addCycL1/1,
         addTinyCycL/1,
         addTiny_added/1,
         isa_db/2,
         ist_tiny/2,
         cycl_to_mpred/2,
         cycl_to_mpred0/2,
         loadTinyKB/0,
         
         call_el_stub/3,
         
         
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

:- meta_predicate((cwtdl(0,+,+),transfer_predicate(?,0,0),transTiny(?,0))).


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


/*
:- multifile(t/3).
:- multifile(t/4).
:- multifile(t/5).
:- multifile(t/6).
:- multifile(t/7).
:- multifile(t/8).
*/

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

:- dynamic(lmcache:isCycAvailable_known/0).
:- volatile(lmcache:isCycAvailable_known/0).

isa_db(I,C):-clause(isa(I,C),true).
:- set_module(elmt:class(development)).
:- kb_shared(arity/2).
:- kb_shared((elmt:exactlyAssertedELMT/4,elmt:exactlyAssertedELMT/5,elmt:exactlyAssertedELMT/6,elmt:exactlyAssertedELMT/7)).

/*
:- kb_shared((elmt:exactlyAssertedELMT/4,elmt:exactlyAssertedELMT/5,elmt:exactlyAssertedELMT/6,elmt:exactlyAssertedELMT/7)).
:- dynamic((exactlyAssertedEL_next/4,exactlyAssertedEL_next/5,exactlyAssertedEL_next/6,exactlyAssertedEL_next/7)).
:- dynamic((exactlyAssertedEL_first/4,exactlyAssertedEL_first/5,exactlyAssertedEL_first/6,exactlyAssertedEL_first/7)).
:- dynamic(assertedTinyKB_implies_first/4).
:- dynamic(assertedTinyKB_not_first/3).
:- dynamic((exactlyAssertedEL_first/5,exactlyAssertedEL_with_vars/5,exactlyAssertedEL_with_vars/6,assertedTinyKB_implies_Already/4)).
*/

 % :- set_prolog_flag(subclause_expansion,true).

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
isa(I,C):-elmt:exactlyAssertedELMT(isa,I,C,_,_).
genls(I,C):-elmt:exactlyAssertedELMT(genls,I,C,_,_).
arity(I,C):-elmt:exactlyAssertedELMT(arity,I,C,_,_).
argIsa(P,N,C):-elmt:exactlyAssertedELMT(argIsa,P,N,C,_,_).
argGenl(P,N,C):-elmt:exactlyAssertedELMT(argGenl,P,N,C,_,_).
argQuotedIsa(P,N,C):-elmt:exactlyAssertedELMT(argQuotedIsa,P,N,C,_,_).
*/
% queuedTinyKB(CycL,MT):- (mtUndressedMt(MT);mtDressedMt(MT)),(STR=vStrMon;STR=vStrDef),  tinyKB_All(CycL,MT,STR),
% \+ clause(elmt:exactlyAssertedELMT(CycL,_,_,_),true).
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
tinyKB_All(PO,MT,STR):- % current_predicate(_:'TINYKB-ASSERTION'/5),!,
    if_defined(tiny_kb_ASSERTION(PLISTIn,PROPS)),
        once((sexpr_sterm_to_pterm(PLISTIn,P),
               memberchk(amt(MT),PROPS),
               memberchk(str(STR),PROPS), 
              (member(vars(VARS),PROPS)->(nput_variable_names( []),fixvars(P,0,VARS,PO),nput_variable_names( PO));PO=P ))).

loadTinyKB:-forall((tinyKB(C,MT,STR),cyc_to_clif(C,P)),((print_assertion(P,MT,STR),wdmsg(ain(P))))).
% ssveTinyKB:-tinyKB_All(tinyKB(P,MT,STR),tell((print_assertion(P,MT,STR),ain(P)))).

print_assertion(P,MT,STR):- P=..PL,append([exactlyAssertedELMT|PL],[MT,STR],PPL),PP=..PPL, 
 portray_clause(current_output,elmt:PP,[numbervars(false)]).


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

:- must( \+ is_pfc_file ).

into_mpred_form_locally(V,V):- current_prolog_flag(logicmoo_load_state,making_renames),!.
into_mpred_form_locally(V,R):- into_mpred_form(V,R),!. 

call_el_stub(V,MT,STR):-into_mpred_form_locally(V,M),!,M=..ML,((ML=[t|ARGS]-> true; ARGS=ML)),
 CALL=..[exactlyAssertedELMT|ARGS],!,
 baseKB:call(elmt:CALL,MT,STR).
make_el_stub(V,MT,STR,CALL):-into_mpred_form_locally(V,M),!,M=..ML,((ML=[t|ARGS]-> true; ARGS=ML)),append(ARGS,[MT,STR],CARGS),CALL=..[elmt:exactlyAssertedELMT|CARGS],!.

tinyAssertion(V,MT,STR):- 
 nonvar(V) -> call_el_stub(V,MT,STR);
  (tinyAssertion0(W,MT,STR),once(into_mpred_form_locally(W,V))).

tinyAssertion0(t(A,B,C,D,E),MT,STR):-elmt:exactlyAssertedELMT(A,B,C,D,E,MT,STR).
tinyAssertion0(t(A,B,C,D),MT,STR):-elmt:exactlyAssertedELMT(A,B,C,D,MT,STR).
tinyAssertion0(t(A,B,C),MT,STR):-elmt:exactlyAssertedELMT(A,B,C,MT,STR).
tinyAssertion0(t(A,B),MT,STR):-elmt:exactlyAssertedELMT(A,B,MT,STR).


addTinyCycL(CycLIn):- into_mpred_form_locally(CycLIn,CycL),
  ignore((tiny_support(CycL,_MT,CALL),must(retract(CALL)))),!,
  addCycL(CycL),!.



tiny_support(CycLIn,MT,CALL):- compound(CycLIn),!,into_mpred_form_locally(CycLIn,CycL), 
  CycL=..[F|Args], append(Args,[MT,_STR],WMT),
  CCALL=..[exactlyAssertedELMT,F|WMT],!,
  ((baseKB:clause(elmt:CCALL,true), CCALL=CALL) ; baseKB:clause(elmt:CCALL,(CALL,_))).
tiny_support(CycLOut,MT,CALL):- between(4,7,Len),
 functor(CCALL,exactlyAssertedELMT,Len),
 CCALL=..[exactlyAssertedELMT,F|WMT],
 append(Args,[MT,_STR],WMT),
 baseKB:call(elmt:CCALL),(atom(F)->CycL=..[F|Args];append_termlist(F,Args,CycL)),((baseKB:clause(CCALL,true), CCALL=CALL) ; baseKB:clause(CCALL,(CALL,_))), fully_expand(CycL,CycLOut).


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

:- dynamic(addTiny_added/1).

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



logicmoo_i_cyc_xform:- dmsg("Compiling tinyKB should take under a minute"),
    gripe_time(60,baseKB:qcompile(library('logicmoo/plarkc/logicmoo_i_cyc_xform.pfc'))).
:- current_prolog_flag(do_renames,WAS),writeq(current_prolog_flag(do_renames,WAS)),nl.


:- after_boot(dmsg("Dont forget to ?- logicmoo_i_cyc_xform.")).
% :- logicmoo_i_cyc_xform.


:- fixup_exports.

end_of_file.
end_of_file.
end_of_file.
end_of_file.
end_of_file.
end_of_file.
end_of_file.
end_of_file.








end_of_file.
end_of_file.
end_of_file.
end_of_file.
end_of_file.
end_of_file.
end_of_file.
end_of_file.









end_of_file.
end_of_file.
end_of_file.
end_of_file.
end_of_file.
end_of_file.
end_of_file.
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



