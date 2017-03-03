/* <module> logicmoo_plarkc - special module hooks into the logicmoo engine allow
%   clif syntax to be recocogized via our CycL/KIF handlers 
% 
% Logicmoo Project: A LarKC Server written in Prolog
% Maintainer: Douglas Miles
% Dec 13, 2035
%
*/

end_of_file.
end_of_file.
end_of_file.
end_of_file.
end_of_file.
:- module(logicmoo_snark,[
  load_snark/0,mpred_load_restore_file/1,mpred_load_restore_file/1,mpred_save_restore_file/1,
  with_ukb_snark/2]).

:- module_transparent((
  load_snark/0,mpred_load_restore_file/1,mpred_load_restore_file/1,mpred_save_restore_file/1,
  with_ukb_snark/2)).

/*


:- ensure_loaded(system:library('logicmoo/snark/common_logic_snark.pl')). 
:- ensure_loaded(system:library('logicmoo/snark/common_logic_boxlog.pl')).
:- ensure_loaded(system:library('logicmoo/snark/common_logic_skolem.pl')).
:- ensure_loaded(system:library('logicmoo/snark/common_logic_compiler.pl')). 
:- ensure_loaded(system:library('logicmoo/snark/common_logic_kb_hooks.pl')).
*/

:- add_library_search_path('./pfc2.0/',[ 'mpred_*.pl']).

/*
:- add_library_search_path('./logicmoo/',[ '*.pl']).
%:- add_library_search_path('./logicmoo/pttp/',[ 'dbase_i_mpred_*.pl']).
%:- add_library_search_path('./logicmoo/../',[ 'logicmoo_*.pl']).
%:- must(add_library_search_path('./logicmoo/mpred_online/',[ '*.pl'])).
:- add_library_search_path('./logicmoo/snark/',[ '*.pl']).
:- add_library_search_path('./logicmoo/plarkc/',[ '*.pl']).

*/

% 	 	 
%% with_ukb_snark( ?VALUE1, ?VALUE2) is semidet.
%
% Hook To [with_ukb_snark/2] For Module Logicmoo_snark.
% Using Ukb Snark.
%
with_ukb_snark(KB,G):- with_umt(KB,G).

%:- system:initialization(use_listing_vars).


%:- add_import_module(baseKB,system,end).
%:- initialization(maybe_add_import_module(baseKB,system,end)).
% :- with_ukb_snark(baseKB,baseKB:use_module(baseKB:logicmoo_base)).

:-export(checkKB:m1/0).

/*  Provides a prolog database replacement that uses an interpretation of KIF
%
%  t/N
%  hybridRule/2
%  
%
% Logicmoo Project PrologMUD: A MUD server written in Prolog
% Maintainer: Douglas Miles
% Dec 13, 2035
%
*/
%= Compute normal forms for SHOIQ formulae.
%= Skolemize SHOI<Q> formula.
%=
%= Copyright (C) 1999 Anthony A. Aaby <aabyan@wwc.edu>
%= Copyright (C) 2006-2007 Stasinos Konstantopoulos <stasinos@users.sourceforge.net>
%= Douglas R. Miles <logicmoo@gmail.com>
%=
%= This program is free software; you can redistribute it and/or modify
%= it under the terms of the GNU General Public License as published by
%= the Free Software Foundation; either version 2 of the License, or
%= (at your option) any later version.
%=
%= This program is distributed in the hope that it will be useful,
%= but WITHOUT ANY WARRANTY; without even the implied warranty of
%= MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
%= GNU General Public License for more details.
%=
%= You should have received a copy of the GNU General Public License along
%= with this program; if not, write to the Free Software Foundation, Inc.,
%= 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.
%=
%= FORMULA SYNTAX
%=
%= not(A)
%= &(F, F)
%= v(F, F)
%= '=>'(F, F)
%= '<=>'(F, F)
%=    all(X,A)
%=    exists(X,A)
%=    atleast(X,N,A)
%=    atmost(X,N,A)
end_of_file.
:- module(logicmoo_engine, [ tsn/0 ] ). 

:- ensure_loaded(library(logicmoo_user)).

:- include(logicmoo(mpred/'mpred_header.pi')).

% SWI Prolog modules do not export operators by default
% so they must be explicitly placed in the user namespace

:-
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
 op(300,fx,'~'),
 op(300,fx,'-').

:- if( \+ op(_,_,(user:kb_shared))).
% :- op(1150,fx,(user:kb_shared)).
:- endif.



:- was_dynamic(kif_pred_head/1).
:- style_check(-singleton).

kif_pred_head(P):- var(P),!,isa(F,prologKIF),arity(F,A),functor(P,F,A).
kif_pred_head(P):- get_functor(P,F,_),isa(F,prologKIF).
kif_pred_head(P):- get_functor(P,F,_),isa(F,prologPTTP).


:- was_dynamic(pttp_pred_head/1).

pttp_pred_head(P):- var(P),isa(F,prologPTTP),arity(F,A),functor(P,F,A).
pttp_pred_head(P):- get_functor(P,F,_),isa(F,prologPTTP).

% :- kb_shared(kify_comment/1).


pttp_listens_to_head(_OP,P):- pttp_pred_head(P).

pttp_listens_to_stub(prologPTTP).
pttp_listens_to_stub(prologKIF).


baseKB:mpred_provide_setup(Op,H):- provide_kif_op(Op,H).

% OPHOOK ASSERT
provide_kif_op(clause(assert,How),(HeadBody)):- 
   pttp_listens_to_head(clause(assert,How),HeadBody),
   why_to_id(provide_kif_op,(HeadBody),ID),
   kif_add_boxes1(ID,(HeadBody)).

% OPHOOK CALL
provide_kif_op(call(How),Head):- 
  pttp_listens_to_head(call(How),Head),
  pttp_call(Head).

% OPHOOK CLAUSES
provide_kif_op(clauses(How),(Head:- Body)):- 
   pttp_listens_to_head(clauses(How),Head),
   baseKB:mpred_provide_storage_clauses(Head,Body,_Why).

% OPHOOK 
provide_kif_op(OP,(HeadBody)):- 
   pttp_listens_to_head(OP,HeadBody),
   kif_process(OP,HeadBody).


% CLAUSES HOOK 
baseKB:mpred_provide_storage_clauses(H,B,wid3(IDWhy)):- wid(IDWhy,_,(H:- B)).
baseKB:mpred_provide_storage_clauses(H,true,wid3(IDWhy)):- wid(IDWhy,_,(H)),compound(H),not(functor(H,':-',2)).


% REGISTER HOOK
baseKB:mpred_provide_setup(OP,HeadIn,StubType,RESULT):-  pttp_listens_to_stub(StubType),!,
   get_pifunctor3(HeadIn,Head,F),
      assert_if_new(isa(F,prologPTTP)),
         ensure_universal_stub(Head),
         RESULT = declared(pttp_listens_to_head(OP,Head)).


/*

:- was_dynamic(baseKB:int_proven_t/10).

int_proven_t(P, X, Y, E, F, A, B, C, G, D):- t(P,X,Y),
        test_and_decrement_search_cost(A, 0, B),
        C=[H, [true_t(P, X, Y), D, E, F]|I],
        G=[H|I].


:- was_dynamic(baseKB:int_assumed_t/10).
int_assumed_t(P, X, Y, E, F, A, B, C, G, D):- t(P,X,Y),
        test_and_decrement_search_cost(A, 0, B),
        C=[H, [assumed_t(P, X, Y), D, E, F]|I],
        G=[H|I].


*/
:- dynamic(kif_test_string/1).
kif_test_string_disabled(
"
% )
tell.

all(R,room(R) => exists(D, (door(D) & has(R,D)))).
room(room1).

ask.

room(What).

door(What).

:- kif_add(a(XX) & b(XX) => c(XX)).
:- kif_add(all(R,room(R) => exists(D, (door(D) & has(R,D))))).
:- kif_add(loves(Child,fatherFn(Child))).
:- kif_add((p => q)).
:- kif_add(~p <=> ~q).
:- kif_add(p <=> q).
:- kif_add(all(P, person(P) => -exists(D, dollar(D) & has(P,D)))).

:- kif_add(go(sam) & (go(bill) v go(sally) ) & go(nancy)).

:- kif_add(rains_tuesday => wear_rain_gear xor carry_umbrella).
:- kif_add(exists(P, (person(P) & all(C, car(C) => ~has(P,C))))).

/*
:- kif_add(room(R) => exists(D, (door(D) & has(R,D)))).
:- kif_add((goes(jane) xor goes(sandra) => goes(bill))).
:- kif_add(exists(P, exists(C, (person(P) & car(C) & has(P,C))))).
:- kif_add(~all(P,person(P) => exists(C, car(C) & has(P,C)))).
:- kif_add((go(sam) & go(bill)) v (go(sally) & go(nancy))).
:- kif_add(go(sam) & (go(bill) v go(sally) ) & go(nancy)).
:- kif_add(exists(C, course(C) & exists(MT1, midterm(C,MT1) & exists(MT2, midterm(C,MT2) & different(MT1,MT2))))).
:- kif_add(exists(C, course(C) & ~exists(MT3, midterm(C,MT3)))).
*/

"
).


/*
:- told.
:- dmsg_show(_).
:- dmsg("i see this").
:- kif_add(exists(C, course(C) & ~exists(MT3, midterm(C,MT3)))).
:- forall(kif_test_string(TODO),(kif_io(string(TODO),current_output)))
:- set_no_debug.
:- quietly.
:- nodebug.

:- wdmsg("we see this").

:- kif_add((p => q)).
:- kif_add(~p <=> ~q).
:- kif_add(tRoom(R) => exists(D, (tDoor(D) & has(R,D)))).
:- kif_add(all(P, person(P) => ~(exists(D, dollar(D) & has(P,D))))).
:- kif_add(p <=> q).
:- kif_add(all(P, person(P) => exists(D, dollar(D) & has(P,D)))).
*/
kif_result(_).
:- was_export((kif_test)/1).
kif_test(X):-kif_add(X).
:- op(1000,fy,(kif_test)).
:- assert_until_eof(t_l:canonicalize_types).

:- discontiguous kif_sanity_test_0/0.

kif_sanity_test_0:-kif_test(all(R, exists(D, room(R) => (door(D) & has(R,D))))).

kif_sanity_test_0:-kif_test(p(A,R) & q(A,R)).


:- kif_result(
(=> mdefault((
   room(R) => 
      {D = skIsDoorInRoomArg2ofHasFn(R)},has(R,D) & door(D))))).






% kif_sanity_test_0:- kif_test(loves(fatherFn(Child),Child)).


% :- prolog.
%:- must(((kif_test(isa(F,tPred) => exists(A, (isa(A,ftInt) & arity(F,A))))))).

:- nop(( kif_result(
(==> mdefault((
   tPred(F) ==> 
      {A = skIsIntInPredArg2ofArityFn(F)},arity(F,A) & ftInt(A))
 ))))).


kif_sanity_test_0:-kif_test'(relationAllExists causes-EventEvent Exhibitionism VisualEvent)'.

kif_sanity_test_0:-kif_test '(relationAllExists properSubEvents Exhibitionism (DisplayingFn SexOrgan))'.


kif_sanity_test_0:-kif_test '(knows UnitedStatesOfAmerica (thereExists ?THING  (and  (assets ChevronCorporation ?THING)  (objectFoundInLocation ?THING Kazakhstan))))'.
kif_sanity_test_0:-kif_test '
(not (beliefs UnitedStatesOfAmerica (not (thereExists ?THING  (and  (assets ChevronCorporation ?THING)  (objectFoundInLocation ?THING Kazakhstan))))))
'.
kif_sanity_test_0:-kif_test '
(not (beliefs UnitedStatesOfAmerica (not (forAll ?THING  (not (and  (assets ChevronCorporation ?THING)  (objectFoundInLocation ?THING Kazakhstan)))))))
'.
kif_sanity_test_0:-kif_test '
(knows UnitedStatesOfAmerica (not (forAll ?THING  (not (and  (assets ChevronCorporation ?THING)  (objectFoundInLocation ?THING Kazakhstan))))))
'.

kif_sanity_test_0:-kif_test '
(knows UnitedStatesOfAmerica (and  KA KB KC KD))
'.

kif_sanity_test_0:-kif_test '
(beliefs UnitedStatesOfAmerica (and  BA BB BC BD))
'.

kif_sanity_test_0:-kif_test '
(knows UnitedStatesOfAmerica (or  KOA KOB KOC KOD))
'.

kif_sanity_test_0:-kif_test '
(beliefs UnitedStatesOfAmerica (or  BOA BOB BOC BOD))
'.

kif_sanity_test_0:-kif_test '
(implies 
       (and 
           (different ?THEMAN ?WOMAN) 
           (intendedMaleficiary ?CRIME ?THEMAN) 
           (deliberateActors ?CRIME ?WOMAN) 
           (behaviorCapable ?THEMAN 
               (CollectionSubsetFn Punishing 
                   (TheSetOf ?RESPONSE 
                       (maleficiary ?RESPONSE ?WOMAN))) deliberateActors)) 

       (optionAvailableToAgent-SitType ?THEMAN 
           (CollectionSubsetFn 
               (AttemptingFn Punishing) 
               (TheSetOf ?RETALIATION 
                   (and 
                       (intendedMaleficiary ?RETALIATION ?WOMAN) 
                       (purposeInEvent ?THEMAN ?RETALIATION 
                           (not 
                               (thereExists ?ANOTRACT 
                                   (and 
                                       (isa ?ANOTRACT PurposefulAction) 
                                       (startsAfterEndingOf ?ANOTRACT ?CRIME) 
                                       (maleficiary ?ANOTRACT ?THEMAN) 
                                       (deliberateActors ?ANOTRACT ?WOMAN)))))))) deliberateActors))'.

%:-prolog.

kif_sanity_test_0:-kif_test '
(implies
       (and 
           (isa ?AGREEMENT Agreement) 
           (intangibleParts ?AGREEMENT ?OBLIGATION) 
           (isa ?OBLIGATION Obligation) 
           (agreeingAgents ?AGREEMENT ?WOMAN) 
           (agentViolatesObligation ?WOMAN ?OBLIGATION)) 
       (agentViolatesAgreement ?WOMAN ?AGREEMENT))'.

% :-prolog.

kif_sanity_test_0:-kif_test '
(implies 
       (and 
           (isa ?SEEING VisualEvent) 
           (objectActedOn ?SEEING ?WOMAN) 
           (isa ?WOMAN ExhibitionistOffender) 
           (actorPartsInvolved ?SEEING ?PART-TYPE) 
           (physicalPartTypes Eyes ?PART-TYPE) 
           (performedBy ?SEEING ?THEMAN)) 
       (increases-Generic ?SIT 
           (relationExistsInstance bodilyDoer 
               Shaming ?THEMAN) probability-Generic))'.


kif_sanity_test_0:-kif_test '
(implies 
       (and 
           (isa ?ACT CriminalAct) 
           (isa ?ACT Exhibitionism) 
           (perpetrator ?ACT ?PERP)) 
       (isa ?PERP ExhibitionistOffender))'.


kif_sanity_test_0:-kif_test '
(implies 
       (and 
           (isa ?PUNISH Punishing) 
           (performedBy ?PUNISH ?THEMAN) 
           (maleficiary ?PUNISH ?WOMAN)) 
       (beliefs ?THEMAN 
           (thereExists ?OBLIGATION 
               (agentViolatesObligation ?WOMAN ?OBLIGATION))))'.

kif_sanity_test_0:-kif_test '
(implies (and (isa ?MORAL-SHAMING Shaming)  (performedBy ?MORAL-SHAMING ?THEMAN)  (obligatedAgents TheGoldenRule ?THEMAN)) (agentViolatesObligation ?THEMAN TheGoldenRule))
'.

kif_sanity_test_0:-kif_test '
(thereExists ?THEMAN (implies 
   (thereExists ?MORAL-SHAMING (and (isa ?MORAL-SHAMING Shaming) (performedBy ?MORAL-SHAMING ?THEMAN)  (obligatedAgents TheGoldenRule ?THEMAN)))
   (agentViolatesObligation ?THEMAN TheGoldenRule)))'.


kif_sanity_test_0:-kif_test '
(implies 
       (and 
           (isa ?INST1 Exhibitionism) 
           ((PresentTenseVersionFn doneBy) ?INST1 ?INST2)) 
       (isa ?INST2 ExhibitionistOffender))'.


kif_sanity_test_0:-kif_test '
(implies 
       (and 
           (isa ?MS VisualEvent) 
           (actorPartsInvolved ?MS ?MP) 
           (isa ?MP Eyes)) 
       (holdsIn ?MS 
           (portalState ?MP OpenPortal)))'.

kif_sanity_test_0:-kif_test '
(implies 
       (and 
           (performedBy ?ACT ?WOMAN)
           (isa ?ACT (DisplayingFn SexOrgan))           
           (lawProscribesActType ?LAW Exhibitionism) 
           (subjectToCOC ?WOMAN ?LAW)) 
       (and 
           (isa ?ACT Exhibitionism) 
           (agentViolatesObligation ?WOMAN ?LAW)))'.

kif_sanity_test_0:-kif_test '
(not 
       (and 
           (subjectToCOC ?SUNBATHER KeepAreolaCoveredInPublic) 
           (objectFoundInLocation ?SUNBATHER ?BEACH) 
           (isa ?BEACH ToplessBeach)))'.


kif_sanity_test_0:-kif_test '
(implies 
       (and 
           (isa ?COC LegalCode-ModernWestern) 
           (isa ?ACT Exhibitionism) 
           (subjectToCOC ?WOMAN ?COC)
           (agentViolatesObligation ?WOMAN KeepAreolaCoveredInPublic) 
           (performedBy ?ACT ?WOMAN)) 
       (ist ?COC 
           (isa ?ACT CriminalAct)))'.

kif_sanity_test_0:-kif_test '
(implies 
       (and 
           (isa ?AREOLA 
               (BodyPartCollectionFn ?WOMAN Areola)) 
           (subjectToCOC ?WOMAN KeepAreolaCoveredInPublic) 
           (locationState ?WOMAN InPublic)) 
       (thereExists ?CLOTH 
           (and 
               (or 
                   (agentViolatesObligation ?WOMAN KeepAreolaCoveredInPublic) 
                   (covers-Generic ?CLOTH ?AREOLA)) 
               (or 
                   (agentViolatesObligation ?WOMAN KeepAreolaCoveredInPublic) 
                   (wearsClothing ?WOMAN ?CLOTH)))))'.


kif_sanity_test_0:-kif_test '
(implies 
       (and 
           (different ?THEMAN ?WOMAN) 
           (intendedMaleficiary ?CRIME ?THEMAN) 
           (deliberateActors ?CRIME ?WOMAN) 
           (behaviorCapable ?THEMAN 
               (CollectionSubsetFn Punishing 
                   (TheSetOf ?RESPONSE 
                       (maleficiary ?RESPONSE ?WOMAN))) deliberateActors)) 

       (optionAvailableToAgent-SitType ?THEMAN 
           (CollectionSubsetFn 
               (AttemptingFn Punishing) 
               (TheSetOf ?RETALIATION 
                   (and 
                       (intendedMaleficiary ?RETALIATION ?WOMAN) 
                       (purposeInEvent ?THEMAN ?RETALIATION 
                           (not 
                               (thereExists ?ANOTRACT 
                                   (and 
                                       (isa ?ANOTRACT PurposefulAction) 
                                       (startsAfterEndingOf ?ANOTRACT ?CRIME) 
                                       (maleficiary ?ANOTRACT ?THEMAN) 
                                       (deliberateActors ?ANOTRACT ?WOMAN)))))))) deliberateActors))'.

kif_sanity_test_0:-kif_test '
(beliefs InternationalCommunity 
       (thereExists ?WEAP 
           (and 
               (isa ?WEAP ChemicalWeapon) 
               (possesses Israel ?WEAP))))'.




:- if((fail)).

kif_sanity_test_0:-kif_test '
(implies 
       (hasBeliefSystems ?WOMAN Karma) 
       (beliefs ?WOMAN 
           (implies 
               (and 
                   (isa ?MORAL-SHAMING Shaming)
                   (isa ?ANY Punishing)
                   (sinner ?MORAL-SHAMING ?THEMAN) 
                   (isa ?THEMAN 
                       (IncarnationPhysicalFn ?SOUL Organism-Whole)) 
                   (not 
                       (punishmentFor ?THEMAN ?ANY 
                           (sinner ?MORAL-SHAMING ?THEMAN)))) 
               (thereExists ?NEXTLIFE 
                   (thereExists ?PUN 
                       (and 
                           (isa ?PUN Punishing) 
                           (startsAfterEndingOf ?NEXTLIFE ?THEMAN) 
                           (isa ?NEXTLIFE 
                               (IncarnationPhysicalFn ?SOUL Organism-Whole)) 
                           (punishmentFor ?NEXTLIFE ?PUN 
                               (sinner ?MORAL-SHAMING ?THEMAN))))))))'.


kif_sanity_test_0:-kif_test '
(implies 
       (and 
           (isa ?ACTION PurposefulAction) 
           (eventOccursAt ?ACTION ?LOCATION) 
           (geographicalSubRegions ?LAND ?LOCATION) 
           (territoryOf ?COUNTRY ?LAND) 
           (isa ?COUNTRY IndependentCountry) 
           (beliefs ?COUNTRY 
               (directingAgent ?ACTION ?AGENT))) 
       (causes-SitProp ?ACTION 
           (beliefs ?COUNTRY 
               (behaviorCapable ?AGENT 
                   (CollectionSubsetFn PurposefulAction 
                       (TheSetOf ?OBJ 
                           (eventOccursAt ?OBJ ?LAND))) directingAgent))))'.

:- endif.
:- if(if_defined(show_argtype_tests)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% this rule ...

kif_sanity_test_0:-kif_test((   wearing(A,B)  => has(A,B)  )).

% has to qualify argument types before canicalization

kif_sanity_test_0:-  kif_test((argInst(has,1,A) & argInst(has,2,B) => (wearing(A,B) => has(A,B)))).

% Which produced this code:
%
%       has(A, B):-wearing(A, B), argInst(has, 1, A), argInst(has, 2, B).
%
%       not_wearing(A, B):- not_has(A, B), argInst(has, 1, A), argInst(has, 2, B).  % why are the last two litterals so important? 
%
%       not_argInst(has, 1, A):- not_has(A, B), wearing(A, B), argInst(has, 2, B).   % notice we can disprove types
%
%       not_argInst(has, 2, A):- not_has(B, A), wearing(B, A), argInst(has, 1, B).


%


kif_sanity_test_0:-kif_test(has(A,B) => (argInst(has, 1, A) & argInst(has, 2, B))).

%         not_has(A, _):- not_argInst(has, 1, A).
%
%         argInst(has, 1, A):-has(A, _).
%
%         not_has(_, B)):- not_argInst(has, 2, B).
%
%         argInst(has, 2, A):-has(_, A).



kif_sanity_test_0:-kif_test(has(A,B) =>  (kb_argInst(KB, has, 1, A) & kb_argInst(KB, has, 2, B))).

% BAD!
%         (( not_has(A, _)):- not_kb_argInst( _BAD, has, 1, A)).
%
%          (kb_argInst( _BAD, has, 1, A):-has(A, _)).
%
%           (( not_has(_, A)):- not_kb_argInst( _BAD ,  has, 2, A)).
%
%            (kb_argInst( _BAD, has, 2, A):-has(_, A)).



% :- prolog.
% GOOD! (the software does this for us but wanted to show the singlton in the consequent on the conjuction)

kif_sanity_test_0:-kif_test(   argInst(kb_argInst, 1 ,KB) =>  (        has(A,B) =>  (kb_argInst(KB, has, 1, A) & kb_argInst(KB, has, 2, B)))).

%     (( not_argInst(kb_argInst, 1,KB)):-has(A, _),  not_kb_argInst(KB, has, 1, A)).
%
%     (( not_has(A, _)):-argInst(kb_argInst, 1,KB),  not_kb_argInst(KB, has, 1, A)).
%
%     (kb_argInst(KB, has, 1, A):- argInst(kb_argInst, 1,KB), has(A, _)).
%
%    (( not_argInst(kb_argInst, 1,KB)):-has(_, B),  not_kb_argInst(KB, has, 2, B)).
%
%     (( not_has(_, B)):-argInst(kb_argInst, 1,KB),  not_kb_argInst(KB, has, 2, B)).
%
%    (kb_argInst(KB, has, 2, B):-argInst(kb_argInst, 1,KB), has(_, B)).

% EVEN BETTER?
kif_sanity_test_0:-kif_test(   argInst(kb_argInst, 1 ,KB) & argInst(has, 1 , A) & argInst(has, 2 , B) =>  (  has(A,B) =>  (kb_argInst(KB, has, 1, A) & kb_argInst(KB, has, 2, B)))).


%   ain= (not_has(A, B)):- not_kb_argInst(C, has, 1, A), argInst(has, 2, B), argInst(kb_argInst, 1, C), argInst(has, 1, A)).
%
%   ain= (kb_argInst(C, has, 1, A):-has(A, B), argInst(has, 2, B), argInst(kb_argInst, 1, C), argInst(has, 1, A)).
%
%   ain= (not_argInst(has, 2, A)):-has(B, A), not_kb_argInst(C, has, 1, B), argInst(kb_argInst, 1, C), argInst(has, 1, B)).
%
%   ain= (not_argInst(kb_argInst, 1, A)):-has(B, C), not_kb_argInst(A, has, 1, B), argInst(has, 2, C), argInst(has, 1, B)).
%
%   ain= (not_argInst(has, 1, A)):-has(A, B), not_kb_argInst(C, has, 1, A), argInst(has, 2, B), argInst(kb_argInst, 1, C)).
%
%   (not_has(C, A)):- not_kb_argInst(B, has, 2, A), argInst(has, 2, A), argInst(kb_argInst, 1, B), argInst(has, 1, C)).
%
%   (kb_argInst(B, has, 2, A):-has(C, A), argInst(has, 2, A), argInst(kb_argInst, 1, B), argInst(has, 1, C)).
%
%   (not_argInst(has, 2, A)):-has(C, A), not_kb_argInst(B, has, 2, A), argInst(kb_argInst, 1, B), argInst(has, 1, C)).
%
%   (not_argInst(kb_argInst, 1, A)):-has(C, B), not_kb_argInst(A, has, 2, B), argInst(has, 2, B), argInst(has, 1, C)).
%
%   (not_argInst(has, 1, A)):-has(A, B), not_kb_argInst(C, has, 2, B), argInst(has, 2, B), argInst(kb_argInst, 1, C)).


:- endif. %if_defined(show_argtype_tests)


kif_sanity_test_0:-kif_test(all(R,isa(R,tAgent) => exists(D, (isa(D,tNose) & mudContains(R,D))))).


baseKB:sanity_test:- kif_test(all(R,'=>'(room(R) , exists(D, '&'(door(D) , has(R,D)))))).

baseKB:sanity_test:- kif_to_boxlog(not((a , b ,  c , d)),S),!,disjuncts_to_list(S,L),
  list_to_set(L,SET),forall(member(P,SET),writeln(P)),!.

baseKB:sanity_test:- logicmoo_example3.

baseKB:regression_test:- logicmoo_example3.


kif_sanity_tests:- forall(clause(kif_sanity_test_0,B),must(B)).

:- if((gethostname(ubuntu))).
% :- logicmoo_example3.

%:- prolog.
:- endif.

kif_sanity_test_0:- kif_test(all(X, (~tNotFly(X) => ~tPengin(X)))).
kif_sanity_test_0:- kif_test(not(and(omitArgIsa(RELN, N), argIsa(RELN, N, _THING)))).


kif_sanity_test_0:- kif_result((tNotFly(X):-tPengin(X))).
   % we prove we dont yet know if something not a pengiun when we call notFly and it fails
kif_sanity_test_0:- kif_result((  ~(tPengin(A)) :-  ~tNotFly(A)  )).

default_logic_uses:-uses_logic(logicmoo_kb_refution).

%:- initialization(default_logic_uses).
%:- default_logic_uses.

:- if_startup_script(tkif).
:- if_startup_script(ensure_loaded(mpred_kif_testing)).

% = % :- ensure_loaded(plarkc/mpred_clif).

% = % :- ensure_loaded(logicmoo_plarkc).

%:- autoload.
  


load_snark:- mpred_load_restore_file(never). 

:- fixup_exports.









