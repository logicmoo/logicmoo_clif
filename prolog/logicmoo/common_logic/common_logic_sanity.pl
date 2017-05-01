/* 
% ===============================================================================================================
 % File 'common_logic_sanity.pl'
 % Purpose: Emulation of OpenCyc for SWI-Prolog
 % Maintainer: Douglas Miles
 % Contact: $Author: dmiles $@users.sourceforge.net ;
 % Version: 'interface.pl' 1.0.0
 % Revision:  $Revision: 1.9 $
 % Revised At:   $Date: 2002/06/27 14:13:20 $
% ===============================================================================================================
 % File used as storage place for all predicates which make us more like Cyc
 % special module hooks into the logicmoo engine allow
 % syntax to be recocogized via our CycL/KIF handlers 
 %
 % Dec 13, 2035
 % Douglas Miles
*/

% File: /opt/PrologMUD/pack/logicmoo_base/prolog/logicmoo/plarkc/common_logic_sanity.pl
:- module(common_logic_sanity,[kif_test/1,test_boxlog/1,test_boxlog/2,test_defunctionalize/1]).


:-
 op(1199,fy,('==>')), 
 op(1198,fy,('=>')), 
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

:- ensure_loaded(library(logicmoo_snark)).

:- use_module(library(script_files)).

fst:-  set_prolog_flag(write_attributes,ignore),freeze(X,(\+ is_ftVar(X),X==[]->(dumpST,break);true)),rtrace((trace,test_boxlog(~ &(human(X), male(X))))).

:- export(fst/0).


zebra :- make,load_clif(pack(logicmoo_base/t/examples/fol/'exactly.clif')).

zebra5 :- make,load_clif(pack(logicmoo_base/t/examples/fol/'zebra5.clif')).
zebra1 :- make,load_clif(pack(logicmoo_base/t/examples/fol/'zebra1.clif')).
zebra0 :- make,load_clif(pack(logicmoo_base/t/examples/fol/'zebra0.clif')).

rzebra5 :- rtrace(load_clif(pack(logicmoo_base/t/examples/fol/'exactly.clif'))).

z:- cls,zebra5,!.
z:- rzebra5,!.

boxlog :- ensure_loaded(pack(logicmoo_base/t/examples/fol/'fol_sanity.pl')).

kif_uncompile:- pfclog_uncompile,boxlog_uncompile,clif_uncompile.
kif_compile:- clif_compile,boxlog_compile,pfclog_compile.
kif_recompile:- kif_uncompile,kif_compile.
kif_show:-  baseKB:listing(clif/1),baseKB:listing(boxlog/1),baseKB:listing(pfclog/1).
:- export(kif_recompile/0).
:- export(kif_compile/0).
:- export(kif_uncompile/0).
:- export(kif_show/0).


:- kb_shared(compile_clif/0).
clif_uncompile:-  ain(==>( \+ compile_clif)),clif_show.
clif_recompile:-  ain(==>( \+ compile_clif)), ain(==> compile_clif),clif_show.
clif_compile:-  ain(==> compile_clif),clif_show.
clif_show:-  baseKB:listing(clif/1),baseKB:listing(boxlog/1).
:- export(clif_recompile/0).
:- export(clif_compile/0).
:- export(clif_uncompile/0).
:- export(clif_show/0).

:- kb_shared(compile_boxlog/0).
:- export(boxlog_recompile/0).
:- export(boxlog_compile/0).
:- export(boxlog_uncompile/0).
:- export(boxlog_show/0).
boxlog_uncompile:-  ain(==>( \+ compile_boxlog)),boxlog_show.
boxlog_recompile:-  ain(==>( \+ compile_boxlog)), ain(==> compile_boxlog),boxlog_show.
boxlog_compile:-  ain(==> compile_boxlog),boxlog_show.
boxlog_show:-  baseKB:listing(boxlog/1),baseKB:listing(pfclog/1).

:- kb_shared(compile_pfclog/0).
:- export(pfclog_recompile/0).
:- export(pfclog_compile/0).
:- export(pfclog_uncompile/0).
:- export(pfclog_show/0).

pfclog_uncompile:-  ain(==>( \+ compile_pfclog)),pfclog_show.
pfclog_recompile:-  ain(==>( \+ compile_pfclog)), ain(==> compile_pfclog),pfclog_show.
pfclog_compile:-  ain(==> compile_pfclog),pfclog_show.
pfclog_show:-  baseKB:listing(pfclog/1).


show_kif_to_boxlog(P):- test_boxlog(P),ain(P).

 % test_boxlog(P,BoxLog):-logicmoo_motel:kif_to_motelog(P,BoxLog),!.
test_boxlog(P,BoxLog):- kif_to_boxlog(P,BoxLog).                               

test_defunctionalize(I):-defunctionalize(I,O),sdmsg(O).

sdmsg(Form):-
   if_defined(demodal_sents(_KB,Form,Out),Form=Out),
   % if_defined(local_pterm_to_sterm(OutM,Out),OutM=Out),
   wdmsgl(wdmsg,Out).

sdmsgf(Form):-
   if_defined(demodal_sents(_KB,Form,Out),Form=Out),
   % if_defined(local_pterm_to_sterm(OutM,Out),OutM=Out),
   wdmsgl(fmt9,Out).

/*
test_boxlog(P):- source_location(_,_),!,nl,nl,b_implode_varnames(P),test_boxlog(P,O),nl,nl,
   % b_implode_varnames(O),
  (is_list(O)->maplist(portray_one_line,O);dmsg(O)),flush_output.
*/

:- export(test_boxlog/1).
test_boxlog(P):- must_det(test_boxlog0(P)),!.
test_boxlog0(P):-
 \+ \+
 must_det_l((
  (nb_current('$variable_names', Vs)->b_implode_varnames0(Vs);true),
  b_implode_varnames(P),flush_output,
  wdmsg(:- test_boxlog(P)), 
  test_boxlog(P,O),
  sdmsgf(O),flush_output,
  boxlog_to_pfc(O,PFC),
  sdmsgf(pfc=PFC),flush_output)).


%% tsn is det.
%
% Tsn.
%
% tsn:- with_all_dmsg(forall(clause(kif,C),must(C))).

/*
%% regression_test is det.
%
% Hook To [baseKB:regression_test/0] For Module Common_logic_snark.
% Regression Test.
%

% baseKB:regression_test:- tsn.
*/

:- op(0,fy,(kif_test)).
%% kif_test(+Goal ) is det.
%
% Kif test
%
kif_test(TODO):-atomic(TODO),kif_io(string(TODO),current_output).
kif_test(X):- kif_add(X).
:- op(1200,fy,(kif_test)).


kif_result(_).


baseKB:sanity_test:- kif_test(all(R,'=>'(room(R) , exists(D, '&'(door(D) , has(R,D)))))).

baseKB:sanity_test:- kif_to_boxlog(not((a , b ,  c , d)),S),!,disjuncts_to_list(S,L),
  list_to_set(L,SET),forall(member(P,SET),writeln(P)),!.


kif_sanity_tests:- forall(clause(kif_sanity_test_0,B),must(B)).

default_logic_uses:-uses_logic(logicmoo_kb_refution).

%:- initialization(default_logic_uses).
%:- default_logic_uses.


:- if_startup_script(reexport(kif_sanity_tests)).

% = % :- reexport(plarkc/mpred_clif).

% = % :- reexport(logicmoo_plarkc).

%:- autoload.


:- fixup_exports.


:- test_boxlog(( ~fallacy_t(PROP) => unknown_t(PROP) v false_t(PROP) v true_t(PROP) )).
:- test_boxlog(( ~unknown_t(PROP) => true_t(PROP) v false_t(PROP)  )).
:- test_boxlog(( ~false_t(PROP) => fallacy_t(PROP) v unknown_t(PROP) v true_t(PROP) )).
:- test_boxlog(( answerable_t(PROP) <=> askable_t(PROP) & ~unknown_t(PROP) )).
:- test_boxlog(( answerable_t(PROP) => true_t(PROP) v false_t(PROP)  )).
:- test_boxlog(( askable_t(PROP) <=> ~fallacy_t(PROP) )).
:- test_boxlog(( askable_t(PROP) => true_t(PROP) v unknown_t(PROP) v false_t(PROP)  )).
:- test_boxlog(( askable_t(PROP) v fallacy_t(PROP) )).
:- test_boxlog(( asserted_t(PROP) => true_t(PROP) )).
:- test_boxlog(( fallacy_t(PROP) => false_t(PROP) & true_t(PROP) & ~unknown_t(PROP) & ~attemptable_t(PROP) )).   
:- test_boxlog(( true_t(PROP) & false_t(PROP) => fallacy_t(PROP) )).
:- test_boxlog(( true_t(PROP) v unknown_t(PROP) v false_t(PROP)  )).

:- test_boxlog(( true_t(PROP) => attemptable_t(PROP) )).
:- test_boxlog(( attemptable_t(PROP) => ~false_t(PROP) & ~fallacy_t(PROP)  )).

:- test_boxlog(( ~true_t(PROP) => false_t(PROP) v fallacy_t(PROP) v attemptable_t(PROP) )).
:- test_boxlog(( false_t(PROP) <=> ~true_t(PROP) & ~attemptable_t(PROP) & ~unknown_t(PROP) )).
:- test_boxlog(( true_t(PROP) => ~false_t(PROP) & attemptable_t(PROP) & ~unknown_t(PROP) )).
:- test_boxlog(( ~asserted_t(PROP) => attemptable_t(PROP) v false_t(PROP) v fallacy_t(PROP) )).
:- test_boxlog(( ~attemptable_t(PROP) => false_t(PROP) v fallacy_t(PROP) )).
:- test_boxlog(( attemptable_t(PROP) => ~false_t(PROP) & ~fallacy_t(PROP)  )).            
:- test_boxlog(( unknown_t(PROP) => ~true_t(PROP) & attemptable_t(PROP) & ~asserted_t(PROP) & ~false_t(PROP) )).
%:- test_boxlog(( ist(MT1,askable_t(PROP))  & genlMt(MT1,MT2) => ist(MT2, (true_t(PROP) v unknown_t(PROP) v false_t(PROP)  )))).
% :- test_boxlog(( ist(MT1,asserted_t(PROP)) & genlMt(MT1,MT2) => ist(MT2,true_t(PROP)) )).




end_of_file.

% /mnt/gggg/logicmoo_workspace/pack/logicmoo_base/prolog/logicmoo/common_logic/common_logic_sanity.pl:181
% \+ if_startup_script(sanity:reexport(kif_sanity_tests)).
% /mnt/gggg/logicmoo_workspace/pack/logicmoo_base/prolog/logicmoo/common_logic/common_logic_sanity.pl:193
% :- test_boxlog(=>(~asserted_t(PROP_VAR), v(v(attemptable_t(PROP_VAR), false_t(PROP_VAR)), fallacy_t(PROP_VAR)))).
prove_attemptable_t(A, B, anc(C, D)) :-
        prove_not_false_t(A,
                          B,
                          anc([attemptable_t(A)|C], D)),
        prove_not_fallacy_t(A,
                            B,
                            anc([attemptable_t(A)|C], D)),
        prove_not_asserted_t(A,
                             B,
                             anc([attemptable_t(A)|C], D)).
prove_false_t(A, B, anc(C, D)) :-
        prove_not_attemptable_t(A,
                             B,
                             anc([false_t(A)|C], D)),
        prove_not_fallacy_t(A,
                            B,
                            anc([false_t(A)|C], D)),
        prove_not_asserted_t(A,
                             B,
                             anc([false_t(A)|C], D)).
prove_fallacy_t(A, B, anc(C, D)) :-
        ( prove_not_attemptable_t(A,
                               B,
                               anc([fallacy_t(A)|C], D)),
          prove_not_false_t(A,
                            B,
                            anc([fallacy_t(A)|C], D))
        ),
        prove_not_asserted_t(A,
                             B,
                             anc([fallacy_t(A)|C], D)).
prove_asserted_t(A, B, anc(C, D)) :-
        ( prove_not_attemptable_t(A,
                               B,
                               anc([asserted_t(A)|C], D)),
          prove_not_false_t(A,
                            B,
                            anc([asserted_t(A)|C], D))
        ),
        prove_not_fallacy_t(A,
                            B,
                            anc([asserted_t(A)|C], D)).
% /mnt/gggg/logicmoo_workspace/pack/logicmoo_base/prolog/logicmoo/common_logic/common_logic_sanity.pl:194
% :- test_boxlog(=>(~fallacy_t(PROP_VAR), v(v(unknown_t(PROP_VAR), false_t(PROP_VAR)), true_t(PROP_VAR)))).
prove_unknown_t(A, B, anc(C, D)) :-
        prove_not_false_t(A,
                          B,
                          anc([unknown_t(A)|C], D)),
        prove_not_true_t(A,
                         B,
                         anc([unknown_t(A)|C], D)),
        prove_not_fallacy_t(A,
                            B,
                            anc([unknown_t(A)|C], D)).
prove_false_t(A, B, anc(C, D)) :-
        prove_not_unknown_t(A,
                            B,
                            anc([false_t(A)|C], D)),
        prove_not_true_t(A,
                         B,
                         anc([false_t(A)|C], D)),
        prove_not_fallacy_t(A,
                            B,
                            anc([false_t(A)|C], D)).
prove_true_t(A, B, anc(C, D)) :-
        ( prove_not_unknown_t(A,
                              B,
                              anc([true_t(A)|C], D)),
          prove_not_false_t(A,
                            B,
                            anc([true_t(A)|C], D))
        ),
        prove_not_fallacy_t(A,
                            B,
                            anc([true_t(A)|C], D)).
prove_fallacy_t(A, B, anc(C, D)) :-
        ( prove_not_unknown_t(A,
                              B,
                              anc([fallacy_t(A)|C], D)),
          prove_not_false_t(A,
                            B,
                            anc([fallacy_t(A)|C], D))
        ),
        prove_not_true_t(A,
                         B,
                         anc([fallacy_t(A)|C], D)).
% /mnt/gggg/logicmoo_workspace/pack/logicmoo_base/prolog/logicmoo/common_logic/common_logic_sanity.pl:195
% :- test_boxlog(=>(~false_t(PROP_VAR), v(v(fallacy_t(PROP_VAR), unknown_t(PROP_VAR)), true_t(PROP_VAR)))).
prove_fallacy_t(A, B, anc(C, D)) :-
        prove_not_unknown_t(A,
                            B,
                            anc([fallacy_t(A)|C], D)),
        prove_not_true_t(A,
                         B,
                         anc([fallacy_t(A)|C], D)),
        prove_not_false_t(A,
                          B,
                          anc([fallacy_t(A)|C], D)).
prove_unknown_t(A, B, anc(C, D)) :-
        prove_not_fallacy_t(A,
                            B,
                            anc([unknown_t(A)|C], D)),
        prove_not_true_t(A,
                         B,
                         anc([unknown_t(A)|C], D)),
        prove_not_false_t(A,
                          B,
                          anc([unknown_t(A)|C], D)).
prove_true_t(A, B, anc(C, D)) :-
        ( prove_not_fallacy_t(A,
                              B,
                              anc([true_t(A)|C], D)),
          prove_not_unknown_t(A,
                              B,
                              anc([true_t(A)|C], D))
        ),
        prove_not_false_t(A,
                          B,
                          anc([true_t(A)|C], D)).
prove_false_t(A, B, anc(C, D)) :-
        ( prove_not_fallacy_t(A,
                              B,
                              anc([false_t(A)|C], D)),
          prove_not_unknown_t(A,
                              B,
                              anc([false_t(A)|C], D))
        ),
        prove_not_true_t(A,
                         B,
                         anc([false_t(A)|C], D)).
% /mnt/gggg/logicmoo_workspace/pack/logicmoo_base/prolog/logicmoo/common_logic/common_logic_sanity.pl:196
% :- test_boxlog(=>(~attemptable_t(PROP_VAR), v(false_t(PROP_VAR), fallacy_t(PROP_VAR)))).
prove_false_t(A, B, anc(C, D)) :-
        prove_not_fallacy_t(A,
                            B,
                            anc([false_t(A)|C], D)),
        prove_not_attemptable_t(A,
                             B,
                             anc([false_t(A)|C], D)).
prove_fallacy_t(A, B, anc(C, D)) :-
        prove_not_false_t(A,
                          B,
                          anc([fallacy_t(A)|C], D)),
        prove_not_attemptable_t(A,
                             B,
                             anc([fallacy_t(A)|C], D)).
prove_attemptable_t(A, B, anc(C, D)) :-
        prove_not_false_t(A,
                          B,
                          anc([attemptable_t(A)|C], D)),
        prove_not_fallacy_t(A,
                            B,
                            anc([attemptable_t(A)|C], D)).
% /mnt/gggg/logicmoo_workspace/pack/logicmoo_base/prolog/logicmoo/common_logic/common_logic_sanity.pl:197
% :- test_boxlog(=>(~true_t(PROP_VAR), v(v(false_t(PROP_VAR), fallacy_t(PROP_VAR)), attemptable_t(PROP_VAR)))).
prove_false_t(A, B, anc(C, D)) :-
        prove_not_fallacy_t(A,
                            B,
                            anc([false_t(A)|C], D)),
        prove_not_attemptable_t(A,
                             B,
                             anc([false_t(A)|C], D)),
        prove_not_true_t(A,
                         B,
                         anc([false_t(A)|C], D)).
prove_fallacy_t(A, B, anc(C, D)) :-
        prove_not_false_t(A,
                          B,
                          anc([fallacy_t(A)|C], D)),
        prove_not_attemptable_t(A,
                             B,
                             anc([fallacy_t(A)|C], D)),
        prove_not_true_t(A,
                         B,
                         anc([fallacy_t(A)|C], D)).
prove_attemptable_t(A, B, anc(C, D)) :-
        ( prove_not_false_t(A,
                            B,
                            anc([attemptable_t(A)|C], D)),
          prove_not_fallacy_t(A,
                              B,
                              anc([attemptable_t(A)|C], D))
        ),
        prove_not_true_t(A,
                         B,
                         anc([attemptable_t(A)|C], D)).
prove_true_t(A, B, anc(C, D)) :-
        ( prove_not_false_t(A,
                            B,
                            anc([true_t(A)|C], D)),
          prove_not_fallacy_t(A,
                              B,
                              anc([true_t(A)|C], D))
        ),
        prove_not_attemptable_t(A,
                             B,
                             anc([true_t(A)|C], D)).
% /mnt/gggg/logicmoo_workspace/pack/logicmoo_base/prolog/logicmoo/common_logic/common_logic_sanity.pl:198
% :- test_boxlog(=>(~unknown_t(PROP_VAR), v(true_t(PROP_VAR), false_t(PROP_VAR)))).
prove_true_t(A, B, anc(C, D)) :-
        prove_not_false_t(A,
                          B,
                          anc([true_t(A)|C], D)),
        prove_not_unknown_t(A,
                            B,
                            anc([true_t(A)|C], D)).
prove_false_t(A, B, anc(C, D)) :-
        prove_not_true_t(A,
                         B,
                         anc([false_t(A)|C], D)),
        prove_not_unknown_t(A,
                            B,
                            anc([false_t(A)|C], D)).
prove_unknown_t(A, B, anc(C, D)) :-
        prove_not_true_t(A,
                         B,
                         anc([unknown_t(A)|C], D)),
        prove_not_false_t(A,
                          B,
                          anc([unknown_t(A)|C], D)).
% /mnt/gggg/logicmoo_workspace/pack/logicmoo_base/prolog/logicmoo/common_logic/common_logic_sanity.pl:199
% :- test_boxlog(<=>(answerable_t(PROP_VAR), &(askable_t(PROP_VAR), ~unknown_t(PROP_VAR)))).
% /mnt/gggg/logicmoo_workspace/pack/logicmoo_base/prolog/logicmoo/common_logic/common_logic_sanity.pl:200
% :- test_boxlog(=>(answerable_t(PROP_VAR), v(true_t(PROP_VAR), false_t(PROP_VAR)))).
prove_true_t(A, B, anc(C, D)) :-
        prove_not_false_t(A,
                          B,
                          anc([true_t(A)|C], D)),
        prove_answerable_t(A,
                           B,
                           anc([true_t(A)|C], D)).
prove_false_t(A, B, anc(C, D)) :-
        prove_not_true_t(A,
                         B,
                         anc([false_t(A)|C], D)),
        prove_answerable_t(A,
                           B,
                           anc([false_t(A)|C], D)).
prove_not_answerable_t(A, B, anc(C, D)) :-
        prove_not_true_t(A,
                         B,
                         anc(C, [answerable_t(A)|D])),
        prove_not_false_t(A,
                          B,
                          anc(C, [answerable_t(A)|D])).
% /mnt/gggg/logicmoo_workspace/pack/logicmoo_base/prolog/logicmoo/common_logic/common_logic_sanity.pl:201
% :- test_boxlog(<=>(askable_t(PROP_VAR), ~fallacy_t(PROP_VAR))).
% /mnt/gggg/logicmoo_workspace/pack/logicmoo_base/prolog/logicmoo/common_logic/common_logic_sanity.pl:202
% :- test_boxlog(=>(askable_t(PROP_VAR), v(v(true_t(PROP_VAR), unknown_t(PROP_VAR)), false_t(PROP_VAR)))).
prove_true_t(A, B, anc(C, D)) :-
        prove_not_unknown_t(A,
                            B,
                            anc([true_t(A)|C], D)),
        prove_not_false_t(A,
                          B,
                          anc([true_t(A)|C], D)),
        prove_askable_t(A,
                        B,
                        anc([true_t(A)|C], D)).
prove_unknown_t(A, B, anc(C, D)) :-
        prove_not_true_t(A,
                         B,
                         anc([unknown_t(A)|C], D)),
        prove_not_false_t(A,
                          B,
                          anc([unknown_t(A)|C], D)),
        prove_askable_t(A,
                        B,
                        anc([unknown_t(A)|C], D)).
prove_false_t(A, B, anc(C, D)) :-
        ( prove_not_true_t(A,
                           B,
                           anc([false_t(A)|C], D)),
          prove_not_unknown_t(A,
                              B,
                              anc([false_t(A)|C], D))
        ),
        prove_askable_t(A,
                        B,
                        anc([false_t(A)|C], D)).
prove_not_askable_t(A, B, anc(C, D)) :-
        ( prove_not_true_t(A,
                           B,
                           anc(C, [askable_t(A)|D])),
          prove_not_unknown_t(A,
                              B,
                              anc(C, [askable_t(A)|D]))
        ),
        prove_not_false_t(A,
                          B,
                          anc(C, [askable_t(A)|D])).
% /mnt/gggg/logicmoo_workspace/pack/logicmoo_base/prolog/logicmoo/common_logic/common_logic_sanity.pl:203
% :- test_boxlog(v(askable_t(PROP_VAR), fallacy_t(PROP_VAR))).
prove_askable_t(A, B, anc(C, D)) :-
        prove_not_fallacy_t(A,
                            B,
                            anc([askable_t(A)|C], D)).
prove_fallacy_t(A, B, anc(C, D)) :-
        prove_not_askable_t(A,
                            B,
                            anc([fallacy_t(A)|C], D)).
% /mnt/gggg/logicmoo_workspace/pack/logicmoo_base/prolog/logicmoo/common_logic/common_logic_sanity.pl:204
% :- test_boxlog(=>(asserted_t(PROP_VAR), true_t(PROP_VAR))).
prove_true_t(A, B, anc(C, D)) :-
        prove_asserted_t(A,
                         B,
                         anc([true_t(A)|C], D)).
prove_not_asserted_t(A, B, anc(C, D)) :-
        prove_not_true_t(A,
                         B,
                         anc(C, [asserted_t(A)|D])).
% /mnt/gggg/logicmoo_workspace/pack/logicmoo_base/prolog/logicmoo/common_logic/common_logic_sanity.pl:205
% :- test_boxlog(=>(attemptable_t(PROP_VAR), &(~false_t(PROP_VAR), ~fallacy_t(PROP_VAR)))).
prove_not_false_t(A, B, anc(C, D)) :-
        prove_attemptable_t(A,
                        B,
                        anc(C, [false_t(A)|D])).
prove_not_fallacy_t(A, B, anc(C, D)) :-
        prove_attemptable_t(A,
                        B,
                        anc(C, [fallacy_t(A)|D])).
prove_not_attemptable_t(A, B, anc(C, D)) :-
        (   prove_false_t(A,
                          B,
                          anc(C, [attemptable_t(A)|D]))
        ;   prove_fallacy_t(A,
                            B,
                            anc(C, [attemptable_t(A)|D]))
        ).
% /mnt/gggg/logicmoo_workspace/pack/logicmoo_base/prolog/logicmoo/common_logic/common_logic_sanity.pl:206
% :- test_boxlog(=>(fallacy_t(PROP_VAR), &(&(&(false_t(PROP_VAR), true_t(PROP_VAR)), ~unknown_t(PROP_VAR)), ~attemptable_t(PROP_VAR)))).
prove_false_t(A, B, anc(C, D)) :-
        prove_fallacy_t(A,
                        B,
                        anc([false_t(A)|C], D)).
prove_true_t(A, B, anc(C, D)) :-
        prove_fallacy_t(A,
                        B,
                        anc([true_t(A)|C], D)).
prove_not_unknown_t(A, B, anc(C, D)) :-
        prove_fallacy_t(A,
                        B,
                        anc(C, [unknown_t(A)|D])).
prove_not_attemptable_t(A, B, anc(C, D)) :-
        prove_fallacy_t(A,
                        B,
                        anc(C, [attemptable_t(A)|D])).
prove_not_fallacy_t(A, B, anc(C, D)) :-
        (   (   (   prove_not_false_t(A,
                                      B,
                                      anc(C,
                                          [fallacy_t(A)|D]))
                ;   prove_not_true_t(A,
                                     B,
                                     anc(C, [fallacy_t(A)|D]))
                )
            ;   prove_unknown_t(A,
                                B,
                                anc(C, [fallacy_t(A)|D]))
            )
        ;   prove_attemptable_t(A,
                             B,
                             anc(C, [fallacy_t(A)|D]))
        ).
% /mnt/gggg/logicmoo_workspace/pack/logicmoo_base/prolog/logicmoo/common_logic/common_logic_sanity.pl:207
% :- test_boxlog(<=>(false_t(PROP_VAR), &(&(~true_t(PROP_VAR), ~attemptable_t(PROP_VAR)), ~unknown_t(PROP_VAR)))).
% /mnt/gggg/logicmoo_workspace/pack/logicmoo_base/prolog/logicmoo/common_logic/common_logic_sanity.pl:208
% :- test_boxlog(=>(attemptable_t(PROP_VAR), &(~false_t(PROP_VAR), ~fallacy_t(PROP_VAR)))).
prove_not_false_t(A, B, anc(C, D)) :-
        prove_attemptable_t(A,
                         B,
                         anc(C, [false_t(A)|D])).
prove_not_fallacy_t(A, B, anc(C, D)) :-
        prove_attemptable_t(A,
                         B,
                         anc(C, [fallacy_t(A)|D])).
prove_not_attemptable_t(A, B, anc(C, D)) :-
        (   prove_false_t(A,
                          B,
                          anc(C, [attemptable_t(A)|D]))
        ;   prove_fallacy_t(A,
                            B,
                            anc(C, [attemptable_t(A)|D]))
        ).
% /mnt/gggg/logicmoo_workspace/pack/logicmoo_base/prolog/logicmoo/common_logic/common_logic_sanity.pl:209
% :- test_boxlog(=>(&(true_t(PROP_VAR), false_t(PROP_VAR)), fallacy_t(PROP_VAR))).
prove_fallacy_t(A, B, anc(C, D)) :-
        prove_true_t(A,
                     B,
                     anc([fallacy_t(A)|C], D)),
        prove_false_t(A,
                      B,
                      anc([fallacy_t(A)|C], D)).
prove_not_true_t(A, B, anc(C, D)) :-
        prove_false_t(A, B, anc(C, [true_t(A)|D])),
        prove_not_fallacy_t(A,
                            B,
                            anc(C, [true_t(A)|D])).
prove_not_false_t(A, B, anc(C, D)) :-
        prove_true_t(A, B, anc(C, [false_t(A)|D])),
        prove_not_fallacy_t(A,
                            B,
                            anc(C, [false_t(A)|D])).
% /mnt/gggg/logicmoo_workspace/pack/logicmoo_base/prolog/logicmoo/common_logic/common_logic_sanity.pl:210
% :- test_boxlog(=>(true_t(PROP_VAR), &(&(~false_t(PROP_VAR), attemptable_t(PROP_VAR)), ~unknown_t(PROP_VAR)))).
prove_not_false_t(A, B, anc(C, D)) :-
        prove_true_t(A, B, anc(C, [false_t(A)|D])).
prove_attemptable_t(A, B, anc(C, D)) :-
        prove_true_t(A,
                     B,
                     anc([attemptable_t(A)|C], D)).
prove_not_unknown_t(A, B, anc(C, D)) :-
        prove_true_t(A,
                     B,
                     anc(C, [unknown_t(A)|D])).
prove_not_true_t(A, B, anc(C, D)) :-
        (   (   prove_false_t(A,
                              B,
                              anc(C, [true_t(A)|D]))
            ;   prove_not_attemptable_t(A,
                                     B,
                                     anc(C, [true_t(A)|D]))
            )
        ;   prove_unknown_t(A,
                            B,
                            anc(C, [true_t(A)|D]))
        ).
% /mnt/gggg/logicmoo_workspace/pack/logicmoo_base/prolog/logicmoo/common_logic/common_logic_sanity.pl:211
% :- test_boxlog(=>(true_t(PROP_VAR), attemptable_t(PROP_VAR))).
prove_attemptable_t(A, B, anc(C, D)) :-
        prove_true_t(A,
                     B,
                     anc([attemptable_t(A)|C], D)).
prove_not_true_t(A, B, anc(C, D)) :-
        prove_not_attemptable_t(A,
                            B,
                            anc(C, [true_t(A)|D])).
% /mnt/gggg/logicmoo_workspace/pack/logicmoo_base/prolog/logicmoo/common_logic/common_logic_sanity.pl:212
% :- test_boxlog(v(v(true_t(PROP_VAR), unknown_t(PROP_VAR)), false_t(PROP_VAR))).
prove_true_t(A, B, anc(C, D)) :-
        prove_not_unknown_t(A,
                            B,
                            anc([true_t(A)|C], D)),
        prove_not_false_t(A,
                          B,
                          anc([true_t(A)|C], D)).
prove_unknown_t(A, B, anc(C, D)) :-
        prove_not_true_t(A,
                         B,
                         anc([unknown_t(A)|C], D)),
        prove_not_false_t(A,
                          B,
                          anc([unknown_t(A)|C], D)).
prove_false_t(A, B, anc(C, D)) :-
        prove_not_true_t(A,
                         B,
                         anc([false_t(A)|C], D)),
        prove_not_unknown_t(A,
                            B,
                            anc([false_t(A)|C], D)).
% /mnt/gggg/logicmoo_workspace/pack/logicmoo_base/prolog/logicmoo/common_logic/common_logic_sanity.pl:213
% :- test_boxlog(=>(unknown_t(PROP_VAR), &(&(&(~true_t(PROP_VAR), attemptable_t(PROP_VAR)), ~asserted_t(PROP_VAR)), ~false_t(PROP_VAR)))).
prove_not_true_t(A, B, anc(C, D)) :-
        prove_unknown_t(A,
                        B,
                        anc(C, [true_t(A)|D])).
prove_attemptable_t(A, B, anc(C, D)) :-
        prove_unknown_t(A,
                        B,
                        anc([attemptable_t(A)|C], D)).
prove_not_asserted_t(A, B, anc(C, D)) :-
        prove_unknown_t(A,
                        B,
                        anc(C, [asserted_t(A)|D])).
prove_not_false_t(A, B, anc(C, D)) :-
        prove_unknown_t(A,
                        B,
                        anc(C, [false_t(A)|D])).
prove_not_unknown_t(A, B, anc(C, D)) :-
        (   (   (   prove_true_t(A,
                                 B,
                                 anc(C, [unknown_t(A)|D]))
                ;   prove_not_attemptable_t(A,
                                         B,
                                         anc(C,
                                             [unknown_t(A)|D]))
                )
            ;   prove_asserted_t(A,
                                 B,
                                 anc(C, [unknown_t(A)|D]))
            )
        ;   prove_false_t(A,
                          B,
                          anc(C, [unknown_t(A)|D]))
        ).

