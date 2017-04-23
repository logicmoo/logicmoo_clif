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
:- module(common_logic_sanity,[kif_test/1]).


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


:- kb_shared(compile_clif/0).
clif_uncompile:-  ain(==>( \+ compile_clif)),clif_show.
clif_recompile:-  ain(==>( \+ compile_clif)), ain(==> compile_clif),clif_show.
clif_compile:-  ain(==> compile_clif),clif_show.
clif_show:-  listing(clif/1),listing(boxlog/1).
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
boxlog_show:-  listing(boxlog/1),listing(pfclog/1).

:- kb_shared(compile_pfclog/0).
:- export(pfclog_recompile/0).
:- export(pfclog_compile/0).
:- export(pfclog_uncompile/0).
:- export(pfclog_show/0).

pfclog_uncompile:-  ain(==>( \+ compile_pfclog)),pfclog_show.
pfclog_recompile:-  ain(==>( \+ compile_pfclog)), ain(==> compile_pfclog),pfclog_show.
pfclog_compile:-  ain(==> compile_pfclog),pfclog_show.
pfclog_show:-  listing(pfclog/1).


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


