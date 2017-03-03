:- module(logicmoo_repl,[]).
/*
 Basic startup

*/

:- set_prolog_flag(lm_expanders,default).
:- set_prolog_flag(dialect_pfc,default).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% LOAD WEB HOOKS AND LOGTALK
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- if(\+ current_module(baseKB)).
:- statistics.
:- system:ensure_loaded(library(logicmoo_webbot)).
:- set_module(baseKB:class(development)).
:- set_prolog_flag(access_level,system).
:- set_prolog_flag(logicmoo_qsave,true).
:- else.
:- set_prolog_flag(logicmoo_qsave,false).
:- endif.

:- system:use_module(library(pfc)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% INIT BASIC FORWARD CHAINING SUPPORT
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- '$set_source_module'(baseKB).
:- '$set_typein_module'(baseKB).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% [Optionaly] Load the EXTRA Logicmoo WWW System
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% forward chaing state browser
:- system:ensure_loaded(library(xlisting_web)).


add_history_ideas:- 
       % use_module(library(editline)),
        use_module(library(prolog_history)),

        add_history(start_telnet),
        add_history(help(match_regex/2)),
        add_history(list_undefined),
        add_history(listing(after_boot_goal/1)),
	add_history(ensure_loaded(run_mud_game)),
	add_history(statistics),        
        add_history(qsave_lm(lm_repl)),        
        add_history(make),        
        add_history(mmake),
        add_history(login_and_run),        
        forall(system:after_boot_goal(G),add_history(G)),
        add_history(loadSumo),
        add_history(loadTinyKB),
        add_history(threads),
        add_history(after_boot_call(must_det)),
        add_history(after_boot_call),
        add_history(use_module(library(sexpr_reader))),
        add_history(input_to_forms("( #\\a #\\u0009 . #\\bell )",'$VAR'('O'),'$VAR'('Vs'))),
        add_history(tstl),
        add_history(qconsult_kb7166),
        add_history(ensure_loaded(library(logicmoo_webbot))),
        add_history(ensure_loaded(library(logicmoo_repl))),
        add_history(ensure_loaded(library(logicmoo_engine))),
        add_history(ensure_loaded(library(logicmoo_user))),
        add_history([init_mud_server]),
        add_history([init_mud_server_run]),
        !.

:- during_boot(add_history_ideas).

:- '$set_source_module'(baseKB).
:- '$set_typein_module'(baseKB).

:- set_prolog_flag(do_renames,restore).
:- use_module(library(gvar_syntax)).
:- system:use_module(library(dif)).

:- baseKB:import(dif:dif/2).
:- baseKB:export(dif:dif/2).
:- baseKB:use_module(library(prolog_predicate)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% These are probly loaded by other modules
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%:- ensure_loaded(library(multivar)).
%:- ensure_loaded(library(udt)).
%:- ensure_loaded(library(atts)).
%:- use_module(library(persistency)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% [Optionaly] Load the EXTRA Logicmoo WWW System
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% :- baseKB:ensure_loaded(library(xlisting_web)).
% :- (if_file_exists(ensure_loaded(library(logicmoo/logicmoo_run_pldoc)))).
% :- (if_file_exists(ensure_loaded(library(logicmoo/logicmoo_run_swish)))).

:- after_boot((system:kill_unsafe_preds)).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% BINA48 Code!!!
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%:- load_library_system(daydream).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% INIT LOGICMOO (AUTOEXEC)  Load the infernce engine
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- set_prolog_flag(do_renames,restore).
:- baseKB:ensure_loaded(library(pfc)).
:- set_prolog_flag(do_renames,restore).

:- ls.

:- load_library_system(logicmoo_user).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% SETUP SANITY TEST EXTENSIONS
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
decl_kb_shared_tests:-
 sanity(listing((kb_shared)/1)),
 kb_shared(baseKB:sanity_test/0),
 kb_shared(baseKB:regression_test/0),
 kb_shared(baseKB:feature_test/0),
 kb_shared((
        baseKB:feature_test/0,
        baseKB:mud_test/2,
        baseKB:regression_test/0,
        baseKB:sanity_test/0,
        baseKB:agent_call_command/2,
        action_info/2,
        type_action_info/3)).

:- decl_kb_shared_tests.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% ONE SANITY TEST
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
system:iRR7_test:-
 baseKB:(
    ain(isa(iRR7,tRR)),
    ain(genls(tRR,tRRP)),
    (\+ tRRP(iRR7) -> (xlisting(iRR7),xlisting(tRRP)) ; true),
    must( isa(iRR7,tRR) ),
    must( isa(iRR7,tRRP) ),
    must( tRRP(iRR7) )).

% :- iRR7_test.

:- after_boot_sanity_test(iRR7_test).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% KIF READER SANITY TESTS
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

show_kif(Str):- sanity(must(input_to_forms_debug(Str,kif_assertion_recipe))).


:- add_history((input_to_forms("
(=> (disjointDecomposition ?CLASS @ROW) (forall (?ITEM1 ?ITEM2) 
  (=> (and (inList ?ITEM1 (ListFn @ROW)) (inList ?ITEM2 (ListFn @ROW)) (not (equal ?ITEM1 ?ITEM2))) 
   (disjoint ?ITEM1 ?ITEM2))))"
  ,O,Vs),!,wdmsg(O+Vs))).

/*
:- must(input_to_forms("(=> (disjointDecomposition ?CLASS @ROW) (forall (?ITEM1 ?ITEM2) (=> (and (inList ?ITEM1 (ListFn @ROW)) (inList ?ITEM2 (ListFn @ROW)) (not (equal ?ITEM1 ?ITEM2))) (disjoint ?ITEM1 ?ITEM2))))",O,Vs)),!,wdmsg(O+Vs).
:- must(((input_to_forms("(=> (disjointDecomposition ?CLASS @ROW) (forall (?ITEM1 ?ITEM2) (=> (and (inList ?ITEM1 (ListFn @ROW)) (inList ?ITEM2 (ListFn @ROW)) (not (equal ?ITEM1 ?ITEM2))) (disjoint ?ITEM1 ?ITEM2))))",O,Vs)),!,wdmsg(O+Vs))).
:- must(input_to_forms_debug("(=> (disjointDecomposition ?CLASS @ROW) (forall (?ITEM1 ?ITEM2) (=> (and (inList ?ITEM1 (ListFn @ROW)) (inList ?ITEM2 (ListFn @ROW)) (not (equal ?ITEM1 ?ITEM2))) (disjoint ?ITEM1 ?ITEM2))))",kif_assertion_recipe)).
*/
:- show_kif("(=> (disjointDecomposition ?CLASS @ROW) (forall (?ITEM1 ?ITEM2) (=> (and (inList ?ITEM1 (ListFn @ROW)) (inList ?ITEM2 (ListFn @ROW)) (not (equal ?ITEM1 ?ITEM2))) (disjoint ?ITEM1 ?ITEM2))))").
:- show_kif("(=> (isa ?NUMBER ImaginaryNumber) (exists (?REAL) (and (isa ?REAL RealNumber) (equal ?NUMBER (MultiplicationFn ?REAL (SquareRootFn -1))))))").
:- show_kif("(=> (isa ?PROCESS DualObjectProcess) (exists (?OBJ1 ?OBJ2) (and (patient ?PROCESS ?OBJ1) (patient ?PROCESS ?OBJ2) (not (equal ?OBJ1 ?OBJ2)))))").
:- show_kif("(=> (contraryAttribute @ROW) (=> (inList ?ELEMENT (ListFn @ROW)) (isa ?ELEMENT Attribute)))").
:- show_kif("(=> (and (contraryAttribute @ROW1) (identicalListItems (ListFn @ROW1) (ListFn @ROW2))) (contraryAttribute @ROW2))").
:- show_kif("(=> (contraryAttribute @ROW) (forall (?ATTR1 ?ATTR2) (=> (and (equal ?ATTR1 (ListOrderFn (ListFn @ROW) ?NUMBER1)) (equal ?ATTR2 (ListOrderFn (ListFn @ROW) ?NUMBER2)) (not (equal ?NUMBER1 ?NUMBER2))) (=> (property ?OBJ ?ATTR1) (not (property ?OBJ ?ATTR2))))))").
:- show_kif("(=> (equal ?NUMBER (MultiplicationFn 1 ?NUMBER)) (equal (MeasureFn ?NUMBER CelsiusDegree) (MeasureFn (DivisionFn (SubtractionFn ?NUMBER 32) 1.8) FahrenheitDegree)))").
:- show_kif("(DivisionFn (SubtractionFn ?NUMBER 32) 1.8 #C(1.2 9))").


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% LOAD LOGICMOO KB EXTENSIONS
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- check_clause_counts.

% :- load_library_system(library(logicmoo_engine)).
% :- load_library_system(logicmoo(logicmoo_plarkc)).

:- after_boot((set_prolog_flag(pfc_booted,true),flag_call(runtime_debug=true),set_prolog_flag(read_attvars,false))).

:- nb_setval('$oo_stack',[]).
:- b_setval('$oo_stack',[]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% QSAVE LM_REPL
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% {flatTrans(G)}==>{listing(G/2)}.
:- if(current_prolog_flag(logicmoo_qsave,true)).
:- statistics.
:- baseKB:qsave_lm(lm_repl).
:- endif.



