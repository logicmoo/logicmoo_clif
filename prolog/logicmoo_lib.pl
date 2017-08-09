/*  LogicMOO User Modules Setup
%
%
% Dec 13, 2035
% Douglas Miles

*/
:- module(logicmoo_lib,
 [
 % logicmoo_user_stacks/0,
 ]).

/*

:- current_prolog_flag(readline,Was),writeln(readline=Was).
:- if(exists_source(library(editline))).
:- set_prolog_flag(readline,editline).
:- endif.
% :- set_prolog_flag(readline,true).

:- if(current_prolog_flag(readline,editline)).
:- system:ensure_loaded(library(readline)).
:- listing(prolog:history/2).
:- abolish(prolog:history/2).
:- system:reconsult(library(editline)).
:- else.
:- if(exists_source(library(readline))).
:- if(exists_source(library(editline))).
:- system:ensure_loaded(library(editline)).
:- listing(prolog:history/2).
:- abolish(prolog:history/2).
:- endif.
:- unload_file(library(readline)).
:- system:consult(library(readline)).
:- endif.
:- endif.
:- current_prolog_flag(readline,Was),writeln(readline=Was).
*/

:- set_prolog_flag(report_error,true).
:- set_prolog_flag(access_level,system).
:- set_prolog_flag(debug_on_error,true).
:- set_prolog_flag(optimise,false).
:- set_prolog_flag(last_call_optimisation,false).
/*
:- set_prolog_flag(fileerrors,false).
:- set_prolog_flag(debug,true).
:- set_prolog_flag(gc,false).
:- set_prolog_flag(gc,true).
:- debug.
*/


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% SETUP KB EXTENSIONS
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- '$set_typein_module'(baseKB).
:- '$set_source_module'(baseKB).

:- use_module(library(plunit)).
:- kb_global(plunit:loading_unit/4).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- dmsg("LOGICMOO/CYC Alignment util").
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- set_prolog_flag(do_renames,restore).
:- gripe_time(60,baseKB:ensure_loaded(library('logicmoo/plarkc/logicmoo_i_cyc_rewriting'))).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- dmsg("[Required] Load the Logicmoo Web System").
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- user:use_module(library(logicmoo_util_common)).

:- if(\+ app_argv('--nonet')).
:- load_library_system(library(logicmoo_webbot)).
:- endif.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- dmsg("[Required] Load the Logicmoo Type System").
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- load_library_system(library(logicmoo_typesystem)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- dmsg("[Mostly Required] Load the Logicmoo Plan Generator System").
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- load_library_system(library(logicmoo_planner)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- dmsg("[Mostly Required] Load the Prolog LarKC System").
% LOAD CYC KB EXTENSIONS
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- load_library_system(library(logicmoo_plarkc)).
:- check_clause_counts.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- dmsg("SETUP CYC KB EXTENSIONS (TINYKB)").
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- during_boot(set_prolog_flag(do_renames,restore)).
:- gripe_time(60,baseKB:ensure_loaded(library('logicmoo/plarkc/logicmoo_u_cyc_kb_tinykb.pl'))).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- dmsg("SETUP CYC KB EXTENSIONS (FULLKB)").
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- during_boot(set_prolog_flag(do_renames,restore)).
%:- gripe_time(60,baseKB:ensure_loaded(library('logicmoo/plarkc/logicmoo_i_cyc_kb.pl'))).
:- check_clause_counts.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- dmsg("[Mostly Required] Load the Logicmoo Parser/Generator System").
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- load_library_system(library(parser_all)).
%:- load_library_system(library(parser_e2c)).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- dmsg("[Required] Load the CYC Network Client and Logicmoo CycServer Emulator (currently server is disabled)").
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% :- load_library_system(library(plark/logicmoo/logicmoo_u_cyc_api)).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- dmsg("[Optional] NOT YET Load the Logicmoo RDF/OWL Browser System").
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% :- load_library_system(logicmoo(mpred_online/mpred_rdf)).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- dmsg("[Debugging] Normarily this set as 'true' can interfere with debugging").
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% :- set_prolog_flag(gc,false).
% Yet turning it off we cant even startup without crashing
% :- set_prolog_flag(gc,true).


% :- sanity(doall(printAll(current_prolog_flag(_N,_V)))).
% :- after_boot(during_net_boot(kill_unsafe_preds)).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Regression tests that first run whenever a person starts the MUD on the public server
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%:- load_library_system(pack(logicmoo_base/t/examples/pfc/'sanity_col_as_unary.pfc')).
%:- load_library_system(pack(logicmoo_base/t/examples/pfc/'sanity_birdt.pfc')).
%:- load_library_system(pack(logicmoo_base/t/examples/pfc/'sanity_sv.pfc')).
%:- load_library_system(pack(logicmoo_base/t/examples/pfc/'sanity_foob.pfc')).


