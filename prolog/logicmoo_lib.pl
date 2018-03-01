/*  LogicMOO User Modules Setup
%
%
% Dec 13, 2035
% Douglas Miles

*/
:- module(logicmoo_lib,
 [
 % logicmoo_user_stacks/0, 
  maybe_save_lm/0
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



% :- multifile prolog:message//1, prolog:message_hook/3.
% prolog:message(ignored_weak_import(Into, From:PI))--> { nonvar(Into),Into \== system,dtrace(dmsg(ignored_weak_import(Into, From:PI))),fail}.
% prolog:message(Into)--> { nonvar(Into),functor(Into,_F,A),A>1,arg(1,Into,N),\+ number(N),dtrace(wdmsg(Into)),fail}.
% prolog:message_hook(T,error,Warn):- dtrace(wdmsg(nessage_hook(T,warning,Warn))),fail.
% prolog:message_hook(T,warning,Warn):- dtrace(wdmsg(nessage_hook(T,warning,Warn))),fail.

:- user:ensure_loaded(library(logicmoo_utils)).
:- ensure_loaded(library(rtrace)).
:- ensure_loaded(library(dmsg)).

:- if(app_argv('--wamcl'); app_argv('--lisp')).
:- use_module(library(wamcl_runtime)).
:- endif.


/*
:- flag_call(unsafe_speedups=true).
:- flag_call(runtime_debug=0).
:- flag_call(runtime_debug=2).
% ?- current_prolog_flag(unsafe_speedups , true) .
:- flag_call(unsafe_speedups=false).
*/
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- dmsg("SET TOPLEVEL OPTIONS").
% ?- listing.  (uses varaibles)
% slows the system startup down consideraly
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% :- set_prolog_flag(toplevel_print_factorized,true). % default false
%:- set_prolog_flag(toplevel_mode,backtracking). % OR recursive 
%:- after_boot(dmsg(qconsult_kb7166)).
% :- use_listing_vars.
%:- set_prolog_flag(write_attributes,portray).
% :- debug.

/*
:- set_prolog_flag(fileerrors,false).
:- set_prolog_flag(debug,true).
:- set_prolog_flag(gc,false).
:- set_prolog_flag(gc,true).
:- debug.
*/

:- set_prolog_flag(report_error,true).
:- set_prolog_flag(access_level,system).
:- set_prolog_flag(toplevel_print_anon,true).
:- set_prolog_flag(debug_on_error,true).
:- set_prolog_flag(optimise,false).
:- set_prolog_flag(last_call_optimisation,false).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- dmsg("SETUP KB EXTENSIONS").
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- '$set_typein_module'(baseKB).
:- '$set_source_module'(baseKB).

:- use_module(library(plunit)).
:- kb_global(plunit:loading_unit/4).

% :- ['/home/prologmud_server/lib/swipl/pack/prologmud_samples/prolog/prologmud_sample_games/run_clio'].

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- dmsg("PACK LOADER").
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- user:load_library_system(logicmoo_packs).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- dmsg("AUTOLOAD PACKAGES").
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- during_boot(rescan_pack_autoload_packages).

%:- reload_library_index.
%:- autoload([verbose(true)]).
:- reload_library_index.

:- if(\+ current_module(baseKB)).
:- set_prolog_flag(logicmoo_qsave,true).
:- else.
:- set_prolog_flag(logicmoo_qsave,false).
:- endif.

:-set_prolog_flag(access_level,system).

:- multifile user:file_search_path/2.
:- dynamic   user:file_search_path/2.

:- user:use_module(library(logicmoo_util_common)).


:- if(exists_source(library(yall))).
:-  multifile(yall:lambda_functor/1),
   dynamic(yall:lambda_functor/1),
   with_no_mpred_expansions(use_module(yall:library(yall),[])),
   show_call(retractall(yall:lambda_functor('/'))).
:- endif.


:- current_prolog_flag(os_argv,[swipl])->
   set_prolog_flag(os_argv,[swipl, '-f', '/dev/null','--nonet','--unsafe','--']); true.

   

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- dmsg("LOAD PARTS OF SYSTEM EARLY").
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 % :- set_prolog_flag(subclause_expansion,default).
 % :- set_prolog_flag(subclause_expansion,false).
 % :- set_prolog_flag(dialect_pfc,default).
:- user:load_library_system(logicmoo_swilib).


:- if(exists_source(library(pce_emacs))).
:- user:use_module(library(pce_emacs)).
:- endif.

:- multifile(swish_trace:installed/1).
:-   dynamic(swish_trace:installed/1).
:-  volatile(swish_trace:installed/1).

:- if(exists_source(library(semweb/rdf_db))).
:- use_module(pengine_sandbox:library(semweb/rdf_db)).
:- endif.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- dmsg("SETUP LOGICMOO OPERATORS").
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- locally(set_prolog_flag(access_level,system),
 ((op(200,fy,'-'),op(300,fx,'-'),
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
 op(300,fx,'-'),
 op(1199,fx,('==>'))))).




%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- dmsg("SETUP PATHS FOR PROLOGMUD/LOGICMOO").
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% :- during_boot((user:ensure_loaded(setup_paths))).

:- user:use_module(library('file_scope')).
% :- use_module(library('clause_expansion')).

 % :- set_prolog_flag(subclause_expansion,true).

% :- during_boot((sanity((lmce:current_smt(SM,M),writeln(current_smt(SM,M)))))).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- dmsg("LOAD LOGICMOO UTILS").
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- user:ensure_loaded(library(logicmoo_utils)).

:- multifile(prolog:make_hook/2).
:- dynamic(prolog:make_hook/2).
prolog:make_hook(before, C):- wdmsg(prolog:make_hook(before, C)),fail.
prolog:make_hook(after, C):- wdmsg(prolog:make_hook(after, C)),maybe_save_lm,fail.

maybe_save_lm:- \+ current_prolog_flag(logicmoo_qsave,true),!.
maybe_save_lm:- current_predicate(lmcache:qconsulted_kb7166/0),call(call,lmcache:qconsulted_kb7166),!.
maybe_save_lm:- qsave_lm(lm_repl4),!.



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
:- whenever_flag_permits(load_network,load_library_system(library(logicmoo_webbot))).
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
:- use_module(logicmoo_plarkc).
:- check_clause_counts.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- dmsg("[Mostly Required] logicmoo_clif").
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- use_module(logicmoo_clif).

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
:- dmsg("MAYBE QSAVE THIS").
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- set_prolog_flag(logicmoo_qsave,false).

:- if( \+ current_prolog_flag(address_bits, 32)).
:- during_boot(set_prolog_stack_gb(16)).
:- endif.

:- fixup_exports.

:- if(false).
:- statistics.
:- listing(qsave_lm/1).
:- endif.



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Regression tests that first run whenever a person starts the MUD on the public server
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%:- load_library_system(pack(logicmoo_base/t/examples/pfc/'sanity_col_as_unary.pfc')).
%:- load_library_system(pack(logicmoo_base/t/examples/pfc/'sanity_birdt.pfc')).
%:- load_library_system(pack(logicmoo_base/t/examples/pfc/'sanity_sv.pfc')).
%:- load_library_system(pack(logicmoo_base/t/examples/pfc/'sanity_foob.pfc')).


