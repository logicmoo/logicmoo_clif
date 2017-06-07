%#!/usr/bin/swipl 

:- module(logicmoo_webbot,[
  prolog_tn_server/0,
  maybe_save_lm/0]).

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
:- user:use_module(library(yall), []).
:- endif.

% :- ['/home/prologmud_server/lib/swipl/pack/prologmud_samples/prolog/prologmud_sample_games/run_clio'].

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% PACK LOADER
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- load_library_system(logicmoo_packs).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% LOAD PARTS OF SYSTEM EARLY
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 % :- set_prolog_flag(subclause_expansion,default).
 % :- set_prolog_flag(subclause_expansion,false).
 % :- set_prolog_flag(dialect_pfc,default).
:- load_library_system(logicmoo_swilib).


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
% DUMPST ON WARNINGS
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- if(false).
skip_warning(informational).
skip_warning(information).
skip_warning(debug).
skip_warning(query).
skip_warning(silent).
skip_warning(debug_no_topic).
skip_warning(break).
skip_warning(io_warning).
skip_warning(interrupt).
skip_warning(statistics).
skip_warning(check).

skip_warning(T):-compound(T),functor(T,F,_),skip_warning(F).
base_message(T1,T2,_):- skip_warning(T1);skip_warning(T2);(thread_self(M),M\==main).
base_message(_,_,_):- \+ current_predicate(dumpST/0),!.
base_message(T,Type,Warn):- dmsg(message_hook(T,Type,Warn)),dumpST,dmsg(message_hook(T,Type,Warn)),!,fail.

:- multifile prolog:message//1, user:message_hook/3.
user:message_hook(T,Type,Warn):- ( \+ current_prolog_flag(runtime_debug,0)),
   catch(once(base_message(T,Type,Warn)),_,fail),fail.
:- endif.



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% SETUP PATHS FOR PROLOGMUD/LOGICMOO 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% :- during_boot((user:ensure_loaded(setup_paths))).

:- user:use_module(library('file_scope')).
% :- use_module(library('clause_expansion')).

 % :- set_prolog_flag(subclause_expansion,true).

% :- during_boot((sanity((lmce:current_smt(SM,M),writeln(current_smt(SM,M)))))).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% LOAD LOGICMOO UTILS
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
% START WEBSERVER
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- load_library_system(logicmoo_cliop).

:- load_library_system(logicmoo_swish).

:- load_library_system(logicmoo_pldoc).

:- load_library_system(logicmoo_plweb).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% SETUP LOGICMOO OPERATORS
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

% :- multifile prolog:message//1, prolog:message_hook/3.
% prolog:message(ignored_weak_import(Into, From:PI))--> { nonvar(Into),Into \== system,dtrace(dmsg(ignored_weak_import(Into, From:PI))),fail}.
% prolog:message(Into)--> { nonvar(Into),functor(Into,_F,A),A>1,arg(1,Into,N),\+ number(N),dtrace(wdmsg(Into)),fail}.
% prolog:message_hook(T,error,Warn):- dtrace(wdmsg(nessage_hook(T,warning,Warn))),fail.
% prolog:message_hook(T,warning,Warn):- dtrace(wdmsg(nessage_hook(T,warning,Warn))),fail.


/*
:- flag_call(unsafe_speedups=true).
:- flag_call(runtime_debug=0).
:- flag_call(runtime_debug=2).
% ?- current_prolog_flag(unsafe_speedups , true) .
:- flag_call(unsafe_speedups=false).
*/

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Sanity tests that first run whenever a person stats the MUD to see if there are regressions in the system
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- if(( ( \+ ((current_prolog_flag(logicmoo_include,Call),Call))) )).
%.
:- endif.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- dmsg("Ensure RPC Telnet").
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- dynamic(lmcache:prolog_tn_server_port/1).

prolog_tn_server:- thread_property(PS,status(running)),PS==prolog_server,!.
prolog_tn_server:- 
   must(ensure_loaded(library(prolog_server))),
   getenv_or('LOGICMOO_PORT',Was,3000),
   WebPort is Was + 1023,
   catch(
    (prolog_server(WebPort, [allow(_)]),asserta(lmcache:prolog_tn_server_port(WebPort))),
     E,(writeq(E),fail)),!.
   
:- during_net_boot(prolog_tn_server).




%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- dmsg("Various RPC Dangers").
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:-use_module(library(process)).

unsafe_preds_init(W,shell,2):-predicate_property(shell(_,_),imported_from(W)).
unsafe_preds_init(W,shell,1):-predicate_property(shell(_),imported_from(W)).
unsafe_preds_init(W,shell,0):-predicate_property(shell,imported_from(W)).
%unsafe_preds_init(M,F,A):-M=files_ex,current_predicate(M:F/A),member(X,[delete]),atom_contains(F,X).
unsafe_preds_init(M,F,A):-M=files_ex,current_predicate(M:F/A),member(X,[delete,copy]),atom_contains(F,X).
%unsafe_preds_init(M,F,A):-M=process,current_predicate(M:F/A),member(X,[kill,create]),atom_contains(F,X).
unsafe_preds_init(M,F,A):-M=process,current_predicate(M:F/A),member(X,[kill]),atom_contains(F,X).
unsafe_preds_init(M,F,A):-M=system,member(F,[shell,halt]),current_predicate(M:F/A).


system:kill_unsafe_preds:- whenever_flag_permits(run_network,system:kill_unsafe_preds0).
system:kill_unsafe_preds0:- \+ if_defined(getuid(0),true),!.
system:kill_unsafe_preds0:- app_argv('--unsafe'),!.
system:kill_unsafe_preds0:-   
   dmsg("kill_unsafe_preds!"),
% (Thus restoring saved state)
   set_prolog_flag(access_level,system),
   
   % [Optionaly] Solve the Halting problem
   unlock_predicate(system:halt/0),
   redefine_system_predicate(system:halt/0),
   abolish(system:halt,0),
   asserta((system:halt :- format('the halting problem is now solved!'))),
   lock_predicate(system:halt/0),   
   unlock_predicate(system:halt/1),
   redefine_system_predicate(system:halt/1),
   abolish(system:halt,1),
   asserta((system:halt(_) :- format('the halting problem was already solved!'))),
   lock_predicate(system:halt/1),
   (dmsg("kill_unsafe_preds!"),locally(set_prolog_flag(access_level,system),
     forall(unsafe_preds_init(M,F,A),bugger:remove_pred(M,F,A)))),
   dmsg("the halting problem is now solved!"). 



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- dmsg("IRC EGGDROP").
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- if(exists_source(library(eggdrop))).
:- ensure_loaded(library(eggdrop)).
% :- during_boot((egg_go_fg)).
:- during_net_boot(egg_go_maybe).
:- endif.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- dmsg("CYC Alignment util").
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- set_prolog_flag(do_renames,restore).
:- baseKB:ensure_loaded(library('logicmoo/plarkc/logicmoo_i_cyc_rewriting')).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- dmsg("SETUP CYC KB EXTENSIONS").
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- during_boot(set_prolog_flag(do_renames,restore)).
:- gripe_time(60,baseKB:ensure_loaded(library('logicmoo/plarkc/logicmoo_u_cyc_kb_tinykb.pl'))).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- dmsg("SET TOPLEVEL OPTIONS").
% ?- listing.  (uses varaibles)
% slows the system startup down consideraly
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% :- set_prolog_flag(toplevel_print_factorized,true). % default false
:- set_prolog_flag(toplevel_print_anon,true).
:- set_prolog_flag(toplevel_mode,backtracking). % OR recursive 
:- after_boot(dmsg(qconsult_kb7166)).
% :- use_listing_vars.
:- set_prolog_flag(write_attributes,portray).
% :- debug.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- dmsg("AUTOLOAD PACKAGES").
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- during_boot(rescan_pack_autoload_packages).

%:- reload_library_index.
%:- autoload([verbose(true)]).
:- reload_library_index.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% QSAVE THIS
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

