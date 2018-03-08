%#!/usr/bin/swipl 

:- module(logicmoo_webbot,[
  prolog_tn_server/0]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- dmsg("LOGICMOO WEB&BOT").
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- multifile(lmcache:prolog_tn_server_port/1).
:- dynamic(lmcache:prolog_tn_server_port/1).

prolog_tn_server:- thread_property(PS,status(running)),PS==prolog_server,!.
prolog_tn_server:- 
   must(ensure_loaded(library(prolog_server))),
   logicmoo_base_port(Base),
   TelnetPort is Base + 223,
   dmsg(TelnetPort= "SWI-PROLOG Telnet"),
   prolog_server(TelnetPort, [allow(_),call(prolog)]),asserta(lmcache:prolog_tn_server_port(TelnetPort)),!.
%   ,E,(writeq(E),fail)),!.
   
:- during_net_boot(prolog_tn_server).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- dmsg("IRC EGGDROP").
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- if(exists_source(library(eggdrop))).
:- with_no_mpred_expansions(ensure_loaded(library(eggdrop))).
% :- during_boot((egg_go_fg)).
:- during_net_boot(egg_go_maybe).
:- endif.


www_start:- app_argv_off('--www'),!.
www_start:- app_argv_off('--net'),!.
www_start:- www_start(3020).

www_start(Port):- dmsg("WWW Server " = Port), http_server_property(Port, goal(_)),!.
www_start(Port):- http_server(http_dispatch,[ port(Port)]). % workers(16) 


:- if(app_argv('--www')).

:- if(app_argv_ok('--swish')).
:- dmsg("SWISH Server").
:- user:load_library_system(logicmoo_swish).
:- endif.

:- if(app_argv_ok('--cliop')).
:- user:load_library_system(logicmoo_cliop).
:- endif.

:- if(app_argv_ok('--plweb')).
:- dmsg("PLWEB Server").
:- user:load_library_system(logicmoo_plweb).
:- endif.

:- if(app_argv_ok('--docs')).
:- dmsg("PLDOC Server").
:- user:load_library_system(logicmoo_pldoc).
:- endif.


:- use_module(library(http/thread_httpd)).
:- use_module(library(http/http_dispatch)).
:- use_module(library(http/http_parameters)).
:- use_module(library(http/html_write)).
:- during_net_boot(www_start).
:- endif.  % --www

:- if((app_argv_ok('--sigma'))).
:- user:load_library_system(library(xlisting_web)).
:- endif.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Sanity tests that first run whenever a person stats the MUD to see if there are regressions in the system
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- if(( ( \+ ((current_prolog_flag(logicmoo_include,Call),Call))) )).
%.
:- endif.


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

system:kill_unsafe_preds0:- locally(set_prolog_flag(access_level,system),kill_unsafe_preds1).

system:keep_unsafe_preds1:- \+ if_defined(getuid(0),true),!.
system:keep_unsafe_preds1:- app_argv1('--unsafe'),!.   
system:keep_unsafe_preds1:- app_argv('--nonet'),!.   
system:keep_unsafe_preds1:- \+ app_argv('--irc'), \+ app_argv('--all'),!.


system:kill_unsafe_preds1:-
   unlock_predicate(system:halt/0),
   redefine_system_predicate(system:halt/0),
   abolish(system:halt,0),
   asserta((system:halt :- format('the halting problem is now solved!'))),
   lock_predicate(system:halt/0),fail.
system:kill_unsafe_preds1:- system:keep_unsafe_preds1,!,dmsg("keep_unsafe_preds1!").
system:kill_unsafe_preds1:- 
   dmsg("kill_unsafe_preds!"),
% (Thus restoring saved state)
   % [Optionaly] Solve the Halting problem  
   unlock_predicate(system:halt/1),
   redefine_system_predicate(system:halt/1),
   abolish(system:halt,1),
   asserta((system:halt(_) :- format('the halting problem was already solved!'))),
   lock_predicate(system:halt/1),
   (dmsg("kill_unsafe_preds!"),locally(set_prolog_flag(access_level,system),
     forall(unsafe_preds_init(M,F,A),bugger:remove_pred(M,F,A)))),
   dmsg("the halting problem is now solved!"). 




end_of_file.


