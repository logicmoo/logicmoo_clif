%#!/usr/bin/swipl 

:- module(logicmoo_webbot,[logicmoo_goal/0,logicmoo_toplevel/0]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% DEFAULT PROLOG FLAGS
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- set_prolog_stack(global, limit(32*10**9)).
:- set_prolog_stack(local, limit(32*10**9)).
:- set_prolog_stack(trail, limit(32*10**9)).
:- set_prolog_flag(double_quotes,string).


:- if( (current_prolog_flag(os_argv,List),  (member('--nopce',List) ; member('--nogui',List)) )).
:- set_prolog_flag(logicmoo_headless,true).
:- set_prolog_flag(xpce,true).
:- unsetenv('DISPLAY').
:- endif.

/*
:- set_prolog_flag(access_level,system).
:- set_prolog_flag(compile_meta_arguments,false). % default is false
*/

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% LOAD LOGTALK
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- user:(
   % use_module(library(logtalk)),
   ensure_loaded('/usr/share/logtalk/integration/logtalk_swi'),
   listing('$lgt_default_flag'/2)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% LOAD PARTS OF SYSTEM EARLY
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- system:use_module(library(base32)).

:- system:use_module(library(http/http_dispatch)).
:- use_module(library(http/thread_httpd)).
:- use_module(thread_httpd:library(http/http_dispatch)).
:- use_module(library(http/http_path)).
:- use_module(library(http/http_server_files)).
:- use_module(library(http/http_parameters)).
:- use_module(library(http/html_head)).
:- use_module(library(http/html_write)).
:- use_module(library(threadutil)).
:- system:use_module(library(shell)).
:- use_module(library(console_input)).
:- if(current_predicate(system:mode/1)).
:- system:use_module(library(quintus),except([mode/1])). 
:- else.
:- system:use_module(library(quintus)). 
:- endif.
:- system:use_module(library(dialect/ifprolog),except([op(_,_,_)])).
:- abolish(system:time/1).
:- use_module(library(dialect/hprolog)).
:- abolish(hprolog:time/1).
:- system:use_module(library(statistics),[time/1]).
:- system:use_module(library(statistics)).
:- baseKB:use_module(library(statistics),[time/1]).
:- autoload([verbose(false)]).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% MISC UTILS
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- system:use_module(library(logicmoo_util_common)).

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
        add_history([init_mud_server]),
        add_history([init_mud_server_run]),
        !.
:- during_boot(add_history_ideas).



logicmoo_goal:- debug, 
 module(baseKB),
 dmsg("logicmoo_goal"),
 module(baseKB),
 nb_setval('$oo_stack',[]),
 threads, 
 make:make_no_trace,
 after_boot_call,
 add_history_ideas,
 dmsg("  [logicmoo_repl]."),
 dmsg("  [init_mud_server]."),
 dmsg("  [init_mud_server_run]."),!.

logicmoo_toplevel:-  debug,
 module(baseKB),
 make:make_no_trace,
 listing(after_boot_goal/1),
 dmsg("logicmoo_toplevel"),
 prolog.



:- if( (current_prolog_flag(os_argv,List), \+ member('--noclio',List)) ).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% MAKE SURE CLIOPATRIA RUNS
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- multifile(swish_trace:installed/1).
:- volatile(swish_trace:installed/1).
:- use_module(pengine_sandbox:library(semweb/rdf_db)).

% 

% :- user:ensure_loaded(run_cliopatria).


/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
This file provides a skeleton startup file.  It can be localized by running

    % ./configure			(Unix)
    % Double-clicking win-config.exe	(Windows)

After  that,  the  system  may  be  customized  by  copying  or  linking
customization  files  from  config-available    to  config-enabled.  See
config-enabled/README.txt for details.

To run the system, do one of the following:

    * Running for development
      Run ./run.pl (Unix) or open run.pl by double clicking it (Windows)

    * Running as Unix daemon (service)
      See daemon.pl
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

% Setup search path for cliopatria. We add  both a relative and absolute
% path. The absolute path allow us to  start in any directory, while the
% relative one ensures that the system remains working when installed on
% a device that may be mounted on a different location.

add_relative_search_path(Alias, Abs) :-
	is_absolute_file_name(Abs), !,
	prolog_load_context(file, Here),
	relative_file_name(Abs, Here, Rel),
	assertz(user:file_search_path(Alias, Rel)).
add_relative_search_path(Alias, Rel) :-
	assertz(user:file_search_path(Alias, Rel)).


:- if(exists_directory('../../ClioPatria/')).
:- add_relative_search_path(cliopatria, '../../ClioPatria').
:- endif.
:- if(exists_directory('../../../ClioPatria/')).
:- add_relative_search_path(cliopatria, '../../../ClioPatria').
:- endif.

% Make loading files silent. Comment if you want verbose loading.

:- current_prolog_flag(verbose, Verbose),
   asserta(saved_verbose(Verbose)),
   set_prolog_flag(verbose, silent).


		 /*******************************
		 *	      LOAD CODE		*
		 *******************************/

% Use the ClioPatria help system.  May   be  commented to disable online
% help on the source-code.

:- use_module(cliopatria('applications/help/load')).

% Load ClioPatria itself.  Better keep this line.

:- use_module(cliopatria(cliopatria)).

% Get back normal verbosity of the toplevel.

:- (   retract(saved_verbose(Verbose))
   ->  set_prolog_flag(verbose, Verbose)
   ;   true
   ).


:- cp_server.

:- volatile(http_log:log_stream/2).
:- volatile(http_session:urandom_handle/1).

:- endif.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% DEFAULT LOGICMOO FLAGS
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- set_prolog_flag(double_quotes,string).
:- set_prolog_flag(autoload_logicmoo,false).
:- if( \+ current_module(prolog_stack)).
:- use_module(library(prolog_stack)).
 prolog_stack:stack_guard(none).
:- endif.


setup_for_debug :- set_prolog_flag(report_error,true),set_prolog_flag(debug_on_error,true),
   set_prolog_flag(debugger_write_options,[quoted(true), portray(true), max_depth(1000), attributes(portray)]),
   set_prolog_flag(generate_debug_info,true).


:- during_boot(setup_for_debug).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% LOAD CYC KB LOADER
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- ensure_loaded(library('pldata/plkb7166/kb7166')).
:- qcompile_kb7166.


:-  abolish(rdf_rewrite:arity,2),  % clause(rdf_rewrite:arity(A, B),functor(A, _, B),R),erase(R),
   asserta((rdf_rewrite:arity(A, B) :- (compound(A),functor(A, _, B)))). % AND DOES NOT BREAK LOGICMOO
ensure_webserver_p(Port):- format(atom(A),'httpd@~w',[Port]),thread_property(N,status(V)),V=running,atom(N),atom_concat(A,_,N),!.
ensure_webserver_p(Port) :-catch((thread_httpd:http_server(http_dispatch,[ port(Port), workers(16) ])),E,(writeln(E),fail)).
ensure_webserver_3020:- (getenv('LOGICMOO_PORT',Was);Was=3000),
   WebPort is Was + 20, ensure_webserver_p(WebPort).



:- during_boot(ensure_webserver_3020).

:- autoload([verbose(false)]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Ensure hMUD
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- if(exists_directory(hmud)).
:- absolute_file_name('hmud/',O),
   during_boot(http_handler('/hmud/', http_reply_from_files(O, []), [prefix])).
:- during_boot(ignore(catch(shell('killall perl ; ./hmud/policyd'),E,dmsg(E)))).
:- else.
:- during_boot(http_handler('/hmud/', http_reply_from_files(pack(hMUD), []), [prefix])).
:- during_boot(ignore(catch(shell('killall perl ; ../hmud/policyd'),E,dmsg(E)))).
:- endif.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% (X)WINDOWS (DE)BUGGERY
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
start_x_ide:- \+ current_prolog_flag(logicmoo_headless,true),!.
start_x_ide:- prolog_ide(thread_monitor),prolog_ide(debug_monitor),
   % prolog_ide(open_debug_status),
   guitracer,
   use_module(library(pce_prolog_xref)),
   noguitracer.

:- after_boot(start_x_ide).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% SETUP PATHS FOR PROLOGMUD/LOGICMOO 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% :- during_boot((user:ensure_loaded(setup_paths))).

:- use_module(library('file_scope')).
% :- use_module(library('clause_expansion')).


% :- during_boot((sanity((lmce:current_smt(SM,M),writeln(current_smt(SM,M)))))).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% LOAD LOGICMOO UTILS
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- user:ensure_loaded(system:library(logicmoo_utils)).
:- multifile(prolog:make_hook/2).
:- dynamic(prolog:make_hook/2).
prolog:make_hook(BA, C):- wdmsg(prolog:make_hook(BA, C)),fail.


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

:- dynamic(lmcache:prolog_tn_server/1).

getenv_safely(Name,ValueO,Default):-
   (getenv(Name,RV)->Value=RV;Value=Default),
    (number(Default)->( \+ number(Value) -> atom_number(Value,ValueO); Value=ValueO);(Value=ValueO)).

prolog_tn_server:- is_thread(prolog_server),thread_property(prolog_server,status(running)),!.
prolog_tn_server:- 
   ensure_loaded(library(prolog_server)),
   getenv_safely('LOGICMOO_PORT',Was,3000),
   WebPort is Was + 1023,
   catch((prolog_server(WebPort, [allow(_)])),_,fail),!,
   asserta(lmcache:prolog_tn_server(WebPort)).
prolog_tn_server:- is_thread(prolog_server),thread_property(prolog_server,status(running)),!.
prolog_tn_server:- catch((prolog_server(4023, [allow(_)])),_,fail).
prolog_tn_server:- catch((prolog_server(5023, [allow(_)])),_,fail),!.

:- during_boot(prolog_tn_server).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- dmsg("Various RPC Dangers").
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
unsafe_preds_init(W,shell,2):-predicate_property(shell(_,_),imported_from(W)).
unsafe_preds_init(W,shell,1):-predicate_property(shell(_),imported_from(W)).
unsafe_preds_init(W,shell,0):-predicate_property(shell,imported_from(W)).
%unsafe_preds_init(M,F,A):-M=files_ex,current_predicate(M:F/A),member(X,[delete]),atom_contains(F,X).
unsafe_preds_init(M,F,A):-M=files_ex,current_predicate(M:F/A),member(X,[delete,copy]),atom_contains(F,X).
%unsafe_preds_init(M,F,A):-M=process,current_predicate(M:F/A),member(X,[kill,create]),atom_contains(F,X).
unsafe_preds_init(M,F,A):-M=process,current_predicate(M:F/A),member(X,[kill]),atom_contains(F,X).
unsafe_preds_init(M,F,A):-M=system,member(F,[shell,halt]),current_predicate(M:F/A).

system:kill_unsafe_preds:- 
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
:- ensure_loaded(user:library(eggdrop)).
% :- during_boot((egg_go_fg)).
:- during_boot((egg_go)).
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
:- gripe_time(60,baseKB:ensure_loaded(library('logicmoo/plarkc/logicmoo_i_cyc_kb_tinykb.pfc'))).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- dmsg("SET TOPLEVEL OPTIONS").
% ?- listing.  (uses varaibles)
% slows the system startup down consideraly
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- set_prolog_flag(toplevel_print_factorized,true). % default false
:- set_prolog_flag(toplevel_print_anon,true).
:- set_prolog_flag(toplevel_mode,backtracking). % OR recursive 
:- ensure_loaded(system:library(logicmoo_utils)).
:- after_boot(dmsg(qconsult_kb7166)).
% :- use_listing_vars.
:- set_prolog_flag(write_attributes,portray).

:- debug.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- dmsg("AUTOLOAD PACKAGES").
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

/*
pack_autoload_packages(NeedExistingIndex):- 
 forall(user:expand_file_search_path(library(''),Dir),
  ignore(( (\+ NeedExistingIndex ; absolute_file_name('INDEX',_Absolute,[relative_to(Dir),access(read),file_type(prolog),file_errors(fail)]))->
   make_library_index(Dir, ['*.pl']) -> 
  (user:library_directory(Dir) -> true ; (asserta(user:library_directory(Dir)) , reload_library_index))))).

:- during_boot(pack_autoload_packages(true)).
*/

rescan_pack_autoload_packages:- 
 forall((pack_property(_Pack, directory(PackDir)),prolog_pack:pack_info_term(PackDir,autoload(true))),
  prolog_pack:post_install_autoload(PackDir, [autoload(true)])).

:- during_boot(rescan_pack_autoload_packages).

:- reload_library_index.
:- autoload([verbose(true)]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% QSAVE THIS
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


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
base_message(T,Type,Warn):- dmsg(message_hook(T,Type,Warn)),dumpST,dmsg(message_hook(T,Type,Warn)),!,fail.

:- multifile prolog:message//1, user:message_hook/3.
user:message_hook(T,Type,Warn):- once(base_message(T,Type,Warn)),fail.

:- ensure_loaded(system:logicmoo_utils).


:- if(current_prolog_flag(logicmoo_qsave,true)).
:- statistics.
:- make.
:- listing(qsave_lm/1).
:- add_history_ideas,qsave_lm(lm_webbot).
:- endif.


