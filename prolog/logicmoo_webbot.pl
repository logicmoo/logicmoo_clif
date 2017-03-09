%#!/usr/bin/swipl 

:- module(logicmoo_webbot,[prolog_tn_server/0]).

:- if(\+ current_module(baseKB)).
:- set_prolog_flag(logicmoo_qsave,true).
:- else.
:- set_prolog_flag(logicmoo_qsave,false).
:- endif.

:-set_prolog_flag(access_level,system).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% LOAD CYC KB LOADER
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- ensure_loaded(library('pldata/plkb7166/kb7166')).
% :- qcompile_kb7166.



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% LOAD PARTS OF SYSTEM EARLY
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 % :- set_prolog_flag(subclause_expansion,default).
 % :- set_prolog_flag(subclause_expansion,false).
 % :- set_prolog_flag(dialect_pfc,default).
:- system:ensure_loaded(logicmoo_swilib).



:- if( (current_prolog_flag(os_argv,List), \+ member('--noclio',List)) ).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% MAKE SURE CLIOPATRIA RUNS
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- multifile(swish_trace:installed/1).
:- volatile(swish_trace:installed/1).
:- use_module(pengine_sandbox:library(semweb/rdf_db)).



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

:- autoload([verbose(false)]).

:-  abolish(rdf_rewrite:arity,2),  % clause(rdf_rewrite:arity(A, B),functor(A, _, B),R),erase(R),
   asserta((rdf_rewrite:arity(A, B) :- (compound(A),functor(A, _, B)))). % AND DOES NOT BREAK LOGICMOO

:- endif.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% START WEBSERVER
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

ensure_webserver_p(Port):- format(atom(A),'httpd@~w',[Port]),thread_property(N,status(V)),V=running,atom(N),atom_concat(A,_,N),!.
ensure_webserver_p(Port) :-catch((thread_httpd:http_server(http_dispatch,[ port(Port), workers(16) ])),E,(writeln(E),fail)).
ensure_webserver_3020:- (getenv('LOGICMOO_PORT',Was);Was=3000),
   WebPort is Was + 20, ensure_webserver_p(WebPort).


:- during_boot(ensure_webserver_3020).

:- autoload([verbose(false)]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% DUMPST ON WARNINGS
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
base_message(_,_,_):- \+ current_predicate(dumpST/0),!.
base_message(T,Type,Warn):- dmsg(message_hook(T,Type,Warn)),dumpST,dmsg(message_hook(T,Type,Warn)),!,fail.

:- multifile prolog:message//1, user:message_hook/3.
user:message_hook(T,Type,Warn):- ( \+ current_prolog_flag(runtime_debug,0)),
   catch(once(base_message(T,Type,Warn)),_,fail),fail.

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
% SETUP PATHS FOR PROLOGMUD/LOGICMOO 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% :- during_boot((user:ensure_loaded(setup_paths))).

:- use_module(library('file_scope')).
% :- use_module(library('clause_expansion')).

 % :- set_prolog_flag(subclause_expansion,true).

% :- during_boot((sanity((lmce:current_smt(SM,M),writeln(current_smt(SM,M)))))).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% LOAD LOGICMOO UTILS
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- user:ensure_loaded(system:library(logicmoo_utils)).

:- multifile(prolog:make_hook/2).
:- dynamic(prolog:make_hook/2).
prolog:make_hook(before, C):- wdmsg(prolog:make_hook(before, C)),fail.
prolog:make_hook(after, C):- wdmsg(prolog:make_hook(after, C)),maybe_save_lm,fail.

maybe_save_lm:- \+ current_prolog_flag(logicmoo_qsave,true),!.
maybe_save_lm:- current_predicate(lmcache:qconsulted_kb7166/0),call(call,lmcache:qconsulted_kb7166),!.
maybe_save_lm:- qsave_lm(lm_repl4),!.

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

getenv_safely(Name,ValueO,Default):-
   (getenv(Name,RV)->Value=RV;Value=Default),
   ( \+ number(Value) -> atom_number(Value,ValueO); Value=ValueO).

prolog_tn_server:- thread_property(PS,status(running)),PS==prolog_server,!.
prolog_tn_server:- 
   must(ensure_loaded(library(prolog_server))),
   getenv_safely('LOGICMOO_PORT',Was,3000),
   WebPort is Was + 1023,
   catch(
    (prolog_server(WebPort, [allow(_)]),asserta(lmcache:prolog_tn_server_port(WebPort))),
     E,(writeq(E),fail)),!.
   

:- during_boot((prolog_tn_server)).



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


:- ensure_loaded(system:logicmoo_utils).

:- set_prolog_flag(logicmoo_qsave,false).

:- if(current_prolog_flag(logicmoo_qsave,true)).
:- statistics.
:- listing(qsave_lm/1).
:- endif.


