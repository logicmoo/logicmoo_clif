#!/usr/local/bin/swipl 

:- module(logicmoo_cliop,[cliop_server/0]).

cliop_server:- ['./run_clio'].

end_of_file.


:- ['./run'].
:- [cpack/trill_on_swish/src/lib/authenticate].


end_of_file.


:- 
   forall(retract(user:file_search_path(cpack, _)),true),forall(retract(user:file_search_path(cpacks, _)),true),
   add_file_search_path_safe(cpack,'./cpack'), % add_file_search_path_safe(cpacks,'./cpack'),

   forall(retract(user:file_search_path(cp_application, _)),true),
   absolute_file_name(.,O), add_file_search_path_safe(cp_application,O), 
    listing(user:file_search_path('config_enabled',_)),
    add_file_search_path_safe(user,O),
    listing(user:file_search_path/2),
    forall(user:file_search_path(library, E),writeln(user:file_search_path(library, E))),!.

:- ['./run_clio'].

end_of_file.


:- use_module(library(must_trace)).

:- current_prolog_flag(os_argv,List),dmsg((app_argv=List)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% USE CLIOPATRIA ?
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- if(true;((( (app_argv('--clio') ; app_argv('--all')) , \+ app_argv('--noclio'))))).


:- add_file_search_path_safe(cliopatria,pack('ClioPatria')).

:- add_file_search_path_safe(data,'./data').
:- add_file_search_path_safe(config_enabled,'./config-enabled').

:- forall(retract(user:file_search_path(cp_application, '/home/prologmud_server/lib/swipl/pack/logicmoo_base/prolog')),true).
:- absolute_file_name(.,O), add_file_search_path_safe(cp_application,O).


:- dynamic(saved_os_argv/1).

:- if( (app_argv('--clio')) ).
:- current_prolog_flag(os_argv,List),append(Before,['--clio'|After],List),
   asserta(saved_os_argv(Before)),
   set_prolog_flag(os_argv,[ swipl | After]).
:- else.
:- current_prolog_flag(os_argv,List),
   asserta(saved_os_argv(List)).
:- set_prolog_flag(os_argv,[swipl]).
:- endif.


:- if(current_prolog_flag(os_argv,[_])).
% :- set_prolog_flag(os_argv,[swipl,cpack,install,cpack_repository]).
:- endif.

:- saved_os_argv(List),dmsg((next_os_argv=List)).
:- current_prolog_flag(os_argv,List),dmsg((clio_argv=List)).

:- export(cliop_server/0).

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

/*
add_relative_search_path(Alias, Abs) :-
	is_absolute_file_name(Abs), !,
	prolog_load_context(file, Here),
	relative_file_name(Abs, Here, Rel),
	assertz(user:file_search_path(Alias, Rel)).
add_relative_search_path(Alias, Rel) :-
	assertz(user:file_search_path(Alias, Rel)).

% file_search_path(cliopatria, '/home/prologmud_server/lib/swipl/pack/ClioPatria').
% :- add_relative_search_path(cliopatria, '/home/prologmud_server/lib/swipl/pack/ClioPatria').

% Make loading files silent. Comment if you want verbose loading.
*/

:- current_prolog_flag(verbose, Verbose),
   asserta(saved_verbose(Verbose)),
   set_prolog_flag(verbose, true).


		 /*******************************
		 *	      LOAD CODE		*
		 *******************************/

% Use the ClioPatria help system.  May   be  commented to disable online
% help on the source-code.

:- user:use_module(cliopatria('applications/help/load')).

% Load ClioPatria itself.  Better keep this line.

:- user:use_module(cliopatria(cliopatria)).


:- multifile user:file_search_path/2.
:- dynamic   user:file_search_path/2.

:- forall(source_file(M:add_relative_search_path(_,_), _), abolish(M:add_relative_search_path/2)).

user:file_search_path(library, E) :-
         clause(user:file_search_path(library, Exp),true),
         ( \+ atom(Exp) -> true ; \+ is_absolute_file_name(Exp)),
         absolute_file_name(Exp,E,[solutions(all)]).
         


:- user:import(cp_server:cp_server/1).



cliop_server0 :- 
   forall(retract(user:file_search_path(cpack, _)),true),forall(retract(user:file_search_path(cpacks, _)),true),
   add_file_search_path_safe(cpack,'./cpack'), % add_file_search_path_safe(cpacks,'./cpack'),

   forall(retract(user:file_search_path(cp_application, _)),true),
   absolute_file_name(.,O), add_file_search_path_safe(cp_application,O), 
    listing(user:file_search_path('config_enabled',_)),
    add_file_search_path_safe(user,O),
    listing(user:file_search_path/2),
    forall(user:file_search_path(library, E),writeln(user:file_search_path(library, E))),!.

cliop_server:-
  cliop_server0,
  baseKB:call( '@'(cp_server([]),user)).

:- system:import(cliop_server/0).  

% :- initialization cliop_server.
:- cliop_server.

% Get back normal verbosity of the toplevel.

:- (   retract(saved_verbose(Verbose))
   ->  set_prolog_flag(verbose, Verbose)
   ;   true
   ).

:- break.

:-  abolish(rdf_rewrite:arity,2),  % clause(rdf_rewrite:arity(A, B),functor(A, _, B),R),erase(R),
   asserta((rdf_rewrite:arity(A, B) :- (compound(A),functor(A, _, B)))). % AND DOES NOT BREAK LOGICMOO

:- retract(saved_os_argv(List)),set_prolog_flag(os_argv,List).

:- endif.  % --noclio


