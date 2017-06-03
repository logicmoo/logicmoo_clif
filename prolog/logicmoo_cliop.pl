:- module(logicmoo_cliop,[]).

:- current_prolog_flag(os_argv,List),dmsg((os_argv=List)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% USE CLIOPATRIA ?
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- if( (current_prolog_flag(os_argv,List), member('--clio',List)) ;
   (current_prolog_flag(os_argv,List), member('--all',List)) ).


:- add_file_search_path_safe(cliopatria,pack('ClioPatria')).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% CLIOPATRIA ARGV
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- dynamic(saved_os_argv/1).

:- if( (current_prolog_flag(os_argv,List), member('--clio',List)) ).
:- current_prolog_flag(os_argv,List),append(Before,['--clio'|After],List),
   asserta(saved_os_argv(Before)),
   set_prolog_flag(os_argv,[ swipl | After]).
:- else.
:- current_prolog_flag(os_argv,List),
   asserta(saved_os_argv(List)).
:- set_prolog_flag(os_argv,[swipl]).
:- endif.


:- if(current_prolog_flag(os_argv,[_])).
:- set_prolog_flag(os_argv,[swipl,cpack,install,cpack_repository]).
:- endif.

:- saved_os_argv(List),dmsg((next_os_argv=List)).
:- current_prolog_flag(os_argv,List),dmsg((clio_argv=List)).

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
% absolute_file_name(cliopatria,X,[type(directory),solutions(all),access(read),file_errors(fail),case_sensitive(false),relative_path('/mnt/gggg/logicmoo_workspace/pack')]).
% absolute_file_name(pack(cliopatria),X,[type(directory),solutions(all),access(read),file_errors(fail),case_sensitive(false),relative_path('/mnt/gggg/logicmoo_workspace/pack')]).


% Make loading files silent. Comment if you want verbose loading.

:- current_prolog_flag(verbose, Verbose),
   asserta(saved_verbose(Verbose)),
   set_prolog_flag(verbose, silent).

:- if(exists_source(cliopatria('applications/help/load'))).

:- multifile(user:send_message/2).
:- dynamic(user:send_message/2).
user:send_message(A, C) :-
    cp_messages:
    (    current_prolog_flag(html_messages, true),
        level_css_class(A, B),
        html(pre(class(B), \html_message_lines(C)), D, []),
        with_mutex(html_messages, print_html(D))),
        flush_output,
        fail.

		 /*******************************
		 *	      LOAD CODE		*
		 *******************************/

% Use the ClioPatria help system.  May   be  commented to disable online
% help on the source-code.

:- user:use_module(cliopatria('applications/help/load')).

% Load ClioPatria itself.  Better keep this line.

:- user:use_module(cliopatria(cliopatria)).

% Get back normal verbosity of the toplevel.

:- (   retract(saved_verbose(Verbose))
   ->  set_prolog_flag(verbose, Verbose)
   ;   true
   ).

:- dmsg(load_conf_d([ 'config-enabled' ], [])).
:- load_conf_d([ 'config-enabled' ], []).

:- dmsg(cp_server).
:- during_net_boot(cp_server:cp_server).

:- endif. % clio exists?


%:- autoload([verbose(false)]).

:-  abolish(rdf_rewrite:arity,2),  % clause(rdf_rewrite:arity(A, B),functor(A, _, B),R),erase(R),
   asserta((rdf_rewrite:arity(A, B) :- (compound(A),functor(A, _, B)))). % AND DOES NOT BREAK LOGICMOO

:- retract(saved_os_argv(List)),set_prolog_flag(os_argv,List).
:- endif.  % --noclio

