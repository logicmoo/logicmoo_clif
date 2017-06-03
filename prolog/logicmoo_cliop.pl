:- module(logicmoo_cliop,[]).

:- if( (current_prolog_flag(os_argv,List), member('--clio',List)) ;
   (current_prolog_flag(os_argv,List), member('--all',List)) ).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% USE CLIOPATRIA ?
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% :- add_file_search_path_safe(cliopatria,'/mnt/gggg/logicmoo_workspace/pack/ClioPatria').


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

/*
:- if(exists_directory('../../ClioPatria/')).
:- add_relative_search_path(cliopatria, '../../ClioPatria').
:- endif.
:- if(exists_directory('../../../ClioPatria/')).
:- add_relative_search_path(cliopatria, '../../../ClioPatria').
:- endif.
:- if(exists_directory('../../../../ClioPatria/')).
:- add_relative_search_path(cliopatria, '../../../../ClioPatria').
:- endif.
:- if(exists_directory('../../../../../ClioPatria/')).
:- add_relative_search_path(cliopatria, '../../../../../ClioPatria').
:- endif.
*/

/*

Warning: /home/prologmud_server/lib/swipl/pack/swish-with-filesystem-interaction/lib/chat.pl:67:
        /home/prologmud_server/lib/swipl/pack/swish-with-filesystem-interaction/lib/storage.pl:76: Initialization goal failed
Warning: /home/prologmud_server/lib/swipl/pack/swish-with-filesystem-interaction/lib/chat.pl:72:
        /home/prologmud_server/lib/swipl/pack/swish-with-filesystem-interaction/lib/chatstore.pl:59: Initialization goal failed
ERROR: /home/prologmud_server/lib/swipl/pack/prologmud_samples/prolog/prologmud_sample_games/config-enabled/cpack_repository.pl:2:
        source_sink `cpack_repository(applications/cpack_submit)' does not exist
Warning: /home/prologmud_server/lib/swipl/pack/prologmud_samples/prolog/prologmud_sample_games/config-enabled/cpack_repository.pl:2:
        Goal (directive) failed: conf_cpack_repository:use_module(cpack_repository(applications/cpack_submit))
ERROR: /home/prologmud_server/lib/swipl/pack/prologmud_samples/prolog/prologmud_sample_games/config-enabled/cpack_repository.pl:3:
        source_sink `cpack_repository(applications/cpack_home)' does not exist
Warning: /home/prologmud_server/lib/swipl/pack/prologmud_samples/prolog/prologmud_sample_games/config-enabled/cpack_repository.pl:3:
        Goal (directive) failed: conf_cpack_repository:use_module(cpack_repository(applications/cpack_home))
ERROR: /home/prologmud_server/lib/swipl/pack/prologmud_samples/prolog/prologmud_sample_games/config-enabled/cpack_server.pl:3:
        source_sink `api(cpack)' does not exist
Warning: /home/prologmud_server/lib/swipl/pack/prologmud_samples/prolog/prologmud_sample_games/config-enabled/cpack_server.pl:3:
        Goal (directive) failed: conf_cpack_server:use_module(api(cpack))
ERROR: /home/prologmud_server/lib/swipl/pack/prologmud_samples/prolog/prologmud_sample_games/config-enabled/foaf_user.pl:2:
        source_sink `applications(foaf_user_profile)' does not exist
Warning: /home/prologmud_server/lib/swipl/pack/prologmud_samples/prolog/prologmud_sample_games/config-enabled/foaf_user.pl:2:
        Goal (directive) failed: conf_foaf_user:use_module(applications(foaf_user_profile))
ERROR: /home/prologmud_server/lib/swipl/pack/prologmud_samples/prolog/prologmud_sample_games/config-enabled/isearch.pl:3:
        source_sink `isearch(applications/isearch)' does not exist
Warning: /home/prologmud_server/lib/swipl/pack/prologmud_samples/prolog/prologmud_sample_games/config-enabled/isearch.pl:3:
        Goal (directive) failed: conf_isearch:use_module(isearch(applications/isearch))
ERROR: /home/prologmud_server/lib/swipl/pack/prologmud_samples/prolog/prologmud_sample_games/config-enabled/notifications.pl:38:
        source_sink `config(user_profile)' does not exist
Warning: /home/prologmud_server/lib/swipl/pack/prologmud_samples/prolog/prologmud_sample_games/config-enabled/notifications.pl:38:
        Goal (directive) failed: config_notifications:use_module(config(user_profile))
ERROR: /home/prologmud_server/lib/swipl/pack/prologmud_samples/prolog/prologmud_sample_games/config-enabled/notifications.pl:39:
        source_sink `config_enabled(email)' does not exist
Warning: /home/prologmud_server/lib/swipl/pack/prologmud_samples/prolog/prologmud_sample_games/config-enabled/notifications.pl:39:
        Goal (directive) failed: config_notifications:use_module(config_enabled(email))
ERROR: /home/prologmud_server/lib/swipl/pack/logicmoo_base/prolog/logicmoo_webbot.pl:245:
        /home/prologmud_server/lib/swipl/pack/prologmud_samples/prolog/prologmud_sample_games/config-enabled/user_profile.pl:45: Initialization goal raised exception:
        source_sink `data(profiles)' does not exist

*/

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

:- during_net_boot(cp_server:cp_server).

:- endif. % clio exists?


%:- autoload([verbose(false)]).

:-  abolish(rdf_rewrite:arity,2),  % clause(rdf_rewrite:arity(A, B),functor(A, _, B),R),erase(R),
   asserta((rdf_rewrite:arity(A, B) :- (compound(A),functor(A, _, B)))). % AND DOES NOT BREAK LOGICMOO

:- retract(saved_os_argv(List)),set_prolog_flag(os_argv,List).
:- endif.  % --noclio

