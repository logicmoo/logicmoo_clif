:- module(logicmoo_swish,[]).


:- multifile(swish_trace:installed/1).
:-   dynamic(swish_trace:installed/1).
:-  volatile(swish_trace:installed/1).

:- if(exists_source(library(semweb/rdf_db))).
:- use_module(pengine_sandbox:library(semweb/rdf_db)).
:- endif.


:- use_module(logicmoo_cliop).

                 /*******************************
		 *	       CONFIG		*
		 *******************************/

:- multifile
	swish_config:config/2,			% Name, Value
	swish_config:source_alias/2,		% Alias, Options
	swish_config:verify_write_access/3,	% Request, File, Options
	pengines:authentication_hook/3,		% Request, Application, User
	pengines:not_sandboxed/2,		% User, Application
	user:file_search_path/2.		% Alias, Path

user:file_search_path(swish, '/home/prologmud_server/lib/swipl/pack/swish-with-filesystem-interaction').
user:file_search_path(project, '.').

:- dynamic http:location/3.
:- multifile http:location/3.
http:location(root, '/', [priority(1100)]).
http:location(swish, root('ish'), [priority(-100)]).
http:location(swish, root('swish'), [priority(500)]).

:- add_file_search_path_safe(swish,pack('swish-with-filesystem-interaction')).

:- multifile pengines:allowed/2.
:- dynamic pengines:allowed/2.
% pengines:allowed(_, _) :-!.

/*

%prolog:prolog_load_file(library(swish/X),How):- trace, prolog:load_files([swish(lib/X)],How),!.
%prolog:prolog_load_file(swish(lib/swish/X),How):- prolog:load_files([swish(lib/X)],How),!.
*/

swish_config:config(show_beware,        false).
swish_config:config(community_examples, true).

swish_config:source_alias(project, [access(both), search('*.pl')]).
swish_config:source_alias(library, []).

swish_config:verify_write_access(_Request, _File, _Options).

pengines:authentication_hook(_Request, swish, User) :-
	current_user(User).
pengines:not_sandboxed(_User, _Application).


:- if(current_predicate(getuid/1)).
current_user(User) :- 
	getuid(UID),
	user_info(UID, Info),
	user_data(name, Info, User),!.
:- endif.
current_user(default).

no_auth_needed(Request):- is_list(Request),memberchk(path_info(Path),Request),mimetype:file_mime_type(Path,Type),memberchk(Type,[image/_,_/javascript]),!.
no_auth_needed(Request):- is_list(Request),!,memberchk(path(Path),Request),no_auth_needed(Path).
no_auth_needed('/chat').
no_auth_needed('/').

:- multifile swish_config:authenticate/2.
:- dynamic swish_config:authenticate/2.

swish_config:authenticate(Request, User) :-
        swish_http_authenticate:logged_in(Request, User), !.

swish_config:authenticate(_Request, User) :- 
  http_session:
    (http_in_session(_SessionID),
     http_session_data(oauth2(OAuth, _)),
     http_session_data(user_info(OAuth, Info))),
   User=Info.name,!.

swish_config:authenticate(Request, User) :- 
  no_auth_needed(Request),
  current_user(User),!.



swish_config:authenticate(Request, User) :- http_session:http_in_session(SessionID),
  current_user(User),
  with_output_to(current_error,
  ((http_session:http_in_session(SessionID),
    listing(http_session: session_data(SessionID,_Data))))),
  with_output_to(current_error,wdmsg((http_session:authenticate(Request, User)))),
  !.

swish_config:authenticate(Request, User) :- \+ http_session:http_in_session(_),
  current_user(User),
  with_output_to(current_error,wdmsg((swish_config:authenticate(Request, User)))),
  !.


:- user:use_module(swish(swish)).

:-  http_server(http_dispatch,
		    [ port(3050),
		      workers(16)
		    ]).



:- multifile
	cp_menu:menu_item/2,
	cp_menu:menu_popup_order/2.
:- dynamic
	cp_menu:menu_item/2,
	cp_menu:menu_popup_order/2.

:- asserta(cp_menu:menu_item(400=places/swish,		'SWISH')).
:- asserta(cp_menu:menu_popup_order(swish,       550)).
:- asserta(cp_menu:menu_item(200=swish/swish,		'SWISH')).


