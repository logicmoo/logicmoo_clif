:- module(logicmoo_swish,[]).
/** <module>

Remote SWISH as an IDE for developing a Remote application.
*/

:- use_module(library(must_trace)).

:- add_file_search_path_safe(swish,pack('swish-with-filesystem-interaction')).
% :- add_file_search_path_safe(swish,'cpack/swish').
%
%:- add_file_search_path_safe(plweb,pack('plweb')).

:- use_module(library(http/thread_httpd)).
:- use_module(library(http/http_dispatch)).
:- use_module(library(http/http_path)).
:- use_module(library(www_browser)).
:- if(exists_source(library(uid))).
:- use_module(library(uid)).
:- endif.



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



:- multifile
	user:file_search_path/2,
	swish_config:config/2,
	swish_config:source_alias/2.

% make example(File) find the example data
user:file_search_path(example, swish(examples/trill)).
%user:file_search_path(example, pack(pfc/t/sanity_base)).
%user:file_search_path(example, pack(logicmoo_base/t/examples)).


:- prolog_load_context(directory,Dir),asserta(user:file_search_path(swish, Dir)).
user:file_search_path(project, '.').

:- dynamic http:location/3.
:- multifile http:location/3.
http:location(root, '/', [priority(1100)]).
http:location(swish, root('swish'), [priority(500)]).


:- multifile pengines:allowed/2.
:- dynamic pengines:allowed/2.
% pengines:allowed(_, _) :-!.

/*

%prolog:prolog_load_file(library(swish/X),How):- trace, prolog:load_files([swish(lib/X)],How),!.
%prolog:prolog_load_file(swish(lib/swish/X),How):- prolog:load_files([swish(lib/X)],How),!.
*/

%swish_config:config(show_beware,        false).
%swish_config:config(community_examples, true).

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
   current_predicate(swish_http_authenticate:logged_in/2),
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


:- use_module(swish(swish)).

  
swish_config:authenticate(Request, "bad_user") :- 
  wdmsg(swish_config:authenticate(Request, "bad_user")),!.
  

%%	swish
%
%	Start the SWISH server and open the main page in your browser.

swish :-
	swish('prologmoo.com':3050).

swish(Port) :-
	http_server_property(Port, goal(swish_ide:http_dispatch)), !,
	open_browser(Port).
swish(_:Port) :-
	integer(Port),
	http_server_property(Port, goal(swish_ide:http_dispatch)), !,
	open_browser(Port).
swish(Port) :-
	http_server(http_dispatch,
		    [ port(Port),
		      workers(16)
		    ]),
	open_browser(Port).

open_browser(Address) :-
	host_port(Address, Host, Port),
	http_server_property(Port, scheme(Scheme)),
	http_absolute_location(root(.), Path, []),
	format(atom(URL), '~w://~w:~w~w', [Scheme, Host, Port, Path]),
	wdmsg(www_open_url(URL)).

host_port(Host:Port, Host, Port) :- !.
host_port(Port, 'prologmoo.com', Port).


:- swish.


/*
:- [library(pengines)].
:- pengine_rpc("http://prologmoo.com:3050",
                       sin_table(X,Y),
                       [ src_text(':- dynamic(sin_table/2). sin_table(1,2).'),
                         application(swish)
                       ]),
   wdmsg(sin_table(X,Y)).
*/
:- listing(swish_config:authenticate/2).

:- multifile
	cp_menu:menu_item/2,
	cp_menu:menu_popup_order/2.
:- dynamic
	cp_menu:menu_item/2,
	cp_menu:menu_popup_order/2.

:- asserta(cp_menu:menu_item(400=places/swish,		'SWISH')).
:- asserta(cp_menu:menu_popup_order(swish,       550)).
:- asserta(cp_menu:menu_item(200=swish/swish,		'SWISH')).


