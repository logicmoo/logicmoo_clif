#!/usr/bin/env swipl

:- module(logicmoo_plweb,[
          ensure_webserver_3040/0,
          recursive_directory_files/2,
          ensure_webserver_p/1]).

kill_3040:- threads,wdmsg(kill_3040),!.
kill_3040:- whenever_flag_permits(run_network,ignore(catch(shell('kill -9 $(lsof -t -i:3040 -sTCP:LISTEN) &>2 ||:'),E,dmsg(E)))).

:- use_module(library(http/thread_httpd)).
:- use_module(library(http/http_dispatch)).


:- add_file_search_path_safe(plweb,pack(plweb)).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% START WEBSERVER
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

really_ensure_webserver_p(Port):- http_server_property(Port, goal(_)),!.

really_ensure_webserver_p(Port):-  format(atom(A),'httpd@~w',[Port]),thread_property(N,status(V)),
 V=running,
 atom(N),
 atom_concat(A,_,N ),!.
really_ensure_webserver_p(Port):- 
 kill_3040,catch((thread_httpd:http_server(http_dispatch,[ port(Port), workers(16) ])),E,(writeln(E),fail)),!.


ensure_webserver_p(WebPort):- whenever_flag_permits(run_network, really_ensure_webserver_p(WebPort)).

ensure_webserver_3040:- getenv_or('LOGICMOO_PORT',Was,3000),
   WebPort is Was + 40, ensure_webserver_p('0.0.0.0':WebPort).

:- during_net_boot(ensure_webserver_3040).

%:- autoload([verbose(false)]).

%:- consult(plweb(load)).

%:- use_module(plweb(pack_analyzer)).



%%	recursive_directory_files(+Dir, -Files) is det.
%
%	True when Files is a list holding all files in Dir, recursively.

recursive_directory_files(Dir,[]):-ignore_dir_files(Dir),!.
recursive_directory_files(Dir, Files):-
	dir_prefix(Dir, Prefix),
	recursive_directory_files(Dir, Prefix, Files0, []),
        exclude(ignore_dir_files0,Files0,Files).

recursive_directory_files(Dir, Prefix, AllFiles, Rest) :-
	directory_files(Dir, Files),
	dir_files(Files, Dir, Prefix, AllFiles, Rest).

dir_files([], _, _, Files, Files).
dir_files([H|T], Dir, Prefix, Files, Rest) :-                           
	(   ignore_dir_files(H)
	->  dir_files(T, Dir, Prefix, Files, Rest)
	;   directory_file_path(Dir, H, Entry),
	    (	exists_directory(Entry)
	    ->	recursive_directory_files(Entry, Prefix, Files, Rest0)
	    ;	atom_concat(Prefix, File, Entry),
		Files = [File|Rest0]
	    ),
	    dir_files(T, Dir, Prefix, Rest0, Rest)
	).

dir_prefix(., '') :- !.
dir_prefix(Dir, Prefix) :-
	(   sub_atom(Dir, _, _, 0, /)
	->  Prefix = Dir
	;   atom_concat(Dir, /, Prefix)
	).


ignore_dir_files0(A):- \+ atom_contains(A,'examples'),!,atom_contains(A,'.').

ignore_dir_files(A):- \+ atom(A),!,true.
ignore_dir_files(.).

ignore_dir_files(A):- mimetype:file_mime_type(A,Type),memberchk(Type,[image/_,_/javascript]),!.
ignore_dir_files(..).
ignore_dir_files(A):-atom_contains(A,'.class'),!.
ignore_dir_files(A):-atom_contains(A,'.git'),!.
ignore_dir_files(A):-atom_concat(_,'.o',A),!.
ignore_dir_files(A):-atom_contains(A,'.h'),!.
ignore_dir_files(A):-atom_contains(A,'.j'),!.
ignore_dir_files(A):-atom_contains(A,~),!.
ignore_dir_files(A):-atom_contains(A,?),!.
% ignore_dir_files(A):-atom_contains(A,'/.'),!.
baseKB:lplw:- logicmoo_plweb:recursive_directory_files('../../..',O),length(O,N),maplist(writeln,O),writeln(N).
% :- baseKB:lplw.


