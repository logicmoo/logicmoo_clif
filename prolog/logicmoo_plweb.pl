%#!/usr/bin/swipl 
:- module(logicmoo_plweb,[
          ensure_webserver_3020/0,
          ensure_webserver_p/1]).

kill_3020:- threads,wdmsg(kill_3020),!.
kill_3020:- whenever_flag_permits(run_network,ignore(catch(shell('kill -9 $(lsof -t -i:3020 -sTCP:LISTEN) &>2 ||:'),E,dmsg(E)))).

:- use_module(logicmoo_swish).

:- add_file_search_path_safe(plweb,pack(plweb)).

% :- consult(plweb(load)).·

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% START WEBSERVER
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%



ensure_webserver_p(Port):- format(atom(A),'httpd@~w',[Port]),thread_property(N,status(V)),V=running,atom(N),atom_concat(A,_,N),!.
ensure_webserver_p(Port):- whenever_flag_permits(run_network,
 (kill_3020,catch((thread_httpd:http_server(http_dispatch,[ port(Port), workers(16) ])),E,(writeln(E),fail)))),!.

ensure_webserver_3020:- (getenv('LOGICMOO_PORT',Was);Was=3000),
   WebPort is Was + 20, ensure_webserver_p(WebPort).

:- during_boot(ensure_webserver_3020).

%:- autoload([verbose(false)]).


:- break.



