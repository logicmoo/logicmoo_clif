%#!/usr/bin/swipl 

:- module(logicmoo_webbot,[
 www_start/0,www_start/1]).

:- whenever_flag_permits(load_network,load_library_system(library(logicmoo_network))).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- dmsg("LOGICMOO WEBBOT").
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

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
:- use_module(swi(library/http/html_write)).
:- endif.  % --www

:- if((app_argv_ok('--sigma'))).
:- dmsg("SIGMA-KE Server").
:- user:use_module(library(xlisting_web)).
:- user:listing(baseKB:shared_hide_data/1).
:- endif.

:- if(app_argv('--www')).
:- during_net_boot(www_start).
:- endif.

% :- break.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Sanity tests that first run whenever a person stats the MUD to see if there are regressions in the system
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- if(( ( \+ ((current_prolog_flag(logicmoo_include,Call),Call))) )).
%.
:- endif.



end_of_file.


