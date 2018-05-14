/* <module> logicmoo_plarkc - special module hooks into the logicmoo engine allow
%   clif syntax to be recocogized via our CycL/KIF handlers 
% 
% Logicmoo Project: A LarKC Server written in Prolog
% Maintainer: Douglas Miles
% Dec 13, 2035
%
*/
:- module(logicmoo_pdt,[start_pdt/0]).

% :- absolute_file_name(swi(xpce/prolog/lib),X), assert_if_new(user:library_directory(X)).

ensure_guitracer:-!.
ensure_guitracer:- break,
 absolute_file_name(swi(xpce/prolog/lib),X), assert_if_new(user:library_directory(X)), 
 user:use_module(library(pce_prolog_xref)),
 user:use_module(library(emacs_extend)),
 user:use_module(library(trace/gui)),
 user:use_module(library(pce)),
 user:use_module(library(gui_tracer)),
 reload_library_index.

%:- abolish(start_pdt/0).
start_pdt:-
 % ensure_guitracer, 
 % user:use_module('/opt/logicmoo_workspace/lib/swipl/xpce/prolog/lib/gui_tracer.pl'),
 %break,
 user:consult(library('logicmoo/pdt_server/socketProcessXXX.tmp.pl')).

:- if(\+ thread_property(_,alias(pdt_console_server))).
:- if(\+ thread_property(_,alias('consult_server@35421'))).
:- if(app_argv('--pdt')).
%:- break.
:- during_net_boot(start_pdt).
:- endif.
:- endif.
:- endif.


