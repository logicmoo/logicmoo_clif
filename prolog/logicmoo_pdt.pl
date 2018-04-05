/* <module> logicmoo_plarkc - special module hooks into the logicmoo engine allow
%   clif syntax to be recocogized via our CycL/KIF handlers 
% 
% Logicmoo Project: A LarKC Server written in Prolog
% Maintainer: Douglas Miles
% Dec 13, 2035
%
*/
:- module(logicmoo_pdt,[]).


start_pdt:- user:consult('logicmoo/pdt_server/socketProcessXXX.tmp.pl').

:- if(app_argv('--pdt')).
:- if(\+ thread_property(_,alias(pdt_console_server))).
% :- during_net_boot(start_pdt).
:- endif.
:- endif.

