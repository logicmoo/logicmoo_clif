/*  LogicMOO User Modules Setup
%
%
% Dec 13, 2035
% Douglas Miles

*/
:- module(logicmoo_user_module,
 [
 % logicmoo_user_stacks/0,
 /*(1199,fx,('==>')),
 op(1190,xfx,('::::')),
 op(1180,xfx,('==>')),
 op(1170,xfx,'<==>'),
 op(1160,xfx,('<-')),
 op(1150,xfx,'=>'),
 op(1140,xfx,'<='),
 op(1130,xfx,'<=>'),
 op(600,yfx,'&'),
 op(600,yfx,'v'),
 op(350,xfx,'xor'),
 op(300,fx,'~'),
 op(300,fx,'-')*/  ]).


:- current_prolog_flag(readline,Was),writeln(readline=Was).
% :- set_prolog_flag(readline,editline).
% :- set_prolog_flag(readline,true).

:- if(current_prolog_flag(readline,editline)).
:- use_module(library(readline)).
:- listing(prolog:history/2).
:- abolish(prolog:history/2).
:- current_prolog_flag(readline,Was),writeln(readline=Was).
:- if(exists_source(library(editline))).
:- reconsult(library(editline)).
:- endif.
:- else.
:- if(exists_source(library(editline))).
:- use_module(library(editline)).
:- listing(prolog:history/2).
:- abolish(prolog:history/2).
:- endif.
:- current_prolog_flag(readline,Was),writeln(readline=Was).
:- set_prolog_flag(readline,readline).
:- reconsult(library(readline)).
:- endif.

:- set_prolog_flag(pfc_booted,false).
:- current_prolog_flag(unsafe_speedups,_)->true;set_prolog_flag(unsafe_speedups,true).
:- user:use_module(logicmoo_snark).
:- user:use_module(library(pfc)).
:- user:use_module(library(xlisting)).
:- user:use_module(library(gvar_syntax)).
:- user:use_module(library(dictoo)).
:- set_prolog_flag(pfc_booted,false).


/*
:- set_prolog_flag(report_error,true).
:- set_prolog_flag(fileerrors,false).
:- set_prolog_flag(access_level,system).
:- set_prolog_flag(debug_on_error,true).
:- set_prolog_flag(debug,true).
:- set_prolog_flag(gc,false).
:- set_prolog_flag(gc,true).
:- set_prolog_flag(optimise,false).
:- set_prolog_flag(last_call_optimisation,false).
:- debug.
*/
% :- after_boot((ignore((hook_database:call(retract,(ereq(G):- find_and_call(G))),fail)))).

% % :- set_prolog_flag(mpred_te,true).
 % :- set_prolog_flag(subclause_expansion,true).
:- set_prolog_flag(pfc_booted,true).
:- create_prolog_flag(retry_undefined,default,[type(term),keep(true)]).
:- set_prolog_flag(retry_undefined,true).
:- set_prolog_flag(read_attvars,false).

:- ((hook_database:call(asserta_if_new,(ereq(G):- !, baseKB:call_u(G))))).
:- after_boot((wdmsg(after_boot),hook_database:call(asserta_new,(ereq(G):- !, baseKB:call_u(G))))).

:- after_boot((wdmsg(after_boot),hook_database:call(asserta_new,(ereq(G):- !, baseKB:call_u(G))))).

:-  prolog_statistics:time((baseKB:ensure_loaded(baseKB:library(logicmoo/pfc/'autoexec.pfc')))).


