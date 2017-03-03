/* <module> logicmoo_plarkc - special module hooks into the logicmoo engine allow
%   clif syntax to be recocogized via our CycL/KIF handlers
%
% Logicmoo Project: A LarKC Server written in Prolog
% Maintainer: Douglas Miles
% Dec 13, 2035
%
*/
:- module(lm_cyc,[cyc_exec/1,cyc_exec/2]).



:- use_module(library(jpl)).


cyc_exec(X):-cyc_exec(X,_).

cyc_exec(X,X).

