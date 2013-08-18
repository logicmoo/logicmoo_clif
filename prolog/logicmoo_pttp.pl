/* <module> logicmoo_plarkc - special module hooks into the logicmoo engine allow
%   clif syntax to be recocogized via our CycL/KIF handlers 
% 
% Logicmoo Project: A LarKC Server written in Prolog
% Maintainer: Douglas Miles
% Dec 13, 2035
%
*/
:- module(logicmoo_pttp,[]).

:- system:reexport(library('logicmoo/pttp/dbase_i_mpred_pttp_statics.pl')).
:- system:reexport(library('logicmoo/pttp/dbase_i_mpred_pttp.pl')).

