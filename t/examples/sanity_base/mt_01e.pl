/* <module>
%
%  PFC is a language extension for prolog.
%
%  It adds a new type of module inheritance
%
% Dec 13, 2035
% Douglas Miles
*/
:- module(mt_01e,[]).

:- ensure_loaded(library(pfc)).

:- begin_pfc.

:- sanity(current_prolog_flag(retry_undefined,true)).
:- set_prolog_flag(retry_undefined,true).

:- mpred_test(mtCycL(mt_01e)).
:- mpred_test(\+ mtProlog(mt_01e)).
:- mpred_test(tMicrotheory(mt_01e)).

genlMt(kb1,mt_01e).

:- mpred_test(\+ mtProlog(kb1)).
:- mpred_test(\+ mtCycL(kb1)).

:- mpred_test(tMicrotheory(kb1)).


