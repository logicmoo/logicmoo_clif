/* <module>
%
%  PFC is a language extension for prolog.
%
%  It adds a new type of module inheritance
%
% Dec 13, 2035
% Douglas Miles
*/
:- module(mt_01,[]).

:- ensure_loaded(library(pfc)).

:- set_defaultAssertMt(myMt).

:- begin_pfc.

predicateConventionMt(loves/2,socialMt).

mt1:like(sally,joe).

genlMt(mt1,socialMt).

% this will raise upward the assertion.. is this OK?
like(A,B)==>loves(B,A).

:- mpred_must(socialMt:loves(joe,sally)).


