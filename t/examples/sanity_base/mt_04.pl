/* <module>
%
%  PFC is a language extension for prolog.
%
%  It adds a new type of module inheritance
%
% Dec 13, 2035
% Douglas Miles
*/
:- module(mt_04,[]).

:- ensure_loaded(library(pfc)).

:- begin_pfc.

:- set_defaultAssertMt(myMt).

mtProlog(code1).
mtCycL(kb2).
mtCycL(kb3).


kb2:b.

baseKB:genlMt(kb2,code1).

kb2: (?- a).

genlMt(kb3,kb2).

kb3: (a==>c).



% code1: (a <- b).
:- ain((code1: (a:-b))).


