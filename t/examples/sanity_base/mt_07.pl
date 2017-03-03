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

:- user:ensure_loaded(system:library(logicmoo_utils)).
:- ensure_loaded(library(pfc)).


%:- add_import_module(mt_01,baseKB,end).

:- set_defaultAssertMt(myMt).

mtProlog(code1).
mtCycL(kb2).
mtCycL(kb3).

% code1: (a <- b).
code1: (a:- printAll('$current_source_module'(M)),b).


kb2: (b).

genlMt(kb2,code1).

kb2: (?- a).

genlMt(kb3,kb2).


predicateConventionMt(c,code1).

kb3: (a==>c).

% to make sure a does not get accdently defined in kb2 or kb3
:- mpred_must(\+ clause(kb3:a,_)).
:- mpred_must(\+ clause(kb2:a,_)).

% c is forward chained back into 'code1' where it becomes asserted
:- mpred_must(clause(code1:c,_)).
