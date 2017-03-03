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




code1: (a:- printAll('$current_source_module'(M)),b).

kb2: (b).

genlMt(kb2,code1).


% before test, to make sure a was not accdently defined in kb2
:- sanity(\+ clause(kb2:a,_)).

% before test, genlMt makes the rule available and should not corrupt the code1 module
:- sanity(\+ clause(code1:b,_)).

% make sure genlMt didnt unassert 
:- sanity(clause(kb2:b,_)).



% run the test
kb2: (?- a).


% to make sure a does not get accdently defined in kb2
:- mpred_must(\+ clause(kb2:a,_)).

% genlMt makes the rule available and should not corrupt the code1 module
:- mpred_must(\+ clause(code1:b,_)).

% genlMt 

:- mpred_must(\+ clause(code1:b,_)).
