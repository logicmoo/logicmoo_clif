:- module(kbii,[]).

:- set_prolog_flag(os_argv,[swipl, '-f', '/dev/null','--nonet']).
:- include(test_header).
:- set_kif_option(+assert).

% must_be_satifiable(P):- kif_to_boxlog(P,BoxLog),all_asserted(BoxLog).

% Version A - Two rooms
exists(R1,room_number(R1,22)).
exists(R1,room_number(R1,77)).
all(R, (room_number(R,22) => (room(R) & ~big(R)))) .
all(R, (room_number(R,77) => (room(R) & big(R)))) .    

% need proof that 
?- must_be_satifiable(( room_number(R1,22) & room_number(R2,77) => R1 \= R2 )).


:- reset_kb(kbii).

% Version B - Simpler
all(R, (room_number(R,22) => ( ~big(R)))) .    
all(R, (room_number(R,77) => ( big(R)))) .

% need proof that 
?- must_be_satifiable(( room_number(R1,22) & room_number(R2,77) => R1 \= R2 )).

% ISSUE: https://github.com/logicmoo/logicmoo_workspace/issues/440 
% EDIT: https://github.com/logicmoo/logicmoo_workspace/edit/master/packs_sys/logicmoo_base/t/examples/fol/room_numbers_01.pfc.pl 
% JENKINS: https://jenkins.logicmoo.org/job/logicmoo_workspace/lastBuild/testReport/logicmoo.base.examples.fol/ROOM_NUMBERS_01/ 
% ISSUE_SEARCH: https://github.com/logicmoo/logicmoo_workspace/issues?q=is%3Aissue+label%3AROOM_NUMBERS_01 

