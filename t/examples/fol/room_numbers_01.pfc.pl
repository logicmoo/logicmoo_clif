:- module(kbii,[]).

:- set_prolog_flag(os_argv,[swipl, '-f', '/dev/null','--nonet']).
:- include(test_header).
:- set_kif_option(+assert).

exists(R1,room_number(R1,22)).

exists(R1,room_number(R1,77)).

all(R, (room_number(R,22) => (room(R) & ~big(R)))) .    

all(R, (room_number(R,77) => (room(R) & big(R)))) .    

% need proof that 
?- sanity_test(( room_number(R1,22) & room_number(R2,77) => R1 \= R2 )).


end_of_file.

% simpler
all(R, (room_number(R,22) => ( ~big(R)))) .    
all(R, (room_number(R,77) => ( big(R)))) .    
% need proof that 
?- sanity_test(( room_number(R1,22) & room_number(R2,77) => R1 \= R2 )).



