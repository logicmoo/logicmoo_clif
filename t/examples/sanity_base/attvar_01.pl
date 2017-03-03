#!/usr/bin/env swipl

:- module(attvar_01,[]).

:- ensure_loaded(system:library(logicmoo_utils)).
:- ensure_loaded(library(pfc)).
:- set_prolog_flag(assert_attvars,true).

:-export(demo_nb_linkval/1).
demo_nb_linkval(T) :-
        T = nice(N),
        (   N = world,
            nb_linkval(myvar, T),
            fail
        ;   nb_getval(myvar, V),
            writeln(V)
        ).

:- debug_logicmoo(_).
% :- nodebug_logicmoo(http(_)).
:- debug_logicmoo(logicmoo(_)).

:- file_begin(pfc).


:- dynamic(sk_out/1).
:- dynamic(sk_in/1).

:- read_attvars(true).
:- set_prolog_flag(read_attvars,true).
 :- enable_mpred_expansion.

sk_in(avar([vn='Ex',sk='SKF-666'])).

:- listing(sk_in).

:- must((sk_in(Ex),get_attr(Ex,sk,What),What=='SKF-666')).




q :- q(X), writeln(X).
q(X) :- '$depth_of_var'(X, D), format('Depth = ~w~n', [D]), D < 5, q(X),notail.

notail.

/*
Running this says:

1 ?- q.
Depth = 1
Depth = 2
Depth = 3
Depth = 4
Depth = 5

*/
