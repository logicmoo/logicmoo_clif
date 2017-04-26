#!/usr/bin/env swipl

:- ensure_loaded(logicmoo_user).
:- set_prolog_flag(dialect,clif).

% all objects in the universe that may drink coffee do drink coffee
all(X, if(possible(drinks(X, coffee)),drinks(X, coffee))).

% all objects in the universe that may live in the green house do live in the green house
all(X, if(possible(lives(X, green)),lives(X, green) )).

% only things that possibly can drink coffee live in the green house?
all(X, lives(X, green) & drinks(X, coffee)).

