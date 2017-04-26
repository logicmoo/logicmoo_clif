#!/usr/bin/env swipl

:- ensure_loaded(library(logicmoo_user)).

:- set_prolog_flag(dialect,clif).


% maximum cardinality of livesAt/2 is 1
instance(livesAt,'FunctionalBinaryPredicate').
% thus implies
arity(livesAt,2).
domain(livesAt,1,human).
domain(livesAt,2,dwelling).

% maximum cardinality of livesAt/2 is 1
arity(drinks,2).
domain(drinks,1,human).
domain(drinks,2,beverage_class).


% all objects in the universe that may drink coffee do drink coffee
all(X, if(possible(drinks(X, coffee)),drinks(X, coffee))).

% all objects in the universe that may live in the green house do live in the green house
all(X, if(possible(livesAt(X, green_house)),lives(X, green_house) )).

% =================================================================================
% But given the above: 
%
%   Only things that possibly can drink coffee live in the green house?
%
% =================================================================================
all(X, livesAt(X, green_house) & drinks(X, coffee)).

~possible(livesAt(fred,green_house)).

