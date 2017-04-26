#!/usr/bin/env swipl

% =================================================================================
% Load the system
% =================================================================================

:- ensure_loaded(library(logicmoo_user)).

:- set_prolog_flag(dialect,clif).

% =================================================================================
% Set our engine up
% =================================================================================

% deduce instances from usages in args having the effect of deducing human,dwelling,beverage_class are classes
==> make_wff(true).
% set false so make_wff/1 will be noticed (default is true)
==> assume_wff(false).
% set truth maintainance system to remove previous assertions that new assertions disagree with 
==> tms_mode(remove_conflicting).

:- set_prolog_flag(runtime_debug,3). % mention it when we remove previous assertions

% =================================================================================
% Define a couple predicates
% =================================================================================

% maximum cardinality of livesAt/2 is 1
instance(livesAt,'FunctionalBinaryPredicate').
% thus implies
arity(livesAt,2).
domain(livesAt,1,human).
domain(livesAt,2,dwelling).

% define drinks/2
arity(drinks,2).
domain(drinks,1,human).
domain(drinks,2,beverage_class).

% =================================================================================
% Note these two assertions are implicit to the system and have no side effect 
% (they are here to serve as a reminder)
% =================================================================================

% all objects in the universe that do drink coffee, may drink coffee
all(X, if(drinks(X, coffee),possible(drinks(X, coffee)))).

% for any objects in the universe that live in the green house must obvously have that as a possibility
all(X, if(livesAt(X, green),possible(livesAt(X, green)))).

% =================================================================================
% But given the above: 
%
%   Only things that possibly can drink coffee live in the green house?
%
% =================================================================================
all(X, livesAt(X, green_house) & drinks(X, coffee)).

~possible(livesAt(fred,green_house)).

% Does fred drink coffee? (should be unknown)
:- \+ drinks(fred,coffee).

possible(livesAt(joe,green_house)).
:- drinks(joe,coffee).


% =================================================================================
% These two assertions are a bit weird but are for fun
% =================================================================================

% all objects in the universe that may drink coffee do drink coffee
%all(X, if(possible(drinks(X, coffee)),drinks(X, coffee))).

% all objects in the universe that may live in the green house do live in the green house
%all(X, if(possible(livesAt(X, green_house)),lives(X, green_house) )).




