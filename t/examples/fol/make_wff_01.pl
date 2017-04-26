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
domain(drinks,1,drinker).
domain(drinks,2,beverage_class).

% =================================================================================
% Test 1
% =================================================================================

possible(livesAt(fred,green_house)).

:- must(instance(fred,human)).
:- must(instance(green_house,dwelling)).

% =================================================================================
% Test 2
% =================================================================================

all(X, if(livesAt(X, green_house),drinks(X, coffee))).

:- must(possible(instance(fred,drinker))).
:- must(instance(coffee,beverage_class)).


% =================================================================================
% Test 3
% =================================================================================

livesAt(sue,green_house).

:- must(instance(sue,drinker)).


% =================================================================================
% Test 4
% =================================================================================

livesAt(sue,red_house).

:- must(\+ instance(sue,drinker)).


