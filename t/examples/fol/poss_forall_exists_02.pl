#!/usr/bin/env swipl

:- ensure_loaded(logicmoo_user).
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



% =================================================================================
% Note these two assertions are implicit to the system and have no side effect
% =================================================================================

% all objects in the universe that may drink coffee do drink coffee
all(X, if(drinks(X, coffee),possible(drinks(X, coffee)))).

% all objects in the universe that may live in the green house do live in the green house
all(X, if(livesAt(X, green),possible(livesAt(X, green)))).

% =================================================================================
% Some facts about the world
% =================================================================================

livesAt(joe,red_house).

~possible(drinks(bob,coffee)).

~possible(livesAt(fred,green_house)).

% =================================================================================
% But given the above: 
%
%   Only things that possibly can drink coffee live in the green house?
%  
%   Only currently individuals whom are not living in the red house live in the green?
%
% =================================================================================
all(X, livesAt(X, green_house) & drinks(X, coffee)).

% Does anyone live at the green house? (Should be none?)
:- mpred_test(livesAt(_X,green_house)).

% Can anyone live at the green house? (Should be every cant?)
:- mpred_test(~possible(livesAt(_X,green_house))).




