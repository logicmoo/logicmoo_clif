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

% all objects in the universe that do drink coffee, may drink coffee
all(X, if(drinks(X, coffee),possible(drinks(X, coffee)))).

% for any objects in the universe that live in the green house must obvously have that as a possibility
all(X, if(livesAt(X, green),possible(livesAt(X, green)))).

% =================================================================================
% Some facts about the world
% =================================================================================

livesAt(joe,red_house).

:- must(~possible(livesAt(joe,green_house))).

:- printAll(mpred_why(~possible(livesAt(joe,green_house)),_Why)).

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
exists(X, livesAt(X, green_house) & drinks(X, coffee)).

% Does anyone live at the green house? (Should be one right?)
:- mpred_test(livesAt(_X,green_house)).

% Can anyone live at the green house? (Should be everyone but the one listed above?)
:- mpred_test(~possible(livesAt(_X,green_house))).


