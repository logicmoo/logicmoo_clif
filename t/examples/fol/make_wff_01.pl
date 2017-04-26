#!/usr/bin/env swipl

% =================================================================================
% Load the system
% =================================================================================

:- ensure_loaded(library(logicmoo_user)).

:- make.

:- set_lang(clif).
:- use_pfc.

% =================================================================================
% Set our engine up
% =================================================================================

% deduce instances from usages in args having the effect of deducing human,dwelling,beverage_class are classes
==> feature_setting(make_wff,true).
% set truth maintainance system to remove previous assertions that new assertions disagree with 
==> feature_setting(tms_mode,remove_conflicting).

:- set_prolog_flag(runtime_debug,3). % mention it when we remove previous assertions

:- set_prolog_flag_until_eof(do_renames,mpred_expansion).

:- kif_compile.


% =================================================================================
% Define a couple predicates
% =================================================================================
:- set_prolog_flag(access_level,system).
:- redefine_system_predicate(arity(_,_)).
:- unlock_predicate(arity(_,_)).
:- multifile arity/2.

% maximum cardinality of livesAt/2 is 1
==> isa(livesAt,'FunctionalBinaryPredicate').
% thus implies
==> arity(livesAt,2).
==> argIsa(livesAt,1,human).
==> argIsa(livesAt,2,dwelling).

% define drinks/2
==> arity(drinks,2).
==> argIsa(drinks,1,drinker).
==> argIsa(drinks,2,beverage_class).

% =================================================================================
% Test 1
% =================================================================================

==> poss(livesAt(fred,green_house)).

:- must(isa(fred,human)).
:- must(isa(green_house,dwelling)).

% =================================================================================
% Test 2
% =================================================================================

==> all(X, if(livesAt(X, green_house),drinks(X, coffee))).

failed:- must(poss(isa(fred,drinker))).
:- must(isa(coffee,beverage_class)).


% =================================================================================
% Test 3
% =================================================================================

==> livesAt(sue,green_house).

:- must(isa(sue,drinker)).

:- mpred_why(isa(sue,drinker)).


% =================================================================================
% Test 4
% =================================================================================

% ==> livesAt(sue,red_house).

failed:- must(\+ isa(sue,drinker)).


