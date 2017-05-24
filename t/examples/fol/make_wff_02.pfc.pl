

% =================================================================================
% Define a couple predicates
% =================================================================================
:- set_prolog_flag(access_level,system).
:- redefine_system_predicate(arity(_,_)).
:- unlock_predicate(arity(_,_)).
:- multifile arity/2.

% maximum cardinality of livesAt/2 is 1
%==> isa(livesAt,'FunctionalBinaryPredicate').
==> singleValuedInArg(livesAt,2).
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

:- mpred_test(isa(fred,human)).
:- mpred_test(isa(green_house,dwelling)).

% =================================================================================
% Test 2
% =================================================================================

:- mpred_trace_exec.

prove_holds_t(F,A,B)==>t(F,A,B).

prove_not_holds_t(F,A,B)==> ~t(F,A,B).


==> livesAt(fran,green_house).
==> livesAt(sue,green_house).



proven(G) :- call_u(G).

==> all(X, if(livesAt(X, green_house),drinks(X, coffee))).

:- kif_add(isa(joe,drinker)).

:- mpred_test(isa(fran,drinker)).

:- mpred_test((isa(fran,X),X==drinker)).

:- mpred_test(poss(isa(fred,drinker))).

:- mpred_test(isa(coffee,beverage_class)).

% =================================================================================
% Test 3
% =================================================================================

==> livesAt(sue,green_house).
% :- repropagate(all(X, if(livesAt(X, green_house),drinks(X, coffee)))).
:- mpred_test(isa(sue,drinker)).

:- mpred_why(isa(sue,drinker)).

% =================================================================================
% Test 4 
% =================================================================================

==> livesAt(sue,red_house).

==> livesAt(ralf,red_house).

:- mpred_test(\+ isa(ralf,drinker)).

:- mpred_why(isa(sue,drinker)).
failure:- mpred_test(\+ isa(sue,drinker)).

