
% test dealing  with counts of instances for modality

:- module(cute6,[]).

:- include(test_header).

%===== domain =======

% there are 4 possibly cute puppies
:- test_boxlog([+assert],exactly(4, X, puppy(X) & poss(cute(X)))).

% there are 2 (for sure) cute puppies
:- test_boxlog([+assert],exactly(2, X, puppy(X) & cute(X))).

% there are 5 puppies
:- test_boxlog([+assert],exactly(5, X, puppy(X))).

% cute things cannot be ugly things and visa versa
:- test_boxlog([+assert],forall( X, iff(cute(X),not(ugly(X))))).

% all puppies are cute or ugly
:- test_boxlog([+assert],forall( X, if(puppy(X),(ugly(X) v cute(X))))).

%===== tests =======

% means total 5 puppies 
:- test_boxlog([+test_query],( findall(X,puppy(X),L),length(L,5))).

% 2 are for sure actually cute
:- test_boxlog([+test_query],( findall(X,(puppy(X),cute(X)),L),length(L,2))).

% leaving 3 more as possibly cute
:- test_boxlog([+test_query],( findall(X,(puppy(X),poss(cute(X))),L),length(L,3))).

% the last puppy is not for sure known cute or or not cute so it may be ugly
:- test_boxlog([+test_query],( findall(X,(puppy(X),poss(ugly(X))),L),length(L,1))).


end_of_file.

%===== debugging notes =======

:- 
  mpred_test((tru(puppy(Puppy1)),tru(puppy(Puppy2)),Puppy1=Puppy2)).
/*
Puppy1 = Puppy2,
add_cond(Puppy2, [puppy, poss(cute(Puppy2)), made_skolem(skF(skIsCuteIsPuppyX_0FnSk, vv), 4)]) ;
Puppy1 = Puppy2,
add_cond(Puppy2, [puppy, poss(cute(Puppy2)), made_skolem(skF(skIsCuteIsPuppyX_0FnSk, vv), 2)]) ;
Puppy1 = Puppy2,
add_cond(Puppy2, [puppy, poss(cute(Puppy2)), made_skolem(skF(skIsCuteIsPuppyX_0FnSk, vv), 3)]) ;
Puppy1 = Puppy2,
add_cond(Puppy2, [puppy, poss(cute(Puppy2)), made_skolem(skF(skIsCuteIsPuppyX_0FnSk, vv), 1)]).
*/

go_test:- forall(no_repeats(proven_neg(G)),writeln(proven_neg(G))).



?- 
   tru(puppy(Puppy1)),tru(puppy(Puppy2)),tru(puppy(Puppy3)),tru(puppy(Puppy4),tru(puppy(Puppy5)),
   comingle_vars([Puppy1,Puppy2,Puppy3,Puppy4],NewP).
