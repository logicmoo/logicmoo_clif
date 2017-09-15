

:- module(cute6,[]).

:- include(test_header).

:- test_boxlog([+assert],exactly(4, X, puppy(X) & poss(cute(X)))).

end_of_file.

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
