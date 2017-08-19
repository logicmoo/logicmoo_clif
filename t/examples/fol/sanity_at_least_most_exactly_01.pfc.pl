#!/usr/bin/env swipl

:- module(t123,[]).

:- include(test_header).
:- module(t123).   
:- '$set_source_module'(t123).

% :- process_this_script.

:- statistics.



subtest([subtest_assert(tHuman(joe)),
        mpred_test(isa(_,tHeart))]).

subtest([subtest_assert(tHuman(joe)),
        mpred_test(hasOrgan(joe,_))]).

subtest([subtest_assert(tHeart(_)),
        mpred_test(~hasOrgan(jack,_))]).



:- ain(tHuman(iBob)).

testable_quants(X,Fml,Q,Name):-member(QF,[exactly,atmost,atleast]),member(QN,[0,1,2,3,5,10]),Q=..[QF,QN,X,Fml],atom_concat(QF,QN,Name).
testable_quants(X,Fml,Q,Name):-member(QF,[all,exists]),Q=..[QF,X,Fml],atom_concat(QF,'1',Name).
testable_quants(X,Fml,~Q,Name):-member(QF,[all,exists]),Q=..[QF,X,Fml],atom_concat(QF,'0',Name).


% single lit

:- add_test(most1, (all([[Human,tHuman]],atmost(1,[[M1Spouse,tSpouse]],hasSpouse(Human,M1Spouse))))).
:- add_test(least1, (all([[Human,tHuman]],atleast(1,[[LeastIdea,tIdea]],hasIdea(Human,LeastIdea))))).
:- add_test(exactly1, (all([[Human,tHuman]],exactly(1,[[Heart,tHeart]],hasHeart(Human,Heart))))).
:- add_test(exists1, (all([[Human,tHuman]],exists([[SomeClue,tClue]],hasClue(Human,SomeClue))))).

:- add_test(most2, (all([[Human,tHuman]],atmost(2,[[M2Kidney,tKidney]],hasKidney(Human,M2Kidney))))).
:- add_test(least2, (all([[Human,tHuman]],atleast(2,[[L2Dream,tDream]],hasDream(Human,L2Dream))))).
:- add_test(exactly2, (all([[Human,tHuman]],exactly(2,[[E2ye,tEye]],hasEye(Human,E2ye))))).
:- add_test(exists2, (all([[Human,tHuman]],exists([[Lung1,tLung],[Lung2,tLung]],hasLung(Human,Lung1)&hasLung(Human,Lung2)&leftOf(Lung1,Lung2))))).

:- add_test(most0, (all([[Human,tHuman]],atmost(0,[[M0Wing,tWing]],hasWing(Human,M0Wing))))).
:- add_test(least0, (all([[Human,tHuman]],atleast(0,[[L0Dollar,tDollar]],hasDollar(Human,L0Dollar))))).
:- add_test(exactly0, (all([[Human,tHuman]],exactly(0,[[E0Coin,tCoin]],hasCoin(Human,E0Coin))))).
:- add_test(exists0, (all([[Human,tHuman]],~exists([[CommonSense,tCommonSense]],hasCommonSense(Human,CommonSense))))).
      
% or
:- add_test(most1b, (all([[Human,tHuman]],atmost(1,[[M1Spouse,tSpouse]],hasSpouse(Human,M1Spouse) v controls(Human,M1Spouse))))).
:- add_test(least1b, (all([[Human,tHuman]],atleast(1,[[LeastIdea,tIdea]],hasIdea(Human,LeastIdea) v controls(Human,LeastIdea))))).
:- add_test(exactly1b, (all([[Human,tHuman]],exactly(1,[[Heart,tHeart]],hasHeart(Human,Heart) v controls(Human,Heart))))).
:- add_test(exists1b, (all([[Human,tHuman]],exists([[SomeClue,tClue]],hasClue(Human,SomeClue) v controls(Human,SomeClue))))).

:- add_test(most2b, (all([[Human,tHuman]],atmost(2,[[M2Kidney,tKidney]],hasKidney(Human,M2Kidney) v controls(Human,M2Kidney))))).
:- add_test(least2b, (all([[Human,tHuman]],atleast(2,[[L2Dream,tDream]],hasDream(Human,L2Dream) v controls(Human,L2Dream))))).
:- add_test(exactly2b, (all([[Human,tHuman]],exactly(2,[[E2ye,tEye]],hasEye(Human,E2ye) v controls(Human,E2ye))))).
:- add_test(exists2b, (all([[Human,tHuman]],exists([[Lung1,tLung],[Lung2,tLung]],hasLung(Human,Lung1) v hasLung(Human,Lung2) v leftOf(Lung1,Lung2) v controls(Human,Lung1) v controls(Human,Lung2))))).

:- add_test(most0b, (all([[Human,tHuman]],atmost(0,[[M0Wing,tWing]],hasWing(Human,M0Wing) v controls(Human,M0Wing))))).
:- add_test(least0b, (all([[Human,tHuman]],atleast(0,[[L0Dollar,tDollar]],hasDollar(Human,L0Dollar) v controls(Human,L0Dollar))))).
:- add_test(exactly0b, (all([[Human,tHuman]],exactly(0,[[E0Coin,tCoin]],hasCoin(Human,E0Coin) v controls(Human,E0Coin))))).
:- add_test(exists0b, (all([[Human,tHuman]],~exists([[CommonSense,tCommonSense]],hasCommonSense(Human,CommonSense) v controls(Human,CommonSense))))).

% implies
:- add_test(most1c, (all([[Human,tHuman]],atmost(1,[[M1Spouse,tSpouse]],hasSpouse(Human,M1Spouse) => controls(Human,M1Spouse))))).
:- add_test(least1c, (all([[Human,tHuman]],atleast(1,[[LeastIdea,tIdea]],hasIdea(Human,LeastIdea) => controls(Human,LeastIdea))))).
:- add_test(exactly1c, (all([[Human,tHuman]],exactly(1,[[Heart,tHeart]],hasHeart(Human,Heart) => controls(Human,Heart))))).
:- add_test(exists1c, (all([[Human,tHuman]],exists([[SomeClue,tClue]],hasClue(Human,SomeClue) => controls(Human,SomeClue))))).

:- add_test(most2c, (all([[Human,tHuman]],atmost(2,[[M2Kidney,tKidney]],hasKidney(Human,M2Kidney) => controls(Human,M2Kidney))))).
:- add_test(least2c, (all([[Human,tHuman]],atleast(2,[[L2Dream,tDream]],hasDream(Human,L2Dream) => controls(Human,L2Dream))))).
:- add_test(exactly2c, (all([[Human,tHuman]],exactly(2,[[E2ye,tEye]],hasEye(Human,E2ye) => controls(Human,E2ye))))).
:- add_test(exists2c, (all([[Human,tHuman]],exists([[Lung1,tLung],[Lung2,tLung]],
  (hasLung(Human,Lung1) & hasLung(Human,Lung2) & leftOf(Lung1,Lung2)) => (controls(Human,Lung1) & controls(Human,Lung2)))))).

:- add_test(most0c, (all([[Human,tHuman]],atmost(0,[[M0Wing,tWing]],hasWing(Human,M0Wing) => controls(Human,M0Wing))))).
:- add_test(least0c, (all([[Human,tHuman]],atleast(0,[[L0Dollar,tDollar]],hasDollar(Human,L0Dollar) => controls(Human,L0Dollar))))).
:- add_test(exactly0c, (all([[Human,tHuman]],exactly(0,[[E0Coin,tCoin]],hasCoin(Human,E0Coin) => controls(Human,E0Coin))))).
:- add_test(exists0c, (all([[Human,tHuman]],~exists([[CommonSense,tCommonSense]],hasCommonSense(Human,CommonSense) => controls(Human,CommonSense))))).


% and
:- add_test(most0a, (all([[Human,tHuman]],atmost(0,[[M0Wing,tWing]],hasWing(Human,M0Wing)&controls(Human,M0Wing))))).
:- add_test(least0a, (all([[Human,tHuman]],atleast(0,[[L0Dollar,tDollar]],hasDollar(Human,L0Dollar)&controls(Human,L0Dollar))))).
:- add_test(exactly0a, (all([[Human,tHuman]],exactly(0,[[E0Coin,tCoin]],hasCoin(Human,E0Coin)&controls(Human,E0Coin))))).
:- add_test(exists0a, (all([[Human,tHuman]],~exists([[CommonSense,tCommonSense]],hasCommonSense(Human,CommonSense)&controls(Human,CommonSense))))).

:- add_test(most2a, (all([[Human,tHuman]],atmost(2,[[M2Kidney,tKidney]],hasKidney(Human,M2Kidney)&controls(Human,M2Kidney))))).
:- add_test(least2a, (all([[Human,tHuman]],atleast(2,[[L2Dream,tDream]],hasDream(Human,L2Dream)&controls(Human,L2Dream))))).
:- add_test(exactly2a, (all([[Human,tHuman]],exactly(2,[[E2ye,tEye]],hasEye(Human,E2ye)&controls(Human,E2ye))))).
:- add_test(exists2a, (all([[Human,tHuman]],exists([[Lung1,tLung],[Lung2,tLung]],hasLung(Human,Lung1)&hasLung(Human,Lung2)&leftOf(Lung1,Lung2)&controls(Human,Lung1)&controls(Human,Lung2))))).


:- add_test(most1a, (all([[Human,tHuman]],atmost(1,[[M1Spouse,tSpouse]],hasSpouse(Human,M1Spouse)&controls(Human,M1Spouse))))).
:- add_test(least1a, (all([[Human,tHuman]],atleast(1,[[LeastIdea,tIdea]],hasIdea(Human,LeastIdea)&controls(Human,LeastIdea))))).
:- add_test(exactly1a, (all([[Human,tHuman]],exactly(1,[[Heart,tHeart]],hasHeart(Human,Heart)&controls(Human,Heart))))).
:- add_test(exists1a, (all([[Human,tHuman]],exists([[SomeClue,tClue]],hasClue(Human,SomeClue)&controls(Human,SomeClue))))).




:- cls.

rats:- forall(is_test(Test),call(Test)).

end_of_file.


:- mpred_test(\+ tHeart(_)).
:- mpred_test(\+ hasOrgan(iBob,_)).


:- 
 ain(hasOrgan(iBob,iBobsHeart)).
:- 
 ain(tHeart(iBobsHeart)).





% You''ve proved Animal does not exist when:
% 1) you dont need skolems and
%    1a) no hearts exists or
%    1b) Human has no organs
% 2) when you need skolems and 
%    2a) no skolem hearts exist or
%    2b) no skolem organs for Human 
prove_not_isa(Human, tHuman) :-
        (   prove_not_need(skIsHeartInArg2ofHasorgan_1FnSk(Human)),
            (   prove_not_isa(Heart, tHeart)
            ;   prove_not_holds_t(hasOrgan, Human, Heart)
            )
        ;   prove_need(skIsHeartInArg2ofHasorgan_1FnSk(Human)),
            (   prove_not_isa(skIsHeartInArg2ofHasorgan_1FnSk(Human), tHeart)
            ;   prove_not_holds_t(hasOrgan,
                                  Human,
                                  skIsHeartInArg2ofHasorgan_1FnSk(Human))
            )
        ).

% Good:
% You need skolems for Human when no hearte exist for anyone
%  or that human has no organs
% plus confirm this is indeed a human
prove_need(skIsHeartInArg2ofHasorgan_1FnSk(Human)) :-
        (   prove_not_isa(Heart, tHeart)
        ;   prove_not_holds_t(hasOrgan, Human, Heart)
        ),
        prove_isa(Human, tHuman).

% This is broken:  Everything is a heart of you dont need skolems and you have and what you dont need a skolems for was human
prove_isa(Heart, tHeart) :-
        prove_not_need(skIsHeartInArg2ofHasorgan_1FnSk(Human)),
        prove_isa(Human, tHuman).

% This is broken:  Everything is an orgam of you dont need skolems and you have and what you dont need a skolems for was human
prove_holds_t(hasOrgan, Human, Heart) :-
        prove_not_need(skIsHeartInArg2ofHasorgan_1FnSk(Human)),
        prove_isa(Human, tHuman).

% This is broken:
prove_not_need(skIsHeartInArg2ofHasorgan_1FnSk(Human)) :-
        (   prove_not_isa(skIsHeartInArg2ofHasorgan_1FnSk(Human), tHeart)
        ;   prove_not_holds_t(hasOrgan,
                              Human,
                              skIsHeartInArg2ofHasorgan_1FnSk(Human))
        ),
        prove_isa(Human, tHuman).

% Good:
prove_isa(skIsHeartInArg2ofHasorgan_1FnSk(Human), tHeart) :-
        prove_need(skIsHeartInArg2ofHasorgan_1FnSk(Human)),
        prove_isa(Human, tHuman).
prove_holds_t(hasOrgan, Human, skIsHeartInArg2ofHasorgan_1FnSk(Human)) :-
        prove_need(skIsHeartInArg2ofHasorgan_1FnSk(Human)),
        prove_isa(Human, tHuman).


end_of_file.

the other year.. i was creating a helpsystem for a commandline util for playing as a robot in secondlife.. 
so human controlled commands had crazy help system .. i had written this in C#
what i was going to say about why cyc ended up the way it did was jus tthe concxept that you know there can be  many cfg for english out there and temproary onces


