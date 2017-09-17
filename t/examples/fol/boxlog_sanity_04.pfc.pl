

:- module(kbii,[]).

:- include(test_header).

:- set_prolog_flag(retry_undefined,false).

:- ensure_loaded(library(script_files)).


%:- ensure_abox(kbii).
:- set_fileAssertMt(kbii).


:- process_this_script.


:- set_prolog_flag(os_argv,[swipl, '-f', '/dev/null','--nonet']).


:- cls.      




% ================================================================================================================
% Exactly 1 puppy
% ================================================================================================================


:- test_boxlog(exactly(1, X, puppy(X))).

 /*

proven_neg(puppy(X)) :-
        dif_objs(X, Puppy1),
        tru(puppy(Puppy1)).
proven_neg(different(X, Puppy1)) :-
        tru(puppy(Puppy1)),
        tru(puppy(X)).
proven_tru(puppy(Puppy1)) :-
        skolem(Puppy1, count(1, inf, skF(skIsPuppyExists_0FnSk, vv(KB, Puppy1))), 1).
make_existential(Puppy1, count(1, inf, skF(skIsPuppyExists_0FnSk, vv(KB, Puppy1))), 1) :-
        ensure_cond(Puppy1, puppy(Puppy1)).

*/


% ================================================================================================================
% At most 1 puppy
% ================================================================================================================


:- test_boxlog(atmost(1, X, puppy(X))).

 /*

proven_neg(puppy(X)) :-
        dif_objs(X, Puppy0),
        tru(puppy(Puppy0)).
proven_neg(different(X, Puppy0)) :-
        tru(puppy(X)),
        tru(puppy(Puppy0)).

*/



% ================================================================================================================
% At Least 1 puppy
% ================================================================================================================


:- test_boxlog(atleast(1, X, puppy(X))).

 /* 

proven_tru(puppy(X)) :-
        skolem(X, count(1, inf, skF(skIsPuppyX_0FnSk, vv(KB, X))), 1).
make_existential(X, count(1, inf, skF(skIsPuppyX_0FnSk, vv(KB, X))), 1) :-
        ensure_cond(X, puppy(X)).

*/



% ================================================================================================================
% Exactly 5 puppies
% ================================================================================================================


:- test_boxlog(exactly(5, X, puppy(X))).

 /*

proven_neg(puppy(Puppy1)) :-
        tru(puppy(Puppy2)),
        dif_objs(Puppy1, Puppy2),
        tru(puppy(Puppy3)),
        dif_objs(Puppy1, Puppy3),
        tru(puppy(Puppy4)),
        dif_objs(Puppy1, Puppy4),
        tru(puppy(Puppy5)),
        dif_objs(Puppy1, Puppy5),
        dif_objs(Puppy1, Puppy6),
        tru(puppy(Puppy6)).
proven_neg(different(Puppy1, Puppy6)) :-
        tru(puppy(Puppy6)),
        tru(puppy(Puppy5)),
        dif_objs(Puppy1, Puppy5),
        tru(puppy(Puppy4)),
        dif_objs(Puppy1, Puppy4),
        tru(puppy(Puppy1)),
        tru(puppy(Puppy2)),
        dif_objs(Puppy1, Puppy2),
        dif_objs(Puppy1, Puppy3),
        tru(puppy(Puppy3)).
proven_tru(puppy(X)) :-
        skolem(X, count(5, inf, skF(skIsPuppyX_0FnSk, vv(KB, X))), _38364906).
make_existential(X, count(5, inf, skF(skIsPuppyX_0FnSk, vv(KB, X))), _38364906) :-
        ensure_cond(X, puppy(X)).

*/


% ================================================================================================================
% At most 5 puppies
% ================================================================================================================


:- test_boxlog(atmost(5, X, puppy(X))).

 /*

proven_neg(puppy(X)) :-
        tru(puppy(Puppy0)),
        dif_objs(X, Puppy0),
        tru(puppy(Puppy1)),
        dif_objs(X, Puppy1),
        tru(puppy(Puppy2)),
        dif_objs(X, Puppy2),
        tru(puppy(Puppy3)),
        dif_objs(X, Puppy3),
        dif_objs(X, Puppy4),
        tru(puppy(Puppy4)).
proven_neg(different(X, Puppy4)) :-
        tru(puppy(Puppy4)),
        tru(puppy(Puppy3)),
        dif_objs(X, Puppy3),
        tru(puppy(Puppy2)),
        dif_objs(X, Puppy2),
        tru(puppy(X)),
        tru(puppy(Puppy0)),
        dif_objs(X, Puppy0),
        dif_objs(X, Puppy1),
        tru(puppy(Puppy1)).

*/



% ================================================================================================================
% At Least 5 puppies
% ================================================================================================================


:- test_boxlog(atleast(5, X, puppy(X))).

 /*

proven_tru(puppy(X)) :-
        skolem(X, count(5, inf, skF(skIsPuppyX_0FnSk, vv(KB, X))), _39370268).
make_existential(X, count(5, inf, skF(skIsPuppyX_0FnSk, vv(KB, X))), _39370268) :-
        ensure_cond(X, puppy(X)).

*/








% ================================================================================================================
% Exactly 1 cute puppy
% ================================================================================================================


:- test_boxlog(exactly(1, X, puppy(X)&cute(X))).

 /*

proven_neg(cute(X)) :-
        tru(puppy(X)),
        tru(puppy(Puppy1)),
        dif_objs(X, Puppy1),
        tru(cute(Puppy1)).
proven_neg(puppy(X)) :-
        tru(cute(X)),
        tru(puppy(Puppy1)),
        dif_objs(X, Puppy1),
        tru(cute(Puppy1)).
proven_neg(different(X, Puppy1)) :-
        tru(puppy(Puppy1)),
        tru(cute(Puppy1)),
        tru(puppy(X)),
        tru(cute(X)).
proven_tru(cute(Puppy1)) :-
        skolem(Puppy1,
               count(1, inf, skF(skIsCuteIsPuppyExists_0FnSk, vv(KB, Puppy1))),
               1).
proven_tru(puppy(Puppy1)) :-
        skolem(Puppy1,
               count(1, inf, skF(skIsCuteIsPuppyExists_0FnSk, vv(KB, Puppy1))),
               1).
make_existential(Puppy1, count(1, inf, skF(skIsCuteIsPuppyExists_0FnSk, vv(KB, Puppy1))), 1) :-
        ensure_cond(Puppy1, puppy(Puppy1)),
        ensure_cond(Puppy1, cute(Puppy1)).

*/


% ================================================================================================================
% At most 1 cute puppy
% ================================================================================================================


:- test_boxlog(atmost(1, X, puppy(X)&cute(X))).

 /*

proven_neg(cute(X)) :-
        tru(puppy(X)),
        tru(puppy(Puppy0)),
        dif_objs(X, Puppy0),
        tru(cute(Puppy0)).
proven_neg(puppy(X)) :-
        tru(cute(X)),
        tru(puppy(Puppy0)),
        dif_objs(X, Puppy0),
        tru(cute(Puppy0)).
proven_neg(different(X, Puppy0)) :-
        tru(puppy(X)),
        tru(cute(X)),
        tru(puppy(Puppy0)),
        tru(cute(Puppy0)).

*/



% ================================================================================================================
% At Least 1 cute puppy
% ================================================================================================================


:- test_boxlog(atleast(1, X, puppy(X)&cute(X))).

 /*

proven_tru(cute(X)) :-
        skolem(X, count(1, inf, skF(skIsCuteIsPuppyX_0FnSk, vv(KB, X))), 1).
proven_tru(puppy(X)) :-
        skolem(X, count(1, inf, skF(skIsCuteIsPuppyX_0FnSk, vv(KB, X))), 1).
make_existential(X, count(1, inf, skF(skIsCuteIsPuppyX_0FnSk, vv(KB, X))), 1) :-
        ensure_cond(X, puppy(X)),
        ensure_cond(X, cute(X)).

*/




% ================================================================================================================
% Exactly 5 cute puppies
% ================================================================================================================


:- test_boxlog(exactly(5, X, puppy(X)&cute(X))).

 /*

proven_neg(cute(Cute1)) :-
        tru(puppy(Cute1)),
        tru(puppy(Puppy2)),
        tru(cute(Puppy2)),
        dif_objs(Cute1, Puppy2),
        tru(puppy(Puppy3)),
        tru(cute(Puppy3)),
        dif_objs(Cute1, Puppy3),
        tru(puppy(Puppy4)),
        tru(cute(Puppy4)),
        dif_objs(Cute1, Puppy4),
        tru(puppy(Puppy5)),
        tru(cute(Puppy5)),
        dif_objs(Cute1, Puppy5),
        tru(puppy(Puppy6)),
        dif_objs(Cute1, Puppy6),
        tru(cute(Puppy6)).
proven_neg(puppy(Cute1)) :-
        tru(cute(Cute1)),
        tru(puppy(Puppy2)),
        tru(cute(Puppy2)),
        dif_objs(Cute1, Puppy2),
        tru(puppy(Puppy3)),
        tru(cute(Puppy3)),
        dif_objs(Cute1, Puppy3),
        tru(puppy(Puppy4)),
        tru(cute(Puppy4)),
        dif_objs(Cute1, Puppy4),
        tru(puppy(Puppy5)),
        tru(cute(Puppy5)),
        dif_objs(Cute1, Puppy5),
        tru(puppy(Puppy6)),
        dif_objs(Cute1, Puppy6),
        tru(cute(Puppy6)).
proven_neg(different(Cute1, Puppy6)) :-
        tru(puppy(Puppy6)),
        tru(cute(Puppy6)),
        tru(puppy(Puppy5)),
        tru(cute(Puppy5)),
        dif_objs(Cute1, Puppy5),
        tru(puppy(Puppy4)),
        tru(cute(Puppy4)),
        dif_objs(Cute1, Puppy4),
        tru(puppy(Cute1)),
        tru(cute(Cute1)),
        tru(puppy(Puppy2)),
        tru(cute(Puppy2)),
        dif_objs(Cute1, Puppy2),
        tru(puppy(Puppy3)),
        dif_objs(Cute1, Puppy3),
        tru(cute(Puppy3)).
proven_tru(cute(X)) :-
        skolem(X, count(5, inf, skF(skIsCuteIsPuppyX_0FnSk, vv(KB, X))), _WHICH9206).
proven_tru(puppy(X)) :-
        skolem(X, count(5, inf, skF(skIsCuteIsPuppyX_0FnSk, vv(KB, X))), _WHICH9206).
make_existential(X, count(5, inf, skF(skIsCuteIsPuppyX_0FnSk, vv(KB, X))), _WHICH9206) :-
        ensure_cond(X, puppy(X)),
        ensure_cond(X, cute(X)).

*/


% ================================================================================================================
% At most 5 cute puppies
% ================================================================================================================


:- test_boxlog(atmost(5, X, puppy(X)&cute(X))).

 /*

proven_neg(cute(X)) :-
        tru(puppy(X)),
        tru(puppy(Puppy0)),
        tru(cute(Puppy0)),
        dif_objs(X, Puppy0),
        tru(puppy(Puppy1)),
        tru(cute(Puppy1)),
        dif_objs(X, Puppy1),
        tru(puppy(Puppy2)),
        tru(cute(Puppy2)),
        dif_objs(X, Puppy2),
        tru(puppy(Puppy3)),
        tru(cute(Puppy3)),
        dif_objs(X, Puppy3),
        tru(puppy(Puppy4)),
        dif_objs(X, Puppy4),
        tru(cute(Puppy4)).
proven_neg(puppy(X)) :-
        tru(cute(X)),
        tru(puppy(Puppy0)),
        tru(cute(Puppy0)),
        dif_objs(X, Puppy0),
        tru(puppy(Puppy1)),
        tru(cute(Puppy1)),
        dif_objs(X, Puppy1),
        tru(puppy(Puppy2)),
        tru(cute(Puppy2)),
        dif_objs(X, Puppy2),
        tru(puppy(Puppy3)),
        tru(cute(Puppy3)),
        dif_objs(X, Puppy3),
        tru(puppy(Puppy4)),
        dif_objs(X, Puppy4),
        tru(cute(Puppy4)).
proven_neg(different(X, Puppy4)) :-
        tru(puppy(Puppy4)),
        tru(cute(Puppy4)),
        tru(puppy(Puppy3)),
        tru(cute(Puppy3)),
        dif_objs(X, Puppy3),
        tru(puppy(Puppy2)),
        tru(cute(Puppy2)),
        dif_objs(X, Puppy2),
        tru(puppy(X)),
        tru(cute(X)),
        tru(puppy(Puppy0)),
        tru(cute(Puppy0)),
        dif_objs(X, Puppy0),
        tru(puppy(Puppy1)),
        dif_objs(X, Puppy1),
        tru(cute(Puppy1)).

*/



% ================================================================================================================
% At Least 5 cute puppies
% ================================================================================================================


:- test_boxlog(atleast(5, X, puppy(X)&cute(X))).

 /*

proven_tru(cute(X)) :-
        skolem(X, count(5, inf, skF(skIsCuteIsPuppyX_0FnSk, vv(KB, X))), _1014058).
proven_tru(puppy(X)) :-
        skolem(X, count(5, inf, skF(skIsCuteIsPuppyX_0FnSk, vv(KB, X))), _1014058).
make_existential(X, count(5, inf, skF(skIsCuteIsPuppyX_0FnSk, vv(KB, X))), _1014058) :-
        ensure_cond(X, puppy(X)),
        ensure_cond(X, cute(X)).

*/









% ================================================================================================================
% Exactly 1 possibly cute puppy
% ================================================================================================================


:- test_boxlog(exactly(1, X, puppy(X)&poss(cute(X)))).

 /*

proven_neg(cute(X)) :-
        tru(puppy(X)),
        tru(puppy(Puppy1)),
        dif_objs(X, Puppy1),
        tru(cute(Puppy1)).
proven_neg(puppy(X)) :-
        tru(cute(X)),
        tru(puppy(Puppy1)),
        dif_objs(X, Puppy1),
        tru(cute(Puppy1)).
proven_neg(different(X, Puppy1)) :-
        tru(puppy(Puppy1)),
        tru(cute(Puppy1)),
        tru(puppy(X)),
        tru(cute(X)).
proven_poss(cute(Puppy1)) :-
        skolem(Puppy1,
               count(1, inf, skF(skIsCuteIsPuppyExists_0FnSk, vv(KB, Puppy1, KB))),
               1).
proven_tru(puppy(Puppy1)) :-
        skolem(Puppy1,
               count(1, inf, skF(skIsCuteIsPuppyExists_0FnSk, vv(KB, Puppy1, KB))),
               1).
make_existential(Puppy1, count(1, inf, skF(skIsCuteIsPuppyExists_0FnSk, vv(KB, Puppy1, KB))), 1) :-
        ensure_cond(Puppy1, puppy(Puppy1)),
        ensure_cond(Puppy1, cute(Puppy1)).

*/


% ================================================================================================================
% At most 1 possibly cute puppy
% ================================================================================================================


:- test_boxlog(atmost(1, X, puppy(X)&poss(cute(X)))).

 /*

proven_neg(cute(X)) :-
        tru(puppy(X)),
        tru(puppy(Puppy0)),
        dif_objs(X, Puppy0),
        tru(cute(Puppy0)).
proven_neg(puppy(X)) :-
        tru(cute(X)),
        tru(puppy(Puppy0)),
        dif_objs(X, Puppy0),
        tru(cute(Puppy0)).
proven_neg(different(X, Puppy0)) :-
        tru(puppy(X)),
        tru(cute(X)),
        tru(puppy(Puppy0)),
        tru(cute(Puppy0)).

*/



% ================================================================================================================
% At Least 1 possibly cute puppy
% ================================================================================================================


:- test_boxlog(atleast(1, X, puppy(X)&poss(cute(X)))).

 /*

proven_poss(cute(X)) :-
        skolem(X, count(1, inf, skF(skIsCuteIsPuppyX_0FnSk, vv(KB, X, KB))), 1).
proven_tru(puppy(X)) :-
        skolem(X, count(1, inf, skF(skIsCuteIsPuppyX_0FnSk, vv(KB, X, KB))), 1).
make_existential(X, count(1, inf, skF(skIsCuteIsPuppyX_0FnSk, vv(KB, X, KB))), 1) :-
        ensure_cond(X, puppy(X)),
        ensure_cond(X, cute(X)).

*/




% ================================================================================================================
% Exactly 5 possibly cute puppies
% ================================================================================================================


:- test_boxlog(exactly(5, X, puppy(X)&poss(cute(X)))).

 /*

proven_neg(cute(Cute1)) :-
        tru(puppy(Cute1)),
        tru(puppy(Puppy2)),
        tru(cute(Puppy2)),
        dif_objs(Cute1, Puppy2),
        tru(puppy(Puppy3)),
        tru(cute(Puppy3)),
        dif_objs(Cute1, Puppy3),
        tru(puppy(Puppy4)),
        tru(cute(Puppy4)),
        dif_objs(Cute1, Puppy4),
        tru(puppy(Puppy5)),
        tru(cute(Puppy5)),
        dif_objs(Cute1, Puppy5),
        tru(puppy(Puppy6)),
        dif_objs(Cute1, Puppy6),
        tru(cute(Puppy6)).
proven_neg(puppy(Cute1)) :-
        tru(cute(Cute1)),
        tru(puppy(Puppy2)),
        tru(cute(Puppy2)),
        dif_objs(Cute1, Puppy2),
        tru(puppy(Puppy3)),
        tru(cute(Puppy3)),
        dif_objs(Cute1, Puppy3),
        tru(puppy(Puppy4)),
        tru(cute(Puppy4)),
        dif_objs(Cute1, Puppy4),
        tru(puppy(Puppy5)),
        tru(cute(Puppy5)),
        dif_objs(Cute1, Puppy5),
        tru(puppy(Puppy6)),
        dif_objs(Cute1, Puppy6),
        tru(cute(Puppy6)).
proven_neg(different(Cute1, Puppy6)) :-
        tru(puppy(Puppy6)),
        tru(cute(Puppy6)),
        tru(puppy(Puppy5)),
        tru(cute(Puppy5)),
        dif_objs(Cute1, Puppy5),
        tru(puppy(Puppy4)),
        tru(cute(Puppy4)),
        dif_objs(Cute1, Puppy4),
        tru(puppy(Cute1)),
        tru(cute(Cute1)),
        tru(puppy(Puppy2)),
        tru(cute(Puppy2)),
        dif_objs(Cute1, Puppy2),
        tru(puppy(Puppy3)),
        dif_objs(Cute1, Puppy3),
        tru(cute(Puppy3)).
proven_poss(cute(X)) :-
        skolem(X,
               count(5, inf, skF(skIsCuteIsPuppyX_0FnSk, vv(KB, X, KB))),
               _2043876).
proven_tru(puppy(X)) :-
        skolem(X,
               count(5, inf, skF(skIsCuteIsPuppyX_0FnSk, vv(KB, X, KB))),
               _2043876).
make_existential(X, count(5, inf, skF(skIsCuteIsPuppyX_0FnSk, vv(KB, X, KB))), _2043876) :-
        ensure_cond(X, puppy(X)),
        ensure_cond(X, cute(X)).

*/


% ================================================================================================================
% At most 5 possibly cute puppies
% ================================================================================================================


:- test_boxlog(atmost(5, X, puppy(X)&poss(cute(X)))).

 /*

proven_neg(cute(X)) :-
        tru(puppy(X)),
        tru(puppy(Puppy0)),
        tru(cute(Puppy0)),
        dif_objs(X, Puppy0),
        tru(puppy(Puppy1)),
        tru(cute(Puppy1)),
        dif_objs(X, Puppy1),
        tru(puppy(Puppy2)),
        tru(cute(Puppy2)),
        dif_objs(X, Puppy2),
        tru(puppy(Puppy3)),
        tru(cute(Puppy3)),
        dif_objs(X, Puppy3),
        tru(puppy(Puppy4)),
        dif_objs(X, Puppy4),
        tru(cute(Puppy4)).
proven_neg(puppy(X)) :-
        tru(cute(X)),
        tru(puppy(Puppy0)),
        tru(cute(Puppy0)),
        dif_objs(X, Puppy0),
        tru(puppy(Puppy1)),
        tru(cute(Puppy1)),
        dif_objs(X, Puppy1),
        tru(puppy(Puppy2)),
        tru(cute(Puppy2)),
        dif_objs(X, Puppy2),
        tru(puppy(Puppy3)),
        tru(cute(Puppy3)),
        dif_objs(X, Puppy3),
        tru(puppy(Puppy4)),
        dif_objs(X, Puppy4),
        tru(cute(Puppy4)).
proven_neg(different(X, Puppy4)) :-
        tru(puppy(Puppy4)),
        tru(cute(Puppy4)),
        tru(puppy(Puppy3)),
        tru(cute(Puppy3)),
        dif_objs(X, Puppy3),
        tru(puppy(Puppy2)),
        tru(cute(Puppy2)),
        dif_objs(X, Puppy2),
        tru(puppy(X)),
        tru(cute(X)),
        tru(puppy(Puppy0)),
        tru(cute(Puppy0)),
        dif_objs(X, Puppy0),
        tru(puppy(Puppy1)),
        dif_objs(X, Puppy1),
        tru(cute(Puppy1)).
        
*/



% ================================================================================================================
% At Least 5 possibly cute puppies
% ================================================================================================================


:- test_boxlog(atleast(5, X, puppy(X)&poss(cute(X)))).

 /*

proven_poss(cute(X)) :-
        skolem(X,
               count(5, inf, skF(skIsCuteIsPuppyX_0FnSk, vv(KB, X, KB))),
               _4393116).
proven_tru(puppy(X)) :-
        skolem(X,
               count(5, inf, skF(skIsCuteIsPuppyX_0FnSk, vv(KB, X, KB))),
               _4393116).
make_existential(X, count(5, inf, skF(skIsCuteIsPuppyX_0FnSk, vv(KB, X, KB))), _4393116) :-
        ensure_cond(X, puppy(X)),
        ensure_cond(X, cute(X)).


*/
