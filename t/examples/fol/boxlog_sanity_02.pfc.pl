:- include(test_header).

:- process_this_script.

% Initially Dmiles thought LEM was the culprit, it was not.
% this is a more generalized problem in Nomics


% ==============================================================
% Section 1:  Problem with Nomics
% ==============================================================

% Turn off modal extensions (default was true)
:- set_prolog_flag(logicmoo_modality,false).

% Rule 1: If no cute puppies exist, then Joan will buy a horse
~exists(X,cute_puppy(X)) => buys(joan,horse).

% Rule 2: It is impossible for broke people to buy things
forall([P,A], broke(P)=> ~buys(P,A)).

% Fact A: Joan is a broke person
broke(joan).

% Expose the problem
:- mpred_test(cute_puppy(_)).
 /*

What = skIsCutepuppyExists_0FnSk ;

% Result: True
% Proof1:
%   broke(joan)
%   ~buys(joan,_)
%   exists(X,cute_puppy(X))

'' :-
        proven_not_tru(buys(joan, horse)).
'' :-
        proven_not_tru(cute_puppy(skIsCutepuppyExists_0FnSk)).
cute_puppy(_33699386) :-
        fwc,
        proven_not_tru(cute_puppy(skIsCutepuppyExists_0FnSk)),
        { _33699386=skIsCutepuppyExists_0FnSk
        },
        proven_not_tru(buys(joan, horse)),
        { is_unit(_33699386)
        }.
'' :-
        mfl(header_sane,
            '/home/prologmud_server/lib/swipl/pack/logicmoo_base/t/examples/fol/boxlog_sanity_02.pfc.pl',
            17).
*/


% yet, Joan could not afford a horse, regardless of the existence cute puppies
%
% How could it have been prevented?
%
% Firstly the very first rule could have qualified:
%  "If Joan is not broke,..."
%
% Why did we not?
%
%  Financial solvency was a Nomic property and we didn''t know about money at the time Joan authored the first rule
%
%  If the first rule was compiled int the system could we have tempered the second rule with:
%  "For everyone except joan, ..." ????
%  


% ==============================================================
% Section 2: Exasterbation
% ==============================================================

% Rule 3:  If a cute puppy exists than Paul will buy it
exists(X,cute_puppy(X)) => buys(paul,X).

% A cute puppy was created in Section 1
:- mpred_test(buys(paul,What)).

 /*
'' :-
        cute_puppy(skIsCutepuppyExists_0FnSk).
buys(paul, _33453090) :-
        fwc,
        cute_puppy(_33453090),
        { is_unit(_33453090)
        }.
'' :-
        mfl(header_sane,
            '/home/prologmud_server/lib/swipl/pack/logicmoo_base/t/examples/fol/boxlog_sanity_02.pfc.pl',
            73).
What = skIsCutepuppyExists_0FnSk.
 */


end_of_file.

:- listing(header_sane:_).

% ==============================================================
% Section 3: Decidablity?
% ==============================================================

% Is the existence of cute puppies really even knowable/decidable in an "Open World"?

% Rule 4: Cute puppies exists or not (LEM)
nesc(exists(X,cute_puppy(X)) v ~exists(X,cute_puppy(X))).

% Rule 5: It is nescarilly not true that puppie do and dont exist 
nesc(~(exists(X,cute_puppy(X)) & ~exists(X,cute_puppy(X)))).



% ==============================================================
% Section L: LogicMOO
% ==============================================================
% so forget everything we thought we knew about logic..
%
:- mpred_retractall(header_sanity:_).

% Turn modal extensions back on:
:- set_prolog_flag(logicmoo_modality,true).

% this secretly rewrites:
%
%     P 
%
% into 
%
%  <>P -> []P
%
%

% Rule 1: If no cute puppies exist, then Joan will buy a horse
~exists(X,cute_puppy(X)) => buys(joan,horse).

% so what logicmoo hears internally:
%
%   poss(~exists(X,cute_puppy(X)) => buys(joan,horse)) 
%     =>
%   nesc(~exists(X,cute_puppy(X)) => buys(joan,horse)).
%
%  meaning:  "if this rule is even possible, then this rule is nessarily true."
%


% Rule 2: It is impossible for broke people to buy things, + "but only if it is even possible as a rule"
forall([P,A], broke(P)=> ~buys(P,A)).


% Fact A: Joan is a broke person + "if this fact is even possible"
broke(joan).











