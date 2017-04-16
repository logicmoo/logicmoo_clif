:- module(common_logic_loader,
	  [load_clif/1,
           kif_process/1,
           kif_io/2,          
           kif_process/2,
           kif_read/3]).
/** <module> common_logic_loader
% Provides interface for loading/interpretation of CLIF/KIF Files
%
%  t/N
%  hybridRule/2
%  
%
% Logicmoo Project PrologMUD: A MUD server written in Prolog
% Maintainer: Douglas Miles
% Dec 13, 2035
%
*/

:- meta_predicate
   % common_logic_snark
   kif_process(*,*),
   % common_logic_snark
   kif_process(*).
   % common_logic_snark


:- thread_local(t_l:kif_action_mode/1).
:- asserta_if_new(t_l:kif_action_mode(tell)).

:- thread_local(t_l:kif_reader_mode/1).
:- asserta_if_new(t_l:kif_reader_mode(lisp)).

:- public(kif_io/0).
%% kif_io is det.
%
% Knowledge Interchange Format.
%
kif_io:- current_input(In),current_output(Out),!,kif_io(In,Out).


load_clif(File):- 
  with_lisp_translation(File, kif_process).

:- public(kif_process/1).



%% kif_process( :GoalAssert) is det.
%
% Knowledge Interchange Format Process.
%
kif_process(Var):- is_ftVar(Var),!,wdmsg(warn(var_kif_process(Var))).
% kif_process(Assert):- atom(Assert),set_kif_mode(Assert).
kif_process(List):- is_list(List),must(sexpr_sterm_to_pterm(List,Wff)),!,
   t_l:kif_action_mode(Mode),show_success(kif_process(Mode,Wff)),!.
kif_process(Wff):- t_l:kif_action_mode(Mode),show_success(kif_process(Mode,Wff)),!.

set_kif_mode(Assert):- must_be(atom,Assert),
  retractall(t_l:kif_action_mode(_)),asserta(t_l:kif_action_mode(Assert)),
  fmtl(t_l:kif_action_mode(Assert)),!.


%% kif_process( ?Other, :GoalWff) is det.
%
% Knowledge Interchange Format Process.
%
kif_process(_,Var):- must_be(nonvar,Var),fail.
kif_process(_,end_of_file):- !.
kif_process(_,prolog):- prolog,!.
kif_process(_,Atom):- atom(Atom),current_predicate(Atom/0),!,call(Atom).
kif_process(_,Atom):- atom(Atom),current_predicate(Atom/1),!,set_kif_mode(Atom).
kif_process(_,'kif-mode'(Assert)):- set_kif_mode(Assert).
kif_process(_,'kif_mode'(Assert)):- set_kif_mode(Assert).
kif_process(_,':-'(Wff)):- !, kif_process(call,Wff).
kif_process(_,'?-'(Wff)):- !, kif_ask(Wff).
kif_process(_,'ask'(Wff)):- !, kif_ask(Wff).
kif_process(_,'tell'(Wff)):- !, kif_add(Wff).
kif_process(call,Call):- !,call(Call).
kif_process(tell,Wff):- is_static_predicate(Wff), !, call(Wff).
kif_process(tell,Wff):- !, kif_add(Wff).
kif_process(ask,Wff):- !, kif_ask(Wff).
kif_process(Other,Wff):- !, wdmsg(error(missing_kif_process(Other,Wff))),!,fail.


%open_input(InS,InS):- is_stream(InS),!.
%open_input(string(InS),In):- text_to_string(InS,Str),string_codes(Str,Codes),open_chars_stream(Codes,In),!.


%% kif_read( ?InS, ?Wff, ?Vs) is det.
%
% Knowledge Interchange Format Read.
%
kif_read(In,Wff,Vs):- !, input_to_forms(In,Wff,Vs).
kif_read(In,Wff,Vs):- 
  (t_l:kif_reader_mode(lisp) ->
  without_must( catch(input_to_forms(In,Wff,Vs),E,(dmsg(E:kif_read_input_to_forms(In,Wff,Vs)),fail)))*-> true ;
      (catch(read_term(In,Wff,[module(user),double_quotes(string),variable_names(Vs)]),E,
                 (dmsg(E:kif_read_term_to_forms(In,Wff,Vs)),fail)))).

%= ===== to test program =====-
% :- ensure_loaded(logicmoo(snark/common_logic_sexpr)).

:- public(kif_io/2).
:- assert_until_eof(t_l:canonicalize_types).



%% kif_io( ?InS, ?Out) is det.
%
% Knowledge Interchange Format Input/output.
%
kif_io(In,Out):-
   repeat,
      on_x_debug((
          once((t_l:kif_action_mode(Mode),write(Out,Mode),write(Out,'> '))),
          once(on_x_debug(kif_read(In,Wff,Vs))),
          once(on_x_debug((put_variable_names( Vs), portray_clause(Out,Wff,[variable_names(Vs),quoted(true)])))),
          on_x_debug(kif_process(Wff)),
           Wff == end_of_file)),!.


:- assert_until_eof(t_l:canonicalize_types).


:- fixup_exports.

