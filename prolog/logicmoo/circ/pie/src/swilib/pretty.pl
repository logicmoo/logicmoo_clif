/*
* Copyright (C) 2002, 2003, 2016 Christoph Wernhard
* 
* This program is free software; you can redistribute it and/or modify it
* under the terms of the GNU General Public License as published by the Free
* Software Foundation; either version 2 of the License, or (at your option)
* any later version.
* 
* This program is distributed in the hope that it will be useful, but WITHOUT
* ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
* FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public License for
* more details.
* 
* You should have received a copy of the GNU General Public License along with
* this program; if not, write to the Free Software Foundation, Inc., 59 Temple
* Place, Suite 330, Boston, MA 02111-1307 USA
*/

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- module(pretty, 
   	[ pp/1, pp/2, pp/3, pp_clause/1, pp_clause/2,
	  set_pp_width/1
 	]).

:- module_transparent pp/1.
:- module_transparent pp/2.
:- module_transparent pp/3.
:- module_transparent pp_clause/1.
:- module_transparent pp_clause/2.

:- use_module(term_handling).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- flag(pp_width, _, 74).
:- flag(op_module, _, user).
	
pp_width(X) :-
	flag(pp_width, X, X).

set_pp_width(N) :-
	flag(pp_width, _, N).

pp_clause(C) :-
	context_module(Module),
	pp_clause_m(C, [], Module).

pp_clause(C, VariableNames) :-
	context_module(Module),
	pp_clause_m(C, VariableNames, Module).

pp_clause_m((H :- B), VariableNames, Module) :-
        !,
	flag(op_module, _, Module),
	copy_term(H-B-VariableNames, H1-B1-VariableNames1),
	std_term_variables(H1-B1, Vs),
	( namevars(Vs, VariableNames1) ->
	  true  
	; numbervars(H1-B1, 0, _)
	),
	pp1(H1, 0, none, 0, 1200, none, none),
	write(' :- '),
	nl,
	pp_body(B1).
pp_clause_m(H, VariableNames, Module) :-
	flag(op_module, _, Module),
	copy_term(H-VariableNames, H1-VariableNames1),
	std_term_variables(H1, Vs),
	( namevars(Vs, VariableNames1) ->
	  true  
	; numbervars(H1, 0, _)
	),
	pp1(H1, 0, none, 0, 1200, none, none),
	write('.'),
	nl.

pp_body((L, Ls)) :-
	!,
	pp1(L, 8, ',', 2, 1000, xfy, l),
	write(','),
	nl,
	pp_body(Ls).
pp_body(L) :-
	pp1(L, 8, ',', 2, 1000, xfy, r),
	write('.'),
	nl.

pp(X) :-
	context_module(Module),
	flag(op_module, _, Module),
	copy_term(X, X1),
	numbervars(X1, 0, _),
	pp1(X1, 0, none, 0, 1200, none, none),
	!. % blue cut

%%%% 
%%%% pp/2, pp/3 generates vars _V<NUM> for variables not in
%%%% VariableNames. So these should not be used as input.
%%%% 
pp(X, VariableNames) :-
	context_module(Module),
	pp_m(X, VariableNames, 0, Module).

pp(X, VariableNames, Indent) :-
	context_module(Module),
	pp_m(X, VariableNames, Indent, Module).

pp_m(X, VariableNames, Indent, Module) :-
	flag(op_module, _, Module),
	copy_term(X-VariableNames, X1-VariableNames1),
	std_term_variables(X1, Vs),
	( namevars(Vs, VariableNames1) -> 
	  true
	; numbervars(X1, 0, _)
	),
	pp1(X1, Indent, none, 1200, 0, none, none),
	!. % blue cut
	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

gen_anonymous_var_name(VarName) :-
	gensym('_V', VarName).

namevars([V|Vs], VariableNames) :-
	( member(Name=V1, VariableNames),
	  V == V1 ->
	  true
	; fail
	),
	V = '$N'(Name),
	namevars(Vs, VariableNames).
namevars([], _).

:- assert((user:portray('$N'(X)) :- write(X))).
%
% use a short functor, since it counts when the print_length is
% approximated using term_to_atom.

writeq1(X) :-
	flag(op_module, Module, Module),
	( prolog_flag(dialect, yap) ->
	  Options = [ quoted(true), 
		      numbervars(true),
		      portray(true) ]
	; Options = [ quoted(true), 
		      character_escapes(true),
		      numbervars(true),
		      spacing(next_argument),
		      %% in swi 8.02 this seems to print too many spaces in
		      %% some situations: e.g. "a(b, (e;f))"
		      portray(true),
		      module(Module) ]
	),
	write_term(X, Options).

current_op1(A,B,C) :-
	flag(op_module, Module, Module),
	current_op(A,B,Module:C).

writeq_op(',') :-
	!,
	flag(op_module, Module, Module),
	write_term(',', [ module(Module) ]).
writeq_op(X) :-
	writeq1(X).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


fits_in_line(Term, Indent) :-
	pp_width(W),
	print_length(Term, L),
	L1 is Indent + L,
	L1 =< W,
	!.

print_length(Term, L) :-
	with_output_to(atom(A), writeq1(Term)),
	atom_length(A, L1),
	v_subterm(Term, 0, N),
	L is max(0, L1-N*8).

v_subterm(X, N, N) :-
	var(X),
	!.
v_subterm('$N'(_), N, N1) :-
	!,
	N1 is N+1.
v_subterm(X, N, N) :-
	atomic(X),
	!.
v_subterm(X, N, N1) :-
	X =.. [_|Args],
	map_v_subterm(Args, N, N1).

map_v_subterm([], N, N).
map_v_subterm([X|Xs], N, N1) :-
	v_subterm(X, N, N2),
	map_v_subterm(Xs, N2, N1).





indent(N) :-
	output_position(LPos),
	( N > LPos ->
	  I1 is N - LPos,
	  spaces(I1)
	; true
	).

output_position(Pos) :-
	current_output(Out),
	line_position(Out, Pos).
%
% $stream_position' seems to have changed in newer versions of SWI,
% was there a problem with line_position in older versions?
% stream_property(Out, position('$stream_position'(_, _, Pos))).
%

spaces(N) :-
	N > 0,
	!,
	write(' '),
	N1 is N - 1,
	spaces(N1).
spaces(_).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


pp1(X, Ind, DOp, DN, DPri, DAss, DPart) :-
	X \= [_|_],
	compound(X),
	functor(X, Op, N),
	N=2, current_op1(Pri, Ass, Op), (Ass=xfx;Ass=xfy;Ass=yfx),
	!,
	indent(Ind),
	( bracket_needed(DOp, DN, DPri, DAss, DPart, Op, N, Pri) ->
	  write(' ('),
	  Ind1 is Ind+2
	; Ind1 = Ind
	),
	arg(1, X, Left),
	pp1(Left, Ind1, Op, N, Pri, Ass, x),
	( Op=',' ->
	  true
	; write(' ')
	),
	arg(2, X, Right),
	writeq_op(Op),
	output_position(OPos),
	( fits_in_line(Right, OPos) ->
	  write(' ')
        ; nl
        ),
	pp1(Right, Ind1, Op, N, Pri, Ass, y),
	( bracket_needed(DOp, DN, DPri, DAss, DPart, Op, N, Pri) ->
	  write(')')
	; true
	).
pp1(X, Ind, _, _, DPri, DAss, _) :-
	fits_in_line(X, Ind),
	!,
	indent(Ind),
	( compound(X),
	  functor(X, Op, 1),
	  current_op1(Pri, _, Op),
	  ( Pri > DPri ; Pri = DPri, DAss = fy ) ->
	  write('('), writeq1(X), write(')')
	; compound(X),
	  functor(X, Op, 2),
	  current_op1(Pri, _, Op),
	  ( Pri > DPri ; Pri = DPri, DAss = xfy ) ->
	  write('('), writeq1(X), write(')')
	; writeq1(X)
	).
pp1([X|Xs], Ind, _, _, _, _, _) :-
	!,
	indent(Ind),
	write('['),
	Ind1 is Ind+1,
	current_op1(Pri, xfy, ','),
	pp1(X, Ind1, ',', 2, Pri, xfy, x),
        pp1_seq(Xs, Ind1, ',', Pri),
        write(']').
pp1(X, Ind, DOp, DN, DPri, DAss, DPart) :-
	compound(X),
	functor(X, Op, N),
	N=1, current_op1(Pri, Ass, Op), (Ass=fx;Ass=fy),
	!,
	indent(Ind),
	( bracket_needed(DOp, DN, DPri, DAss, DPart, Op, N, Pri) ->
	  write('('),
	  Ind1 is Ind+1
	; Ind1 = Ind
	),
	writeq_op(Op),
	arg(1, X, Left),
	pp1(Left, Ind1, Op, N, Pri, Ass, nil),
	( bracket_needed(DOp, DN, DPri, DAss, DPart, Op, N, Pri) ->
	  write(')')
	; true
	).
pp1('$VAR'(X), Ind, _, _, _, _, _) :-
	!,
	indent(Ind),
	writeq1('$VAR'(X)).
pp1('$N'(X), Ind, _, _, _, _, _) :-
	!,
	indent(Ind),
	writeq1('$N'(X)).
pp1(X, Ind, _, _, _, _, _) :-
	compound(X),
	functor(X, F, N),
	N > 0,
	!,
	X =.. [F,X1|Xs],
	indent(Ind),
	writeq1(F),
	write('('),
        print_length(F, IndF),
	Ind1 is Ind + IndF + 1,
	current_op1(Pri, xfy, ','),
	pp1(X1, Ind1, ',', 2, Pri, xfy, x),
        pp1_seq(Xs, Ind1, ',', Pri),
        write(')').
pp1(X, Ind, _, _, _, _, _) :-
	atomic(X),
	!,
	indent(Ind),
	writeq1(X).


pp1_seq([X|Xs], Ind, Op, Pri) :-
	!,
	write(','),
	nl,
	pp1(X, Ind, Op, 2, Pri, xfy, x),
	pp1_seq(Xs, Ind, Op, Pri).
pp1_seq([], _, _, _) :-
	!.
pp1_seq(X, Ind, Op, Pri) :- % a non-nil cdr
	write('|'),
	nl,
	pp1(X, Ind, Op, 2, Pri, xfy, x).


bracket_needed(DOp, DN, DPri, DAss, DPart, Op, N, Pri) :-
	( DOp=Op, DN=N ->
	  ( DAss=xfy, DPart==x -> true
	  ; DAss=yfx, DPart==y -> true
	  ; DAss=xfx -> true
	  )
	; Pri >= DPri 
	).




	

