
:- if( exists_source(library(logicmoo_clif)) -> true ;
 ((dynamic(user:file_search_path/2),multifile(user:file_search_path/2),
  absolute_file_name('../../prolog',Dir),asserta(user:file_search_path(library,Dir))))).
:- endif.

% runtype: default = pfc
:- if(current_prolog_flag(runtime_testing_module,_)->true;
  set_prolog_flag(runtime_testing_module,test_header)).
:- endif.

:- if(( \+ current_prolog_flag(test_header,_),set_prolog_flag(test_header,loaded))).




:- if((prolog_load_context(module,user), \+ current_module(pfc_lib))).
:- module(header_sane,[test_header_include/0]).

:- assert(test_header_include).

:- endif.


:- set_prolog_flag(nonet,true).
:- set_prolog_flag(run_network,false).
:- set_prolog_flag(load_network,false).



%:- set_prolog_flag(runtime_speed,0). % 0 = dont care
:- set_prolog_flag(runtime_speed, 0). % 1 = default
:- set_prolog_flag(runtime_debug, 3). % 2 = important but dont sacrifice other features for it
:- set_prolog_flag(runtime_safety, 3).  % 3 = very important
:- set_prolog_flag(unsafe_speedups, false).

:- endif.


subtest_assert(I) :- kif_assert(I).


dbanner:- nl,nl,dmsg('%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%'),nl,nl.

test_assert(A):-
  nop(kif_assert(A)),
  test_boxlog(A),
  nop(forall(subtest(T),do_subtest(T))).


do_subtest(List):- must_maplist(call,List).

add_test(Name,Assert):-
  b_implode_varnames(Name+Assert),
  assert(is_test(Name)),
   dbanner,dmsg(test_boxlog(Name)),dbanner,
  test_boxlog(Assert),
   dbanner,dmsg(completed_test_boxlog(Name)),dbanner,
   assert(( Name:- mmake, dbanner,dmsg(running_test(Name)),dbanner,
      test_assert(Assert),
      dbanner,dmsg(completed_running_test(Name)),dbanner)).


:- '$current_source_module'(W), '$set_typein_module'(W).



:- set_prolog_flag(debug, true).
:- set_prolog_flag(retry_undefined,false).
:- set_prolog_flag(gc, false).


:- use_module(library(prolog_stack)).


:-
 op(1199,fx,('==>')), 
 op(1190,xfx,('::::')),
 op(1180,xfx,('==>')),
 op(1170,xfx,'<==>'),  
 op(1160,xfx,('<-')),
 op(1150,xfx,'=>'),
 op(1140,xfx,'<='),
 op(1130,xfx,'<=>'), 
 op(600,yfx,'&'), 
 op(600,yfx,'v'),
 op(350,xfx,'xor'),
 op(300,fx,'~'),
 op(300,fx,'-').


fav_debug:- 
 '$set_source_module'(header_sane),
 set_prolog_flag(access_level,system),
 set_prolog_flag(report_error,true),
 set_prolog_flag(backtrace_show_lines, true),
 set_prolog_flag(backtrace, true),
 set_prolog_flag(debug_on_error,true),
 set_prolog_flag(debug,true),
 set_prolog_flag(backtrace_goal_depth, 2000),
 set_prolog_flag(debugger_show_context,true),
 % set_prolog_flag(gc,false),
 set_prolog_flag(debugger_write_options,[quoted(true), portray(true), max_depth(300), attributes(write)]).


bt:-
  prolog_stack:get_prolog_backtrace_lc(8000, Stack, [goal_depth(300)]),
  print_prolog_backtrace(user_output, Stack).

:- fav_debug.



show_test(G):- defaultAssertMt(KB),must(show_call(KB:G)).
show_call_test(G):- defaultAssertMt(KB),must(show_call(KB:G)).


%= define the example language
% :- fully_expand_real(change(assert,ain),(example_known_is_success(_30487686):-_30487686),O),writeln(O).
example_known_is_success(G):-  G.
example_impossible_is_success(G):-  ~(G).
example_known_is_failure(G):-  \+ G.
example_impossible_is_failure(G):- \+  ~(G).

%= define the four truth values
example_proven_true(G):- example_known_is_success(G),example_impossible_is_failure(G).
example_proven_false(G):- example_impossible_is_success(G),example_known_is_failure(G).
example_inconsistent(G):- example_known_is_success(G),example_impossible_is_success(G).
example_unknown(G):- example_known_is_failure(G),example_impossible_is_failure(G).
  
% :-multifile lmconf:shared_hide_data/1.
%= lmconf:shared_hide_data(hideMeta):-is_main_thread.
%= lmconf:shared_hide_data(hideTriggers):-is_main_thread.

% = clear the screen
% :- shell(cls).

%= save compiled clauses using forward chaining storage (by default)
%= we are using forward chaining just so any logical errors, performance and program bugs manefest
%= immediately
% :- set_clause_compile(fwc).

:- fixup_exports.
:- set_prolog_flag(retry_undefined,true).


:- set_prolog_IO(user_input,user_output,user_output).


:- multifile prolog:message//1, user:message_hook/3.
% user:message_hook(import_private(pfc_lib,_:_/_),warning,_):- source_location(_,_),!.
user:message_hook(io_warning(_,'Illegal UTF-8 start'),warning,_):- source_location(_,_),!.
user:message_hook(T,Type,Warn):- source_location(_,_), current_predicate(maybe_message_hook/3),
  memberchk(Type,[error,warning]),once(maybe_message_hook(T,Type,Warn)),fail.


:- if(( \+ current_module(pfc_lib) )).
:- use_module(library(pfc)).

% :- dynamic(ttExpressionType/1).
:- kb_global(baseKB:ttExpressionType/1).

:- set_prolog_flag(runtime_debug, 0). 
%:- use_module(library(logicmoo_user)).
% logicmoo_clif should maybe load from logicmoo_user
:- use_module(library(logicmoo_clif)).
:- set_prolog_flag(runtime_debug, 3). 
:- endif.

:- prolog_load_context(source,File),((atom_contains(File,'.pfc');atom_contains(File,'.clif'))-> sanity(is_pfc_file) ; must_not_be_pfc_file).

:- if(is_pfc_file).

:- mpred_trace_exec.

:- else.

:- mpred_trace_exec.

:- endif.

:- sanity((defaultAssertMt(Mt1),fileAssertMt(Mt2),source_module(Mt3),Mt1==Mt2,Mt1==Mt3)).

:-assert(t_l:each_file_term(must_kif_process_after_rename)).

:- if((prolog_load_context(source,File),(atom_contains(File,'.clif')))).


% install_constant_renamer_until_eof:-  
  %call_on_eof(show_missing_renames), 
%  set_prolog_flag_until_eof(do_renames,term_expansion).

:- set_prolog_flag(runtime_debug, 0). 
:- use_module(library(logicmoo_clif)).
:- set_prolog_flag(runtime_debug, 3). 

:- set_prolog_flag(do_renames,term_expansion).
:- ((prolog_load_context(source,File), atom_contains(File,'.clif')) ->
   (current_stream(File, read, Stream),with_lisp_translation(Stream,must_kif_process_after_rename)); true).

%:- call(call,((asserta(((system:goal_expansion(Here,Loc,_,_):- dmsg(s_goal_expansion(Here,Loc)),trace,fail))),
%   asserta(((system:term_expansion(Here,Loc,_,_):- dmsg(s_term_expansion(Here,Loc)),trace,fail)))))).

:- else.

:- endif.

