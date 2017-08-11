
% runtype: default = pfc
:- if(current_prolog_flag(runtime_testing_module,_)->true;
  set_prolog_flag(runtime_testing_module,test_header)).
:- endif.

:- if(( \+ current_prolog_flag(test_header,_),set_prolog_flag(test_header,loaded))).


:- if((prolog_load_context(module,user), \+ current_module(pfc_lib))).
:- module(header_sane,[test_header_include/0]).

test_header_include.

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


:- if(( \+ current_module(pfc_lib) )).
:- use_module(library(pfc)).

:- set_prolog_flag(runtime_debug, 0). 
:- use_module(library(logicmoo_clif)).
:- set_prolog_flag(runtime_debug, 3). 

:- prolog_load_context(source,File),(atom_contains(File,'.pfc')-> sanity(is_pfc_file) ; must_not_be_pfc_file).
:- endif.

:- multifile prolog:message//1, user:message_hook/3.
% user:message_hook(import_private(pfc_lib,_:_/_),warning,_):- source_location(_,_),!.
user:message_hook(io_warning(_,'Illegal UTF-8 start'),warning,_):- source_location(_,_),!.
user:message_hook(T,Type,Warn):- source_location(_,_),
  memberchk(Type,[error,warning]),once(maybe_message_hook(T,Type,Warn)),fail.


:- if(is_pfc_file).

:- mpred_trace_exec.

:- else.

:- mpred_trace_exec.

:- endif.

:- '$current_source_module'(W), '$set_typein_module'(W).



:- set_prolog_flag(debug, true).
:- set_prolog_flag(retry_undefined,true).
:- set_prolog_flag(gc, false).

:- sanity((defaultAssertMt(Mt1),fileAssertMt(Mt2),source_module(Mt3),Mt1==Mt2,Mt1==Mt3)).

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

