:- multifile user:message_hook/3.
:- dynamic user:message_hook/3.
:- dynamic pdt_startup_error_message/1.
:- dynamic collect_pdt_startup_error_messages/0.
collect_pdt_startup_error_messages.
user:message_hook(_,Level,Lines):-
    collect_pdt_startup_error_messages,
    (Level == error; Level == warning),
    prolog_load_context(term_position, T),
    (   T = '$stream_position'(_,Line,_,_,_)
    ->  true
    ;   T = '$stream_position'(_,Line,_,_)
    ),
    prolog_load_context(source, File),
    with_output_to(atom(Msg0), (current_output(O), print_message_lines(O, '', Lines))),
    format(atom(Msg), 'Location: ~w:~w~nMessage: ~w', [File, Line, Msg0]),
    assertz(pdt_startup_error_message(Msg)),
    fail.
write_pdt_startup_error_messages_to_file(_File) :-
    retractall(collect_pdt_startup_error_messages),
    \+ pdt_startup_error_message(_),
    !.
write_pdt_startup_error_messages_to_file(File) :-
    open(File, write, Stream),
    forall(pdt_startup_error_message(Msg),format(Stream, '~w~n', [Msg])),
    close(Stream).

:- (current_prolog_flag(xpce_threaded, _) -> set_prolog_flag(xpce_threaded, true) ; true).
%:- (current_prolog_flag(dialect, swi) -> guitracer ; true).
:- (  (current_prolog_flag(dialect, swi), current_prolog_flag(windows, true))  -> win_window_pos([show(false)]) ; true).
:- (current_prolog_flag(windows,_T) -> set_pro(tty_control,false) ; true).
:- ['./consult_server.pl'].

assertz_user_file_search_path(Name,Path):-
   %prolog_load_context(directory,Dir),
   source_location(Dir,_),
   must(absolute_file_name(Path,AbsPath,[access(exist),file_type(directory),relative_to(Dir)])),
   assertz(user:file_search_path(Name,AbsPath)),
   format('~N :-~q.~n',[assertz(user:file_search_path(Name,AbsPath))]),!.

:- assertz_user_file_search_path(pdt_contextview_pl, './org.cs3.pdt.graphicalviews_3.1.2.201603251848/pl').
:- assertz_user_file_search_path(pdt_common_pl, './org.cs3.pdt.common_3.1.2.201603251848/pl').
:- assertz_user_file_search_path(pdt_prolog_library, './org.cs3.prolog.library_3.1.2.201603251848/pl').
:- assertz_user_file_search_path(pdt_builder_analyzer, './org.cs3.pdt.builder_3.1.2.201603251848/prolog-src/analyzer').
:- assertz_user_file_search_path(lib_pdt_console_pl, './org.cs3.pdt.console_3.1.2.201603251848/pl').
:- assertz_user_file_search_path(prolog_connector_pl, './org.cs3.pdt.connector_3.1.2.201603251848/pl').
:- assertz_user_file_search_path(pdt_pl, './org.cs3.pdt.editor_3.1.2.201603251848/pl').

:- [prolog_connector_pl(load)].
:- [pdt_common_pl(load)].
:- [pdt_contextview_pl(load)].
:- [pdt_prolog_library('_load.pl')].
:- [pdt_pl(load)].
:- [lib_pdt_console_pl(loader)].
:- ['./org.cs3.pdt.analysis_3.1.2.201603251848/pl/load.pl'].
:- if(\+ thread_property(_,alias('consult_server@35421'))).
:- must(consult_server(35421,'/tmp/fp_1522012126371_0.8230701758113668')).
:- endif.
:- must(write_pdt_startup_error_messages_to_file('/tmp/fp_1522012126371_0.6983157812319148')).
