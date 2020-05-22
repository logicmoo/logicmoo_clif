#!/usr/bin/env swipl

:- module(logicmoo_plweb,[]).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- dmsg("Ensure PLWEB").
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- user:['/usr/lib/swi-prolog/library/theme/auto.pl'].

:- multifile(predicate_options:predicate_options/3).
:- dynamic(predicate_options:predicate_options/3).

:- attach_packs('/opt/logicmoo_workspace/packs_web/plweb/packs').

%:- user:['/opt/logicmoo_workspace/packs_web/plweb/plweb.pl'].
%:- plweb:with_mutex(plweb_init, server_init).
:- doc_enable(true).

maybe:- logicmoo_base_port(Base), X is Base+20,
   plweb:server([port(X)]).

                           