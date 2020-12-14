%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% modellprovning.pl
% Laboration 3, DD1351, KTH
%
% Program checks if given proof, in Computation Tree Logic, is valid or not. 
% CTL rules were given in the task description for the programmer to implement.
%
% Computation Tree Logic: https://en.wikipedia.org/wiki/Computation_tree_logic
%
% check(V, L, S, U, F)
% V - The Ls in form of adjacency lists (Verticies)
% L - The labeling
% S - Current state
% U - Currently recorded states
% F - CTL Formula to check.
%
% Tom Axberg
% taxberg@kth.se
% 2020-12-14
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Reads input
verify(Input) :-
        see(Input), 
        read(V), read(L), read(S), read(F), 
        seen, 
        check(V, L, S, [], F), !.

% And
check(V, L, S, [], and(F,G)) :- 
        check(V, L, S, [], F),
        check(V, L, S, [], G).

% Or
check(V, L, S, [], or(F,G)) :- 
        check(V, L, S, [], F);
        check(V, L, S, [], G).

% Imp
check(V, L, S, [], imp(F,G)) :- 
        \+check(V, L, S, [], F);
        check(V, L, S, [], G).

% AX
check(V, L, S, [], ax(F)) :-
        member([S, Ls], V),
        check_all_states(V, L, Ls, [], F).

% EX
check(V, L, S, [], ex(F)) :-
        member([S, Ls], V),
        check_exist_state(V, L, Ls, [], F).

% AG1, S is in U
check(_, _, S, U, ag(_)) :-
        member(S, U).

% AG2, S is NOT in U
check(V, L, S, U, ag(F)) :-
        \+ member(S, U),
        check(V, L, S, [], F),
        member([S, Ls], V),
        check_all_states(V, L, Ls, [S|U], ag(F)).

% EG1
check(_, _, S, U, eg(_)) :-
        member(S, U).

% EG2
check(V, L, S, U, eg(F)) :- 
        \+ member(S, U),
        check(V, L, S, [], F),
        member([S, Ls], V),
        check_exist_state(V, L, Ls, [S|U], eg(F)).

% % EF1
check(V, L, S, U, ef(F)) :- 
        \+ member(S, U),
        check(V, L, S, [], F).

% EF2
check(V, L, S, U, ef(F)) :- 
        \+ member(S, U),
        member([S, Ls], V),
        check_exist_state(V, L, Ls, [S|U], ef(F)).

% AF1
check(V, L, S, U, af(F)) :-
        \+ member(S, U),
        check(V, L, S, [], F).

% AF2
check(V, L, S, U, af(F)) :- 
        \+ member(S, U),
        member([S, Ls], V),
        check_all_states(V, L, Ls, [S|U], af(F)).

%% Literals
% p
check(_, L, S, [], X) :- 
        member([S, Ls], L),
        member(X, Ls).

% neg p
check(_, L, S, [], neg(X)) :-
        member([S, Ls], L),
        \+member(X, Ls).


%% check_all_states calls check witch all states in in first argument.
% Fact
check_all_states(_, _, [], _, _).

% Handles cases when U is not empty.
check_all_states(V, L, [H|T], U, X) :-
        check(V, L, H, U, X),
        check_all_states(V, L, T, [H|U], X).

% Handles cases when U is empty.
check_all_states(V, L, [H|T], [], X) :-
        check(V, L, H, [], X),
        check_all_states(V, L, T, [], X).

%% check_exist_state gives true if one call to check gives true.
% Fact
check_exist_state(_, _, [], _, _) :- fail.

% Handles cases when U is not empty.
check_exist_state(V, L, [H|T], U, X) :-
        check(V, L, H, U, X);
        check_exist_state(V, L, T, [H|U], X).
        
% Handles cases when U is empty.
check_exist_state(V, L, [H|T], [], X) :-
        check(V, L, H, [], X);
        check_exist_state(V, L, T, [], X).
