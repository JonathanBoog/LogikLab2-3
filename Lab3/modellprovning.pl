% Model checker
%
% Author: Jonathan Lavén & Julius Geiryd
%
% 2024-11-22

% For SICStus, uncomment line below: (needed for member/2)
:- use_module(library(lists)).


% Load model, initial state and formula from file.
verify(Input) :-
    see(Input), read(T), read(L), read(S), read(F), seen,
    check(T, L, S, [], F).



% check(T, L, S, U, F)
% T - The transitions in form of adjacency lists
% L - The labeling
% S - Current state
% U - Currently recorded states
% F - CTL Formula to check.
%
% Should evaluate to true if the sequent below is valid.
%
% (T,L), S |- F
% U
% To execute: consult('your_file.pl'). verify('input.txt').

% Literals
check(_, L, S, [], X) :- 
    getInnerList(L, S, List),
    member(X, List).

% Neg
check(_, L, S, [], neg(X)) :- 
    getInnerList(L, S, List),
    \+ member(X, List).

% And
check(T, L, S, [], and(F,G)) :- 
    check(T, L, S, [], F),
    check(T, L, S, [], G).

% Or
check(T, L, S, [], or(F, _)) :-
    check(T, L, S, [], F).
check(T, L, S, [], or(_, G)) :-
    check(T, L, S, [], G).
    
% AX
check(T, L, S, U, ax(F)) :-
    getInnerList(T, S, NextStates),
    checkAllStates(T, L, NextStates, U, F).

% EX
check(T, L, S, U, ex(F)) :-
    getInnerList(T, S, NextStates),
    member(Next, NextStates),
    check(T, L, Next, U, F).

% AG1
check(_, _, S, U, ag(_)) :-
    member(S, U).

% AG2 
check(T, L, S, U, ag(F)) :-
    \+ member(S, U),
    check(T, L, S, [], F),
    getInnerList(T, S, NextStates),
    checkAllStates(T, L, NextStates, [S|U], ag(F)).

% EG1
check(_, _, S, U, eg(_)) :-
    member(S, U).

% EG2
check(T, L, S, U, eg(F)) :-
    \+ member(S, U),
    check(T, L, S, [], F),
    getInnerList(T, S, NextStates),
    member(Next, NextStates),
    check(T, L, Next, [S|U], eg(F)).
    
% EF1
check(T, L, S, U, ef(F)) :-
    \+ member(S, U),
    check(T, L, S, [], F).
    
% EF2
check(T, L, S, U, ef(F)) :- 
    \+ member(S, U),
    getInnerList(T, S, NextStates),
    member(Next, NextStates),
    check(T, L, Next, [S|U], ef(F)).

% AF1
check(T, L, S, U, af(F)) :-
    \+ member(S, U),
    check(T, L, S, [], F).  

% AF2
check(T, L, S, U, af(F)) :-
    \+ member(S, U),
    getInnerList(T, S, NextStates),
    checkAllStates(T, L, NextStates, [S|U], af(F)).


% Hjälpfunktioner
getInnerList([[S,Res]|_], S, Res).
getInnerList([_|T], S, Res) :- 
    getInnerList(T, S, Res).

checkAllStates(_, _, [], _, _).
checkAllStates(T, L, [Head|Tail], U, F) :-
    check(T, L, Head, U, F),
    checkAllStates(T, L, Tail, U, F).