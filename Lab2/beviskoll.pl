% Proof checker on Natural Deduction
%
% Author: Jonathan Lavén & Julius Geiryd
%
% 2024-11-20

verify(InputFileName) :- 
  see(InputFileName),
  read(Prems), read(Goal), read(Proof),
  seen,
  valid_proof(Prems, Goal, Proof).

% Proofs can't be empty.
valid_proof(_, _, []) :- false.

% Calls for the last line and the entire proof to be verified with an added seen list (empty at the beginning).
valid_proof(Prems, Goal, Proof) :-
  last_box_elem(Proof, [_, Goal, _]), % Proofs should end with the Goal.
  verify_line(Prems, Goal, Proof, []). 

% Basecase for verify_line
verify_line(_, _, [], _).

% Premise.
% Check if a premise is in the Prems list. If true, store line in Seen and call on the rest of the proof.
verify_line(Prems, Goal, [[LineNum, Predicate, premise]|T], Seen) :-
  member(Predicate, Prems),
  verify_line(Prems, Goal, T, [[LineNum, Predicate, premise]|Seen]).

% Assumption.
% Not allowed to end a proof with an assumption (last line).
verify_line(_, _, [[[_, _, assumption]|[]]|[]], _) :- false.

% Box & Assumption
% Box (CurrentBox) in a box (OuterBox). 
verify_line(Prems, Goal, [[[LineNum, Predicate, assumption]|CurrentBox]|OuterBox], Seen) :-
  verify_line(Prems, Goal, CurrentBox, [[LineNum, Predicate, assumption]|Seen]),
  verify_line(Prems, Goal, OuterBox, [[[LineNum, Predicate, assumption]|CurrentBox]|Seen]).

% Copy.
verify_line(Prems, Goal, [[LineNum, Predicate, copy(X)]|T], Seen) :-
  find_line(X, Seen, Predicate),
  verify_line(Prems, Goal, T, [[LineNum, Predicate, copy(X)]|Seen]).

% And inttroduction.
% Look up the lines that are referenced to and see if they exist in Seen.
verify_line(Prems, Goal, [[LineNum, and(A, B), andint(X, Y)]|T], Seen) :-
  find_line(X, Seen, A),
  find_line(Y, Seen, B),
  verify_line(Prems, Goal, T, [[LineNum, and(A, B), andint(X, Y)]|Seen]).

% And elimination 1.
verify_line(Prems, Goal, [[LineNum, A, andel1(X)]|T], Seen) :-
  find_line(X, Seen, and(A, _)),
  verify_line(Prems, Goal, T, [[LineNum, A, andel1(X)]|Seen]).

% And eliminiation 2.
verify_line(Prems, Goal, [[LineNum, B, andel2(X)]|T], Seen) :-
  find_line(X, Seen, and(_, B)),
  verify_line(Prems, Goal, T, [[LineNum, B, andel2(X)]|Seen]).

% Or introduction 1.
verify_line(Prems, Goal, [[LineNum, or(A, B), orint1(X)]|T], Seen) :-
  find_line(X, Seen, A),
  verify_line(Prems, Goal, T, [[LineNum, or(A, B), orint1(X)]|Seen]).

% Or introduction 2.
verify_line(Prems, Goal, [[LineNum, or(A, B), orint2(X)]|T], Seen) :-
  find_line(X, Seen, B),
  verify_line(Prems, Goal, T, [[LineNum, or(A, B), orint2(X)]|Seen]).

% Or elimination. 
verify_line(Prems, Goal, [[LineNum, C, orel(X, Y, U, V, W)]|T], Seen) :-
  find_line(X, Seen, or(A, B)), % X is an or statement.
  first_box_elem(Box1, [Y, A, _]),
  last_box_elem(Box1, [U, C, _]),
  first_box_elem(Box2, [V, B, _]),
  last_box_elem(Box2, [W, C, _]),
  verify_line(Prems, Goal, T, [[LineNum, C, orel(X, Y, U, V, W)]|Seen]).

% Implication introduction. 
verify_line(Prems, Goal, [[LineNum, imp(A, B), impint(X, Y)]|T], Seen) :-
  box_in_list(Seen, Box), % Make sure that Box isn't in a closed box.
  first_box_elem(Box, [X, A, _]), 
  last_box_elem(Box, [Y, B, _]),
  verify_line(Prems, Goal, T, [[LineNum, imp(A, B), impint(X, Y)]|Seen]).

% Implication elimination.
verify_line(Prems, Goal, [[LineNum, B, impel(X, Y)]|T], Seen) :-
  find_line(X, Seen, A),
  find_line(Y, Seen, imp(A, B)),
  verify_line(Prems, Goal, T, [[LineNum, B, impel(X, Y)]|Seen]).

% Negation introduction.
% Returns the negation of the assumption.
verify_line(Prems, Goal, [[LineNum, neg(A), negint(X, Y)]|T], Seen) :-
  first_box_elem(Seen, Box),
  find_line(X, Box, A),
  find_line(Y, Box, cont),
  verify_line(Prems, Goal, T, [[LineNum, neg(A), negint(X, Y)]|Seen]).

% Negation elimination.
% Returns contradiction.
verify_line(Prems, Goal, [[LineNum, cont, negel(X, Y)]|T], Seen) :-
  find_line(X, Seen, A),
  find_line(Y, Seen, neg(A)),
  verify_line(Prems, Goal, T, [[LineNum, cont, negel(X, Y)]|Seen]).

% Contradiction elimination.
% Checks if the predicate on line X is a contradiction.
verify_line(Prems, Goal, [[LineNum, A, contel(X)]|T], Seen) :-
  find_line(X, Seen, cont),
  verify_line(Prems, Goal, T, [[LineNum, A, contel(X)]|Seen]).

% Double negation elimination.
verify_line(Prems, Goal, [[LineNum, A, negnegel(X)]|T], Seen) :-
  find_line(X, Seen, neg(neg(A))),
  verify_line(Prems, Goal, T, [[LineNum, A, negnegel(X)]|Seen]).

% Double negation introduction. 
verify_line(Prems, Goal, [[LineNum, neg(neg(A)), negnegint(X)]|T], Seen) :-
  find_line(X, Seen, A),
  verify_line(Prems, Goal, T, [[LineNum, A, cont]|Seen]).

% MT
% Ensures that B implies A and negation of A is present.
verify_line(Prems, Goal, [[LineNum, neg(B), mt(X, Y)]|T], Seen) :-
  find_line(X, Seen, imp(B, A)),
  find_line(Y, Seen, neg(A)),
  verify_line(Prems, Goal, T, [[LineNum, neg(B), mt(X, Y)]|Seen]).

% PBC
verify_line(Prems, Goal, [[LineNum, A, pbc(X, Y)]|T], Seen) :-
  first_box_elem(Seen, Box),
  find_line(X, Box, neg(A)),
  find_line(Y, Box, cont),
  verify_line(Prems, Goal, T, [[LineNum, neg(A), negint(X, Y)]|Seen]).

% LEM
verify_line(Prems, Goal, [[LineNum, or(A, neg(A)), lem]|T], Seen) :-
  verify_line(Prems, Goal, T, [[LineNum, or(A, neg(A)), lem]|Seen]).


% Get the content of the line with the given line number in the given list.
find_line(_, [], _) :- false.
find_line(LineNum, [[LineNum, Line, _]|_], Line).
find_line(LineNum, [_|T], Match) :- find_line(LineNum, T, Match).

% Get the first element in the given box/list.
first_box_elem([H|_], H).

% Get the last element in the given box/list.
last_box_elem([H|[]], H).
last_box_elem([_|T], H) :- last_box_elem(T, H).

% Determine if the given Box is in the list.
box_in_list([], _) :- false. % No box found
box_in_list([Box|_], Box).
box_in_list([_|T], Box) :- box_in_list(T, Box).
