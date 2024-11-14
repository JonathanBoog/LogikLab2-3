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

% Calls for the last line and the entire proof to be verified with an added (empty) Seen list.
valid_proof(Prems, Goal, Proof) :-
  last_in_box(Proof, [_, Goal, _]), % Proofs should end with the Goal.
  valid_proof(Prems, Goal, Proof, []).

% Basecase for vaild_proof
valid_proof(_, _, [], _).

% Premise.
% Check if a premise is in the Prems list. If true, store line in Seen and call on the rest of the proof.
valid_proof(Prems, Goal, [[LineNum, Predicate, premise]|T], Seen) :-
  member(Predicate, Prems),
  valid_proof(Prems, Goal, T, [[LineNum, Predicate, premise]|Seen]).

% Assumption.
% Not allowed to end a proof with an assumption.
valid_proof(_, _, [[[_, _, assumption]|[]]|[]], _) :- false.

% Parse box.
% Box (CurrentBox) in a box (OuterBox). 
% Explaination for box algorithm: Add lines from CurrentBox to Seen until box closes, CurrentBox is allowed to use all
% previous lines. When CurrentBox closes it is added to Seen as a box, which
% makes OuterBox and the rest of the program unable to access the lines in it
% without the use of the predicates first_in_box and last_in_box.
valid_proof(Prems, Goal, [[[LineNum, Predicate, assumption]|CurrentBox]|OuterBox], Seen) :-
  valid_proof(Prems, Goal, CurrentBox, [[LineNum, Predicate, assumption]|Seen]),
  valid_proof(Prems, Goal, OuterBox, [[[LineNum, Predicate, assumption]|CurrentBox]|Seen]).

% Copy.
valid_proof(Prems, Goal, [[LineNum, Predicate, copy(X)]|T], Seen) :-
  find_line(X, Seen, Predicate),
  valid_proof(Prems, Goal, T, [[LineNum, Predicate, copy(X)]|Seen]).

% And int.
% If and introduction is used, look up the lines that are referenced to
% and see if an and-operation is allowed.
valid_proof(Prems, Goal, [[LineNum, and(A, B), andint(X, Y)]|T], Seen) :-
  find_line(X, Seen, A),
  find_line(Y, Seen, B),
  valid_proof(Prems, Goal, T, [[LineNum, and(A, B), andint(X, Y)]|Seen]).
% And elim 1.

valid_proof(Prems, Goal, [[LineNum, Y, andel1(X)]|T], Seen) :-
  find_line(X, Seen, and(Y, _)),
  valid_proof(Prems, Goal, T, [[LineNum, Y, andel1(X)]|Seen]).

% And elim 2.
valid_proof(Prems, Goal, [[LineNum, Y, andel2(X)]|T], Seen) :-
  find_line(X, Seen, and(_, Y)),
  valid_proof(Prems, Goal, T, [[LineNum, Y, andel2(X)]|Seen]).

% Or int 1.
valid_proof(Prems, Goal, [[LineNum, or(Y, Z), orint1(X)]|T], Seen) :-
  find_line(X, Seen, Y),
  valid_proof(Prems, Goal, T, [[LineNum, or(Y, Z), orint1(X)]|Seen]).

% Or int 2.
valid_proof(Prems, Goal, [[LineNum, or(Z, Y), orint2(X)]|T], Seen) :-
  find_line(X, Seen, Y),
  valid_proof(Prems, Goal, T, [[LineNum, or(Z, Y), orint2(X)]|Seen]).

% Or elim. 
% X is an or statement.
% Y is line number of first statement in first box.
% U is line number of last statement in first box.
% V is line number of first statement in second box.
% W is line number of last statement in second box.
valid_proof(Prems, Goal, [[LineNum, C, orel(X, Y, U, V, W)]|T], Seen) :-
  find_line(X, Seen, or(A, B)),
  first_in_box(Box1, [Y, A, _]),
  first_in_box(Box2, [V, B, _]),
  last_in_box(Box1, [U, C, _]),
  last_in_box(Box2, [W, C, _]),
  valid_proof(Prems, Goal, T, [[LineNum, C, orel(X, Y, U, V, W)]|Seen]).

% Implication introduction. 
% Checks if the box that is being referenced to is in the scope of the current
% box. Checks if A is the first predicate in a box and if B is the last
% predicate in the same box. Checks if the line numbers of A and B matches 
% X and Y.

valid_proof(Prems, Goal, [[LineNum, imp(A, B), impint(X, Y)]|T], Seen) :-
  box_is_in_box(Seen, Box), % Make sure that Box isn't in a closed box.
  first_in_box(Box, [X, A, _]), 
  last_in_box(Box, [Y, B, _]),
  valid_proof(Prems, Goal, T, [[LineNum, imp(A, B), impint(X, Y)]|Seen]).

% Implication elimination.
% Look up the lines being referenced to and check if the predicate on line X
% implies the predicate on line Y. It is assumed that the predicate on line X is true since it
% is in Seen, which can only happen if it is true.

valid_proof(Prems, Goal, [[LineNum, B, impel(X, Y)]|T], Seen) :-
  find_line(X, Seen, A),
  find_line(Y, Seen, imp(A, B)),
  valid_proof(Prems, Goal, T, [[LineNum, B, impel(X, Y)]|Seen]).

% Negation introduction.
% Assumes the predicate on line X and arrives at arbitrary contradiction.
% Returns the negation of the assumption.
valid_proof(Prems, Goal, [[LineNum, neg(A), negint(X, Y)]|T], Seen) :-
  first_in_box(Seen, Box),
  find_line(X, Box, A),
  find_line(Y, Box, cont),
  valid_proof(Prems, Goal, T, [[LineNum, neg(A), negint(X, Y)]|Seen]).

% Negation elimination.
% Assumes something on line X is true and arrives at a contradiction on line Y.
% Returns contradiction.

valid_proof(Prems, Goal, [[LineNum, cont, negel(X, Y)]|T], Seen) :-
  find_line(X, Seen, A),
  find_line(Y, Seen, neg(A)),
  valid_proof(Prems, Goal, T, [[LineNum, cont, negel(X, Y)]|Seen]).

% Contradiction elimination.
% Checks if the predicate on line X is a contradiction.
valid_proof(Prems, Goal, [[LineNum, A, contel(X)]|T], Seen) :-
  find_line(X, Seen, cont),
  valid_proof(Prems, Goal, T, [[LineNum, A, contel(X)]|Seen]).

% Double negation introduction. 
valid_proof(Prems, Goal, [[LineNum, neg(neg(A)), negnegint(X)]|T], Seen) :-
  find_line(X, Seen, A),
  valid_proof(Prems, Goal, T, [[LineNum, A, cont]|Seen]).

% Double negation elimination.
valid_proof(Prems, Goal, [[LineNum, Y, negnegel(X)]|T], Seen) :-
  find_line(X, Seen, neg(neg(Y))),
  valid_proof(Prems, Goal, T, [[LineNum, Y, negnegel(X)]|Seen]).

% MT
% Ensures that B implies A and negation of A is present.

valid_proof(Prems, Goal, [[LineNum, neg(B), mt(X, Y)]|T], Seen) :-
  find_line(X, Seen, imp(B, A)),
  find_line(Y, Seen, neg(A)),
  valid_proof(Prems, Goal, T, [[LineNum, neg(B), mt(X, Y)]|Seen]).

% Proof by contradiction.
% Assume negation of A and arrive at a contradiction. Returns A.
valid_proof(Prems, Goal, [[LineNum, A, pbc(X, Y)]|T], Seen) :-
  first_in_box(Seen, Box),
  find_line(X, Box, neg(A)),
  find_line(Y, Box, cont),
  valid_proof(Prems, Goal, T, [[LineNum, neg(A), negint(X, Y)]|Seen]).

% LEM
valid_proof(Prems, Goal, [[LineNum, or(A, neg(A)), lem]|T], Seen) :-
  valid_proof(Prems, Goal, T, [[LineNum, or(A, neg(A)), lem]|Seen]).


% Get the content of the line with the given Index in the given list.
%   find_line(1, [[1, 2, _]], Line). => Line = 2
find_line(_, [], _) :- false.
find_line(Index, [[Index, Line, _]|_], Line).
find_line(Index, [_|T], Match) :- find_line(Index, T, Match).

% Get the first element in the given list.
%   first_in_box([1, 2, 3], H). => H = 1
first_in_box([H|_], H).

% Get the last element in the given list.
%   last_in_box([1, 2, 3], L). => L = 3
last_in_box([H|[]], H).
last_in_box([_|T], H) :- last_in_box(T, H).

% Determine if the given Box in the list.
%   box_is_in_box([1, 2, 3], 2). => true
box_is_in_box([], _) :- false.
box_is_in_box([Box|_], Box).
box_is_in_box([_|T], Box) :- box_is_in_box(T, Box).

% Return !X.
neg(X) :- not(X).

% check implication.
imp(false, false).
imp(_, true) :- true.
imp(true, Y) :- Y.

% check and
and(A, B) :- A, B.

% check or
or(A, _) :- A.
or(_, B) :- B.