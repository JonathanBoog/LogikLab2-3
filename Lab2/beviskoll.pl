% Proof checker on Natural Deduction
%
% Author: Jonathan Lavén & Julius Geiryd
%
% 2024-11-20

%Reads information from the input file and seperates the Prems, Goal and Proof.
verify(InputFileName) :- see(InputFileName),
    read(Prems), read(Goal), read(Proof),
    seen,
    valid_proof(Prems, Goal, Proof).

%Calls for the last line and the entire proof to be verified
valid_proof(Prems, Goal, Proof) :- verifyLastLine(Goal, Proof), verifyProof(Proof, Prems, Proof).


%Sends the last line in the proof to checkLastLine
verifyLastLine(Goal, Proof) :- last(Proof, LastLine), checkLastLine(LastLine, Goal).

%Check if last line is same as Goal
checkLastLine([_,Term,_], Goal) :- Term == Goal.


%Calls verifyLine for every line in the proof
verifyProof([], _,_).
verifyProof([H|T], Prems, Proof) :- verifyLine(H, Prems, Proof), verifyProof(T, Prems, Proof).



%Check premise
verifyLine([_,Term, premise], Prems, _) :- member(Term, Prems).

%Check assumption
verifyLine([[_,Term, assumption]|T], Prems, Proof) :- verifyProof(T,Prems, Proof).

%Check copy
verifyLine([LineNum, Term, copy(X)], _, Proof) :- X < LineNum, findTerm() 

%Check and-introduction 
verifyLine([LineNum, Term, andint(x,y)], _, Proof) :- 

%Check and-elimination 1
verifyLine([LineNum, Term, andel1(x)], _, Proof) :-  

%Check and-elimination 2
verifyLine([LineNum, Term, andel2(x)], _, Proof) :-

%Check or-introduction 1
verifyLine([LineNum, Term, orint1(x)], _, Proof) :- 

%Check or-introduction 2
verifyLine([LineNum, Term, orint2(x)], _, Proof) :-

%Check or-elimination
verifyLine([LineNum, Term, orel(x,y,u,v,w)], _, Proof) :-

%Check implication introduction
verifyLine([LineNum, Term, impint(x,y)], _, Proof) :-

%Check implication elimination
verifyLine([LineNum, Term, impel(x,y)], _, Proof) :-

%Check neg introduction
verifyLine([LineNum, Term, negint(x,y)], _, Proof) :-

%Check neg elimination 
verifyLine([LineNum, Term, negel(x,y)], _, Proof) :-

%Check contradiction elimination
verifyLine([LineNum, Term, contel(x)], _, Proof) :-

%Check neg neg introduction
verifyLine([LineNum, Term, negnegint(x)], _, Proof) :- 

%Check neg neg elimination
verifyLine([LineNum, Term, negnegel(x)], _, Proof) :-

%Check MT
verifyLine([LineNum, Term, mt(x,y)], _, Proof) :-

%Check proof by contradiction (PBC)
verifyLine([LineNum, Term, pbc(x,y)], _, Proof) :-

%Check LEM
verifyLine([LineNum, Term, lem], _, Proof) :-


findTerm() :- 