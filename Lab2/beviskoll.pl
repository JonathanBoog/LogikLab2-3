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

%Calls for the last line and the entire proof the be verified. Then writes "Proof Passed" if the proof passed
valid_proof(Prems, Goal, Proof) :- verifyLastLine(Goal, Proof), verifyProof(Proof, Prems, Proof), proofVerifyPrint().

%Verifies the last line is the same as the Goal.
verifyLastLine(Goal, Proof) :- last(Proof,LastLine), checkLastLine(LastLine, Goal).

%Checks if the term of the last line is equal to the Goal
checkLastLine([_, Term, _], Goal) :- Term == Goal.

%Calls verifyLine for every line in the proof
verifyProof([], _, _).
verifyProof([H|T], Prems, Proof) :- verifyLine(H, Prems, Proof), verifyProof(T, Prems, Proof). 

%Verifies a line if the functions is a premise
verifyLine([LineNum, Term, premise], Prems, _) :- member(Term, Prems), lineVerifyPrint(LineNum).

%Verifies a line if the functions is a assumption
verifyLine([[LineNum, _, assumption]|T], Prems, Proof) :- verifyProof(T, Prems, Proof), lineVerifyPrint(LineNum).

%Verifies a line if the functions is a copy
verifyLine([LineNum, Term, copy(X)], _, Proof) :- X < LineNum, findTerm(X, Proof, Term), compareLevel(LineNum, Proof, copy(X)), compareBoxNumber(LineNum, Proof, copy(X)), ! , lineVerifyPrint(LineNum).

%Verifies a line if the functions is a andint
verifyLine([LineNum, Term, andint(X,Y)], _, Proof) :- X < LineNum, Y < LineNum, findTerm(X, Proof, TermX), findTerm(Y, Proof, TermY), Term == and(TermX, TermY), compareBoxNumber(LineNum, Proof, andint(X,Y)), lineVerifyPrint(LineNum).

%Verifies a line if the functions is a andel
verifyLine([LineNum, Term, andel1(X)], _, Proof) :- X < LineNum, findTerm(X, Proof, and(Term,_)), compareLevel(LineNum, Proof, andel1(X)), compareBoxNumber(LineNum, Proof, andel1(X)), lineVerifyPrint(LineNum).
verifyLine([LineNum, Term, andel2(X)], _, Proof) :- X < LineNum, findTerm(X, Proof, and(_,Term)), compareLevel(LineNum, Proof, andel2(X)), compareBoxNumber(LineNum, Proof, andel2(X)), lineVerifyPrint(LineNum).

%Verifies a line if the functions is a orint
verifyLine([LineNum, or(Term,_), orint1(X)], _, Proof) :- X < LineNum, findTerm(X, Proof, Term), compareLevel(LineNum, Proof, orint1(X)), compareBoxNumber(LineNum, Proof, orint1(X)), lineVerifyPrint(LineNum).
verifyLine([LineNum, or(_, Term), orint2(X)], _, Proof) :- X < LineNum, findTerm(X, Proof, Term), compareLevel(LineNum, Proof, orint2(X)), compareBoxNumber(LineNum, Proof, orint2(X)), lineVerifyPrint(LineNum).

%Verifies a line if the functions is a orel
verifyLine([LineNum, Term, orel(X,Y,U,V,W)], _, Proof) :- X < LineNum, 
findTerm(X, Proof, or(TermX, TermY)), 
findTerm(Y, Proof, TermX),
findTerm(U, Proof, Term), 
findTerm(V, Proof, TermY), 
findTerm(W, Proof, Term),
compareLevel(LineNum, Proof, orel(X,Y,U,V,W)), compareBoxNumber(LineNum, Proof, orel(X,Y,U,V,W)),
!,lineVerifyPrint(LineNum).  

%Verifies a line if the functions is a impint
verifyLine([LineNum, imp(TermX,TermY), impint(X,Y)], _, Proof) :- X < LineNum, Y < LineNum, findTerm(X, Proof, TermX), findTerm(Y, Proof, TermY), compareLevel(LineNum, Proof, impint(X,Y)), compareBoxNumber(LineNum, Proof, impint(X,Y)), ! , lineVerifyPrint(LineNum).

%Verifies a line if the functions is a impel
verifyLine([LineNum, Term, impel(X,Y)], _, Proof) :- X < LineNum, Y < LineNum, findTerm(Y, Proof, imp(TermX, Term)), findTerm(X, Proof, TermX), compareLevel(LineNum, Proof, impel(X,Y)), compareBoxNumber(LineNum, Proof, impel(X,Y)), lineVerifyPrint(LineNum).

%Verifies a line if the functions is a negint
verifyLine([LineNum, Term, negint(X,Y)], _, Proof) :- X < LineNum, Y < LineNum, findTerm(X, Proof, TermX), findTerm(Y, Proof, cont), neg(TermX) == Term, compareLevel(LineNum, Proof, negint(X,Y)), lineVerifyPrint(LineNum).

%Verifies a line if the functions is a negel
verifyLine([LineNum, Term, negel(X,Y)], _, Proof) :- X < LineNum, Y < LineNum, findTerm(X, Proof, TermX), findTerm(Y, Proof, TermY), neg(TermX) == TermY, compareLevel(LineNum, Proof, negel(X,Y)), Term == cont, ! , lineVerifyPrint(LineNum) .


%Verifies a line if the functions is a contel
verifyLine([LineNum, _, contel(X)], _, Proof) :- X < LineNum, findTerm(X, Proof, cont), compareLevel(LineNum, Proof, contel(X)), compareBoxNumber(LineNum, Proof, contel(X)), lineVerifyPrint(LineNum).


%Verifies a line if the functions is a negnegint
verifyLine([LineNum, Term, negnegint(X)], _, Proof) :- X < LineNum, findTerm(X, Proof, TermX), arg(1, Term, InTerm), arg(1, InTerm, TermX), compareLevel(LineNum, Proof, negnegint(X)), compareBoxNumber(LineNum, Proof, negnegint(X)), lineVerifyPrint(LineNum). 

%Verifies a line if the functions is a negnegel
verifyLine([LineNum, Term, negnegel(X)], _, Proof) :- X < LineNum, findTerm(X, Proof, neg(neg(Term))), compareLevel(LineNum, Proof, negnegel(X)), compareBoxNumber(LineNum, Proof, negnegel(X)), lineVerifyPrint(LineNum).

%Verifies a line if the functions is a mt
verifyLine([LineNum, Term, mt(X,Y)], _, Proof) :- X < LineNum , Y < LineNum, arg(1, Term, InTerm), findTerm(X, Proof, TermX), arg(1, TermX, InTerm), arg(2, TermX, InTermX ), findTerm(Y, Proof, neg(InTermX)), compareLevel(LineNum, Proof, mt(X,Y)), compareBoxNumber(LineNum, Proof, impel(X,Y)), lineVerifyPrint(LineNum).

%Verifies a line if the functions is a pbc
verifyLine([LineNum, Term, pbc(X,Y)], _, Proof) :- X < LineNum, Y < LineNum, findTerm(X, Proof, neg(Term)), findTerm(Y, Proof, cont), compareLevel(LineNum, Proof, pbc(X,Y)), compareBoxNumber(LineNum, Proof, pbc(X,Y)), lineVerifyPrint(LineNum).

%Verifies a line if the functions is a lem
verifyLine([LineNum, or(neg(P), P), lem], _, _) :- lineVerifyPrint(LineNum).
verifyLine([LineNum, or(P, neg(P)), lem], _, _) :- lineVerifyPrint(LineNum).

%Gets the first element of a list
getFirstOfList([H|_], H).

%Gets the seconds element of a list
getSecondOfList([_,B|_], B).

%Tries to find the term in the proof at a line
findTerm(_,[], _) :- false.
findTerm(LineNum, [Line|_], Term) :- getFirstOfList(Line, LineNum), getSecondOfList(Line, Term).
findTerm(LineNum, [[Line|_]|_], Term) :- getFirstOfList(Line, LineNum), getSecondOfList(Line, Term).
findTerm(LineNum, [[_|Ts]|_], Term) :- findTerm(LineNum, Ts, Term).
findTerm(LineNum, [_|T], Term) :- findTerm(LineNum, T, Term).

%Prints 'Line number fullfilled'
lineVerifyPrint(LineNum) :- write("Line "),write(LineNum),write(" fullfilled"),write("\n").

%Prints 'Proof Passed'
proofVerifyPrint :- write("Proof Passed"),write("\n").

%Finds the level of a line
boxLevel(LineNum,[], BoxLevel, ResBoxLevel) :- false.
boxLevel(LineNum, [Line|T], BoxLevel, ResBoxLevel) :- getFirstOfList(Line, LineNum), ResBoxLevel = BoxLevel.
boxLevel(LineNum, [Line|T], BoxLevel, ResBoxLevel) :- getFirstOfList(Line, H), isList(H), NewLevel is BoxLevel + 1, boxLevel(LineNum, Line, NewLevel, ResBoxLevel).
boxLevel(LineNum, [Line|T], BoxLevel, ResBoxLevel) :- boxLevel(LineNum, T, BoxLevel, ResBoxLevel).

%Counts how many boxes you have and the starting line for each box
countBoxes([], Count, ResCount, StartNum, ResStartNum) :- ResCount = Count, ResStartNum = StartNum.
countBoxes([Line|T], Count, ResCount, StartNum, [LineNum|ResStartNum]) :- getFirstOfList(Line, H), isList(H), getFirstOfList(H, LineNum), NewCount is Count + 1, countBoxes(T, NewCount, ResCount, StartNum , ResStartNum).
countBoxes([Line|T], Count, ResCount, StartNum, ResStartNum) :- countBoxes(T, Count, ResCount, StartNum, ResStartNum).


%Gets the box number of a line with line number 'LineNum'. If Its not in a box, the LineNum will be equal to 0.
detBox(LineNum, Proof, ResBoxNum) :- boxLevel(LineNum, Proof, 0, Level), Level = 0, ResBoxNum = 0.
detBox(LineNum, Proof, ResBoxNum) :- countBoxes(Proof, 0, Boxes, [] , StartNum),elementComp(StartNum, LineNum, 0, ResPos), ResBoxNum = ResPos, boxLevel(LineNum, Proof, 0, Level), Level > 0.

%Determise in which position a number should be, if it where to be put into a list with numbers, ordered form smallest to bigest.
elementComp([], Element, Pos, ResPos) :- ResPos is 0.
elementComp([H|[]], Element, Pos, ResPos) :- ResPos is Pos + 1.
elementComp([H|T], Element, Pos, ResPos) :- Element >= H, getFirstOfList(T, Ht), Element < Ht, ResPos is Pos + 1.
elementComp([H|T], Element, Pos, ResPos) :- NewPos is Pos + 1, elementComp(T, Element, NewPos, ResPos).

%Checks if argument is list 
isList([_|_]).
isList([]).

%Makes sure that all Func point to the same box or one of the two values points to something outside any box.
compareBoxNumber(LineNum, Proof, Func) :- arg(1, Func, Value), not(arg(2, Func, _)), detBox(Value, Proof, ResValue), detBox(LineNum, Proof, ResLineNum), !, ResValue = 0.
compareBoxNumber(LineNum, Proof, Func) :- arg(1, Func, Value), not(arg(2, Func, _)), detBox(Value, Proof, ResValue), detBox(LineNum, Proof, ResLineNum), !, ResLineNum = ResValue.
compareBoxNumber(LineNum, Proof, Func) :- arg(1, Func, Value), arg(2, Func, SecValue), detBox(Value, Proof, ResValue), detBox(SecValue, Proof, ResSecValue), !, boxNumberHelper(ResValue, ResSecValue).
compareBoxNumber(LineNum, Proof, Func) :- arg(1, Func, Value), arg(2, Func, Value2), arg(3, Func, Value3), arg(4, Func, Value4), arg(5, Func, Value5), 
detBox(Value, Proof, ResValue), detBox(Value2, Proof, ResValue2), detBox(Value3, Proof, ResValue3), detBox(Value4, Proof, ResValue4), detBox(Value5, Proof, ResValue5), detBox(LineNum, Proof, ResLineNum),
boxNumberHelper(ResValue, ResValue2, ResValue3, ResValue4, ResValue5, ResLineNum).

%Helper predicate to compareBoxNumber
boxNumberHelper(ResValue, ResValue2, ResValue3, ResValue4, ResValue5, ResLineNum) :- ResValue2 = ResValue3, ResValue4 = ResValue5, ResLineNum = ResValue.
boxNumberHelper(0, ResValue2, ResValue3, ResValue4, ResValue5, ResLineNum) :- ResValue2 = ResValue3, ResValue4 = ResValue5.
boxNumberHelper(ResValue, 0) :- true.
boxNumberHelper(ResValue, ResSecValue) :- ResValue = ResSecValue.
boxNumberHelper(0, ResSecValue) :- true.

%Comapres the level of different lines. This makes sure that the targets of the Func are on the correct levels.
compareLevel(LineNum, Proof, Func) :- arg(1, Func, Value), boxLevel(LineNum, Proof, 0, Level), boxLevel(Value, Proof, 0, ValueLevel), Level >= ValueLevel.
compareLevel(LineNum, Proof, Func) :- arg(1, Func, Value), arg(2, Func, SecValue), 
boxLevel(LineNum, Proof, 0, Level), boxLevel(Value, Proof, 0, ValueLevel), boxLevel(SecValue, Proof, 0, SecValueLevel), Diff is ValueLevel-Level, Diff2 is SecValueLevel-Level,
Diff < 2, Diff2 < 2, ValueLevel == SecValueLevel.
compareLevel(LineNum, Proof, Func) :- arg(1, Func, Value), arg(2, Func, Value2), arg(3, Func, Value3), arg(4, Func, Value4), arg(5, Func, Value5),
boxLevel(LineNum, Proof, 0, Level), boxLevel(Value, Proof, 0, ValueLevel), boxLevel(Value2, Proof, 0, ValueLevel2), boxLevel(Value3, Proof, 0, ValueLevel3),
boxLevel(Value4, Proof, 0, ValueLevel4), boxLevel(Value5, Proof, 0, ValueLevel5),
ValueLevel2 = ValueLevel3, ValueLevel4 = ValueLevel5,
Diff is ValueLevel-Level, Diff < 2.
