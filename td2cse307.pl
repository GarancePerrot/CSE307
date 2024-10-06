/*
CSE 307 Relational Programming

TD2 Constraint-based models using lists in Prolog

@author Francois Fages
  

  
PART I. Symbolic Differentiation in Prolog
------------------------------------------

Question 1
----------
Define a symbolic differentiation predicate for polynomial expressions formed with integers, +, * (no exponent)
  and variables denoted by atoms (in order not to confuse them with Prolog variables!)

  derivative(+Polynomial, +Variable, ?Derivative)

where Derivative is the formal partial derivative of Polynomial with respect to Variable.

?- derivative(2*a*b-4*a+1, a, D).
D = (0*a+1*2)*b+0*(2*a)-(0*a+1*4)+0 ;
false.

The predicate atomic/1 can be used to check that a term is an atom or a number (i.e. not a compound term nor a Prolog variable)
and the constraint dif/2 to test disequality.
  
*/

%P is constant.
derivative(P, _ , 0) :-
  number(P).

%P is the same variable.
derivative(P, X, 1) :-
  atom(P),
  P == X.

%P is another variable.
derivative(P, X, 0) :- 
  atom(P),
  P \== X.


%properties of the sum.
derivative( A + B ,X,D) :-
  derivative(A, X, D1),
  derivative(B, X, D2),
  D = D1 + D2.

%properties of the opposite.
derivative( - A , X, D) :-
  derivative(A, X, D1),
  D = - D1.

%properties of the substraction.
derivative( A - B ,X,D) :-
  derivative(A, X, D1),
  derivative(B, X, D2),
  D = D1 - D2.

%properties of function multiplication. 
derivative( A * B,X,D) :-
  derivative(A, X, D1),
  derivative(B, X, D2),
  D = A * D2 + B * D1.


/*
Question 2
--------

Define an algebraic simplification predicate

  simplify(Expression, SimplifiedExpression).

for performing some simple simplifications.

?- derivative(2*a*b-4*a+1, a, D), simplify(D, E).
D = (0*a+1*2)*b+0*(2*a)-(0*a+1*4)+0,
E = 2*b-4 ;
false.

The metapredicate (Condition1 -> Goal1 ; Condition2 -> Goal2; Goal3) can be used to test different conditions in a goal
*/

%problem: my simplification does not stop to false

%constant
simplify(E, E) :- 
  number(E).

%properties of the sum
simplify(0 + E2, E) :-
  simplify(E2, E).

simplify(E1 + 0, E) :-
  simplify(E1, E).

simplify(E1 + E2, ER) :-
  E1 == E2,
  simplify(E1, E),
  ER is 2 * E.

simplify(E1 + E2, ER) :-
  E1 \== E2,
  simplify(E1, E11),
  simplify(E2, E22),
  (number(E11), number(E22) ->  simplify(E11 + E22, ER) ; simplify( E11 + E22, ER)).

%properties of the substraction
simplify(E1 - 0, E) :-
  simplify(E1, E).

simplify(0 - E1, E) :-
  simplify(-E1, E).

simplify(E1 - E2, E) :-
  E1 == E2,
  E = 0.

simplify(E1 - E2, ER) :-
  E1 \== E2,
  simplify(E1, E11),
  simplify(E2, E22),
  (number(E11), number(E22) -> ER is E11 - E22 ; ER = E11 - E22).

%properties of multiplication
simplify(_ * 0, 0).
simplify(0 * _, 0).

simplify(E1 * E2, ER) :-
  simplify(E1, E11),
  simplify(E2, E22),
  (number(E11), number(E22) -> ER is E11 * E22; ER = E11 * E22).

%in the end when no rule matches anymore: E is simplified.
simplify(E, E).               
    

/*

PART II. Constraint-based models using lists in Prolog
------------------------------------------------------

  List are represented in Prolog by first-order terms as follows:

  - the empty list is represented by the constant []
  
  - the list constructor by a binary operator noted '[|]' as in  [FirstElement | ListTail]

  - or in extension with commas as in [X, Y, Z] for a list with 3 elements or [X, Y, Z | ListTail] with at least 3 elements
  
The Prolog predicate member/2 is true if its first argument unifies with one element of the second argument list.

Note that this Prolog predicate enumerates all lists satisfying the relation.

member(X, [X | _]).

member(X, [_ | L]):-
    member(X, L).

?- member(X, [a, b, a]).
X = a ;
X = b ;
X = a ;
false.

?- member(X, L).
L = [X|_] ;
L = [_, X|_] ;
L = [_, _, X|_] .


Question 3
----------

Define the predicate

  remove(?List1, ?X, ?List2)

true if List2 is the List1 with exactly one element unifying with X removed:

?- remove([a, b, a], a, L).
L = [b, a] ;
L = [a, b] ;
false.
  
?- remove([a, b, a], c, L).
false.

?- remove([f(X), b, f(Y)], f(a), L).
X = a,
L = [b, f(Y)] ;
Y = a,
L = [f(X), b] ;
false.

?- remove(L, X, R).
L = [X|R] ;
L = [_A, X|_B],
R = [_A|_B] ;
L = [_A, _B, X|_C],
R = [_A, _B|_C] .

  
*/

%remove(?List1, ?X, ?List2)

remove([X | L], X, L).

remove([A | L1], X, L):-
    remove(L1, X, L11),
    L = [A| L11].

/*
  
Let us consider the following constraint logic program for computing the optimal schedules for the construction of a house structure.

Each task is a couple composed of its starting date (unknown decision variable) and duration (known constant) in number of weeks.

The minimal end date of the project is 15 weeks.
There are several optimal solutions with different starting dates for the non-critical tasks:

?- house(Starts, End).
Starts = [0, 7, 7, 7, 10, 11, 12, 10],
End = 15 ;
Starts = [0, 7, 7, 7, 10, 11, 12, 11],
End = 15 ;
Starts = [0, 7, 7, 7, 10, 11, 12, 12],
End = 15 ;
Starts = [0, 7, 7, 7, 10, 12, 12, 10],
End = 15 .

*/

:- use_module(library(clpfd)).

house(Starts, End) :-
    Starts = [Foundations, Interior_walls, Exterior_walls, Chimney, Roof, Doors, Tiles, Windows],

    Durations_Sum #= 7+4+3+3+2+2+3+3, 

    Starts ins 0..Durations_Sum,
    
    End #=< Durations_Sum,

    Foundations+7 #=< Interior_walls,
    Foundations+7 #=< Exterior_walls,
    Foundations+7 #=< Chimney,
    Exterior_walls+3 #=< Roof,
    Exterior_walls+3 #=< Windows,
    Interior_walls+4 #=< Doors,
    Chimney+3 #=< Tiles,
    Roof+2 #=< Tiles,

    Windows+3 #=< End,
    Doors+2 #=< End,
    Tiles+3 #=< End,

    labeling([min(End)], [End | Starts]).


/*
Question 4
----------

Define a predicate
  
  schedule(+Tasks, ?Starts, +Durations, +Precedences, ?End)

to enumerate the optimal schedules for any list of tasks,
represented by their list of names, list of starting dates and list of durations,
given a list of precedences represented symbolically by couples of the form (task_name1 < task_name2).

You can use the predicates

length(List, N) for determining the length of a list or creating a list of given length,
 
nth1(?Index, ?List, ?Elem) for unifying Elem with the Index's element of List,

sum(+Vars, #=, ?Expr) for summing the elements of a list.

?- schedule(
  [foundations, interior_walls, exterior_walls, chimney, roof, doors, tiles, windows],
  [Foundations, Interior_walls, Exterior_walls, Chimney, Roof, Doors, Tiles, Windows],
  [7,4,3,3,2,2,3,3],
  [
   foundations < interior_walls,
   foundations < exterior_walls,
   foundations < chimney,
   exterior_walls < roof,
   exterior_walls < windows,
   interior_walls < doors,
   chimney < tiles,
   roof < tiles
  ],
  End).
  
Foundations = 0,
Interior_walls = Exterior_walls, Exterior_walls = Chimney, Chimney = 7,
Roof = Windows, Windows = 10,
Doors = 11,
Tiles = 12,
End = 15 ;
  
Foundations = 0,
Interior_walls = Exterior_walls, Exterior_walls = Chimney, Chimney = 7,
Roof = 10,
Doors = Windows, Windows = 11,
Tiles = 12,
End = 15 ;
  
Foundations = 0,
Interior_walls = Exterior_walls, Exterior_walls = Chimney, Chimney = 7,
Roof = 10,
Doors = 11,
Tiles = Windows, Windows = 12,
End = 15 .

*/

:- use_module(library(clpfd)).

schedule(Tasks, Starts, Durations, Precedences, End) :-
  length(Tasks, N),
  length(Starts, N),
  length(Durations, N),
  sum(Durations, #=, S),
  Starts ins 0..S,
  End #=< S,

  translatePrecedences(Tasks, Starts, Durations, Precedences),
  translateEnds(Starts, Durations, End),
  
  labeling([min(End)], [End | Starts]).

translatePrecedences(_, _, _, []).
translatePrecedences(Tasks, Starts, Durations, [TaskA < TaskB | Rest]) :-
  nth1(I, Tasks, TaskA),
  nth1(J, Tasks, TaskB),
  nth1(I, Starts, StartA),
  nth1(J, Starts, StartB),
  nth1(I, Durations, DA),
  StartA + DA #=< StartB,
  translatePrecedences(Tasks, Starts, Durations, Rest).

translateEnds([],_,_).
translateEnds([ StartA | RestS], [DA | RestD], End) :-
  StartA + DA #=< End,
  translateEnds(RestS, RestD, End).


/*
Part III Directed Graphs
------------------------
   
Let us first represent a directed graph of cities related by current offers of car sharing, with the following Datalog predicates:

*/


arc(amsterdam, paris).
arc(paris, lyon).
arc(lyon, rome).
arc(lyon, verone).
arc(lausanne, verone).
arc(verone, rome).
arc(rome, paris). % adding cycle in the graph of offers

/*
Question 5
----------

Define predicate path/2 for the reflexive transitive closure of the arc/2 relation in a graph without circuit.

This predicate is authorized to loop on a cyclic graph like the one above.

?- path(palaiseau, paris).
false.

?- path(amsterdam, rome).
true ;
true ;
true ;
true ;
true .
*/

path(A, B) :- arc(A, B).
path(A, B) :- 
  arc(A, C), 
  path(C, B).


/*
Question 6
----------

Characterize the queries on which the program will loop without producing any answer.

Answer:  Whenever there is a cyclic path producing an infinite loop, the program will be 
stuck in the loop, trying to traverse this path indefinitely and not produce a final answer. 
For example:
arc(palaiseau, rambouillet).
arc(rambouillet, chartres).
arc(chartes, palaiseau).
Trying path(palaiseau, chartres) will lead to an infinite loop.

  
Question 7
----------

Define the predicate

  path(?X, ?Y, ?List)

to enumerate all pathways without circuit from X to Y (or the trivial circuit on X in the case Y=X).

This predicate should not loop on a cyclic graph like the one above.

Hint: use an auxiliary predicate path(X, Y, ListX, ListY)
  including the list of cities already visited to reach X and
  returning the list of all cities visited to reach Y.

The Prolog predicate reverse/2 reverses the arguments of a list in order to get the cities on the pathway in the right order.

Negation by failure can be used with Prolog metapredicate

  \+ Goal

which succeeds if Goal has no success.


?- path(paris, rome, P).
P = [paris, lyon, rome] ;
P = [paris, lyon, verone, rome] ;
false.
  
*/
%path/3
path(X, X, [X]).

path(X, Y, Path) :-
    path(X, Y, [], PathR), 
    reverse(PathR, Path). %reverse the path 

% path/4
path(X, X, Visited, [X|Visited]).

path(X, Y, Visited, Path) :-
    arc(X, Z),           
    \+ member(Z, Visited),   % we have not visited Z
    path(Z, Y, [X|Visited], Path).


/*
Question 8
----------

Prove that your program path/3 terminates on any graph.

Hint: show that there is no infinite branch in the search tree
by giving a complexity measure on the arguments of your path/4 predicate and the graph defined by arc/2 
that strictly decreases at each recursive call along a branch of the search tree.
  

  
Answer:
The complexity measure that we chose is the number of cities that we still have to visit. It corresponds
to the total number of cities minus the number of cities that we have visited (length of Visited). 
As we traverse the path, the length of Visited increases (since we prepend a node to its head), and 
since the total number of cities is fixed, it implies that the number of unvisited cities decreases
with each recursive call, to eventually reach 0, where the recursion stops. 



Question 9
----------

Give a crude bound on the number of nodes in the search tree for the query path(X, Y, List)
as a function O(f(v, a)) of the numbers v of vertices and a of arcs in the graph.

Give an example of a graph with an exponential number of pathways in the number of vertices.


Answer:
A crude bound for the number of nodes in the search tree is O(v * a).
If we consider that each vertex can be connected to any other vertex by a direct arc,
we have that each vertex can be visited by another vertex directly or indirectly through an arc. 
It will result in v*a possible pathways to explore so such number of nodes in the search tree.
  

*/



/*

Let us now consider the CSV file GEODATASOURCE-COUNTRY-BORDERS.CSV
downloaded from the website https://public.opendatasoft.com/explore/dataset/world-administrative-boundaries/export/
representing the countries of the world with their borders.

That CSV file can be read in Prolog as a list of rows with library(csv) as follows:

?- use_module(library(csv)).
true.

?- csv_read_file('GEODATASOURCE-COUNTRY-BORDERS.CSV', Rows).
Rows = [row(country_code, country_name, country_border_code, country_border_name), row('AD', 'Andorra', 'FR', 'France'), row('AD', 'Andorra', 'ES', 'Spain'), row('AE', 'United Arab Emirates', 'OM', 'Oman'), row('AE', 'United Arab Emirates', 'SA', 'Saudi Arabia'), row('AF', 'Afghanistan', 'CN', 'China'), row('AF', 'Afghanistan', 'IR', 'Iran (Islamic Republic of)'), row('AF', 'Afghanistan', 'PK', 'Pakistan'), row(..., ..., ..., ...)|...].



Question 10
-----------
Define a predicate assert_borders/0 to assert the arcs between countries having a common border in that database of borders.
  
For this, use retractall/1 and assert/2 metapredicates to retract and assert arc/2 clauses which are declared both dynamic and multifile.

Note that the graph of borders in that database is symmetrical (except for islands which have an arc with '').
It contains 728 arcs and 249 vertices (countries):
  
?- assert_borders.
true.

?- arc('Japan', X).
X = ''.
  
?- arc('', X).
false.

?- arc('Spain', X).
X = 'Andorra' ;
X = 'France' ;
X = 'Gibraltar' ;
X = 'Morocco' ;
X = 'Portugal'.

?- arc(X, 'Spain').
X = 'Andorra' ;
X = 'France' ;
X = 'Gibraltar' ;
X = 'Morocco' ;
X = 'Portugal'.

?- findall(X, arc(X, _), L), length(L, A), list_to_set(L, S), length(S, N).
L = ['Andorra', 'Andorra', 'United Arab Emirates', 'United Arab Emirates', 'Afghanistan', 'Afghanistan', 'Afghanistan', 'Afghanistan', 'Afghanistan'|...],
A = 728,
S = ['Andorra', 'United Arab Emirates', 'Afghanistan', 'Antigua and Barbuda', 'Anguilla', 'Albania', 'Armenia', 'Angola', 'Antarctica'|...],
N = 249.
  
?- path('Spain', X, L).
X = 'Spain',
L = ['Spain'] ;
X = 'Andorra',
L = ['Spain', 'Andorra'] ;
X = 'France',
L = ['Spain', 'Andorra', 'France'] ;
X = 'Belgium',
L = ['Spain', 'Andorra', 'France', 'Belgium'] ;
X = 'Germany',
L = ['Spain', 'Andorra', 'France', 'Belgium', 'Germany'] ;
X = 'Austria',
L = ['Spain', 'Andorra', 'France', 'Belgium', 'Germany', 'Austria'] .

*/


:- use_module(library(csv)).

:- dynamic arc/2.
:- multifile arc/2.

assert_borders :-
  retractall(arc(_, _)), %retract arc/2 clauses (clear existing facts)
  csv_read_file('GEODATASOURCE-COUNTRY-BORDERS.CSV', Rows), % read csv
  assert_arcs(Rows). 

% assert_arcs/1 on the Rows
assert_arcs([]).

assert_arcs([R | Rows]) :-
  R = row(_, Country1, _, Country2), %extract useful data
  Country1 \= '', %country1 is not empty
  assert(arc(Country1, Country2)), %assert arc
  assert_arcs(Rows). %recursive call on the rest of the rows

assert_arcs([_ | Rows]) :-
  assert_arcs(Rows). %when no matching rule, skip 

/*

It is worth noting that our previous path/3 predicate may get lost in the exponential number of pathways between countries
explored by backtracking in a "generate and test" manner

?- path('France', 'Japan', L).
^CAction (h for help) ? abort
% Execution Aborted

?- path('Spain', 'France', L).
L = ['Spain', 'Andorra', 'France'] ;
^CAction (h for help) ? abort
% Execution Aborted

If interested in pathways of minimal length only, and starting from one given initial vertex,
Dijkstra's vertex marking algorithm for shortest path provides an algorithm with O(v^2) time complexity.
This is still too high complexity however for road maps and GPS navigation for instance.

Search heuristics are necessary and will be presented for this problem in another course.

*/
