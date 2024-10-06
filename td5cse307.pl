%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                                         %
% CSE 307: Relational Programming - F. Fages              %
%                                                         %
%                                                         % 
% TD5: Metainterpretation                                 %
%      Metainterpreter for complete search                %
%      Theorem proving in group theory                    %
%                                                         %
%                                                         %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

				
% For integer arithmetic we prefer to use CLP(FD) rather than Prolog evaluable predicates

:- use_module(library(clpfd)).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% PART I. Meta interpreter for complete search %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

/*
 The following meta-interpreter mimics the Prolog strategy for answering Prolog queries, i.e.
 - selection of the left-most subgoal of the goal to solve
 - executing that subgoal if it is a built-in predicate
 - or rewriting that subgoal with the body of the first rule with a unifiable head
 - continuation of the resolution and exploration of the other rules by depth-first backtracking search

*/


solve((Goal1, Goal2)) :-              %% solve a conjunction of goals
  solve(Goal1),
  solve(Goal2).

solve(Goal) :-
   predicate_property(Goal, built_in), %% Goal is a built-in predicate
   Goal \= (_, _),                     %% Goal is not a conjunction
   Goal \= (_; _),                     %% Goal is not a disjunction
   call(Goal).                         %% call directly 

solve(Head) :-
  \+ predicate_property(Head, built_in), %% Goal is not a built-in predicate
  clause(Head, Body),                    %% look for a clause that has a Head and Body
  solve(Body).                          


/*

Question 1.

  Add clauses to that metainterpreter to solve disjunctive goals of the form (Goal1 ; Goal2)
  
*/

solve((Goal1 ; Goal2)) :-
  (   solve(Goal1)
  ;   solve(Goal2)
  ).



%  Not surprinsingly, this meta-interpreter will loop forever without finding the success answer on the following predicate

loop(X, Y):- loop(Y, X).
loop(a, b).


/*

  We thus want to define a metainterpreter which does not loop on such an example and explores all branches of the search tree in a fair manner.

  This is possible by using iterative deepening instead of depth-first search.

  Iterative deepening performs a depth-first search with a bound on the depth of the search tree to be explored.

  That bound on the depth is increased by 1 iteratively, starting at depth 0.

  Each clause resolution step along a branch of the search tree increases the current length of the derivation by one.

  The execution of built-in predicates counts for 0 resolution step and does not increase the length of the derivation.

  

Question 2.

  Define the predicate search(Goal) to solve a Prolog goal by iterative deepening

  using an auxiliary predicate search(Goal, Current_depth, Bound_depth, Success_depth)

*/



%%calling helper predicate
search(Goal):-
  ( length(_,N),
  search(Goal, 0, N, N) 
    ;
    search(Goal, 0, N, N)
  ).

%%recursive case : DFS search by updating bounds
search(Goal, Current_depth, Bound_depth, Success_depth) :-
    Current_depth =< Bound_depth,
    (
        predicate_property(Goal, built_in),
        Goal \= (_, _),
        Goal \= (_; _),
        call(Goal),
        Current_depth #= Success_depth
    ;
        \+ predicate_property(Goal, built_in),
        clause(Goal, Body),
        Next_depth #= Current_depth + 1,
        search(Body, Next_depth, Bound_depth, Success_depth)
    ).


%%conjunction
search((Goal1, Goal2), Current_depth, Bound_depth, Success_depth_2) :-
  Next_depth #= Current_depth + 1,
  search(Goal1, Next_depth, Bound_depth, Success_depth),
  search(Goal2, Success_depth, Bound_depth, Success_depth_2).

%%disjunction
search((Goal1 ; Goal2), Current_depth, Bound_depth, Success_depth) :-
    (   search(Goal1, Current_depth, Bound_depth, Success_depth)
    ;   search(Goal2, Current_depth, Bound_depth, Success_depth)
    ).


  /*
  
Question 3. Check that you can now enumerate the successes of the looping predicate, by copying the execution of query below

Answer here
-----------

?- search((loop(X,Y))).
true .


    BUT does an error when I type ; after true
*/


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% PART II. Theorem proving     %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

/*
   Let us consider group theory, usually presented with the following axioms:

  - existence of a left neutral element e for any element x, we have for all x e*x=x,

  - existence of a left inverse i(x) for any x, we have for all x exists y y*x=e, i.e. by skolemization noting i() that inverse: for all x i(x)*x=e,

  - associativity of the group operator *, we have for all x,y,z (x*y)*z=x(y*z)

  - plus the logical axioms of equality =

  

  A more succinct presentation for automated theorem proving in Prolog without the axioms of equality is however possible,

  without loss of generalization, for proving expressions of the form x*y=z written o(x,y,z)

  In that representation, the axiom of associativity axiom is written as follows:

  for all x,y,z,u,v o(x,y,u) /\ o(y,z,v) ==> (o(u,z,w) <==> o(x,v,w))

  
  
  We can then express the axioms of group theory with the following Prolog program using a binary predicate

  proof(Proposition, Proof)

  where the first argument is a proposition to prove and the second is one proof of it, as follows
  
*/



proof(o(e,X,X), e).

proof(o(i(X),X,e), i).

proof(o(U,Z,W), l(P,Q,R)) :-
  proof(o(X,Y,U), P),
  proof(o(Y,Z,V), Q),
  proof(o(X,V,W), R).

proof(o(X,V,W), r(P,Q,R)) :-
  proof(o(X,Y,U), P),
  proof(o(Y,Z,V), Q),
  proof(o(U,Z,W), R).

  /*


Question 4. Show with 3 simple queries that the left neutral element is right neutral element,
    the left inverse is right inverse and the double inverse is the identity.

%%some weird outputs

Answer here
-----------
?- proof(o(e, X, X), P1),proof(o(X, e, X), P2).     %% why X = e ? 
X = P1, P1 = P2, P2 = e .


?- proof(o(i(X),X,e), P1), proof(o(X,i(X),e), P2).
X = i(i(X)), P1 = P2, P2 = i.

?- proof(o(e, i(i(X)), X), P).
X = i(i(X)), P = e.


    
Question 5 on proof-based generalization.
-----------------------------------------
    
    Sometimes the proof of a proposition proves a more general theorem.

    Run the above queries with the proofs computed above as inpout to get the most general theorems proved as output

Answer here
-----------

?- proof(o(e, X, X), e), proof(o(X, e, X), e).
X = e.

?- proof(o(i(X),X,e), i), proof(o(X,i(X),e), i).
X = i(i(X)).
    
?- proof(o(e, i(i(X)), X), e).
X = i(i(X)).


    Let us now show that any non-empty subset S stable by division (i.e. multiplication by an inverse) is a subgroup.

    

    We thus assume the existence of one element a in S with the axiom s(a)

    plus the stability by division axiom, for all x,y  s(x) /\ s(y) ==> s(x*i(y))

    

Question 6. Add clauses to the proof predicate to implement those assumptions and prove properties of S

  */  









/*

Question 7. Show with queries that S is a group.

Answer here
-----------








  

*/ 