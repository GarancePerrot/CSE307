/* CSE307 TD4: a toy constraint solver over integers and disjunctive scheduling


  Part I:   Representation of integer variables with interval domains

  Part II:  Representation of constraints

  Part III: Use in disjunctive scheduling


@author Francois Fages
@license public domain

  We use the same syntax as library(clpfd) with the same infix notations for intervals ../2 and constraints #=/2, #=</2 etc.
  
*/
  
:- op(450, xfx, ..). % notation for intervals

:- op(700,xfx,in).   % domain constraint for one variable
:- op(700,xfx,ins).  % domain constraint for a list of variables

:- op(700,xfx,#=).   % constraint predicates to implement
:- op(700,xfx,#\=).
:- op(700,xfx,#>=).
:- op(700,xfx,#=<).
:- op(700,xfx,#>).
:- op(700,xfx,#<).




/*

  

  Part I:   Representation of integer variables with interval domains
  -------------------------------------------------------------------

  
  Our domains are restricted to intervals of integers.

  The interval domain of a variable is represented here

  - by a term domain/3 of the form domain(Min, Max, Constraints)

  - attached to the variable as an attribute using put_attr/2 predicate

  - and is used for representing both the interval domain and the list of constraints posted on the variable.


?- Min..Max = 2..8.
Min = 2,
Max = 8.

?- (X+2 #>= Y) = (Term1 #>= Term2).
Y = Term2,
Term1 = X+2.

?- X in 0..3.
put_attr(X, user, domain(0, 3, [])).

?- X in 0..3, get_domain(X, D).
D = domain(0, 3, []),
put_attr(X, user, domain(0, 3, [])).

*/


%! in(+Var, ?Interval)
% 
% constrains variable Var to belong to an Interval of integer values.
% Either creates, intersects or returns the domain of the variable.

in(X, Min..Max):-
    (
     number(X)
    ->
     Min =< X,
     X =< Max
    ;
     get_attr(X, user, Domain)
    ->
     domain_intersection(domain(Min, Max, []), Domain, Domain_intersection),
     put_attr(X, user, Domain_intersection)
    ;
     put_attr(X, user, domain(Min, Max, []))
    ).


%! get_domain(+Var, ?Domain)
%
% true if Var is a variable with Domain (by default 0..1000)
get_domain(X, Domain):-
    var(X),
    (
     get_attr(X, user, Domain)
    ->
     true
    ;
     Domain = domain(0, 1000, []),
     put_attr(X, user, Domain)
    ).


%! set_domain(+Var, +Domain)
%
% imperatively sets Domain to variable Var

set_domain(X, Domain):-
    put_attr(X, user, Domain).


/*
  QUESTION 1
  ----------

  Define the predicate ins(+VarList, +Interval) to constrain all variables in a list to belong to some interval domain.

?- [X, Y] ins 0..10.
put_attr(X, user, domain(0, 10, [])),
put_attr(Y, user, domain(0, 10, [])).

*/
%We iterate over the list and call the in predicate defined above

ins([], _).
ins([Var | VarList], Interval) :-
    in(Var, Interval),
    ins(VarList, Interval).


/*

  Question 2
  ----------

  Define predicate indomain/1 to non-deterministically instantiate a variable to the values in its domain

  Hint: use Prolog predicate between/3

?- X in 1..3, indomain(X).
X = 1 ;
X = 2 ;
X = 3.

*/
%First we get the domain, its boundaries and then call the between predicate

indomain(X) :-
    get_domain(X, D),
    D = domain(Min, Max, []),
    between(Min, Max, X).


/*

  Question 3
  ----------

  Define predicate label/1 to non-deterministically instanciate a list of variables

*/
%We iterate over the variables and call the predicate indomain defined above to instantiate them
label([]).
label([Var | VarList]) :-
    indomain(Var),
    label(VarList).
    
/*

  Part II:  Representation of constraints
  ---------------------------------------


  QUESTION 4
  ----------

  Define the inequality predicates #<, #>=, #> and the equality predicate #=/2 using the #=< predicate that will be defined later on.

  Hint: you just have to define those 4 predicates by 4 clauses using the infix notations defined above.

*/
%Each time we use the predicate defined just above
% :- op(700,xfx,#=). 
X #= Y :- X #=< Y, Y #=< X.

%:- op(700,xfx,#\=).
X #\= Y :- \+ (X #= Y).

%:- op(700,xfx,#<). 
X #< Y :- X #=< Y, X #\= Y.

%:- op(700,xfx,#>=). 
X #>= Y :- Y #=< X.

%:- op(700,xfx,#>).   
X #> Y :- Y #< X.




/*

  Let us now get into the use of attributed variables

  - not only for representing the domain

  - but for implementing domain filtering and constraint propagation.

  The unification of domain variables defined by attr_unify_hook/2 predicate, basically

  - intersects variable domains

  - and checks constraints with the new bounds

  Domain reduction is performed by

  - using Prolog evaluable arithmetic predicates such as is/2 =</2 </2 etc.
    to implement general constraints #=, #=<, #<, etc. 

  - changing the domain attribute using put_attr/2


  The following clauses implement these features plus two simple cases for the #=</2 constraint


?- [X, Y] ins 0..10, X #=< Y.
put_attr(X, user, domain(0, 10, [X#=<Y])),
put_attr(Y, user, domain(0, 10, [X#=<Y])).

?- [X, Y] ins 0..10, X #=< Y, X #=<5.
put_attr(X, user, domain(0, 5, [X#=<Y])),
put_attr(Y, user, domain(0, 10, [X#=<Y])).

?- [X, Y] ins 0..10, X #=< Y, X #=<5, 3 #=< Y.
put_attr(X, user, domain(0, 5, [X#=<Y])),
put_attr(Y, user, domain(3, 10, [X#=<Y])).

?- [X, Y] ins 0..10, X #< Y.
put_attr(X, user, domain(0, 9, [X+1#=<Y])),
put_attr(Y, user, domain(1, 10, [X+1#=<Y])).

?- [X, Y] ins 0..10, X #< Y, Y #< X.
false.

*/
  
%! attr_unify_hook(+AttValue, +Term)
% 
% This predicate is always called right after the unification of one attributed variable.
% When unified with another attributed variable the intersection of the domains will be the new domain of both variables.


attr_unify_hook(Xatt, Y):-
    (
     get_domain(Y, Yatt)	% unifying 2 domain variables
    ->
     domain_intersection(Xatt, Yatt, Zatt),
     Zatt = domain(Zmin, Zmax, Constraints),
     (
      Zmin=Zmax
     ->
      Y=Zmin,
      iterate_constraints(Constraints)
     ;
      set_domain(Y, Zatt),
      iterate_constraints(Constraints)
     )
    ;
     var(Y)			% unifying with a non-domain variable
    ->
     set_domain(Y, Xatt)
    ;
     number(Y)			% domain variable unified with a number
    ->
     Xatt = domain(Min, Max, Constraints),
     Min =< Y,
     Y =< Max,
     iterate_constraints(Constraints)
    ; 
     false
    ).

%! domain_insersect(DomainX, DomainY, DomainZ)
%
% DomainZ = DomainX inter DomainY

domain_intersection(domain(Xmin, Xmax, Xconstraints), domain(Ymin, Ymax, Yconstraints), domain(Zmin, Zmax, Zconstraints)):-
    Zmin is max(Xmin, Ymin),
    Zmax is min(Xmax, Ymax),
    Zmin=<Zmax,
    append(Xconstraints, Yconstraints, Zconstraints).

%! iterate_constraints(Constraints)
% 
% calls the constraints again.
% A constraint entailment check is missing to simplify that list of constraints.

iterate_constraints([]).
iterate_constraints([Constraint | Constraints]):-
    call(Constraint), 
    iterate_constraints(Constraints).

%! add_element(+Term, +List, ?NewList)
%
% add constraint to the list if not already identically present

add_element(Term, List, NewList):-
    (
     member_identical(List, Term)
    -> 
     NewList = List
    ;
     NewList = [Term | List]
    ).

member_identical([Term1 | List], Term):-
    (
     Term1 == Term
    ->
     true
    ;
     member_identical(List, Term)
    ).

%! remove_element(+Term, +List, ?NewList)
%
% remove all identical occurrences of term from the list

remove_element(Term, List, NewList):-
    remove_identical(List, Term, [], NewList).


remove_identical([], _, List, List).
remove_identical([Term1 | Tail], Term, List, NewList):-
    (
     Term1 == Term
    ->
     remove_identical(Tail, Term, List, NewList)
    ;
     remove_identical(Tail, Term, [Term1 | List], NewList)
    ).

/*
  Let us now give the implementation of X #=< Y in the case where X and Y are two variables

  The cut ! is important for

  - not checking the other clauses you will be asked to write for the other cases

  - and not unifying a domain variable with a complex expressions
*/

%! X #=< Y constraint clause for the case where X and Y are variables
% 
% The clause follows the general constraint propagation rules given in the course for entailment, look ahead, forward checking, etc.


X #=< Y :-
    get_domain(X, domain(Xmin, Xmax, Xconstraints)),
    get_domain(Y, domain(Ymin, Ymax, Yconstraints)),
    !,
    (
     Xmax =< Ymin		% entailment
    ->
     remove_element(X #=< Y, Xconstraints, Xconstraints2), 
     remove_element(X #=< Y, Yconstraints, Yconstraints2), 
     set_domain(X, domain(Xmin, Xmax, Xconstraints2)),
     set_domain(Y, domain(Ymin, Ymax, Yconstraints2))
    ;
     Xmin > Ymax		% disentailment
    ->
     false
    ;
     Xmin = Ymax		% forward checking
    ->
     X = Xmin,
     Y = Ymax 
    ;				% look ahead: updating bounds
     (
      Xmax > Ymax
     ->
      Xmax2 = Ymax
     ;
      Xmax2 = Xmax
     ),
     (
      Ymin < Xmin
     ->
      Ymin2 = Xmin
     ;
      Ymin2 = Ymin
     ),
     				%add_constraint and iterate if necessary
     add_element(X #=< Y, Xconstraints, Xconstraints2),
     add_element(X #=< Y, Yconstraints, Yconstraints2),
     set_domain(X, domain(Xmin, Xmax2, Xconstraints2)),
     set_domain(Y, domain(Ymin2, Ymax, Yconstraints2)),
     (
      (Xmax > Ymax ; Ymin < Xmin)
     ->
      iterate_constraints(Xconstraints2),
      iterate_constraints(Yconstraints2)
     ;
      true
     )
    ).

/*

  Question 5
  ----------

  Add two clauses for the case C #=< D and C #=< Y where C, D are numbers and Y is a variable

*/
%For C and D numbers:
C #=< D :-
    number(C),
    number(D),
    C =< D.

%For C number, Y variable:
C #=< Y :-
    number(C),
    get_domain(Y, domain(Ymin, Ymax, Yconstraints)),
    !,
    (
     C =< Ymin		
    ->
     true
    ;
     C > Ymax		
    ->
     false
    ;
     C = Ymax		
    ->
     Y = Ymax
    ;				
     add_element(C #=< Y, Yconstraints, Yconstraints2),
     set_domain(Y, domain(_, Ymax, Yconstraints2)),
     iterate_constraints(Yconstraints2)
    ).


/*write(Xmax),

  QUESTION 6
  ----------

  Add one clause for the symmetrical case X #=< D between one domain variable X and a number D


*/

X #=< D :-
    number(D),
    get_domain(X, domain(Xmin, Xmax, Xconstraints)),
    !,
    (
     Xmax =< D		
    ->
     true
    ;
     Xmin > D
    ->
     false
    ;	
     Xmin = D
    ->
     X = Xmin
    ;			
     				%add_constraint and iterate if necessary
     add_element(X #=< D, Xconstraints, Xconstraints2),
     set_domain(X, domain(Xmin, _ , Xconstraints2)),
     iterate_constraints(Xconstraints2)
    ).



/*

  QUESTION 7
  ----------

  Add clauses for the cases where

  - one term of the inequality is the sum X+A of a variable and an integer number

  - and the other term is an integer number B or a variable Y (i.e. the important case of scheduling problems ! X + C #=< Y )

  Hint: Generalize the clause given for 2 variables X #=< Y (that clause now corresponds to a particular case for C=0)

*/

%% I did not manage to solve the infinite loop...

X + A #=< Y :-
    number(A),
    get_domain(X, domain(Xmin0, Xmax0, Xconstraints)),
    get_domain(Y, domain(Ymin, Ymax, Yconstraints)),
    !,
    Xmin is Xmin0 + A,
    Xmax is Xmax0 + A,
    (
     Xmax =< Ymin		% entailment
    ->
     remove_element(X + A #=< Y, Xconstraints, Xconstraints2), 
     remove_element(X + A #=< Y, Yconstraints, Yconstraints2), 
     set_domain(X, domain(Xmin0, Xmax0, Xconstraints2)),
     set_domain(Y, domain(Ymin, Ymax, Yconstraints2)),
     Xmin is Xmin0 + A,
     Xmax is Xmax0 + A
    ;
     Xmin is Xmin0 + A ,
     Xmin > Ymax		% disentailment
    ->
     false
    ;
     Xmin is Xmin0 + A ,
     Xmin = Ymax		% forward checking
    ->
     X = Xmin,
     Y = Ymax 
    ;				% look ahead: updating bounds
     (
      Xmax is Xmax0 + A ,
      Xmax > Ymax
     ->
      Xmax2 = Ymax
     ;
      Xmax2 = Xmax
     ),
     (
      Xmin is Xmin0 + A ,
      Ymin < Xmin
     ->
      Ymin2 = Xmin
     ;
      Ymin2 = Ymin
     ),
     				%add_constraint and iterate if necessary
     add_element(X + A #=< Y, Xconstraints, Xconstraints2),
     add_element(X + A #=< Y, Yconstraints, Yconstraints2),
     set_domain(X, domain(Xmin0, Xmax2, Xconstraints2)),
     set_domain(Y, domain(Ymin2, Ymax, Yconstraints2)),
     Xmin is Xmin0 + A ,
     Xmax is Xmax0 + A,
     ( 
      (Xmax > Ymax ; Ymin < Xmin)
     ->
      writeln(Xmax),
      writeln(Xmin),
      writeln(Xmin0 - Xmax2),
      writeln(Ymin2 - Ymax),
      iterate_constraints(Xconstraints2),
      iterate_constraints(Yconstraints2)
     ;
      true
     )
    ).



    
/*

  Part III: Use in disjunctive scheduling
  ---------------------------------------

  Let us return to our scheduling model, here without labeling, since we want to focus on constraint propagation only.
  
*/

house(Starts, End) :-
    Starts = [Foundations, Interior_walls, Exterior_walls, Chimney, Roof, Doors, Tiles, Windows],

    Durations_Sum is 7+4+3+3+2+2+3+3, 

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
    Tiles+3 #=< End.


/*
   

  QUESTION 8
  ----------

  Test your program on the scheduling problem for the construction of a house without labeling (i.e. no value enumeration nor minimisation)

  Check that the minimimum value for the End task give the optimal cost

  Give a query to enumerate all optimal solutions

  Answer here:
  ------------
Test your program on the scheduling problem for the construction of a house without labeling:
?- house(Starts, End),
   End #=< Durations_Sum,
   Foundations + 7 #=< Interior_walls,
   Foundations + 7 #=< Exterior_walls,
   Foundations + 7 #=< Chimney,
   Exterior_walls + 3 #=< Roof,
   Exterior_walls + 3 #=< Windows,
   Interior_walls + 4 #=< Doors,
   Chimney + 3 #=< Tiles,
   Roof + 2 #=< Tiles,
   Windows + 3 #=< End,
   Doors + 2 #=< End,
   Tiles + 3 #=< End.

Check that the minimimum value for the End task gives the optimal cost:
?- house(Starts, End), 
   minimize(labeling([], [End|Starts]), Cost).

Give a query to enumerate all optimal solutions:
?- house(Starts, End), 
   minimize(labeling([], [End|Starts]), Cost),
   labeling([minimize(Cost)], [End|Starts]).

  
*/

    
/*

  QUESTION 9
  ----------

  - Add mutual exclusion constraints between tasks sharing some same resources to the house work problem

  - Model the problem using disjunctive precedence constraints

  - Choose to implement disjunctive either as choice points or by reification with boolean variables

  - Explain the results



 */




 