/*
CSE 307 - Relational Programming

TD1 initiation to SWI-Prolog, relational databases in Datalog, constraint-based Datalog programs

@author Francois Fages
   

This is a Prolog program file, i.e. containing Prolog facts and Prolog rules.

Comments are either lines starting with % or blocks between / and * as here

You can load this file in Prolog top level and execute queries as follows
  
==
  
fages@222-92 lectures % swipl
Welcome to SWI-Prolog (threaded, 64 bits, version 9.0.4)
SWI-Prolog comes with ABSOLUTELY NO WARRANTY. This is free software.
Please run ?- license. for legal details.

For online help and background, visit https://www.swi-prolog.org
For built-in help, use ?- help(Topic). or ?- apropos(Word).

?- [td1cse307].
true.

?- man(X).
X = pierre ;
X = jean ;
X = robert .

==

We ask you to answer the questions in this file

   - either textual answers in comments

   - or Prolog code by completing this file
   
At the end of the TD session you are asked to upload your file on the Moodle

*/
  

/* PART I. Relational Database
   ---------------------------

Let us first use Prolog facts to represent a family database in extension 

*/
  

man(pierre).
man(jean).
man(robert).
man(michel).
man(david).
man(benjamin).
man(joel).


woman(catherine).
woman(paule).
woman(lucie).
woman(magali).
woman(deborah).
woman(claudine).
woman(vanessa).

% binary fact parent(X, Y) means that X is a direct parent of Y, i.e. Y is a child of X

parent(jean, david).
parent(jean, benjamin).
parent(robert, joel).
parent(robert, deborah).
parent(michel, claudine).
parent(michel, vanessa).
parent(pierre, jean).
parent(pierre, lucie).
parent(pierre, michel).
parent(paule, david).
parent(paule, benjamin).
parent(lucie, joel).
parent(lucie, deborah).
parent(magali, claudine).
parent(magali, vanessa).
parent(catherine, jean).
parent(catherine, lucie).
parent(catherine, michel).


% Defining Prolog rules now

% p :- q. reads as p is implied by q

% p :- q, r. reads as p is implied by q and r


% X is a father of Y if X a parent of Y and X is a man

father(X, Y):- parent(X, Y), man(X).


% the disequality predicate dif(X,Y) constrains X and Y to be different

% it is used below to define the relation X is the brother of Y

brother(X, Y) :- parent(Z, Y), dif(X, Y), parent(Z, X), man(X).


/*
  Let us first play with the interpreter.

  Write Prolog queries for answering the following questions and copy them with all Prolog answers below

  Be careful that in Prolog an indentifier starting with a upper case letter denotes a variable ! 
  Constant names must start with a lower case letter (not a good convention for our database)
  
Question 1
----------

  Write a query to determine whether david and benjamin are brothers ?


Your answer
----------
?- brother(benjamin, david).
true; 
true.


Question 2
----------

 Explain why we get twice the success answer in terms of the search tree


Your answer
----------
For simplicity we replace 'benjamin' by 'ben'
In order to get an answer for the query brother(ben, david), we start the search tree
by looking at the first predicate parent(Z, david). There are two possibilities:

brother(ben, david) -> parent(Z, david), dif(ben, david), parent(Z, ben), man(ben)
 
using parent(jean, david).    1) ->  Z = jean, dif(ben, david), parent(Z, ben), man(ben)
using parent(jean, ben).           -> dif(ben, david), man(ben)
dif(ben, david) is true               -> man(ben)
using man(ben).                          -> true

using parent(paule, david).   2) ->  Z = paule, dif(ben, david), parent(Z, ben), man(ben)
using parent(paule, ben).          -> dif(ben, david), man(ben)
dif(ben, david) is true               -> man(ben)
using man(ben).                         -> true 
 
So we get 'true' in both branches of the search tree.

Correction : the relation is established through both parents
  
Question 3
----------

  Who are the brothers of lucie ?

Your answer
----------
?- brother(X, lucie).
X = jean ;
X = michel ;
X = jean ;
X = michel.


Question 4
----------

  Explain why we get twice the same answers


Your answer
----------
We explain it by drawing the search tree: 

brother(X, lucie)  ->  parent(Z, lucie), dif(X, lucie), parent(Z, X), man(X)

using parent(pierre, lucie).       1) -> Z = pierre, dif(X, lucie), parent(Z, X), man(X)
using parent(pierre, jean).           1.1) -> X = jean, dif(X, lucie), man(X)
dif(jean, lucie) is true                     -> X = jean, man(X)
using man(jean).                               -> true
using parent(pierre, lucie).          1.2) -> X = lucie, dif(X, lucie), man(X)
dif(lucie, lucie) is false                   -> false
using parent(pierre, michel).         1.3) -> X = michel, dif(X, lucie), man(X)
dif(michel, lucie) is true                     -> X = michel, man(X)
using man(michel).                               -> true

using parent(catherine, lucie).    2) -> Z = catherine, dif(X, lucie), parent(Z, X), man(X)
using parent(catherine, jean).           2.1) -> X = jean, dif(X, lucie), man(X)
dif(jean, lucie) is true                        -> X = jean, man(X)
using man(jean).                                 -> true
using parent(catherine, lucie).          2.2) -> X = lucie, dif(X, lucie), man(X)
dif(lucie, lucie) is false                      -> false
using parent(catherine, michel).         2.3) -> X = michel, dif(X, lucie), man(X)
dif(michel, lucie) is true                      -> X = michel, man(X)
using man(michel).                                -> true

Therefore we result with 'X = jean; X = michel; X = jean; X = michel.'
  
  
Question 5
----------

  Who are the two parents of david ?


Your answer
----------
?- parent(X, david), parent(Y, david), dif(X, Y).
X = jean,
Y = paule ;
X = paule,
Y = jean .

Correction : parent(X,david).

If we want to have the answer in this order: mother, father, we add: 
?- parent(X, david), parent(Y, david), dif(X, Y), man(Y).
or: 
?- parent(X, david), parent(Y, david), dif(X, Y), woman(X).
X = paule,
Y = jean .

  
Question 6
----------

  Are there somebody with two fathers in this family ?

Your answer
----------
?- father(X , Y), father(Z, Y), dif(X, Z).
false.



  Let us now program in Prolog by defining new predicates in this file

  You will try your definitions by reloading this file in the Prolog interpreter with the query [tp1inf555].

  Write Prolog rules for defining the following relations:
*/

%   Question 7    mother/2

mother(X, Y):- parent(X, Y), woman(X).

% Question 8.    sister/2

sister(X, Y) :- parent(Z, Y), dif(X, Y), parent(Z, X), woman(X).

% Question 9.	grandparent/2

grandparent(X, Y) :- parent(X, Z), parent(Z, Y).
  
% Question 10.	uncle/2

uncle(X, Y) :-
    dif(U, P),
    parent(P, X),
    brother(U, P).



% Question 11.   aunt/2

aunt(X, Y) :-
    dif(A, P),
    parent(P, X),
    sister(A, P).

% Question 12.	ancestor/2

ancestor(X, Y) :- parent(X, Y).
ancestor(X, Y) :- parent(X, Z), ancestor(Z, Y).

/*
Part II Recursive loan predicate using constraint library over the reals clpr
-----------------------------------------------------------------------------

We have seen in the course the following predicate loan/4 which relates 

  - the amount of money in euros borrowed P
  - during 4 years
  - at yearly interest rate percentile I
  - with yearly repayment R in euros
  - and final balance due B in euros.

The constraints over real numbers are writen between {braces} with that library(clpr)
  
The answers are either values or remaining constraints on the variables.
  
The constraints returned by the constraint solver of that library are not perfectly written, especially for non-linear constraints.

?- loan(1000, 5/100, R, 0).
R = 282.0118326034628.

?- loan(1000, 5/100, 200, B).
B = 353.48125000000005.

?- loan(P, 5/100, 200, 0).
P = 709.190100832472.

?- loan(P, 5/100, R, B).
{B=1.2155062500000002*P-4.310125*R}.

?- loan(P, I, R, B).
{B-_A*I+R-_A=0.0, - ... + R-_B+_A=0.0, ... + ... - _C+_B=0.0, ... - ...


*/

:- use_module(library(clpr)).

loan(P, I, R, B):-
   {B1 = P * (1.0 + I) - R},
   {B2 = B1 * (1.0 + I) - R},
   {B3 = B2 * (1.0 + I) - R},
   {B = B3 * (1.0 + I) - R}.

/*

Question 13
-----------
  
  Write a recursive predicate loan/4 with an extra argument N for any number of years for the loan

?- loan(4, 1000, 5/100, R, 0).
R = 282.0118326034628 ;
false.

?- loan(N, 1000, 5/100, R, 0).
R = 1050.0,
{N=<1.0} ;
  
R = 537.8048780487806,
{_= -1.0+N, N>1.0, N=<2.0} ;
  
R = 367.2085646312451,
{_= -2.0+N, _= -1.0+N, N>2.0, N=<3.0} ;
  
R = 282.0118326034628,
{_= -3.0+N, _= -2.0+N, _= -1.0+N, N>3.0, N=<4.0} .

*/
:- use_module(library(clpr)).

loan(0, P ,  _ , _ , B):- {P = B}.

loan(N, P, I, R, B):-
  {N > 0},
  {B1 = P * (1.0 + I) - R},
  {M = N-1},
  loan(M, B1, I, R, B).

/*
Question 14
-----------
  
  Prove the termination of your recursive program loan(N, P, I, R, B)

  Hint: as always, by giving some complexity measure on the arguments that strictly decreases at each recurive call (trivial here)

Your answer
----------
Here, the value of N is the complexity measure. If N is 0 (base case) then the program returns directly the value P.
Otherwise the value of N is instantiated with a positive integer, which is decremented by 1 in each recursive call
({M = N-1} and M is used in the recursive call). The value of N will necessarily reach 0, which corresponds to the base case stated above.
Thus the recursion will stop at N = 0 which proves termination. 

  
Question 15
-----------
  Prove the correctness of your recursive program loan(N, P, I, R, B) 

  Hint: as seen in the course, this amounts to find a convenient recursion hypothesis, that is

  - one general precondition which will have to be verified at each predicate call

  - one postcondition which will have to verified upon success of the call

  
Your answer
-----------

  Precondition:
  -------------
  We have to check that N >= 0 and that B is a variable that does not have a specific value
  already assigned to it, so that we can assign the result of the call in it. 

  correction: 
    N, P, I, R, B are positive numbers (we could add that N is a positive integer but this is not necessary,
     assuming a minimum cost of 1 year)
  
  Post-condition:
  ---------------
  For each recursive call, we have to make sure that B has been assigned with the correct value 
  from the given formula taking as inputs the updated values of N and P.

  correction :  N, P, I, R, B satisfy the relation given in the statement of the problem, that is

  B is the final balance due after max(1, N) repayments of R euros for borrowing an amount P at yearly interest percentile I.
  

  Proof by induction:
  -------------------
  Base case :  If N = 0, the precondition is trivially satisfied by the initial conditions, 
  and the post-condition is also satisfied (we obtain B = P , as if I = 0 , R = 0 )
  Induction Step: We first check the precondition on N, and create a new variable B1 using the loan formula 
  to update P in the following recursive calls which uses the decremented value of N. 
  This ensures that the value of B will be kept unassigned and passed in the following recursive calls until
  the end is reached and B is finally assigned with a value. 
  Thus we conclude that B is correctly computed for the given inputs, which proves correctness of the recursive case. 

  correction:  When N<=1, max(1,N)=1 and B = P * (1.0 + I) - R indeed satisfies the post-condition

  When N>1, max(1,N)=N. By induction hypothesis, the postcondition is satisfied by (N-1, P * (1.0 + I) - R, I, R, B)

  that is to say B is the final balance due after N-1 yearly repayments for borrowing P * (1.0 + I) - R.

  This entails our postcondition since borrowing P over N years leads the next year to borrow P * (1.0 + I) - R over N-1 years. 

*/
