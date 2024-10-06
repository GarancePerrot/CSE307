/* CSE 307 - Relational Programming

  Ecole Polytechnique Bachelor

  TD3
  ---
   
  Part I:   Fourier's example of linear constraint-based model 
   
  Part II:  Production planning

  Part III: Unitary cost-benefit analysis
 

@author Francois Fages
@license public domain


We shall use library(clpr) for solving linear constraints over the real numbers (floating point numbers).

*/

:- use_module(library(clpr)).


/*
   
  Part I: Fourier's example of linear constraint-based model
  ----------------------------------------------------------

We start with the example of Fourier given in his lecture at Académies des Sciences in 1823
  for illustrating his method for deciding the satisfiability of a finite set of linear inequalities over the real numbers,
  and for modeling decision problems with linear constraints.

In his example, the problem is to determine
  
  - in which coordinates (X,Y)
  
  - a given weight p

  - can be placed on a rectangle-triangle table  ABC with the right corner A in coordinates (0,0), B in (0,20) and C in (20,0)

  - in such a way that each leg of the triangle table does not support more than 1 weight unit.
  
The program below seen in course solves this problem

?- fourier(A,B,C,4,X,Y).
false.
  
?- fourier(A,B,C,3,X,Y).
A = B, B = C, C = 1.0,
X = Y, Y = 6.666666666666667
  
?- fourier(A,B,C,2,X,Y), maximize(X).
B = 1.0,
X = 10.0,
{Y=10.0-10.0*A, C=1.0-A, A=<1.0, A>=0.0}

?- fourier(A,B,C,2,X,Y).
{Y=20.0-10.0*A-10.0*B, X=10.0*B, C=2.0-A-B, A+B>=1.0, B=<1.0, A=<1.0}.
  
*/

fourier(A,B,C,P,X,Y):-
    {0=<A, A=<1, 0=<B, B=<1, 0=<C, C=<1},
    {A+B+C=P},
    {P*X=20*B},
    {P*Y=20*C}.


/*

  Question 1
  ----------

  Query the model to determine the placement of a weight of 2 units minimizing the force on A,
  and explain the result.


  Answer
  ------

?- fourier(A,B,C,2,X,Y), minimize(A).
A = 0.0,
B = C, C = 1.0,
X = Y, Y = 10.0.

A is allowed to be 0 so it is minimized at 0.
B = C satsifies the constraint that the sum of the weights is 2, which gives with the fourier constraints X = Y = 10

A has 0 weight on the coordinates and B and C have the same weight on them, and since X and Y are equal, (X,Y) is the midpoint of the segment BC.



  Question 2
  ----------

  Query the model to determine the region where a weight of 2 units can be placed
  and explain the result in terms of the answer constraints.

  Answer
  ------
?- fourier(A,B,C,2,X,Y).
{Y=20.0-10.0*A-10.0*B, X=10.0*B, C=2.0-A-B, A+B>=1.0, B=<1.0, A=<1.0}.
Since  A, B, C are all in [0,1], in order to have 2 as the sum of the weigths, we add the constraint A+B>=1 and deduce the value of C from A,B. 
Then we deduce the value of X by replacing P by 2 (dependent of B), and the value of Y by replacing C by 2.0-A-B in the last constraint. 
  

-> expecting an interpretation or not?

    
  Part II:   Production planning
  ------------------------------

  We have seen in the first course the following CLP(FD) program 

  cakes(B, C, Profit) :-
    [B, C] ins 0..100,
  
    250*B + 200*C #=< 4000,
    2*B #=< 6,
    75*B + 150*C #=< 2000,
    100*B + 150*C #=< 500,
    75*C #=< 500,
  
    Profit #= 400*B+450*C,
  
    labeling([max(Profit)], [B, C]).

  
  for determining how many of each sort of cakes should be baked in order to maximise the profit, knowing that

  a banana cake sold 4 euros takes

  - 250g of self-raising flour,

  - 2 mashed bananas,

  - 75g sugar

  - and 100g of butter;

  a chocolate cake sold 4.5 euros takes

  - 200g of self-raising flour,

  - 75g of cocoa,

  - 150g sugar

  - and 150g of butter;

  and we have at our disposal

  - 4kg of self-raising flour,

  - 6 bananas,

  - 2kg of sugar,

  - 500g of butter

  - and 500g of cocoa.


  Now, we want to solve a continuous relaxation of the problem where portions of cakes can be produced.
  

  Question 3
  ----------

  Define a CLP(R) predicate cakes(B, C, Profit) to solve the problem with real numbers.

?- cakes(B, C, P).
B = 3.0000000000000018,
C = 1.3333333333333317,
P = 1800.0.
  
*/

:- use_module(library(clpr)).
cakes(B, C, Profit) :-
    {0=<B, B=<100, 0=<C, C=<100},
  
    {250*B + 200*C =< 4000},
    {2*B =< 6},
    {75*B + 150*C =< 2000},
    {100*B + 150*C =< 500},
    {75*C =< 500},
  
    {Profit = 400*B+450*C},
    maximize(Profit).


/*

  Question 4
  ----------

  Define a general predicate 

    production(+Resources, +Products, ?Decisions, ?Profit)

  to solve this kind of production planning problem,
  using the following association list format for representing the data:

  - Resources is a list of terms of the form (resource - quantity) which associates the available quantity of each resource,

  - Products is a list of lists giving for each product its name, price, and association list of quantities of resources used per unit of production,

  and the decision variables are given by

  - the association list Decisions which gives the quantity of each product to produce with a term of the form (product - quantity)

  - the variable Profit for the profit made

  Note that, unlike a matrix-based representation, association lists provide a sparse representation of the data in large size problems with few resources used per product.

  ?- production([
               flour - 4000, bananas - 6, sugar - 2000, butter - 500, cocoa - 500
              ],
              [
               [banana_cake, 400, [flour - 250, bananas - 2, sugar - 75, butter - 100]],
               [chocolate_cake, 450, [flour - 200, cocoa - 75, sugar - 150, butter - 150]]
              ],
              [
               banana_cake - B,
               chocolate_cake - C
              ],
              Profit
             ).
B = 3.0000000000000018,
C = 1.3333333333333317,
Profit = 1800.0.
  
  
*/


:- use_module(library(clpr)).
production(Resources, Products, Decisions, Profit) :-

  bound_decisions(Decisions),
  
  distribute_resources(Resources, Products, Decisions),

  profit_formula(Products, Decisions, Profit),

  maximize(Profit).


bound_decisions([]).
bound_decisions([( _ - Quantity) | Rest]) :-
  {0 =< Quantity},
  {Quantity =< 100},
  bound_decisions(Rest).

distribute_resources([] , _, _).
distribute_resources([(Resource - Quantity) | ResourcesRest], Recipes, Decisions) :-
  distribute_one_resource((Resource - Quantity), Recipes, Decisions, ResourceUsage),
  {ResourceUsage =< Quantity},
  distribute_resources(ResourcesRest, Recipes, Decisions).

distribute_one_resource(_,[],_,0).
distribute_one_resource(_,_,[],0).
distribute_one_resource((Resource - _ ), [[_,_,Recipe] | RecipesRest], [(_ - Variable) | DecisionsRest], ResourceUsage) :-
  (member((Resource - N), Recipe) -> R1 = N * Variable ; R1 = 0),
  distribute_one_resource((Resource - _ ),RecipesRest, DecisionsRest, R2),
  ResourceUsage  = R1 + R2.

profit_formula([],[],0).
profit_formula([[Product, Price,_] | ProductsRest ], [(Product - Variable) | DecisionsRest], Profit) :-
  profit_formula(ProductsRest, DecisionsRest, ProfitRest),
  {Profit = Price * Variable + ProfitRest}.




/*

  Question 5
  ----------

  Give a query to your program to solve the following decision making problem and explain the result.
  

  We want to determine a production plan that maximizes the profit

  - for a company that makes 2 products: B (bands) and C (coils)

  - the demands and maximum quanties to produce are 6000 tonnes for B and 4000 tonnes for C

  - 40h are available for the production,
  
  - 200 tonnes of B can be produced per hour, and 100 tonnes of C per hour,

  - the profit per tonne of B produced is 25 and 30 for C.
  
  
  Hint: determine exactly what are the capacity constraints in this problem.


  Answer:
  -------

?- production([
               max_prod_B - 6000, max_prod_C - 4000, hours - 40
              ],
              [
               [bands, 25, [max_prod_B - 1, hours - 1/200]],
               [coils, 30, [max_prod_C - 1,  hours - 1/100]]
              ],
              [
               bands - B,
               coils - C
              ],
              Profit
             ).

B = 100.00000000000001,
C = 100.0,
Profit = 5500.0 .

The production function advices to produce the same amount of B as C, given that we can produce twice as more B than C
in the same time but they provide less benefit. 
  



  Part III: Benefit-Cost Analysis
  -------------------------------
  

  Question 6
  ----------

  Consider the dual model of the cake model and define the predicate

      dual_cakes(Flour, Bananas, Sugar, Butter, Cocoa, Value)

  to determine the "shadow prices" of the resources, i.e. how more profit would provide 1 unit more for each ingredient in our current production.


Using the formula in the lecture (for resource allocation), we obtain the dual model of the cake model by:
*/

:- use_module(library(clpr)).
dual_cakes(Flour, Bananas, Sugar, Butter, Cocoa, Value):-
    {0=<Flour, 0=<Bananas,0=<Sugar,0=<Butter,0=<Cocoa},
  
    { 400 =< 250*Flour + 2* Bananas + 75 * Sugar + 100 * Butter},
    { 450 =< 200*Flour + 150 * Sugar + 150 * Butter + 75 * Cocoa},
  
    {Value = 4000 * Flour + 6 * Bananas + 2000 * Sugar + 500 * Butter + 500 * Cocoa },
    minimize(Value).

/*

  Question 7
  ----------

  Explain the answer and verify the conclusion using your program production/4


  Answer:
  -------


?- dual_cakes(Flour, Bananas, Sugar, Butter, Cocoa, Value).
Flour = Sugar, Sugar = Cocoa, Cocoa = 0.0,
Bananas = 50.000000000000014,
Butter = 3.0,
Value = 1799.999999999999.


We see that the resource usage cost is almost equal to the demand value, so the costs associated with using the ingredients
is almost entirely covered by the revenue produced by selling the cakes, hence the profit is almost null.


 production([
               flour - 4001, bananas - 6, sugar - 2000, butter - 500, cocoa - 500
              ],
              [
               [banana_cake, 400, [flour - 250, bananas - 2, sugar - 75, butter - 100]],
               [chocolate_cake, 450, [flour - 200, cocoa - 75, sugar - 150, butter - 150]]
              ],
              [
               banana_cake - B,
               chocolate_cake - C
              ],
              Profit
             ).
B = 3.0000000000000018,
C = 1.3333333333333317,
Profit = 1800.0.

And we check that it is the same for adding 1 to each resource one by one.

*/

/*

  Question 8
  ----------

  Define the dual predicate of the production/4 predicate,

      benefit_cost_analysis(+Resources, +Products, ?Marginal_Costs, ?Total_Value)

  to perform a benefit-cost analysis of the resources, using the same representation fo the data as for production/4


*/
