%!prolog

/*

  CSE307 - Relational Programming


  TP6 Natural language processing in concurrent Prolog for querying a database


  François Fages 




  This TP6 is about natural language processing in Prolog.
  Our goal is to query the family database of TP1 in natural language, as follows:
  

?- answer("who is the father of david ?", Answer).
Query = father(_39500,david)
Answer = father(jean, david) 

?- answer("is jean the father of david ?", Answer).
Query = father(jean,david)
Answer = father(jean, david) .

?- answer("is david the father of jean ?", Answer).
Query = father(david,jean)
false.
  
?-  answer("the father of david is the father of benjamin", Answer).
Query = father(_45802,david),father(_45802,benjamin)
Answer =  (father(jean, david), father(jean, benjamin)) 

?- answer("the father of david is the father of jean", Answer).
Query = father(_48298,david),father(_48298,jean)
false.
  
?- answer("who is the ancestor of david ?", Answer).
Query = ancestor(_52524,david)
Answer = ancestor(jean, david) ;
Answer = ancestor(paule, david) ;
Answer = ancestor(pierre, david) ;
Answer = ancestor(catherine, david) ;
false.


  We will give below a simple formal grammar of English and will represent the syntactical structure of a sentence in that language
  by a Prolog term, called the abstract syntax tree, which gives the grammatical rules to apply to derive the sentence
  (quite similarly to TP5 on theorem proving for representing the proof tree of a theorem in an axiomatic theory).

  Key to parsing is the computation of the list of leaves of the abstract syntax tree 
  since they must correspond to the list of words in the sentence.
    

Question 1.

  Define the predicate leaves(Term, List) which gives the list of leaves of any Prolog term, in the left to right order.

?- leaves(f(X,g(b)), L).
L = [X, b] ;
false.

  To this end, you will use the predicates var/1, nonvar/1 to test whether a term is a variable

  and the predicate =../2 to decompose a non-variable term in the list of its head symbol and arguments, e.g. 

  ?- f(X,g(b)) =.. L.
  L = [f, X, g(b)].

  Be careful to handle the special case of the empty list constant which may create loops through decomposition, since
  
  ?- [] =.. L.
  L = [[]].

  ?- [] =.. [[] | []].
  true.

*/


leaves(Term, List) :-
  (   var(Term) ->
      List = [Term]
  ;   nonvar(Term),
      (
          Term = [] ->
          List = []
      ;   Term =.. [Head|Rest],
          leaves_all(Rest, ListR),
          (Rest = [] ->                    %% if Rest is empty then Term is a leaf
              List = [Head|ListR]
          ;                                %% otherwise Term is a compound term
              List = ListR
          )
      )
  ).

leaves_all([], []).
leaves_all([H|T], Leaves) :-
  leaves(H, HLeaves),
  leaves_all(T, TLeaves),
  append(HLeaves, TLeaves, Leaves).


/*

  We will look at the grammar later on, but you can already test your predicate leaves/2 with the grammar
  using the parsing predicates defined below, on the following queries:

?- parse("jean is the father", Syntax_Tree).
false.

?- parse("jean is a father", Syntax_Tree).
Syntax_Tree = s(n(jean), vp(is, np(a, father))) ;
false.

?- parse("jean is the father of david", Syntax_Tree).
Syntax_Tree = s(n(jean), vp(is, npo(the, father, of, david))) ;
false.


*/

parse(String, Syntax_Tree):-
    string_to_word_list(String, Word_List),
    sentence(Syntax_Tree),
    leaves(Syntax_Tree, Word_List).

string_to_word_list(String, Word_List) :-
    split_string(String," ","",String_Word_List),
    maplist(atom_string, Word_List, String_Word_List).

/*

Question 2.

  Define the predicate leaves_linear(Term, List) 

  but using an accumulator to improve the performance of leaves and achieve linear time complexity in the number of nodes in the tree

?- leaves_linear(f(X,g(b)), L).
L = [b, X] ;
false.

  Note that since the list of leaves is reversed in the accumulator,
  the predicate parse_linear defined below for testing your predicate reverses the words of the sentence
  
?- parse_linear("jean is the father of david", Syntax_Tree).
Syntax_Tree = s(n(jean), vp(is, npo(the, father, of, david))) ;
false.
*/

parse_linear(String, Syntax_Tree):-
    string_to_reversed_word_list(String, Reversed_Word_List),
    sentence(Syntax_Tree),
    leaves_linear(Syntax_Tree, Reversed_Word_List).
  
string_to_reversed_word_list(String, Reversed_Word_List) :-
    string_to_word_list(String, Word_List),
    reverse(Word_List, Reversed_Word_List).


leaves_linear(Term, List) :-
  leaves_linear_acc(Term, [], List).
  
leaves_linear_acc(Term, Acc, List) :-
    (   var(Term) ->
        List = [Term | Acc]
    ;   nonvar(Term),
        (
            Term = [] ->
            List = Acc
        ;   Term =.. [Head | Rest],
            leaves_linear_acc_all(Rest, Acc, ListR),
            (Rest = [] ->
                List = [Head | ListR]
            ;
                List = ListR
            )
        )
    ).
  
leaves_linear_acc_all([], Acc, Acc).
leaves_linear_acc_all([H | T], Acc, List) :-
    leaves_linear_acc(H, Acc, AccH),
    leaves_linear_acc_all(T, AccH, List).


/*

Question 3.


  Define the predicate leaves_freeze(Term, List) using an accumulator as before,
  but by freezing the computation of the variable leaves until they become instanciated, as follows:

?- leaves_freeze(f(X,g(b)), L).
L = [b|_64752],
freeze(X, leaves_f(X, [], _328)).

?- leaves_freeze(f(X,g(b)), L), X=h(a,c).
X = h(a, c),
L = [b, c, a].
  
  This is key to replace our previous "generate and test" procedure to parse a sentence
  by a more efficient "constrain and generate" parser defined below
  by posting the leaves_freeze predicate before generating the syntax tree
  as in the parse_freeze definition given below

?- parse_freeze("jean is the father of david", Syntax_Tree).
Syntax_Tree = s(n(jean), vp(is, npo(the, father, of, david))) ;
false. 


*/

parse_freeze(String, Syntax_Tree):-
    string_to_reversed_word_list(String, Reversed_Word_List),
    leaves_freeze(Syntax_Tree, Reversed_Word_List),
    sentence(Syntax_Tree).
  

leaves_freeze(Term, List) :-
  leaves_f(Term, [], List).

leaves_f(Term, Acc, List) :-
    (   var(Term) ->
        freeze(Term, leaves_f(Term, Acc, List))
    ;   nonvar(Term),
        (
            Term = [] ->
            List = Acc
        ;   Term =.. [Head | Rest],
            leaves_f_all(Rest, Acc, ListR),
            (Rest = [] ->
                List = [Head | ListR]
            ;
                List = ListR
            )
        )
    ).
  
leaves_f_all([], Acc, Acc).
leaves_f_all([H | T], Acc, List) :-
    leaves_f(H, Acc, AccH),
    leaves_f_all(T, AccH, List).





/*
    
  We now reacall below the family database with all predicate definitions of the questions in TP1.
  

*/

man(jean).
man(david).
man(benjamin).
man(pierre).
man(robert).
man(michel).
man(joel).

woman(catherine).
woman(paule).
woman(lucie).
woman(magali).
woman(deborah).
woman(claudine).
woman(vanessa).

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

father(X, Y):- parent(X, Y), man(X).

brother(X, Y) :- parent(Z, Y), dif(X, Y), parent(Z, X), man(X).

mother(Mother, Child) :-
    parent(Mother, Child),
    woman(Mother).

sister(Sister, X) :-
    parent(Parent, X),
    dif(X, Sister),
    parent(Parent, Sister),
    woman(Sister).

grandparent(GParent, Child) :-
    parent(Parent, Child),
    parent(GParent, Parent).

uncle(Uncle, Nephew) :-
    parent(Dad, Nephew),
    brother(Uncle, Dad).

aunt(Aunt, Nephew) :-
    parent(Dad, Nephew),
    sister(Aunt, Dad).

ancestor(Aieul, X) :- 
    parent(Aieul, X).
ancestor(Aieul, X) :- 
    parent(Parent, X),
    ancestor(Aieul, Parent).


/*

  We consider a simple grammar of the English to query that database.
  The verb "is" will be used in singular form only.

  The grammar is defined below in Prolog with a predicate for each grammatical unit, called a phrase, composed of one or more words.

  Each phrase predicate has one argument representing the abstract syntax tree (also called derivation tree) for the phrase.

  The phrase itself is given by the list of the leaves of the syntax tree term, as follows

  
?- sentence(T), leaves(T,L).
T = s(n(jean), vp(is, n(jean))),
L = [jean, is, jean] ;
T = s(n(jean), vp(is, n(david))),
L = [jean, is, david] ;
  
...
  
T = s(n(jean), vp(is, np(a, brother))),
L = [jean, is, a, brother] ;
T = s(n(jean), vp(is, np(a, sister))),
L = [jean, is, a, sister] ;
T = s(n(jean), vp(is, np(a, mother))),
L = [jean, is, a, mother] ;
T = s(n(jean), vp(is, np(a, father))),
L = [jean, is, a, father] ;
  
...
  
T = s(n(jean), vp(is, npo(the, brother, of, n(jean)))),
L = [jean, is, the, brother, of, jean] ;
T = s(n(jean), vp(is, npo(the, brother, of, n(david)))),
L = [jean, is, the, brother, of, david] ;
T = s(n(jean), vp(is, npo(the, brother, of, n(benjamin)))),
L = [jean, is, the, brother, of, benjamin] ;
  
...

  
  The parsing predicates defined above were just filtering (parse/2, parse_linear/2) or constraining (parse_freeze/2)
  the leaves of the syntax tree to be the words of the sentence

*/

sentence(closed_question(V, N1, N2, QMark)) :-
  verb(V),
  nounphrase(N1),
  nounphrase(N2),
  q_mark(QMark).

sentence(open_question(Q, V, N, QMark)) :-
    who(Q),
    verb(V),
    nounphrase(N),
    q_mark(QMark).

sentence(s(N, V)):-
    nounphrase(N),
    verbphrase(V).

nounphrase(n(N)):-
    name(N).
nounphrase(np(D, N)):-
    article_general(D),
    noun(N).
nounphrase(npo(D, N, O, P)):-
    article_specific(D),
    noun(N),
    of(O),
    name(P).

verbphrase(vp(V, N)):-
    verb(V),
    nounphrase(N).

verb(is).

article_specific(the).
article_general(a).

of(of).

noun(brother).
noun(sister).
noun(mother).
noun(father).
noun(grandmother).
noun(grandfather).
noun(aunt).
noun(uncle).
noun(ancestor).

name(N):-
    man(N).
name(N):-
    woman(N).

who(who).

q_mark(?).






/*

Question 4.

  Add grammatical rules to the sentence predicates to accept interrogative sentences of two forms:
  - closed questions such as "is jean the father of david ?"
  - open questions such as "who is the father of david ?"
  as follows

?- parse_freeze("is jean the father of david ?", T).
T = closed_question(is, jean, npo(the, father, of, david), ?) ;
false.

?- parse_freeze("who is the father of david ?", T).
T = open_question(who, is, npo(the, father, of, david), ?) ;
false.

?- parse_freeze("is jean david ?", T).
T = closed_question(is, jean, n(david), ?) ;
false.


*/

:- discontiguous sentence/1.



%% I did not manage to do question 5

/*

Question 5.

  Add to the grammatical predicates the construction of the meaning of each phrase
  in the form of a Prolog term which for a sentence will be a Prolog goal to call to query the family database and get the answer(s)
  
  The predicate answer/2 defined below will then allow you to query the database in natural language
  by just executing the Prolog goal of the semantics attached to a "sentence" phrase, as follows

?- answer("who is the father of david ?", Answer).
Query = father(_39500,david)
Answer = father(jean, david) 

?- answer("is jean the father of david ?", Answer).
Query = father(jean,david)
Answer = father(jean, david) .

?- answer("is david the father of jean ?", Answer).
Query = father(david,jean)
false.
  
?-  answer("the father of david is the father of benjamin", Answer).
Query = father(_45802,david),father(_45802,benjamin)
Answer =  (father(jean, david), father(jean, benjamin)) 

?- answer("the father of david is the father of jean", Answer).
Query = father(_48298,david),father(_48298,jean)
false.
  
?- answer("who is the ancestor of david ?", Answer).
Query = ancestor(_52524,david)
Answer = ancestor(jean, david) ;
Answer = ancestor(paule, david) ;
Answer = ancestor(pierre, david) ;
Answer = ancestor(catherine, david) ;
false.

  For this, you will use the following Prolog terms to capture the semantics of each phrase:

  exists(X, exists(Y, brother(X,Y))) for the semantics of a noun such as brother

e.g. using now the following semantical term attached to the noun phrase clause for a brother

noun(brother, exists(X, exists(Y, brother(X, Y)))).
  
  exists(X, Goal) for the semantics of a nounphrase

e.g. using the following semantical term attached to the nounphrase predicate clause in the case of a name

nounphrase(n(N), exists(N, true)):- name(N).


  Goal or (Goal1, Goal2) for the semantics of a sentence

*/
/*
semantics(String, Goal):-
    string_to_reversed_word_list(String, Reversed_Word_List),
    leaves_freeze(Syntax_Tree, Reversed_Word_List),
    sentence(Syntax_Tree, Goal).

answer(String, Goal):-
    semantics(String, Goal),
    write('Query = '), writeln(Goal),
    Goal.
*/


