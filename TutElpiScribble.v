From elpi Require Import elpi.
(*
  should start with above line
  before typing in examples from
  https://lpcic.github.io/coq-elpi/tutorial_elpi_lang.html

  Syntax highlithing for this Coq-Elip script may not work right after the codespace setup.
  Just refresh the browser and syntax highlithing will start to work in the codespace web-vscode.
*)

Elpi Program tutorial lp:{{

  kind person  type.
  type mallory, bob, alice  person.

}}.

Elpi Accumulate lp:{{

  pred age o:person, o:int.

  age mallory 23.
  age bob 23.
  age alice 20.

}}.

Elpi Query lp:{{

  age alice A, coq.say "The age of alice is" A

}}.

Elpi Accumulate lp:{{

  pred older o:person, o:person.
  older P Q :- age P N, age Q M, N > M.

}}.

Elpi Query lp:{{

  older bob X,
  coq.say "bob is older than" X

}}.

Elpi Program stlc lp:{{

  kind  term  type.

  type  app   term -> term -> term.
  type  fun   (term -> term) -> term.

}}.

Elpi Accumulate lp:{{

  pred whd i:term, o:term.

  % when the head "Hd" of an "app" (lication) is a
  % "fun" we substitute and continue
  whd (app Hd Arg) Reduct :- whd Hd (fun F), !,
    whd (F Arg) Reduct.

  % otherwise a term X is already in normal form.
  whd X Reduct :- Reduct = X.

}}.

Elpi Query lp:{{

  I = (fun x\x),
  whd I T, coq.say "λx.x ~>" T,
  whd (app I I) T1, coq.say "(λx.x) (λx.x) ~>" T1

}}.

Elpi Accumulate lp:{{

  kind  ty   type.           % the data type of types
  type  arr  ty -> ty -> ty. % our type constructor

  pred of i:term, o:ty. % the type checking algorithm

  % for the app node we ensure the head is a function from
  % A to B, and that the argument is of type A
  of (app Hd Arg) B :-
    of Hd (arr A B), of Arg A.

  % for lambda, instead of using a context (a list) of bound
  % variables we use pi and ==> , explained below
  of (fun F) (arr A B) :-
    pi x\ of x A ==> of (F x) B.

}}.

Elpi Trace Browser.
(*
Elpi Query stlc lp:{{ % We run the query in the stlc program

  of (fun (x\ fun y\ x)) Ty, coq.say Ty

}}.
*)
Elpi Trace Off.
