From elpi Require Import elpi.
(*
  should start with above line
  before typing in examples from
  https://lpcic.github.io/coq-elpi/tutorial_elpi_lang.html

  Syntax highlithing for this Coq-Elip script may not work right after the codespace setup.
  Just refresh the browser and syntax highlithing will start to work in the codespace vscode web.
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

Elpi Query lp:{{
    A = 23, age P A, Msg = "is 23 years old", coq.say P Msg
}}.

Elpi Query lp:{{
   age P A, coq.say "I picked P =" P,
   age Q A, coq.say "I picked Q =" Q,
   not(P = Q),
   coq.say "the last choice worked!",
   coq.say P "and" Q "are" A "years old"
}}.

Elpi Accumulate lp:{{
    pred older o:person, o:person.
    older P Q :- age P N, age Q M, N > M.
}}.

Elpi Query lp:{{
    older bob X,
    coq.say "bob is older than" X
}}.

Elpi Query lp:{{
    older bob X, older mallory X,
    coq.say "both bob and mallory are older than" X
}}.

Elpi Query lp:{{
    F = (x\ age alice x),
    coq.say "F =" F,
    coq.say "F 20 =" (F 20),
    coq.say "F 23 =" (F 23)
}}.

Elpi Program stlc lp:{{
    kind  term  type.
    type  app   term -> term -> term.
    type  fun   (term -> term) -> term.
}}.

Elpi Accumulate lp:{{
    pred whd i:term, o:term.
    whd (app Hd Arg) R :- whd Hd (fun F), !, whd (F Arg) R.
    whd X R :- R = X.
}}.

Elpi Query lp:{{
    I = (fun x\x),
    whd I T, coq.say "λx.x ~>" T,
    whd (app I I) T1, coq.say "(λx.x) (λx.x) ~>" T1
}}.

Elpi Accumulate lp:{{
    type foo, bar term.
}}.

Elpi Query lp:{{
    Fst = fun (x\ fun (y\ x)),
    T = app (app Fst foo) bar,
    whd T T1, coq.say "(Fst foo bar) ~>" T1,
    S = app foo bar,
    whd S S1, coq.say "(foo bar) ~>" S1
}}.

(*
Elpi Bound Steps 10000. (* to avoid hanging from Elpi *)
Elpi Query lp:{{
    D = (fun x\ app x x),
    Omega = app D D,
    whd Omega Hummm, coq.say "not going to happen" Hummm
}}.
Elpi Bound Steps 0. (* reset bound for stpes *)
*)

Elpi Accumulate lp:{{
    kind ty type.
    type arr ty -> ty -> ty.

    pred of i:term, o:ty.
    of (app Hd Arg) B :- of Hd (arr A B), of Arg A.
    of (fun F) (arr A B) :- pi x\ of x A ==> of (F x) B.
}}.

Elpi Query lp:{{
    of (fun x\ x) T, coq.say "|- (λx.x) :" T
}}.

Elpi Query lp:{{
    of (fun x\ fun y\ x) T, coq.say "|- (λx.λy.x) :" T
}}.

Elpi Query lp:{{
    Delta = fun (x\ app x x),
    (of Delta _Ty ; coq.say "Error:" Delta "has no type")
}}.


Elpi Program peano lp:{{

kind nat type.
type z nat.
type s nat -> nat.

pred add o:nat, o:nat, o:nat.

add (s X) Y (s Z) :- add X Y Z.
add z X X.

}}.

Elpi Query lp:{{
    add (s (s z)) (s z) R, coq.say "2 + 1 =" R
}}.

(*
Elpi Bound Steps 10000. (* to avoid hanging from Elpi *)
Elpi Query lp:{{
    add X (s z) Y,
    coq.say X "+ 1 =" Y
}}.
Elpi Bound Steps 0. (* reset bound for stpes *)
*)

Elpi Program peano2 lp:{{

kind nat type.
type z nat.
type s nat -> nat.

pred sum i:nat, i:nat, o:nat.

sum (s X) Y (s Z) :- sum X Y Z.
sum z X X.
sum _ _ _ :-
  coq.error "nothing matched but for this catch all clause!".

}}.

(* Elpi Query lp:{{ sum X (s z) Y }}. *)

Elpi Program peano3 lp:{{
    kind nat type.
    type z nat.
    type s nat -> nat.

    pred sum i:nat, i:nat, o:nat.

    sum (s X) Y (s Z) :- sum X Y Z.
    sum z X X.
    sum X Y Z :- var X, declare_constraint (sum X Y Z) [X].
}}.

Elpi Query lp:{{
    sum X (s z) Y, X = z,
    coq.say "Y =" Y
}}.

Elpi Query lp:{{

    sum X (s z) Y,
    print_constraints, coq.say "Currently Y =" Y,
    X = s Z,
    print_constraints, coq.say "Currently Y =" Y,
    Z = z,
    coq.say "Finally Y =" Y

}}.

Elpi Accumulate lp:{{
    pred even i:nat.
    pred odd  i:nat.
}}.

(*
Elpi Query lp:{{ even (s X), odd (s X) }}. (* hum, not nice *)
*)

Elpi Accumulate lp:{{
    constraint even odd {
        rule (even X) (odd X) <=>
        (coq.say "cannot be even and odd at the same time", fail).
    }
}}.

(* Elpi Query lp:{{ even (s X), odd (s X) }}. (* fails *) *)

Elpi Program function lp:{{
    pred make-palindrome i:list A, o:list A.
    make-palindrome L Result :- std.rev  L Tmp, std.append L Tmp Result.
}}.

Elpi Query lp:{{
    make-palindrome [1,2,3] A,
    coq.say "palindrome of [1,2,3] is" A
}}.

Elpi Accumulate lp:{{
    pred make-palin i:list A, o:list A.
    make-palin L Result :- std.append L {std.rev L} Result.
}}.

Elpi Query lp:{{
    make-palin [1,2,3] A,
    coq.say "palindrome of [1,2,3] is" A
}}.

Elpi Query lp:{{
    calc ( "result " ^ "=" ) X,
    Y is 3 + 2,
    coq.say X Y 
}}.

Elpi Query lp:{{ coq.say "result =" {calc (2 + 3)} }}.

Elpi Accumulate lp:{{
    pred bad i:list int, o:list int.
    bad L Result :- std.map L (x\ r\ TMP is x + 1, r = TMP) Result.

    pred good i:list int, o:list int.
    good L Result :- std.map L (x\ r\ r is x + 1) Result.

    pred good2 i:list int, o:list int.
    good2 L Result :- std.map L (x\ r\ sigma TMP\ TMP is x + 1, r = TMP) Result.
}}.

Elpi Query lp:{{
    % not(bad [1,2,3] A)
    good [1,2,3] A
    % good2 [1,2,3] A
}}.

Elpi Query lp:{{ pi x\ sigma Y\ Y = x, coq.say "Y =" Y }}.

(* Elpi Query lp:{{ sigma Y\ pi x\ Y = x, coq.say "Y =" Y }}. *)


Elpi Trace Browser.

Elpi Query stlc lp:{{ % We run the query in the stlc program

    of (fun (x\ fun y\ x)) Ty, coq.say Ty

}}.

Elpi Trace Off.

