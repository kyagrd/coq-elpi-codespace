From elpi Require Import elpi.

(* This is a simple example of bisimulation, written in Elpi,
   a logic programming language, in a Coq embedded evironment.

   The code defines a pair fo simple labeld transition systems
   and a bisimulation prediate. The bisimulation predicate
   uses the "foreach2" prodicate from the book
   "Higher-Order Logic Programming"
   by Gopalan Nadathur and Dale Miller.
   
https://cs.stackexchange.com/questions/541/when-are-two-simulations-not-a-bisimulation
 *)

Elpi Program bisim lp:{{
    kind proc  type.
    type s, r, p, q  proc.
    type s', p', q'  proc.

    kind act  type.
    type c, t  act.
}}.

Elpi Accumulate lp:{{
    pred step o:proc, o:act, o:proc.

    step s c r.
    step s c p.
    step p t q.

    step s' c p'.
    step p' t q'.
}}.

Elpi Query lp:{{
    step s c X
}}.

Elpi Query lp:{{
    step s c X, step X A Y, coq.say "step" X A Y
}}.

Elpi Accumulate lp:{{
    pred foreach2 o:act -> proc -> prop, o:act -> proc -> prop.
    foreach2 F G :- not(sigma A\ sigma X\ F A X, not (G A X)).

    pred sim  o:proc, o:proc.
    sim P Q :- foreach2 (A\P'\ step P A P')
                        (A\P'\ sigma Q'\ step Q A Q', sim P' Q').

    pred bisim  o:proc, o:proc.
    bisim P Q :- foreach2 (A\P'\ step P A P')
                          (A\P'\ sigma Q'\ step Q A Q', bisim P' Q'),
                 foreach2 (A\Q'\ step Q A Q')
                          (A\Q'\ sigma P'\ step P A P', bisim P' Q').

%% foreach2 없이 풀어서 쓴 코드
%    pred sim  o:proc, o:proc.
%    sim P Q :- not( sigma A\ sigma P'\ step P A P',
%                    not (sigma Q'\ step Q A Q', sim P' Q') ).
}}.

Elpi Query lp:{{
    P = s, Q = s', (bisim P Q,
    coq.say "bisim" P Q ; coq.say "not bisim" P Q).
}}.

Elpi Query lp:{{
    P = q, Q = q', (sim P Q,
    coq.say "sim" P Q ; coq.say "not sim" P Q).
}}.

Elpi Query lp:{{
    P = r, Q = p', (sim P Q,
    coq.say "sim" P Q ; coq.say "not sim" P Q).
}}.

Elpi Query lp:{{
    P = p', Q = r, (sim P Q,
    coq.say "sim" P Q ; coq.say "not sim" P Q).
}}.

Elpi Query lp:{{
    P = s, Q = s', (sim P Q,
    coq.say "sim" P Q ; coq.say "not sim" P Q).
}}.

Elpi Query lp:{{
    P = s', Q = s, (sim P Q,
    coq.say "sim" P Q ; coq.say "not sim" P Q).
}}.


