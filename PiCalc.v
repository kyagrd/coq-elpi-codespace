From elpi Require Import elpi.

Elpi Program bisim lp:{{
    kind name  type.

    kind proc  type.
    type null  proc.                 % 0를 표현하는 null
    type match name -> name -> proc -> proc. % [x=y]P를 표현하는 match x y P
    type par   proc -> proc -> proc. % P|Q를 표현하는 par P Q
    type plus  proc -> proc -> proc. % P+Q를 표현하는 plus P Q
    type in    name -> (name -> proc) -> proc. % x(y).P를 표현 in x (y\P)
    type out   name -> name -> proc -> proc.   % x<y>.P를 표현 out x y P
    type taup  proc -> proc.                   % τ.P를 나타내는 taup P
    type nu    (name -> proc) -> proc.         % nu (x\P)
%%%% type bang  proc -> proc.                   % !P를 나타내는 bang P

    kind act  type.
    type tau  act.
    type up   name -> name -> act. % x에  데이터 y를 output 액션을 나타내는 up x y
    type dn   name -> name -> act. % x에서 데이터 y를 input 액션을 나타내는 dn x y
}}.

Elpi Accumulate lp:{{
    pred one    o:proc, o:act, o:proc.
    pred onep   o:proc, o:(name -> act), o:(name -> proc).
    % Tau
    one (taup P) tau P.             
    % Out
    one (out X Y P) (up X Y) P.     
    % Inp
    onep (in X M) (dn X) M.         
    % Mat
    one (match X X P) A P' :- one P A P'.
    onep (match X X P) A P' :- onep P A P'.
    % Sum-L
    one (plus P _) A P' :- one P A P'.
    onep (plus P _) A P' :- onep P A P'.
    % Sum-R
    one (plus _ Q) A Q' :- one Q A Q'.
    onep (plus _ Q) A Q' :- onep Q A Q'.
    % Par-L
    one (par P Q) A (par P' Q) :- one P A P'.
    onep (par P Q) A (y\par (P' y) Q) :- onep P A P'.
    % Par-R
    one (par P Q) A (par P Q') :- one Q A Q'.
    onep (par P Q) A (y\ par P (Q' y)) :- onep Q A Q'.
    % Comm-L
    one (par P Q) tau (par P' (Q' V)) :- one P (up X V) P',
                                        onep Q (dn X) Q'.
    % Comm-R
    one (par P Q) tau (par (P' V) Q') :- onep P (dn X) P',
                                        one Q (up X V) Q'.
}}.

Elpi Accumulate lp:{{
    type a, b, c  name.

    pred example  o:int, o:proc.
    %           b(y).0 | b<a>.0
    example 1 (par (in b y\ null) (out b a null)).
    %           b(y).b<a>.0 + b<a>.b(y).0
    example 2 (plus (in b y\ out b a null) (out b a (in b y\ null))).
    %           new x.( b(y).0 | x<a>.0 )
    example 3 (nu x\ par (in x y\ null) (out x a null)).
    %           new x.( a<x>.0 )
    example 4 (nu x\ out a x null).
    %           new y.( y(w).0 | b<b>.0 )
    example 5 (in a y\ par (in y w\ null) (out b b null)).
    %           a(y).( y(w).b<b>.0 + b<b>.y(w).0 )
    example 6 (in a y\ plus (in y w\ out b b null) (out b b (in y w\ null))).
    %           new y.( a<y>.( y(w).0 | b<b>.0 ) )
    example 7 (nu y\ out a y (par (in y w\ null) (out b b null))).
    %           new y.( a<y>.( y(w).b<b>.0 + b<b>.y(w).0 ) )
    example 8 (nu y\ out a y (plus (in y w\ out b b null) (out b b (in y w\ null)))).
}}.

Elpi Query lp:{{
    example 1 P, coq.say "example 1:" P. 
}}.

Elpi Query lp:{{
    example 1 P, one P A P'. 
}}.

Elpi Query lp:{{
    example 1 P, one P (up X Y) P'. 
}}.

Elpi Query lp:{{
    example 1 P, one P tau P'. 
}}.

Elpi Query lp:{{
    example 1 P, onep P A P'. 
}}.


