(** ** apply

apply も move: と同様に証明項として関数適用を構築します。
しかし、move: とは異なり、apply に指定したものが
関数適用の（引数位置ではなく）関数位置に入ります。

これを説明するのに、
P と P -> Q が成り立っていたら Q が成り立つという三段論法の証明を使いましょう。
*)

Section Apply.

(**
証明項が煩雑になるのを避けるため、Section を使って
命題 P, Q および P の証明 Hp, P -> Q の証明 Hpq を宣言します。
*)

Variable P Q : Prop.
Variable Hp : P.
Variable Hpq : P -> Q.

(**
三段論法の結論 Q を証明します。
*)
Lemma modus_ponens : Q.
Proof.
  Show Proof.
(**
<<
?Goal
>>
最初の段階では証明項は構築されていないので ?Goal と表示されます。
*)
  apply Hpq.
  Show Proof.
(**
<<
(Hpq ?Goal)
>>
apply Hpq により、証明項として関数適用が構築され、
その関数位置に apply に指定した Hpq が配置されます。
引数は ?Goal となっていて、まだ構築されていません。

この証明項は (Q の証明なので) Q 型の値でなければなりませんが、
それが関数適用とすると、その関数は Q 型の値を返す関数である必要があります。
Hpq は P -> Q 型の値なので、この必要性を満たしています。
Hpq の引数は P 型の値でなければならないので、これから構築する ?Goal は P 型であり、
つまりここから証明すべき命題は P となります。
*)
  exact Hp.
  Show Proof.
(**
<<
(Hpq Hp)
>>
P を証明するのは簡単です。
P 型の値として Hp があるので、それを exact Hp として証明項とすれば終わりです。
そうすると、結局、全体の証明項は Hpq Hp となります。
*)
Qed.

End Apply.

Print modus_ponens.
(**
<<
modus_ponens =
fun (P Q : Prop) (Hp : P) (Hpq : P -> Q) => Hpq Hp
     : forall P Q : Prop, P -> (P -> Q) -> Q
>>

section を終ってから三段論法の証明項を Print で表示すると上のようになります。

Hpq Hp という項に、P, Q, Hp, Hpq という引数の関数抽象が外側にくくられた
証明項になっていることがわかります。

*)
