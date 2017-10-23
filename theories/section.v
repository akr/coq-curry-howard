From mathcomp Require Import all_ssreflect.

(** ** Section
他の tactic の説明の前に、Section というコマンドを紹介しましょう。
Section というのはセクションを作ります。
Foo というセクションを作るには Section Foo. でセクションを始めて、
End Foo. でセクションを終ります。
セクションの中では共通する仮定を宣言することができ、
その仮定に依存した証明は、セクションを終ると、仮定を引数として受け取るように変形されます。
*)

Section SectionExplanation.

Variable P : Prop.
(**
Variable コマンドにより、P が Prop である、つまり何らかの命題Pが存在することが宣言されます。
*)

Lemma LemmaPP': P -> P.
Proof. auto. Qed.
(**
何らかの命題 P が存在することを前提を用いて、
P が成り立つならば P が成り立つことを証明し、その証明に LemmaPP' という名前をつけます。
*)

Print LemmaPP'.
(**
<<
LemmaPP' = id
     : P -> P
>>
証明が終った後、セクションを終る前に、
Print LemmaPP' とすると、上のように表示されます。
つまり、LemmaPP' は P型の値Hを受け取ってHを返す関数です。
*)

End SectionExplanation.

Print LemmaPP'.
(**
<<
LemmaPP' = fun P : Prop => id
     : forall P : Prop, P -> P
>>
セクションを終ってから再度 Print LemmaPP' とすると、上のように異なる表示になります。
ここでは、命題Pを受け取り、P型の値Hを受け取り、Hを返す関数となっています。
つまり、セクションの中での LemmaPP' の値の外側に、Pを受け取る関数抽象が追加されています。
*)

