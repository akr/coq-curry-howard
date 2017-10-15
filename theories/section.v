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

Print LemmaPP'.
(**
証明が終った後、でもセクションは終る前に、
Print LemmaPP' とすると、以下のように表示されます。
<<
LemmaPP' = fun H : P => H
     : forall _ : P, P
>>
つまり、LemmaPP' は P型の値Hを受け取ってHを返す関数です。
*)

End SectionExplanation.

Print LemmaPP'.
(** セクションを終ってから再度 Print LemmaPP' とすると、以下のように異なる表示になります。
<<
LemmaPP' = fun (P : Prop) (H : P) => H
     : forall (P : Prop) (_ : P), P
>>
ここでは、命題Pを受け取り、P型の値Hを受け取り、Hを返す関数となっています。
つまり、セクションの中での LemmaPP' の値の外側に、Pを受け取る関数抽象が追加されています。
*)

