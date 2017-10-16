From mathcomp Require Import all_ssreflect.

(** ** move=>

この forall (P : Prop), P -> P という命題を、今度は
move=> と exact を使って証明してみましょう。
*)

Goal forall (P : Prop), P -> P.
Proof.
  Show Proof.
(**
<<
?Goal
>>
ここでは証明を始めたばかりなので、Goal に与えた
forall P : Prop, P -> P という命題そのものを証明せよ、と Coq から要求されています。
そこで Show Proof とすると ?Goal と表示されます。
つまり、証明項はまったく構築されておらず、
forall P : Prop, P -> P という型の
値をどうにか作ってここに埋めていかなければならないというわけです。
*)
  move=> P.
  Show Proof.
(**
<<
(fun P : Prop => ?Goal)
>>
move=> P により、前提に P : Prop が入り、証明すべき命題は P -> P に変化します。
ここで Show Proof とすると、(fun P : Prop => ?Goal) と表示されます。
つまり、move=> P は証明項を Prop型の値Pを受け取る関数抽象として構築せよ、という指示です。
関数抽象の本体はまだわからないので、?Goal となっており、この部分の型は P -> P です。
そのため、P -> P という型である ?Goal の部分をこれから構築しなければならない、
という状態であることがわかります。

前提に P が入ったのでここからは P を自由に使えますが、このことを
証明項の構造から説明すると、?Goal の部分の外側で P が束縛されているため、
?Goal の中では P を参照できる、という意味になります。
*)
  move=> H.
  Show Proof.
(**
<<
(fun (P : Prop) (H : P) => ?Goal)
>>
move=> H により、前提に H : P が入り、証明すべき命題は P に変化します。
Show Proof とすると、(fun (P : Prop) (H : P) => ?Goal) と表示されます。
つまり、?Goal を（また）関数抽象として構築せよ、という指示を行ったので、
証明項は関数抽象が2段ネストしたものとして (fun (P : Prop) (H : P) => ?Goal) という形に
なり、関数抽象の本体の P という型である ?Goal の部分をこれから構築しなければならない、
という状態であることが分かります。
前提に H が入ったのでここからは H を自由に使えますが、このことを
証明項の構造から説明すると、?Goal の部分の外側で H が束縛されているため、
?Goal の中では H を参照できる、という意味になります。
*)
  exact H.
  Show Proof.
(**
<<
(fun (P : Prop) (H : P) => H)
>>
P という型の値としては H が存在する（参照できる）ので、
それを証明項として与えれば証明は終わりです。
exact H により H を証明項として直接与えると No more subgoals. と表示されて
証明が終ったことがわかります。
ここで Show Proof とすると、(fun (P : Prop) (H : P) => H) と表示され、
上で ?Goal だったところに H が埋められていることが分かります。
証明項に不明な部分はもうないので、やることはもうありません。
Qed で証明を終りましょう。
*)
Qed.
(** 証明を終えるとき、Qed は証明項があらためて正しいかどうか
（ちゃんと正しい型がつく項になっているかどうか）
あらためて検査します。
そのため、怪しげなユーザ拡張の tactic が変な証明項を生成しても、
そのような証明はQedの段階で拒否されます。
*)

(** ところで、Qed としたときに Unnamed_thm0 is defined と表示されます。
つまり、Unnamed_thm0 という定理が定義された、ということですが、
もちろん、後で使いたい定理にこういう内容に関係ない名前をつけるのはよくありません。
自分で定理に名前をつけるときには Goal ではなく Lemma や Theorem で証明を始めます。
Lemmaというのは補題で、Theoremというのは定理ですが、
機能的な違いはとくにありません。ここでは常に Lemma をつかうことにします。
*)

Lemma LemmaPP: forall (P : Prop), P -> P.
(** 証明しようとしているのは上と同じく forall (P : Prop), P -> P という命題であり、
これはその証明を LemmaPP という名前をつけよう、という指定です。
*)
Proof. auto. Qed.

Print LemmaPP.
(** 証明が終った後、Print LemmaPP とすると以下のように表示されます。
<<
  LemmaPP = fun (P : Prop) (H : P) => H
       : forall (P : Prop) (_ : P), P
>>
これは、LemmaPP の値は fun (P : Prop) (H : P) => H という値であり、
その型は forall (P : Prop) (_ : P), P である、という意味です。
プログラムの世界で解釈すれば、まさに LemmaPP の内容が構築した証明項として定義されている、
というわけです。
*)

