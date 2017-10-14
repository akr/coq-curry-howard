From mathcomp Require Import all_ssreflect.

(** * カリーハワード対応とCoqのあいだ

Coq の証明はカリーハワード対応を利用し
lambda項によって表現されているというのはよく知られています。

しかし、Coq の proof editing mode で証明をしていると、
証明のlambda項がどのようなものか意識することは少ないのではないでしょうか。

たとえば、move=> H がなにをする（どんなlambda項を構築する）のか
わかるでしょうか。

（この文章は SSReflect 前提なので、intro じゃなくて move=> を使っています）

ここではいろいろな tactic がなにをするものなのか、また、
それをどうやって調べるのか説明します。

*)

(** ** auto

まず、forall (P : Prop), P -> P という命題を例として考えます。
この命題は auto 一発で証明できます。

*)

Goal forall (P : Prop), P -> P.
Proof.
  auto.

(** ここで、No more subgoals. と表示されて、証明できたことがわかります。
auto で構築された証明は Show Proof. というコマンドで表示できます。*)
  Show Proof.
(** Show Proof. とすると私の環境 (CoqIDE) では (fun P : Prop => id) と表示されます。
id というのはなにかわからないので、
CoqIDE のメニューの View -> Display all low-level contents を有効にして Show Proof.
をやり直すと、
(fun (P : Prop) (H : P) => H) と表示されます。
実は今回は View -> Display notations を無効にするだけでも同じ効果があります。
Display all low-level contents はやりすぎで見づらくなりすぎることも多いのですが、
どれをトグルしたらいいかわからないときはこれを使ってみましょう。

(fun (P : Prop) (H : P) => H) は、
プログラムの世界の言葉で表現するなら、
Prop 型の値Pを受け取り、P型の値Hを受け取り、Hを返す関数です。
証明の世界の言葉で表現するなら、
命題Pを受け取り、Pの証明Hを受け取り、Hを返す関数です。

P は命題であり、カリーハワード対応からすなわち型であるわけですが、
型を普通の引数として受け取るのはちょっと見慣れない形かもしれません。
Coq では、（というか Gallina では）こういう形で型も普通に引数として
受けとることができ、受け取った型はそれ以降の引数の型などに使うことができます。

*)
Qed.

(** ** move=> と exact

この forall (P : Prop), P -> P という命題を、今度は auto を使わずに、
move=> と exact を使って証明してみましょう。

今回は Show Proof. で各ステップごとに構築されていく項を見ていきます。
*)

Goal forall (P : Prop), P -> P.
Proof.
  Show Proof.
(** ここでは証明を始めたばかりなので、Goal に与えた
forall P : Prop, P -> P という命題そのものを証明せよ、と Coq から要求されています。
そこで Show Proof とすると ?Goal と表示されます。
つまり、証明項はまったく構築されておらず、
forall P : Prop, P -> P という型の
証明項全体をこれから構築しなければならないというわけです。
*)
  move=> P.
  Show Proof.
(** move=> P により、前提に P : Prop が入り、証明すべき命題は P -> P に変化します。
ここで Show Proof とすると、(fun P : Prop => ?Goal) と表示されます。
つまり、証明項は (fun P : Prop => ?Goal) という形に構築され、
P -> P という型である ?Goal の部分はこれから構築しなければならない、
という状態であることがわかります。
前提に P が入ったのでここからは P を自由に使えますが、このことを
証明項の構造から説明すると、?Goal の部分の外側で P が束縛されているため、
?Goal の中では P を参照できる、という意味になります。
*)
  move=> H.
  Show Proof.
(** move=> H により、前提に H : P が入り、証明すべき命題は P に変化します。
Show Proof とすると、(fun (P : Prop) (H : P) => ?Goal) と表示されます。
つまり、証明項は (fun (P : Prop) (H : P) => ?Goal) という形に構築され、
P という型である ?Goal の部分をこれから構築しなければならない、
という状態であることが分かります。
前提に H が入ったのでここからは H を自由に使えますが、このことを
証明項の構造から説明すると、?Goal の部分の外側で H が束縛されているため、
?Goal の中では H を参照できる、という意味になります。
*)
  exact H.
  Show Proof.
(** P という型の値は H が存在する（参照できる）ので、
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
自分で定理に名前をつけるときには Goal じゃなくて Lemma や Theorem で証明を始めます。
Lemmaというのは補題で、Theoremというのは定理ですが、
機能的な違いはとくにありません。ここでは常に Lemma をつかうことにします。
*)

Lemma LemmaPP: forall (P : Prop), P -> P.
(** 証明しようとしているのは上と同じく forall (P : Prop), P -> P という命題であり、
これはその証明を LemmaPP という名前をつけよう、という指定です。
*)
Proof. auto. Qed.

Print LemmaPP.
(** Print LemmaPP とすると以下のように表示されます。
<<
  LemmaPP = fun (P : Prop) (H : P) => H
       : forall (P : Prop) (_ : P), P
>>
これは、LemmaPP の値は fun (P : Prop) (H : P) => H という値であり、
その型は forall (P : Prop) (_ : P), P である、という意味です。
プログラムの世界で解釈すれば、まさに LemmaPP の内容が構築した証明項として定義されている、
というわけです。
*)

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
Variable コマンドにより、P が Prop である、つまり何らかの命題Pが存在することが仮定されます。
*)

Lemma LemmaPP': P -> P.
Proof. auto. Qed.

Print LemmaPP'.
(**
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
つまり、セクションの中での LemmaPP' の値の外側に、Pを受け取る部分か追加されています。
*)

(** ** move:
SSReflect で、move=> H は証明対象の命題から前提に移すものですが、
逆に、前提から証明対象の命題に移すのは move: H を使います。
*)

Section MoveBack.

Variable P : Prop.

Goal P -> P.
Proof.
  Show Proof.
(* 先ほどのセクションの説明と同じく、P -> P の証明ですが、
最初に Show Proof とすると、?Goal と表示され、
証明項はまったくできていないことがわかります。
*)
  move=> H.
  Show Proof.
(* move=> H で、前提に移したところで
Show Proof とすると、(fun H : P => ?Goal) となり、
引数Hを受け取るラムダ抽象が構築されることがわかります。 
*)
  move: H.
  Show Proof.
(* ここで move: H として、H を証明対象に戻したところで Show Proof とすると、
(fun H : P => ?Goal H) と表示されます。
まずわかることは「戻す」というのは証明項が元に戻るわけではないことです。
実際には ?Goal が ?Goal H に変化する、つまり、戻したものを引数とする関数呼び出しが構築され、
関数部分が新しいゴールとなります。
*)
  move=> H.
  move: H.
  move=> H.
  move: H.
  Show Proof.
(* 意味もなく move=> H と move: H を繰り返してみると、証明項は
(fun H : P => (fun H0 : P => (fun H1 : P => ?Goal H1) H0) H)
となります。ラムダ抽象と関数呼び出しが増えていることが分かります。
Coq が表示する前提と証明する命題は変わりませんが、
内部では証明項が（意味もなく）膨らんでいるわけです。
move: の動作は確認できたので証明を終りましょう。
ここでは Abort で証明を中断する、つまり証明項を完成させずに終ることにします。
*)
Abort.

End MoveBack.
