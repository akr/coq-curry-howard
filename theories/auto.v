From mathcomp Require Import all_ssreflect.

(** ** auto

まず、forall (P : Prop), P -> P という命題を例として考えます。
この命題は auto 一発で証明できます。
*)

Goal forall (P : Prop), P -> P.
Proof.
  auto.

(** ここで No more subgoals. と表示されて、証明できたことがわかります。
構築された証明項は Show Proof というコマンドで表示できます。*)
  Show Proof.
(** Show Proof とすると私の環境 (CoqIDE) では (fun P : Prop => id) と表示されます。
id というのはなにかわからないので、
CoqIDE のメニューの View -> Display all low-level contents を有効にして Show Proof
をやり直すと、
(fun (P : Prop) (H : P) => H) と表示されます。
実は今回は View -> Display notations を無効にするだけでも同じ効果があります。
Display all low-level contents はやりすぎで見づらくなりすぎることも多いのですが、
どれをトグルしたらいいかわからないときはこれを使ってみましょう。

(fun (P : Prop) (H : P) => H) は Gallina の式です。
Gallina というのは Coq に組み込まれている ML のような言語で、
ここで使っているように証明項にも用いますし、
Gallina で直接プログラムを書くこともあります。

(fun (P : Prop) (H : P) => ...) というのは
Gallina の関数抽象（ラムダ式）で、カリー化されているのでじつは
(fun (P : Prop) => (fun (H : P) => ...)) と同じものです。
関数型言語を知っていればだいたいわかるとは思いますが、
(fun (P : Prop) => ...) は Prop 型の値 P を受け取って ... の部分を返す関数抽象です。

P は命題であり、カリーハワード対応からすなわち型であるわけですが、
型を普通の引数として受け取るのはちょっと見慣れない形かもしれません。
Gallina では型も普通に引数として
受けとることができ、受け取った型はそれ以降の引数の型などに使うことができます。

(fun (P : Prop) (H : P) => H) は、
プログラムの世界の言葉で表現するなら、
Prop 型の値Pを受け取り、P型の値Hを受け取り、Hを返す関数です。
証明の世界の言葉で表現するなら、
命題Pを受け取り、Pの証明Hを受け取り、Hを返す関数です。
そのような関数が存在することが、forall (P : Prop), P -> P の証明である、ということです。

*)
Qed.
