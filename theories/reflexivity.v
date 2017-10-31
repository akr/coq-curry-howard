From mathcomp Require Import all_ssreflect.

(** ** reflexivity

reflexivity は X = X という命題を証明する tactic です。

SSReflect ではふつう <<by []>> などで済ますのであまり使いませんが、
等式の扱いの説明をするのに都合がいいので説明しましょう。

*)

Goal 0 = 0.
Proof.
  reflexivity.
  Show Proof.
(**
<<
(erefl 0)
>>

なんか、省略されているっぽいので Display all low-level contents を有効にして
Show Proof をやり直すと、以下のようになります。

<<
(@Logic.eq_refl nat O)
>>

O というのは 0 です。

Coq の theories/Init/Logic.v をみると、eq は以下のように定義されています。

<<
Inductive eq (A:Type) (x:A) : A -> Prop :=
    eq_refl : x = x :>A
where "x = y :> A" := (@eq A x y) : type_scope.
Notation "x = y" := (x = y :>_) : type_scope.
>>

ちょっといろいろと複雑ですが、これは eq という型と
eq 型の値を構成する eq_refl というコンストラクタを定義しています。
ただし、パラメータがついているので
単にひとつの型とコンストラクタを定義しているわけではありません。

About で eq 定義を調べてみましょう。
(Display implicit arguments を有効にして、Display notations を無効にしておきます)
*)
About eq.
(**
<<
eq : forall (A : Type) (_ : A) (_ : A), Prop
>>

これをみると、eq は A という型と、A型の値ふたつを受け取って、
命題を返す関数であることがわかります。

コンストラクタの eq_refl も調べてみましょう。
*)
About Logic.eq_refl.
(**
<<
Logic.eq_refl : forall (A : Type) (x : A), @eq A x x
>>

About eq_refl だと mathcomp.ssreflect.eqtype.eq_refl が出てきてしまうので、
Logic.eq_refl と指定しています。

eq_refl は A という型と A 型の値 x を受け取って @eq A x x という型の値を返す関数
であることがわかります。

カリーハワード対応により命題と型は同型なので、
eq が命題を返すというのと、
@eq A x x が型というのは同じことです。

さて、eq は 3つのパラメータをとるので、
@eq A a b というように 3つパラメータを与えれば具体的な型になります。
たとえば、@eq nat 1 2 はひとつの具体的な型です。
それに対して、コンストラクタが返す値の型は @eq A x x なので、
必ず x と y は等しくなります。
つまり、@eq_refl nat 1 は @eq nat 1 1 という型であり、
eq_refl で @eq nat 1 2 という型の値を作ることはできません。

そして、eq_refl 以外で eq 型の値を作ることはできません。
（Inductive というのは帰納ということで、帰納的に定義する、というのはそういうことです。）

ついでにいえば、リストの cons みたいな
（リスト型の値を引数として受け取る）コンストラクタと違って、
eq_refl は eq 型の値を受け取る引数を持たないので、
eq 型の値を作るには eq_refl を一回使う以外の方法はありません。

結局、@eq A a b という型は、
a と b が等しい場合は eq_refl によって構成されるただひとつの値を持ちます。
そして、a と b が等しくない場合はまったく値をもちません。

この性質により、@eq A a b という型に対してその型に適合する値を作れるならば、
a と b は等しいということがいえるわけです。
つまり、a と b が等しいという命題や証明を eq 型で実現できるわけです。
*)
Qed.

(**
さて、ここで問題は「等しい」というのはいったいどういう意味か、という点です。
まぁ、最初の 0 = 0 のように、完全に同じ形であれば等しいのはそうでしょうが、
異なる形でも等しいことはないのでしょうか。
たとえば、2 + 4 = 5 + 1 はどうでしょうか。

ということで、試してみましょう。
*)

Goal 2 + 4 = 5 + 1.
Proof.
  reflexivity.
  Show Proof.
(**
<<
(erefl (5 + 1))
>>

どうやら問題なく証明できてしまうようです。
証明項は erefl (5 + 1) であり、
これは <<@Logic.eq_refl nat (addn (S (S (S (S (S O))))) (S O))>> の意味です。

どうも、reflexivity は等式の右辺を erefl の引数にする感じです。

そうでない証明項は許されるのか、exact で証明項を与えて試してみましょう。
*)
Qed.

Goal 2 + 4 = 5 + 1.
Proof.
  exact (erefl 6).
  Show Proof.
(**
<<
(erefl 6)
>>
*)
Qed.

(**
とくに問題なく証明できました。

つまり、erefl 6 つまり @Logic.eq_refl nat 6 という項は
@eq nat (2 + 4) (5 + 1) という型の値として正しく受け付けられるというわけです。

「eq_refl は A という型と A 型の値 x を受け取って @eq A x x という型の値を返す関数」
と上で述べましたが、ここで eq_refl の引数として指定した x は 6 です。
したがって、erefl 6 は @eq nat 6 6 型の値なわけですが、
Coq はここで、この型が @eq nat (2 + 4) (5 + 1) 型と等しいかどうか確認します。
具体的には、計算を進めて同じ項になるかどうかを確認します。
2 + 4 や 5 + 1 は変数が入っていないので計算を最後まで行うことができ、その結果は 6 です。
そのため、Coq は @eq nat 6 6 型と @eq nat (2 + 4) (5 + 1) 型が等しいことを確認でき、
erefl 6 が @eq nat (2 + 4) (5 + 1) 型の要素であることを判断できます。

*)

(**
計算を進めても等しさを確認できない場合もあります。
*)

Section AddComm.

Variable n : nat.

Goal n + 1 = 1 + n.
Proof.
  Fail reflexivity.
(**
ここでは n という自然数の変数があって、n + 1 と 1 + n が等しいことを証明しようとしています。
残念ながら、reflexivity は失敗します。

Coq で n + 1 と 1 + n がどこまで計算を進められるか、Compute というコマンドで
実際に計算を行って確かめてみましょう。
*)
  Compute n + 1.
(**
<<
     = (fix Ffix (x x0 : nat) {struct x} : nat :=
          match x with
          | 0 => x0
          | x1.+1 => (Ffix x1 x0).+1
          end) n 1
     : nat
>>
n + 1 というのは、なにか fix とかいうもので始まる関数が展開されて、
そこで止まってしまいました。
この関数は加算の関数で、最初の引数が 0 かそれ以外かで場合分けを行って計算を行います。
ところが、最初の引数は変数の n であり、これが 0 かどうかは不明です。
そのため、計算がここで止まってしまうのです。

逆に、最初の引数が変数ではなく、具体的な自然数が与えられれば、計算を進めることができます。
1 + n はその例であり、こちらはもっと計算が進みます。
*)
  Compute 1 + n.
(**
<<
     = n.+1
>>
SSReflect の notation が効いているので Display notations を無効にしてやりなおすと
以下のようになります。
<<
     = S n
>>
1 + n では、かなり単純な項になるまで計算が進んでいます。

というわけで、n + 1 と 1 + n では、計算を進めても同じ項にたどり着けないので、
reflexivity は失敗してしまうのです。
*)
Abort.

End AddComm.

(**
あと、いちおう注意しておくと、
reflexivity は完全に計算を進めるわけではありません。
*)
Goal 2 ^ 100 = 2 ^ 100.
Proof.
  reflexivity.
  Show Proof.
(**
<<
(erefl (2 ^ 100))
>>

2 ^ 100 というのは 2 の 100乗で、本当に計算しようとすると、メモリがあふれてしまいます。
（Coq の自然数はペアノの自然数なので、2^100 を計算すると、
S を 2^100 個メモリに並べる必要がありますが、
これを素朴に実装すると 64ビットのメモリ空間でも足りません。
そして、Coq はいまのところ素朴に実装しているのです。
どうにかしてほしいところですが。）

しかし、ここの reflexivity でメモリがあふれないことからわかるように、
計算を進めなくても同じ項であることがわかるなら、それは問題なく判断してくれます。
*)
Qed.


