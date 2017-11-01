Require Import Arith.

(** ** rewrite

rewrite は X = Y という定理を利用して、証明の中で
X を Y に書き換える tactic です。

X = Y は eq X Y の notation なので、ここからは = のことを eq と呼ぶことにします。
(じつは、eq は省略されている引数があって 3引数だったりしますが、ここでは気にしないことに
しましょう。実際の定義を見たいのであれば Coq の theories/Init/Logic.v を覗いてください。)

*)

Section Rewrite.

Variable a b c : nat.

(**
まず、簡単な例として、a * (b + c) を a * (c + b) に書き換えてみましょう。

*)

Goal a * (b + c) = a * (c + b).
Proof.
(**
<<
1 subgoal
a, b, c : nat
______________________________________(1/1)
a * (b + c) = a * (c + b)
>>
*)
  Show Proof.
(**
<<
?Goal
>>

証明がはじまったばかりの段階では、証明項全体をこれから構築していく段階なので、
?Goal とだけ表示されます。
*)
  rewrite Nat.add_comm.
(**
<<
1 subgoal
a, b, c : nat
______________________________________(1/1)
a * (c + b) = a * (c + b)
>>
Coq では、自然数の加算の交換律は Nat.add_comm という補題として用意されているので、
rewrite Nat.add_comm で書き換えを行えます。

このケースでは、rewrite は b + c という部分を書き換えの対象として発見し、
これを c + b に書き換えます。

書き換えた結果、証明すべき命題は a * (c + b) = a * (c + b) に変化します。
*)
  Show Proof.
(**
<<
(eq_ind_r (fun n : nat => a * n = a * (c + b)) ?Goal (Nat.add_comm b c))
>>

書き変えを行った後、Show Proof で証明項を表示すると、上のようになります。

この証明項の内部では eq_ind_r と Nat.add_comm が使われています。
Nat.add_comm は rewrite の引数に指定したのでそれが使われているわけですが、
eq_ind_r は rewrite が内部的に使った定理です。

eq_ind_r がどんな定理なのか About で表示してみましょう。
*)
  About eq_ind_r.
(**
<<
eq_ind_r :
forall (A : Type) (x : A) (P : A -> Prop), P x -> forall y : A, y = x -> P y
Arguments A, x, y are implicit
>>

Arguments A, x, y are implicit というのは A, x, y は省略されるという設定を示しています。

eq_ind_r の定義を確実に確認するため、Display notations を無効にして、
さらに Display implicit arguments を有効にして About eq_ind_r を
やりなおすと、以下のように表示されます。

<<
eq_ind_r :
forall (A : Type) (x : A) (P : forall _ : A, Prop) (_ : P x) (y : A)
  (_ : @eq A y x), P y
>>

P x -> というのが P x という型の無名引数であるとか、y = x が @eq A y x であるとか、
そういうことがわかります。

@eq の @ は eq で引数の省略を行わないという指定です。
通常 eq では第1引数が省略されるのですが、ここでは第1引数の A が表示されています。
(@ はユーザが項を指定するときに、通常は省略される引数を明示的に指定する時も使えます。)

Display implicit arguments の効果は証明項の表示でも有効です。
有効にした状態で Show Proof とすると、以下のように表示されます。

<<
(@eq_ind_r nat (c + b) (fun n : nat => a * n = a * (c + b)) ?Goal (b + c)
   (Nat.add_comm b c))
>>

ここでは eq_ind_r のかわりに @eq_ind_r と @ がついて表示され、
省略を行わない形式であることを示しています。

eq_ind_r の引数は以下のように与えられています。
- A は nat
- x は c + b
- P は fun n : nat => a * n = a * (c + b)
- P x という型の無名引数は ?Goal
- y は b + c
- @eq A y x という型 (y = x という型) の無名引数は Nat.add_comm b c

ここで ?Goal の型は P x なので、(fun n : nat => a * n = a * (c + b)) (c + b) であり、
ちょっと計算を進めると（ベータ展開すると）a * (c + b) = a * (c + b) です。
これはこの時点で証明すべき命題と一致しています。

また、eq_ind_r の返り値の型は P y です。
つまり (fun n : nat => a * n = a * (c + b)) (b + c) であり、
ちょっと計算を進めると a * (b + c) = a * (c + b) です。
これは、rewrite する前の命題と一致しています。

結局、rewrite は eq_ind_r を使って、
P x すなわち a * (c + b) = a * (c + b) の証明から
P y すなわち a * (b + c) = a * (c + b) の証明を作り上げる、
という証明項を構築しています。

P x の部分の証明はまだ行っていないので ?Goal として残っており、
これが次に証明すべき命題としてユーザに提示されるというわけです。
*)
  reflexivity.
  Show Proof.
(**
<<
(eq_ind_r (fun n : nat => a * n = a * (c + b)) eq_refl (Nat.add_comm b c))
>>

rewrite の結果、右辺と左辺が同じ形になったので、reflexivity で証明できます。
Show Proof の結果をみると、
reflexivity で eq_refl という証明項が構築されていることがわかります。
（これは省略された形で、実際は @eq_refl nat (a * (c + b)) です。）
*)
Qed.

End Rewrite.

(**
ところで、rewrite で match, let, 関数抽象の body を書き換えようとして
書き換えられずに困ったことはないでしょうか。
*)

Goal (fun a => a + 2) = (fun a => 2 + a).
Proof.
  Fail rewrite Nat.add_comm.
(**
ここでは、a + 2 を 2 + a に書き換えようとして、
rewrite Nat.add_comm としていますが失敗してしまいます。

これは、rewrite が eq_ind_r を使って作り上げる証明項を考えると理解できます。
eq_ind_r には x として 2 + a, y として a + 2 を渡す必要がありますが、
eq_ind_r の引数の場所で a は束縛されていないので参照できません。
*)
Abort.

(**
書き換えたい項が関数抽象の本体の中にあっても、
書き換えたい項自身の中に束縛変数が含まれていないのであれば、
rewrite で書き換えることができます。
*)

Goal (fun a => a + (2 + 0)) = (fun a => 2 + a).
Proof.
  rewrite Nat.add_0_r.
  Show Proof.
(**
<<
(@eq_ind_r nat 2
   (fun n : nat => (fun a : nat => a + n) = (fun a : nat => 2 + a)) ?Goal
   (2 + 0) (Nat.add_0_r 2))
>>

たとえばこの例では、関数抽象の中にある 2 + 0 を
Nat.add_0_r を使って 2 に書き換えています。

この証明項では、@eq_ind_r の第5引数に 2 + 0 が現れていることが分かります。

この、2 + 0 が置かれている場所では a の束縛は行われていないので、
a は使えません。
2 + 0 に a は使われていないので問題ありませんが、
2 + 0 のところに 2 + a を与えようとすれば証明項は束縛されていない a を参照してしまう
ことになってしまいます。

というわけで、(証明すべき命題の中で) 束縛されている変数は rewrite では使えないわけです。
*)
Abort.
