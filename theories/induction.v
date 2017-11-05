(** ** induction

induction term というのは数学的帰納法を適用する tactic です。
term は帰納的に定義された型である必要があります。

induction が構築する証明項をみるために、a + 0 = a を証明してみましょう。
加算 (Nat.add) は第1引数で場合分けして計算を進めます。
この a + 0 というのは第1引数が変数なため、その場合分けを行えず、
計算を進めることができません。
そのため、これを証明するには帰納法が必要になります。

*)

Goal forall a, a + 0 = a.
Proof.
  intros a.
(**
ゴール: <<a + 0 = a>>
*)
  Show Proof.
(**
証明項: <<(fun a : nat => ?Goal)>>

induction の直前では、intros で構築した関数抽象の本体がゴールとなっています。
*)
  induction a.
(**
ゴール1: <<0 + 0 = 0>>
ゴール2: <<S a + 0 = S a>>

induction の直後では、a が 0 の場合のゴールと、
a が 0 でない (つまり S a の場合の) ゴールのふたつのゴールが生成されています。
*)
    Show Proof.
(**
証明項:
<<(fun a : nat =>
 nat_ind (fun a0 : nat => a0 + 0 = a0)
   ?Goal
   (fun (a0 : nat) (IHa : a0 + 0 = a0) => ?Goal0@{a:=a0})
   a)>>

証明項をみると、nat_ind という関数を呼び出しており、
引数の中には ?Goal と ?Goal0@{n:=n0} があって、
ふたつのゴールがあることがわかります。

nat_ind がどんな関数なのか About でみてみましょう。
*)
    About nat_ind.
(**
<<
nat_ind :
forall P : nat -> Prop,
  P 0 ->
  (forall n : nat, P n -> P (S n)) ->
  forall n : nat,
  P n
>>

Display notations を無効にして About しなおすと以下のようになります。

<<
nat_ind :
forall (P : forall _ : nat, Prop)
  (_ : P O)
  (_ : forall (n : nat) (_ : P n), P (S n))
  (n : nat),
  P n
>>

- 第1引数 P として nat を受け取って命題を返す関数を受けとります。
- 第2引数に P 0 の証明を受け取ります。
- 第3引数に n と P n の証明を受け取って P (S n) の証明を返す関数を受けとります。
- 第4引数に n を受けとります。
- そして、P n の証明を返します。

直感的には、nat_ind は、第2引数から始めて n 回第3引数を適用したものを返すと
理解すればよさそうです。

証明項で実引数は以下のようになっています。

- 第1引数: (fun a0 : nat => a0 + 0 = a0)
- 第2引数: ?Goal
- 第3引数: (fun (a0 : nat) (IHa : a0 + 0 = a0) => ?Goal0@{a:=a0})
- 第4引数: a

返り値の型 P n は (fun a0 : nat => a0 + 0 = a0) a すなわち a + 0 = a であり、
induction を行う直前のゴールと一致しています。

nat_ind の第2引数の型 P 0 は (fun a0 : nat => a0 + 0 = a0) 0 すなわち 0 + 0 = 0 であり、
induction を行った後の最初のゴールと一致しています。

0 + 0 = 0 は計算すれば左右が同じになるので reflexivity で証明できます。
*)
    reflexivity.
  Show Proof.
(**
<<
(fun a : nat =>
 nat_ind (fun a0 : nat => a0 + 0 = a0) eq_refl
   (fun (a0 : nat) (IHa : a0 + 0 = a0) => ?Goal@{a:=a0}) a)
>>

最初のゴールは reflexivity で生成された eq_refl が埋まったことがわかります。
*)

(**
次に、ふたつめのゴールにとりかかることになります。
ここでは、以下の前提が表示されています。
<<
a : nat
IHa : a + 0 = a
>>
そして、<<S a + 0 = S a>> というゴールを証明しなければなりません。

nat_ind の第3引数の型 forall n : nat, P n -> P (S n) を展開すると
forall n : nat, n + 0 = n -> S n + 0 = S n となります。
第3引数の実引数は (fun (a0 : nat) (IHa : a0 + 0 = a0) => ?Goal0@{a:=a0}) であり、
すでに関数抽象が2段階生成されています。
表示されている a と IHa という前提はこの a0 と IHa に対応しています。
ゴールに @{a:=a0} と付記されているのは、
仮引数は a0 なのに前提は a という名前になっていることを示しているのでしょう。

これを証明するにはまず simpl としてゴール内で計算を進められるところを進めてしまいます。
*)
  simpl.
  Show Proof.
(**
ゴール: <<S (a + 0) = S a>>
証明項:
<<(fun a : nat =>
 nat_ind (fun a0 : nat => a0 + 0 = a0) eq_refl
   (fun (a0 : nat) (IHa : a0 + 0 = a0) => ?Goal@{a:=a0}) a)>>

simpl では計算を進めるだけで、そういう計算でたどり着ける項は等しいと考えるので、
証明項は変わりません。

simpl の結果、ゴール内に a + 0 という IHa で書き換えられる部分が出てきたので書き換えます。
*)
  rewrite IHa.
  Show Proof.
(**
ゴール: <<S a = S a>>
証明項:
<<(fun a : nat =>
 nat_ind (fun a0 : nat => a0 + 0 = a0) eq_refl
   (fun (a0 : nat) (IHa : a0 + 0 = a0) =>
    eq_ind_r (fun n : nat => S n = S a0) ?Goal@{a:=a0} IHa) a)>>

rewrite により、eq_ind_r の呼び出しが生成され、ゴールは S a = S a に変化します。
このゴールは両辺が等しいので、reflexivity で証明できます。
*)
  reflexivity.
  Show Proof.
(**
証明項:
<<(fun a : nat =>
 nat_ind (fun a0 : nat => a0 + 0 = a0) eq_refl
   (fun (a0 : nat) (IHa : a0 + 0 = a0) =>
    eq_ind_r (fun n : nat => S n = S a0) eq_refl IHa) a)>>

ゴールに eq_refl が埋まって、ゴールがなくなったのでこれで証明は終了です。
*)
Qed.

(**
induction が nat_ind を呼び出す関数呼び出しを構築することがわかりました。

そこで、induction ではなく、apply で同じ証明項を構築してみましょう。
*)

Goal forall a, a + 0 = a.
Proof.
  intros a.
(**
induction a とするかわりに、(nat_ind (fun a0 : nat => a0 + 0 = a0)) という
関数の呼び出しを構築します。
第1引数を指定しているのは、指定しない場合に Coq が推論する項はこれとは異なる項になってしまうからです。
指定しない場合については後でみてみましょう。
*)
  apply (nat_ind (fun a0 : nat => a0 + 0 = a0)).
  Show Proof.
(**
ゴール1: <<0 + 0 = 0>>
ゴール2: <<forall n : nat, n + 0 = n -> S n + 0 = S n>>
証明項: <<(fun a : nat => nat_ind (fun a0 : nat => a0 + 0 = a0) ?Goal ?Goal0 a)>>

期待通り nat_ind の呼び出しが構築されています。
induction とは異なり、第3引数の関数抽象は構築されていませんが、
apply は関数呼び出しを構築するものですからしょうがないでしょう。

最初のゴールは reflexivity で証明できます。
*)
    reflexivity.
  Show Proof.
(**
証明項: <<(fun a : nat => nat_ind (fun a0 : nat => a0 + 0 = a0) eq_refl ?Goal a)>>

induction による証明項と同じ証明項を作るには、
つぎのゴールに関数抽象を作る必要があります。
これは intros で可能ですが、ひとつ問題なのは前提にすでに a が存在するため、
intro a がエラーになることです。
*)
  Fail intro a.
(**
そこで、まず前提の a を消去します。
これには clear を使います。
*)
  clear a.
  Show Proof.
(**
証明項: <<(fun a : nat => nat_ind (fun a0 : nat => a0 + 0 = a0) eq_refl ?Goal a)>>
clear が前提から消去するのは、束縛された変数を前提としてアクセスできなくするというだけで、
証明項は変わりません。

これで前提が空になったので、intros a IHa として関数抽象を2段階構築します。
*)
  intros a IHa.
  Show Proof.
(**
<<(fun a : nat =>
 nat_ind (fun a0 : nat => a0 + 0 = a0) (@eq_refl nat 0)
   (fun (a0 : nat) (IHa : a0 + 0 = a0) => ?Goal@{a:=a0}) a)>>
これで、induction a 相当の証明項を構築できました。
あとは前と同じように証明します。
*)
  simpl.
  rewrite IHa.
  reflexivity.
Qed.

(**
apply nat_ind とだけ指定した場合にどうなるかみてみましょう。
*)

Goal forall a, a + 0 = a.
Proof.
  intros a.
  apply nat_ind.
  Show Proof.
(**
ゴール1: <<a + 0 = 0>>
ゴール2: <<forall n : nat, a + 0 = n -> a + 0 = S n>>
証明項: <<(fun a : nat => nat_ind (@eq nat (a + 0)) ?Goal ?Goal0 a)>>

ゴール1をみるとこれは証明できなくて、なにか間違えたことがわかります。

証明項をみると、第1引数には (@eq nat (a + 0)) が渡されています。
eq の型をみてみましょう。
*)
About eq.
(**
<<
eq : forall A : Type, A -> A -> Prop
>>

最初の Type 型引数 A に nat が渡されており、つぎの A (つまり nat) 型引数に a + 0 が
渡されています。
最後の A (つまり nat) 型引数は渡されていないので、
結局、(@eq nat (a + 0)) は nat を受け取って Prop を返す関数となります。
これは nat_ind の第1引数の型とあっていますが、期待した引数ではありません。
*)
Abort.



