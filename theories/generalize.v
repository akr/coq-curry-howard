(** ** generalize

generalize というのは、命題を一般化する tactic です。
具体的には、命題のなかの部分項を変数に変えてしまいます。
たとえば、a + 10 という nat な部分項を n に変えると、
もともとは 10以上の値にしかならなかったものが、
変えたあとはそのよう条件は読み取れなくなります。
つまり、条件がなくなって一般化されます。

一般化されると基本的には証明はむずかしくなりますが、
帰納法で証明する場合はこれが必要になる場合があります。

*)

Section Generalize.

Variable a b c : nat.

Goal (a + 10) + b < c.
Proof.
(**
goal: <<a + 10 + b < c>>
*)
  Show Proof.
(**
<<
?Goal
>>
*)
  generalize (a + 10) as n.
(**
goal: <<forall n : nat, n + b < c>>
*)
  Show Proof.
(**
<<
(?Goal (a + 10))
>>

<<generalize (a + 10)>> により、
証明項に関数適用が構築され、その引数部分には generalize に指定した引数が入ります。

また、ゴール中の a + 10 は n という変数に変化し、
n を引数として受け取る関数抽象がもとのゴールの外側についています。
関数抽象の引数名は generalize の as で指定されます。

証明項全体を見ると、a + 10 が n に渡されるので、命題としては元のゴールと同じになっています。
*)
Abort.

(**
なお、generalize に指定する引数は命題に含まれていなくても、
また、複数含まれていてもかまいません。
*)

Goal (a + a) + (a + a) + (a + a) < b.
Proof.
  generalize (a + 1).
(**
goal: <<nat -> a + a + (a + a) + (a + a) < b>>
*)
  Show Proof.
(**
<<
(?Goal (a + 1))
>>

ここでは、ゴールに含まれていない、a + 1 という項を generalize に指定しています。
この場合でも、証明項に関数適用が構築され、
その引数部分に generalize の引数が入るのはかわりません。

ゴール内には a + 1 がないので、置き換えは行われません。
しかし、関数適用された引数を受け取る必要はあるので、nat を受けとる関数抽象が
ゴールに加えられます。
受け取った引数は使われないので、引数に名前は不要で、
実際、generalize はこの場合は引数名を生成しません。
これは、Display notations を無効にすると
以下のように引数名が _ になっていることを確認できます。
<<
forall _ : nat,
lt (Nat.add (Nat.add (Nat.add a a) (Nat.add a a)) (Nat.add a a)) b
>>
*)
Abort.

Goal (a + a) + (a + a) + (a + a) < b.
Proof.
  generalize (a + a) as m.
(**
goal: <<forall m : nat, m + m + m < b>>
*)
  Show Proof.
(**
<<
(?Goal (a + a))
>>

ここでは、generalize に a + a を指定しており、a + a はゴールに3箇所存在するので
それがすべて変数 m に置き換わっています。
*)
  Restart.
  generalize (a + a) at 1 3 as m.
(**
goal: <<forall m : nat, m + (a + a) + m < b>>
*)
  Show Proof.
(**
<<
(?Goal (a + a))
>>

すべてでなく、一部分だけを置き換えるには、generalize に at を指定します。
ここでは、1 3 を指定することにより、1番めと3番めの a + a を置き換えています。

なお、バグか仕様かはわかりませんが、置き換えを行わないようにするには、
at のところに 0 を指定することができるようです。(Coq 8.6, Coq 8.7で確認)
*)
  Restart.
  generalize (a + a) at 0 as m.
(**
goal: <<nat -> a + a + (a + a) + (a + a) < b>>
*)
  Show Proof.
(**
<<
(?Goal (a + a))
>>
*)

Abort.

End Generalize.
