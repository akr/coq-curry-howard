From mathcomp Require Import all_ssreflect.

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
  Show Proof.
(**
<<
?Goal
>>

証明がはじまったばかりの段階では、証明項全体をこれから構築していく段階なので、
?Goal とだけ表示されます。
*)
  rewrite addnC.
(**
SSReflect では、自然数の加算の交換律は addnC という補題として用意されているので、
rewrite addnC で書き換えを行えます。

このケースでは、rewrite は b + c という部分を書き換えの対象として発見し、
これを c + b に書き換えます。

書き換えた結果、証明すべき命題は a * (c + b) = a * (c + b) に変化します。
*)
  Show Proof.
(**
<<
((fun _evar_0_ : a * (c + b) = a * (c + b) =>
  eq_ind_r (fun _pattern_value_ : nat => a * _pattern_value_ = a * (c + b))
    _evar_0_ (addnC b c)) ?Goal)
>>

書き変えを行った後、Show Proof で証明項を表示すると、上のようになります。

なんだか複雑ですが、まず、大きな構造としては、
(なんか複雑な項 ?Goal) という形になっていることがわかります。
つまり、rewrite は証明項を関数適用として具体化し、またその関数部分に具体的な項を割り当てています。
これは、apply と同じです。

また、関数部分に割り当てた項をみると、内部で eq_ind_r と addnC という名前が使われています。
addnC は rewrite に指定したのでそれが使われているわけですが、
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
((fun _evar_0_ : a * (c + b) = a * (c + b) =>
  @eq_ind_r nat (c + b)
    (fun _pattern_value_ : nat => a * _pattern_value_ = a * (c + b)) _evar_0_
    (b + c) (addnC b c)) ?Goal)
>>

ここでは eq_ind_r のかわりに @eq_ind_r と @ がついて表示され、
省略を行わない形式であることを示しています。

この時点で証明すべき命題は a * (c + b) = a * (c + b) ですが、
これは証明項の中の ?Goal の型です。
このことは、?Goal が関数適用の引数であり、それを受け取る関数部分が関数抽象であり、
関数抽象の引数 _evar_0_ の型が a * (c + b) = a * (c + b) であることからも確認できます。

eq_ind_r の引数は以下のように与えられています。
- A は nat
- x は c + b
- P は <<fun _pattern_value_ : nat => a * _pattern_value_ = a * (c + b)>>
- P x という型の無名引数は <<_evar_0_>>
- y は b + c
- @eq A y x という型 (y = x という型) の無名引数は addnC b c

また、eq_ind_r の返り値の型は P y です。

P は nat を受け取って命題を返す関数で、具体的には <<_pattern_value_>> を
受け取って <<a * _pattern_value_ = a * (c + b)>> という命題を返します。
したがって、P x は P (c + b) であり、つまり a * (c + b) = a * (c + b) です。
P y や P (b + c) であり、つまり a * (b + c) = a * (c + b) です。

結局、rewrite は eq_ind_r を使って、
P x すなわち a * (c + b) = a * (c + b) の証明を受け取って、
P y すなわち a * (b + c) = a * (c + b) の証明を返す、という関数を作り上げています。

そういう関数があれば証明すべき命題を後者から前者に変化させることができるので、
rewrite はそれを実際に行っています。
行った結果、残った前者の命題は、次に証明すべき命題としてユーザに提示されるというわけです。
*)
  reflexivity.
  Show Proof.
(**
<<
((fun _evar_0_ : a * (c + b) = a * (c + b) =>
  eq_ind_r (fun _pattern_value_ : nat => a * _pattern_value_ = a * (c + b))
    _evar_0_ (addnC b c)) (erefl (a * (c + b))))
>>

rewrite の結果、右辺と左辺が同じ形になったので、reflexivity で証明できます。
Show Proof の結果をみると、
reflexivity で erefl (a * (c + b)) という証明項が構築されていることがわかります。
*)
Qed.

End Rewrite.

(**
ところで、rewrite で match, let, ラムダ式の body を書き換えようとして
書き換えられずに困ったことはないでしょうか。
*)

Goal (fun a => a + 2) = (fun a => 2 + a).
Proof.
  Fail rewrite addnC.
(**
ここでは、a + 2 を 2 + a に書き換えようとして、
rewrite addnC としていますが失敗してしまいます。

これは、rewrite が eq_ind_r を使って作り上げる関数を考えると理解できます。
eq_ind_r には x として 2 + a, y として a + 2 を渡す必要がありますが、
eq_ind_r の引数の場所では a は束縛されていないので使えません。

束縛されていないものであれば、ラムダ式の body であっても書き換えられます。
たとえば、2 を 1 + 1 に書き換えるには addn1 を逆方向に使うことで可能です。
*)
  rewrite -addn1.
  Show Proof.
(**
<<
((fun _evar_0_ : addn^~ (1 + 1) = [eta addn (1 + 1)] =>
  eq_ind (1 + 1)
    (fun _pattern_value_ : nat =>
     addn^~ _pattern_value_ = [eta addn _pattern_value_]) _evar_0_ 2
    (addn1 1)) ?Goal)
>>
逆方向の書き換えなので、eq_ind_r ではなく eq_ind が使われていますが、
似たような構造であり、また、引数に 1 + 1 が現れていることが分かります。

この証明項では a の束縛は行われていないので、
a は使えません。
1 + 1 に a は使われていないので問題ありませんが、
1 + 1 のところに 2 + a を与えようとすれば証明項は束縛されていない a を参照してしまう
ことになってしまいます。

というわけで、(証明すべき命題の中で) 束縛されている変数は rewrite では使えないわけです。
*)
Abort.
