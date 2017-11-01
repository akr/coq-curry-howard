From mathcomp Require Import all_ssreflect.

(** ** case

case というのは場合分けを行う tactic です。

証明項では match 式によって場合分けが行われるので、
case は証明項に match を構築する tactic といえます。

*)

(**

まず、bool 型の二重否定の除去の証明を見てみましょう。
(なお、難しい話を知っているひとに注意しておきますが、
これは bool の話であり、命題の話ではないので、直観主義論理でも問題なく証明できます。)

*)

Goal forall b, ~~ ~~ b = b.
Proof.
(**
SSReflect では、単に case. と指示すると、
証明すべき命題の最も外側の引数を場合分けします。
今回の場合、証明すべき命題は forall b : bool, ... という形なので、
この b を場合分けします。
*)
  case.
(**
このように場合分けすると、以下のようにふたつの subgoal が生成されます。
<<
2 subgoals
______________________________________(1/2)
~~ ~~ true = true
______________________________________(2/2)
~~ ~~ false = false
>>

この状態で証明項を表示すると以下のようになります。
*)
  Show Proof.
(**
<<
(fun _top_assumption_ : bool =>
 (fun (_evar_0_ : (fun b : bool => ~~ ~~ b = b) true)
    (_evar_0_0 : (fun b : bool => ~~ ~~ b = b) false) =>
  if _top_assumption_ as b return ((fun b0 : bool => ~~ ~~ b0 = b0) b)
  then _evar_0_
  else _evar_0_0) ?Goal ?Goal0)
>>

match じゃなくて if と表示されてしまったので、
Display all low-level contents を有効にして
Show Proof をやりなおすと以下のようになります。

<<
(fun _top_assumption_ : bool =>
 (fun (_evar_0_ : (fun b : bool => @eq bool (negb (negb b)) b) true)
    (_evar_0_0 : (fun b : bool => @eq bool (negb (negb b)) b) false) =>
  match
    _top_assumption_ as b
    return ((fun b0 : bool => @eq bool (negb (negb b0)) b0) b)
  with
  | true => _evar_0_
  | false => _evar_0_0
  end) ?Goal ?Goal0)
>>

これで、case が match を構築することが確認できました。

証明項をみると、まず、?Goal と ?Goal0 というふたつの未知の部分があることがわかります。
これは subgoal がふたつあることに対応しています。

また、?Goal は <<_evar_0_>> に束縛され、その型は (fun b : bool => ~~ ~~ b = b) true です。
この型はちょっと計算を進めると（ベータ展開すると）~~ ~~ true = true になるので、
?Goal は最初の subgoal に対応することが分かります。

同様に、?Goal0 は <<_evar_0_0>> に束縛され、最後の subgoal に対応することが分かります。

証明項全体は <<fun _top_assumption_ : bool => ...>> という形なので、
場合分けの対象の bool 値は <<_top_assumption_>> に束縛されます。

そして、（<<_evar_0_>> と <<_evar_0_0>> に今後行う証明を受け取った後）
以下の match で場合分けが行われます。
<<
match
  _top_assumption_ as b
  return ((fun b0 : bool => ~~ ~~ b0 = b0) b)
with
| true => _evar_0_
| false => _evar_0_0
end
>>

この match では <<_top_assumption_>> で場合分けを行い、
場合分けを行った値を b という変数に束縛した上で、
true もしくは false の分岐を評価します。
今回の場合は <<_evar_0_>> と <<_evar_0_0>> のどちらかの値（証明）を返すだけです。

そして、return のところに書いてある ((fun b0 : bool => ~~ ~~ b0 = b0) b) が
この match 式の型であり、また、各分岐の型にもなっています。

((fun b0 : bool => ~~ ~~ b0 = b0) b) は計算を進めると（ベータ展開すると）
~~ ~~ b = b となり、もともと証明すべき命題になっています。

true が選ばれたときを考えると、b は true になるので、
((fun b0 : bool => ~~ ~~ b0 = b0) true) が true の分岐の型であり、
ちょっと計算を進めると、~~ ~~ true = true になるので
分岐本体の <<_evar_0_>> と型が一致します。

同様に、false が選ばれたときは ((fun b0 : bool => ~~ ~~ b0 = b0) false) という型になり、
分岐本体の <<_evar_0_0>> と型が一致します。

というわけでどっちの分岐が選ばれても型は合うので、match 式自体の型は
（b は <<_top_asssumption_>> なので）、<<~~ ~~ _top_assumption_ = _top_assumption_>> になります。

これの外側を <<fun _top_assumption_ : bool => ...>> という関数抽象でくくってあるので、
全体の型は <<forall _top_assumption_ : bool, ~~ ~~ _top_assumption_ = _top_assumption_>>
であり、ローカル変数の名前を変換（アルファ変換）すると、<<forall b : bool, ~~ ~~ b = b>> という
もともと証明しようとしている命題と同じになることがわかります。

というわけで、あとは場合分けした結果の ~~ ~~ true = true と ~~ ~~ false = false の
証明を行えば証明項を完成できます。

~~ ~~ true と ~~ ~~ false には変数が含まれておらず、実際に計算を進めれば
true と false になります。
つまり、命題はすでに reflexivity で証明できるようになっています。
*)
    reflexivity.
  reflexivity.
  Show Proof.
(**
<<
(fun _top_assumption_ : bool =>
 (fun (_evar_0_ : (fun b : bool => ~~ ~~ b = b) true)
    (_evar_0_0 : (fun b : bool => ~~ ~~ b = b) false) =>
  if _top_assumption_ as b return ((fun b0 : bool => ~~ ~~ b0 = b0) b)
  then _evar_0_
  else _evar_0_0) (erefl true) (erefl false))
>>

証明項をみると、?Goal と ?Goal0 だったところに
reflexivity が構築した (erefl true) と (erefl false) が入っていることがわかります。
*)
Qed.


