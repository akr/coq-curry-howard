(** ** destruct

destruct term というのは指定した term の場合分けを行う tactic です。
term は inductive な型の値でなければなりません。
inductive な型の値はその型のコンストラクタのいずれかで生成されているので、
それぞれのコンストラクタの場合分けします。

コンストラクタで場合分けする、というのはつまり match 式です。
ですから、destruct は証明項に match を構築する tactic といえます。



*)

(** *** case term

まず、(destruct term ではなく) case term という tactic を試します。
case term は destruct term の派生形のひとつで、
destruct term よりも単純な証明項を生成します。

また、case term は SSReflect の case とは異なります。
SSReflect の case は引数をとらずに case. としたり、: tactical をつけて case: という
形なので、Coq 本体の case term とは区別できます。

例として bool 型の二重否定の除去の証明を使います。
(なお、難しい話を知っているひとに注意しておきますが、
これは bool の話であり、命題の話ではないので、直観主義論理でも問題なく証明できます。)

ここでは、negb 関数を使いますが、これは bool の否定を行う関数です。

*)

Goal forall b, negb (negb b) = b.
Proof.
(**
<<
1 subgoal
______________________________________(1/1)
forall b : bool, negb (negb b) = b
>>
最初は、Goal に与えた命題がそのまま証明すべき命題として提示されています。
*)
  Show Proof.
(**
<<
?Goal
>>
もちろん、この最初の時点の証明項は ?Goal です。
*)
  intro b.
(**
<<
1 subgoal
b : bool
______________________________________(1/1)
negb (negb b) = b
>>
Coq の case では引数に term を指定する必要があります。
ここでは b を指定したいのですが、
そのためには前提に b がある（外側で b が束縛されている）必要があります。
そのため、intro で b を前提に動かします。
*)
  Show Proof.
(**
<<
(fun b : bool => ?Goal)
>>
*)
  case b.
(**
<<
2 subgoals
b : bool
______________________________________(1/2)
negb (negb true) = true
______________________________________(2/2)
negb (negb false) = false
>>
case b により、b で場合分けを行います。
b は bool なので true か false のどちらかであり、
それぞれの場合についての命題の証明が必要だと提示されています。
*)
  Show Proof.
(**
<<
(fun b : bool =>
 if b as b0 return (negb (negb b0) = b0) then ?Goal else ?Goal0)
>>
if が表示されてしまったので、Display all low-level contents を有効にして
Show Proof をやりなおしましょう。
<<
(fun b : bool =>
 match b as b0 return (@eq bool (negb (negb b0)) b0) with
 | true => ?Goal@{b:=b}
 | false => ?Goal0@{b:=b}
 end)
>>
case b をやる前には ?Goal だったところに match 式が埋められています。
つまり、case b が match 式を構築したことがわかります。
この match 式は match b as ... と書かれているので、b で分岐します。
true の場合と false の場合それぞれ分岐の中身は ?Goal@{b:=b} と ?Goal0@{b:=b} と
書かれており、これらは subgoal がふたつあることに対応しています。

match 式の as b0 return (negb (negb b0) = b0) の部分は、
この match 式自身の型および各分岐の型を示しています。
b0 を match 対象の b に置き換えた場合が match 式自身の型であり、
b0 を true や false に置き換えた場合が各分岐の型になります。

実際、b0 を b にすれば、negb (negb b) = b という case b とする前の命題になりますし、
b0 を true, false にすれば negb (negb true) = true, negb (negb false) = false という
case b とした後の命題になっています。

というわけで、あとは場合分けした結果の negb (negb true) = true
と negb (negb false) = false の
証明を行えば証明項を完成できます。

negb (negb true) と negb (negb false) には変数が含まれておらず、実際に計算を進めれば
true と false になります。
つまり、命題はすでに reflexivity で証明できるようになっています。
*)
    reflexivity.
  reflexivity.
  Show Proof.
(**
<<
(fun b : bool =>
 if b as b0 return (negb (negb b0) = b0) then eq_refl else eq_refl)
>>

Display all low-level contents を有効にすると以下のようになります。

<<
(fun b : bool =>
 match b as b0 return (@eq bool (negb (negb b0)) b0) with
 | true => @eq_refl bool true
 | false => @eq_refl bool false
 end)
>>

証明項をみると、?Goal@{b:=b} と ?Goal0@{b:=b} だったところに
reflexivity が構築した @eq_refl bool true と @eq_refl bool false が
入っていることがわかります。
*)
Qed.
