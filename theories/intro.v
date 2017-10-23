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
move=> P により、証明すべき命題 forall P : Prop, P -> P の左側の
forall P : Prop という部分が前提に移動して前提に P : Prop が入り、
証明すべき命題は P -> P に変化します。
ここで Show Proof とすると、(fun P : Prop => ?Goal) と表示されます。
つまり、move=> P は証明項を Prop型の値Pを受け取る関数抽象（λ式）として構築せよ、
という指示です。
関数抽象の本体はまだ不明なので ?Goal となっていますが、
この部分の型は (forall P : Prop, P -> P から左側の forall P : Prop を取り除いた型である)
P -> P です。
そのため、P -> P という型である ?Goal の部分をこれから構築しなければならない、
という状態であることがわかります。

なお、この段階で Display notations を無効にすると、証明すべき命題は
P -> P から、forall _ : P, P に変化します。
これにより、P -> P というのは forall _ : P, P の省略形であることがわかります。

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
move=> H により、証明すべき命題 P -> P の左側の P -> が消えて
前提に H : P に移動し、証明すべき命題は P に変化します。

Show Proof とすると、(fun (P : Prop) (H : P) => ?Goal) と表示されます。
つまり、?Goal を（また）関数抽象として構築せよ、という指示を行ったので、
証明項は関数抽象が2段ネストしたものとして (fun (P : Prop) (H : P) => ?Goal) という形に
なり、関数抽象の本体の P という型である ?Goal の部分をこれから構築しなければならない、
という状態であることが分かります。

Display notations が無効にするとわかるように、
これは証明すべき命題 forall _ : P, P の左側の
forall _ : P が前提に移動した、というわけで、
最初の move=> P が forall P : Prop を前提に移動したのと
同様なことをしていることがわかるでしょう。
ただし、forall P : Prop では、Prop 型の値に P という名前がついていましたが、
今回の forall _ : P では、P 型の値に名前がついておらず、_ になっています。
どちらにしても、move=> で指定した名前が関数抽象で導入される変数の名前として使われます。

前提に H が入ったのでここからは H を自由に使えますが、このことを
証明項の構造から説明すると、?Goal の部分の外側で H が束縛されているため、
?Goal の中では H を参照できる、という意味になります。
*)
  exact H.
  Show Proof.
(**
<<
(fun P : Prop => id)
>>
P という型の値としては H が存在する（参照できる）ので、
それを証明項として与えれば証明は終わりです。
exact H により H を証明項として直接与えると No more subgoals. と表示されて
証明が終ったことがわかります。
ここで Show Proof とすると、(fun P : Prop => id) と表示されます。
Display notations を無効にすれば (fun (P : Prop) (H : P) => H) と表示され、
上で ?Goal だったところに H が埋められていることが分かります。
証明項に不明な部分はもうないので、やることはもうありません。
Qed で証明を終りましょう。
*)
Qed.
