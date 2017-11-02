(** ** revert

intro H は 証明対象の命題から前提に移すものですが、
逆に、前提から証明対象の命題に移すのは revert H を使います。

*)

Section Revert.

Variable P : Prop.

Goal P -> P.
Proof.
  Show Proof.
(**
<<
?Goal
>>
先ほどのセクションの説明と同じく、P -> P の証明ですが、
最初に Show Proof とすると、?Goal と表示され、
証明項はまったくできていないことがわかります。
*)
  intro H.
  Show Proof.
(**
<<
(fun H : P => ?Goal)
>>
intro H で、H : P を前提に移したところで
Show Proof とすると、(fun H : P => ?Goal) となり、
引数Hを受け取る関数抽象が構築されることがわかります。
*)
  revert H.
  Show Proof.
(**
<<
(fun H : P => ?Goal H)
>>
ここで revert H として、H : P を証明対象に戻したところで Show Proof とすると、
(fun H : P => ?Goal H) と表示されます。
まずわかることは「戻す」というのは証明項が元に戻るわけではないことです。
実際には ?Goal が ?Goal H に変化する、つまり、戻したものを引数とする関数呼び出しが構築され、
関数部分が新しいゴールとなります。
*)
  intro H.
  revert H.
  intro H.
  revert H.
  Show Proof.
(**
<<
(fun H : P => (fun H0 : P => (fun H1 : P => ?Goal H1) H0) H)
>>
意味もなく intro H と revert H を繰り返してみると、証明項は
(fun H : P => (fun H0 : P => (fun H1 : P => ?Goal H1) H0) H)
となります。関数抽象と関数呼び出しが増えていることが分かります。
Coq が表示する前提と証明する命題は変わりませんが、
内部では証明項が（意味もなく）膨らんでいるわけです。

ここで、?Goal の外側には H, H0, H1 の束縛がありますが、
前提にこれらは表示されていません。
これは、Coq がすべての束縛を前提に表示するわけではなく、
revert は指定した前提を前提から表示しないようにするためです。

ここまでで確認したように、revert は証明項の関数適用とその引数部分を構築しますが、
引数部分にできるものはすでに存在する前提に限られます。
引数部分に任意の証明項を構築したい場合は他の tactic が必要になります。

revert の動作は確認できたので証明を終りましょう。
ここでは Abort で証明を中断する、つまり証明項を完成させずに終ることにします。
*)
Abort.

End Revert.
