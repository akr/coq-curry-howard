From mathcomp Require Import all_ssreflect.

(** ** move:
SSReflect で、move=> H は証明対象の命題から前提に移すものですが、
逆に、前提から証明対象の命題に移すのは move: H を使います。
*)

Section Discharge.

Variable P : Prop.

Goal P -> P.
Proof.
  Show Proof.
(** 先ほどのセクションの説明と同じく、P -> P の証明ですが、
最初に Show Proof とすると、?Goal と表示され、
証明項はまったくできていないことがわかります。
*)
  move=> H.
  Show Proof.
(** move=> H で、前提に移したところで
Show Proof とすると、(fun H : P => ?Goal) となり、
引数Hを受け取るラムダ抽象が構築されることがわかります。 
*)
  move: H.
  Show Proof.
(** ここで move: H として、H を証明対象に戻したところで Show Proof とすると、
(fun H : P => ?Goal H) と表示されます。
まずわかることは「戻す」というのは証明項が元に戻るわけではないことです。
実際には ?Goal が ?Goal H に変化する、つまり、戻したものを引数とする関数呼び出しが構築され、
関数部分が新しいゴールとなります。
*)
  move=> H.
  move: H.
  move=> H.
  move: H.
  Show Proof.
(** 意味もなく move=> H と move: H を繰り返してみると、証明項は
(fun H : P => (fun H0 : P => (fun H1 : P => ?Goal H1) H0) H)
となります。関数抽象と関数呼び出しが増えていることが分かります。
Coq が表示する前提と証明する命題は変わりませんが、
内部では証明項が（意味もなく）膨らんでいるわけです。
move: の動作は確認できたので証明を終りましょう。
ここでは Abort で証明を中断する、つまり証明項を完成させずに終ることにします。
*)
Abort.

End Discharge.
