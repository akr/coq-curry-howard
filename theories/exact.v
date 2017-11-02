(** ** exact

この forall (P : Prop), P -> P という命題を、今度は auto を使わずに、
exact を使って証明してみましょう。

今回は Show Proof で各ステップごとに構築されていく項を見ていきます。
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
  exact (fun (P : Prop) (H : P) => H).
  Show Proof.
(**
<<
(fun (P : Prop) (H : P) => H)
>>
exact では ?Goal に埋めるべき証明項を直接指定することができます。
ここでは、auto で作られたのと同じ、(fun (P : Prop) (H : P) => H) を指定しています。
これにより、No more subgoals. と表示され、証明が終わったことがわかります。
その後で Show Proof とすると、(fun (P : Prop) (H : P) => H) と表示され、
exact で指定した証明項が構築されていることがわかります。
*)
Qed.
