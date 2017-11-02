Require Import Decidable.

(** ** specialize

generalize というのは、定理を特殊化する tactic です。
具体的には、定理の変数を具体的な項に変えた定理を前提に導入します。

ここでは 2重否定の除去を証明してみましょう。

直観主義論理において
命題の2重否定がその命題と等価であるためには、
その命題が decidable でなければなりません。
命題が decidable であればその命題の 2重否定を除去できるという定理 dec_not_not があります。

*)

About dec_not_not.
(**
<<
dec_not_not : forall P : Prop, decidable P -> (~ P -> False) -> P
>>
*)

Section Specialize.

(**
命題P と、それが decidable であるという仮定 DP を定義します。
*)
Variable P : Prop.
Hypothesis DP : decidable P.

Goal ~ ~ P <-> P.
Proof.
(**
ここで、dec_not_not の、decidable という部分は最初に与えてしまって特殊化した
定理を作りましょう。
*)
  specialize (dec_not_not P DP) as not_not.
(**
<<
not_not : (~ P -> False) -> P
>>
specialize により、上の定理が前提に入ります。
*)
  Show Proof.
(**
<<
(let not_not := dec_not_not P DP : (~ P -> False) -> P in ?Goal)
>>
証明項では、let により、not_not という名前で
dec_not_not P DP という証明項が束縛されています。
従って、?Goal の中では、not_not を使えます。

残りは specialize とは関係ないので、以下のように簡単に証明してしまいます。
*)
  split; auto.
Qed.

End Specialize.
