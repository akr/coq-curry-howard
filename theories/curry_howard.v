(** * カリーハワード対応とCoqのあいだ

Coq はカリーハワード対応を利用して
証明をプログラムによって表現しているというのはよく知られています。

カリーハワード対応というのは、
命題と型、証明とプログラムが同じ構造になっているという話です。

しかし、Coq の proof editing mode で証明をしていると、
証明項（プログラムのことですが、あまりプログラムとしては意識しないので証明項と呼びましょう）
がどのようなものか意識することは少ないのではないでしょうか。

たとえば、intros H がなにをする（どんな証明項を構築する）のか
わかるでしょうか。

ここでは Coq のいろいろなコマンドがなにをするものなのか、また、
それをどうやって調べるのか説明します。

*)

(**

- 自動証明
  - % auto % # <a href="auto.html">auto</a> #
- 証明項を直接指定する
  - % exact % # <a href="exact.html">exact</a> #
- 関数抽象を構築する
  - % intro % # <a href="intro.html">intro</a> #
  - % move=> % # <a href="ssr_intro.html">move=&gt;</a> # (SSReflect)
  - % Section % # <a href="section.html">Section</a> #
- 関数適用とその引数部分を構築する
  - % revert % # <a href="revert.html">revert</a> #
  - % generalize % # <a href="generalize.html">generalize</a> #
  - % move:% # <a href="ssr_discharge.html">move:</a> # (SSReflect)
- 関数適用とその関数部分を構築する
  - % apply % # <a href="apply.html">apply</a> #
- let 式を構築する
  - % pose, set % # <a href="set.html">pose, set</a> #
  - % specialize % # <a href="specialize.html">specialize</a> #
- eq_refl で等式を証明する
  - % reflexivity % # <a href="reflexivity.html">reflexivity</a> #
- eq_ind_r で等式による書き換えを行う
  - % rewrite % # <a href="rewrite.html">rewrite</a> #
  - % rewrite % # <a href="ssr_rewrite.html">rewrite</a> # (SSReflect)
- match 式を構築する
  - % destruct % # <a href="destruct.html">destruct</a> #
  - % case % # <a href="ssr_case.html">case</a> # (SSReflect)
- simpl change unfold fold pattern
- clear rename move_after
- 数学的帰納法を適用する
  - % induction % # <a href="induction.html">induction</a> #
  - elim (SSReflect)
- f_equal
  congr (SSReflect)
- assert
  have (SSReflect)
- wlog (SSReflect)
  suff (SSReflect)
- replace
- unlock
- injection case_eq
- refine
- now
- discriminate
- assumption
- contradiction
- inversion

*)

(**
URL:
% https://akr.github.io/coq-curry-howard/curry_howard.html %
# <a href="https://akr.github.io/coq-curry-howard/curry_howard.html">https://akr.github.io/coq-curry-howard/curry_howard.html</a> #

リポジトリ:
% https://github.com/akr/coq-curry-howard %
# <a href="https://github.com/akr/coq-curry-howard">https://github.com/akr/coq-curry-howard</a> #
*)
