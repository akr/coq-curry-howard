(** * カリーハワード対応とCoqのあいだ

Coq はカリーハワード対応を利用して
証明をプログラムによって表現しているというのはよく知られています。

カリーハワード対応というのは、
命題と型、証明とプログラムが同じ構造になっているという話です。

しかし、Coq の proof editing mode で証明をしていると、
証明項（プログラムですが、あまりプログラムとしては意識しないので証明項と呼びましょう）
がどのようなものか意識することは少ないのではないでしょうか。

たとえば、intros H がなにをする（どんな証明項を構築する）のか
わかるでしょうか。

ここでは Coq のいろいろなコマンドがなにをするものなのか、また、
それをどうやって調べるのか説明します。

*)

(**

- % auto % # <a href="auto.html">auto</a> #
- % exact % # <a href="exact.html">exact</a> #
- % intro % # <a href="intro.html">intro</a> #
  SSReflect:
  % move=> % # <a href="ssr_intro.html">move=&gt;</a> #
- % Section % # <a href="section.html">Section</a> #
- revert
  generalize
  SSReflect:
  % move:% # <a href="ssr_discharge.html">move:</a> #
- % apply % # <a href="apply.html">apply</a> #
- % reflexivity % # <a href="reflexivity.html">reflexivity</a> #
- % rewrite % # <a href="rewrite.html">rewrite</a> #
  SSReflect:
  % rewrite % # <a href="ssr_rewrite.html">rewrite</a> #
- % destruct % # <a href="destruct.html">destruct</a> #
  SSReflect:
  % case % # <a href="ssr_case.html">case</a> #
- induction
  SSReflect:
  elim
- f_equal
  SSReflect:
  congr
- assert
  SSReflect:
  have
- SSReflect:
  wlog
  suff
- SSReflect: pose set unlock
- specialize
- unfold fold cutrewrite
- injection case_eq
- refine
- simpl
- clear
- now
- discriminate
- assumption
- contradiction
- pattern

*)

(**
URL:
% https://akr.github.io/coq-curry-howard/curry_howard.html %
# <a href="https://akr.github.io/coq-curry-howard/curry_howard.html">https://akr.github.io/coq-curry-howard/curry_howard.html</a> #

リポジトリ:
% https://github.com/akr/coq-curry-howard %
# <a href="https://github.com/akr/coq-curry-howard">https://github.com/akr/coq-curry-howard</a> #
*)
