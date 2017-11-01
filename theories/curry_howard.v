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
  % move=> (SSReflect) % # <a href="ssr_intro.html">move=&gt; (SSReflect)</a> #
- % Section % # <a href="section.html">Section</a> #
- % move: (SSReflect) % # <a href="ssr_discharge.html">move: (SSReflect)</a> #
- % apply % # <a href="apply.html">apply</a> #
- % reflexivity % # <a href="reflexivity.html">reflexivity</a> #
- % rewrite (SSReflect) % # <a href="ssr_rewrite.html">rewrite (SSReflect)</a> #
- % destruct % # <a href="destruct.html">destruct</a> #
  % case (SSReflect) % # <a href="ssr_case.html">case (SSReflect)</a> #

*)

(**
URL:
% https://akr.github.io/coq-curry-howard/curry_howard.html %
# <a href="https://akr.github.io/coq-curry-howard/curry_howard.html">https://akr.github.io/coq-curry-howard/curry_howard.html</a> #

リポジトリ:
% https://github.com/akr/coq-curry-howard %
# <a href="https://github.com/akr/coq-curry-howard">https://github.com/akr/coq-curry-howard</a> #
*)
