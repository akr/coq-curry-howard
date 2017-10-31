(** * カリーハワード対応とCoqのあいだ

Coq はカリーハワード対応を利用して
証明をプログラムによって表現しているというのはよく知られています。

カリーハワード対応というのは、
命題と型、証明とプログラムが同じ構造になっているという話です。

しかし、Coq の proof editing mode で証明をしていると、
証明項（プログラムですが、あまりプログラムとしては意識しないので証明項と呼びましょう）
がどのようなものか意識することは少ないのではないでしょうか。

たとえば、move=> H がなにをする（どんな証明項を構築する）のか
わかるでしょうか。

（この文章は SSReflect 前提なので、intro じゃなくて move=> を使っています）

ここでは Coq のいろいろなコマンドがなにをするものなのか、また、
それをどうやって調べるのか説明します。

*)

(**

- % auto % # <a href="auto.html">auto</a> #
- % exact % # <a href="exact.html">exact</a> #
- % move=> % # <a href="intro.html">move=&gt;</a> #
- % Section % # <a href="section.html">Section</a> #
- % move: % # <a href="discharge.html">move:</a> #
- % apply % # <a href="apply.html">apply</a> #
- % reflexivity % # <a href="reflexivity.html">reflexivity</a> #
- % rewrite % # <a href="rewrite.html">rewrite</a> #
- % case % # <a href="case.html">case</a> #

*)

(**
URL:
% https://akr.github.io/coq-curry-howard/curry_howard.html %
# <a href="https://akr.github.io/coq-curry-howard/curry_howard.html">https://akr.github.io/coq-curry-howard/curry_howard.html</a> #

リポジトリ:
% https://github.com/akr/coq-curry-howard %
# <a href="https://github.com/akr/coq-curry-howard">https://github.com/akr/coq-curry-howard</a> #
*)
