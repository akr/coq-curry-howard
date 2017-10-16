(** * カリーハワード対応とCoqのあいだ

Coq の証明はカリーハワード対応を利用し
プログラムによって表現されているというのはよく知られています。

カリーハワード対応というのは、
命題と型、証明とプログラムが対応しているという話です。

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

*)