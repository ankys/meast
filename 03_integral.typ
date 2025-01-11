
= ルベーグ積分

== 可測関数

この章の目標は測度空間$(X, cal(F), m)$上の実数値関数$f: X -> RR$に対して積分を導入することであるが、
そのためには積分が定義される可測関数と呼ばれる関数のクラスを定義する必要がある。
もちろん可測関数も可測写像の枠組みで考えられるが、そのためには実数の集合$RR$に完全加法族を定め可測性を定義する必要がある。
ボレル可測性やルベーグ可測性を導入すればよいのだが、理論的に大変なのでここでは積分が定義されるのに必要な条件だけ書き出し、ボレル可測性などは後の章で議論することにする。

可測空間$(X, cal(F))$上の拡張実数値関数$f: X -> macron(RR) = RR union { plus.minus oo }$が、任意の$t in RR$に対して等高集合$f^(-1) ([t,+oo])$が$X$の可測集合であるとき、$f$は_可測関数_であるという。
また、$(X, cal(F))$上の複素数値関数$f: X -> CC$に対して、その実数部分$Re f$と虚数部分$Im f$の両方が実数値可測関数の時、$f$は_可測関数_という。

可測関数は様々な演算について閉じている。
そのことを示す前に可算関数の定義において$t$は有理数に取り替えられることを示す。
有理数の集合$QQ$は可算で$RR$上稠密であることに注意する。

#proposition[
可測空間$(X, cal(F))$上の拡張実数値関数$f: X -> macron(RR) = RR union { plus.minus oo }$が可測関数であることは、任意の$t in QQ$に対して等高集合$f^(-1) ([t, +oo])$が$X$の可測集合であることと同値である。
]

#proof[
有理数$t$は実数でもあるので、片方の主張は自明である。
可測関数であることを示すために$t$を実数とする。
この時$t'$を$t$以下の有理数として
$
[t,+oo] = sect.big_(t' <= t) [t', +oo]
$
が成り立つ。
よって、
$
f^(-1) ([t,+oo]) = sect.big_(t' <= t) f^(-1) ([t', +oo])
$
であり右辺は可測集合の可算交叉なので可測集合で$f$は可測関数である。
したがって証明が完了する。
]

また、次のことも成立する。

#proposition[
可測空間$(X, cal(F))$上の拡張実数値関数$f: X -> macron(RR) = RR union { plus.minus oo }$が可測関数であることは、任意の$t in RR$に対して等高集合$f^(-1) ([-oo, t])$が$X$の可測集合であることと同値である。
]

#proof[
まず
$
f^(-1) (\[-oo, t\)) = f^(-1) ([t, +oo])^c
$
なので、これは可測集合であることに注意する。
さらに実数$t$に対して$t'$を$t$より大きい有理数として
$
[-oo, t] = sect.big_(t' > t) \[-oo, t'\)
$
が成り立つ。
よって、
$
f^(-1) ([- oo, t]) = sect.big_(t' > t) f^(-1) (\[-oo, t'\))
$
であり右辺は可測集合の可算交叉なので可測集合で$f$は可測関数である。
したがって証明が完了する。
]

#proposition([可測関数と極限演算])[
可算個の拡張実数値可測関数の各点での上限、下限、上極限、下極限は可測関数である。
]

等高集合$f^(-1) ([t, +oo])$や$f^(-1) ([-oo, t])$のことを${ f >= t }$や${ f <= t }$のように略記する。

#proof[
可算個の拡張実数値可測関数$f_n$に対して下限$inf_n f_n$が可測関数であることを示す。
実数$t$に対して
$
{ inf_n f_n >= t } = sect.big_n { f_n >= t }
$
であり右辺は可測集合なので、$inf_n f_n$は可測関数である。
同様にして上限$sup_n f_n$も
$
{ sup_n f_n <= t } = sect.big_n { f_n <= t }
$
なので可測関数である。
さらに上極限、下極限は上限、下限で書き表されるのでやはり可測関数である。
]

#proposition([可測関数と四則演算])[
二つの拡張実数値あるいは複素数値の可測関数の和差積商はそれが定義される限り可測関数である。
]

#proof[
拡張実数値可測関数$f, g$に対して和$f+g$が可測関数であることを示す。
有理数$t$に対して
$
{ f+g >= t } = union.big_(a+b >= t) { f >= a } sect { g >= b }
$
であり右辺は可測集合なので、$f+g$は可測関数である。

TODO
]

== 積分の定義

測度空間$(X, m)$上の拡張実数値あるいは複素数値の関数$f$に対してその積分値を定義する。
そのためにはまずは拡張非負値可測関数$f: X -> macron(RR)_(+) = [0, oo]$に対して$y <= f(x)$の部分の面積を考える。
ここで関数値$t >= 0$ごとに等高集合${ f >= t }$の測度は$m({ f >= t })$であり、それを$t$に関する（リーマン）積分をとれば面積が得られるのでこのアイデアでルベーグ積分を定義する。

より詳しくは等高集合${ f >= t }$は$t$が増大すると小さくなることから測度$m({ f >= t })$は単調減少する。
したがってこれは有界閉区間$[0, T]$でリーマン積分可能であり$T -> oo$とすることで広義リーマン積分は収束するか無限大に発散するので、_ルベーグ積分_
$
integral_X f dd(m) := integral_0^oo m({ f >= t }) dd(t) in [0, oo]
$
を定義する。
ルベーグ積分の値が有限値のとき非負値関数$f$は_ルベーグ積分可能_といい$integral_X f dd(m) < oo$とも表す。
ルベーグ積分の記号において$X, dd(m), f$は省略されうる。
反対に$f$の変数$x$を明示したい場合は
$
integral_X f dd(m) = integral_X f (x) dd(m)(x) = integral_X f (x) m(dd(x))
$
などと書くこともある。

一般の（非負値とは限らない）拡張実数値可測関数$f: X -> macron(RR)$に対しては$f$の正部と負部
$
f^+ (x) = max { f(x), 0 },
quad f^- (x) = -min { f(x), 0 }
$
がともにルベーグ積分可能であるとき、
$f$は_ルベーグ積分可能_であるといい_ルベーグ積分_の値を
$
integral_X f dd(m) = integral_X f^+ dd(m)-integral_X f^- dd(m)
$
で定義する。
絶対値を使うと$abs(f) = f^++f^-$なので、
拡張実数値可測関数$f$がルベーグ積分可能であるという条件は非負値関数$abs(f)$がルベーグ積分可能つまり
$
integral_X abs(f) dd(m) < oo
$
と表すことができる。
このためここでのルベーグ積分は絶対可積分の理論である。

複素数値可測関数$f: X -> CC$に対しては$f$の実部$Re f$と虚部$Im f$がともにルベーグ積分可能であるとき、
$f$は_ルベーグ積分可能_であるといい_ルベーグ積分_の値を
$
integral_X f dd(m) = integral_X Re f dd(m)+i integral_X Im f dd(m)
$
で定義する。
あとで見るように複素数値可測関数$f$がルベーグ積分可能であるという条件は非負値関数$abs(f)$がルベーグ積分可能つまり$integral_X abs(f) dd(m) < oo$と表すことができる。
そのため、どの場合でもルベーグ積分可能の条件は$integral_X abs(f) dd(m) < oo$と書くことができる。

== 定義関数と単関数

可測空間$(X, cal(F))$の可測集合$A in cal(F)$に対して_定義関数_$1_A$を
$
1_A (x) = cases(
  1 & (x in A)",",
  0 & (x in.not A),
)
$
で定める。

#proposition([定義関数])[
可測集合$A$の定義関数$1_A$は非負値可測関数で
$
integral_X 1_A dd(m) = m(A)
$
が成り立つ。
]

#proof[
等高集合を計算すると
$
{ 1_A >= t }
= cases(
  X & (t = 0)",",
  A & (0 < t <= 1)",",
  nothing & (t > 1),
)
$
なので、可測であり積分は
$
integral_ X 1_A dd(m)
= integral_0^oo m({ 1_A >= t }) dd(t)
= integral_0^1 m(A) dd(t)+ integral_1^oo 0 dd(t)
= m(A)
$
となる。
]

単関数とは定義関数の線形和で表される関数のことである。
つまり、可測集合$A_1, dots, A_n in cal(F)$と正の数$c_1, dots, c_n$を使って
$
sum_i c_i 1_(A_i) = c_1 1_(A_1)+dots+c_n 1_(A_n)
$
と表される関数を（非負数値）_単関数_という。
単関数の概念は係数$c_1, dots, c_n$が複素数の場合に拡張できるが、理論を進める上では非負の数に対して定義したので十分である。

#proposition([単関数])[
単関数$f = sum_i c_i 1_(A_i) = c_1 1_(A_1)+dots+c_n 1_(A_n)$は可測関数で
$
integral_X f dd(m) = sum_i c_i m(A_i) = c_1 m (A_1)+dots+c_n m (A_n)
$
が成り立つ。
]

この命題の証明は飛ばす。

単関数に対応する可測集合と係数は一意でないが、扱いやすい特別なものとして次の標準形が知られている。
つまり、単関数$f = sum_i c_i 1_(A_i) = c_1 1_(A_1)+dots+c_n 1_(A_n)$に対してとりうる値は高々$2^n$通りなのでこれを$m$通りとして小さい順に$d_1, dots, d_m$とおく。
さらに$B_j = f^(-1) (d_j)$とおくことで単関数$f$の_標準形_
$
f = sum_j d_j 1_(B_j) = d_1 1_(B_1)+dots+d_m 1_(B_m)
$
を得る。
これは$B_1, dots, B_m$は互いに交わりを持たず、$d_1 < dots < d_m$となっていて、その表現は一意になることがわかる。
この形式は関数を縦に切っているのでリーマン積分的であると言える。

ルベーグ積分的な形式もあり、以下のように構成される。
標準形$f = sum_j d_j 1_(B_j) = d_1 1_(B_1)+dots+d_m 1_(B_m)$にした後、$C_i = B_i union dots union B_m$,
$e_1 = d_1$, $e_i = d_i-d_(i -1)$とすれば単関数$f$の_基本形_
$
f = sum_j e_j 1_(C_j) = e_1 1_(C_1)+dots+e_m 1_(C_m)
$
を得る。
これは$X = C_1 supset dots supset C_m$と$e_(i+1) > 0$を満たす。

この節で定義関数や単関数を扱っているのはそれらによってもルベーグ積分を特徴付けられるためである。

#theorem([単関数近似])[
$f$を測度空間$(X, m)$上の非負値可測関数とする。
このとき$g$を$g <= f$を満たす非負値可測単関数として、
$
integral_X f dd(m) = sup_(0 <= g <= f) integral_X g dd(m)
$
が成り立つ。
]

#proof[
$0 <= g <= f$なる非負値単関数$g$についてその基本形を$g = sum_i c_i 1_(A_i) = c_1 1_(A_1)+dots+c_n 1_(A_n)$とする。
$t_0 = 0$, $t_i = c_1+dots+c_i$とおくと、$0 = t_0 < dots < t_n = c_1+dots+c_n := T$は$[0, T]$の分割で、$x in A_i$に対し$f (x) >= g (x) >= a_1+dots+a_i = t_i$なので、
$
integral_X g dd(m)
= sum_i c_i m(A_i)
<= sum_i m({ f >= t_i })(t_i-t_(i-1))
<= integral_0^T m({ f >= t }) dd(t)
<= integral_X f dd(m).
$
よって片側の不等号が得られた。

もう片方の不等号について、広義リーマン積分は定積分の端点$T > 0$と分割$0 = t_0 < dots < t_n = T$についての（下）リーマン和
$
sum_i m({ f >= t_i })(t_i-t_(i-1))
$
の上限であることに注意する。
ここで$A_i = { f >= t_i }$として$g = (t_i-t_(i -1)) 1_(A_i)$とおくとこれは$f$を超えない単関数になっているので、もう片方の不等号もいえる。
]

== 単調収束定理

積分論における単調収束定理とは単調増大する非負値可測関数の列を考えた時に積分の列が各点収束極限の積分に収束するという内容で積分と極限の交換を保証する十分条件を与える。
リーマン積分においては各点収束極限が可積分あるいは可測とは限らないが、ルベーグ積分ではこの単調収束定理が成立する。
単調収束定理に入る前に積分の単調性を示す。

#proposition([積分の単調性])[
測度空間$(X, m)$上の非負値可測関数$f_1, f_2$に対して、すべての$x in X$で$f_1 (x) <= f_2 (x)$のとき
$
integral_X f_1 dd(m) <= integral_X f_2 dd(m)
$
が成り立つ。
特に可算個の非負値可測関数$f_n$に対して
$
sup_n integral_X f_n dd(m) <= integral_X sup_n f_n dd(m)
$
が成り立つ。
]

この「すべての$x in X$で$f_1 (x) <= f_2 (x)$」という条件を$f_1 <= f_2$と略記する。

#proof[
$g$を$g <= f_1$を満たす非負値可測単関数とするとき、$g <= f_1 <= f_2$なので
$
integral_X g dd(m) <= integral_X f_2 dd(m)
$
であり、$g$についての上限をとることでほしかった不等式を得る。
さらに$f_n$に対して$f_n <= sup_n f_n$なので、
$
integral_X f_n dd(m) <= integral_X sup_n f_n dd(m)
$
であり、$n$に関する上限をとって後半部分の主張を得る。
]

#theorem([単調収束定理])[
測度空間$(X, m)$上の非負値可測関数の列$f_n$が単調増加する、つまり$f_n <= f_(n+1)$が成り立つとき、その各点収束極限
$
f(x) := lim_(n -> oo) f_n (x)
$
も非負値可測関数であり
$
lim_(n -> oo) integral_X f_n dd(m) = integral_X f dd(m)
$
が成り立つ。
]

#proof[
単調性の仮定より$f = lim_n f_n = sup_n f_n$なので、前に示したように$f$は可測である。
$0 <= f_n <= f_(n+1) <= f$なので、積分の単調性から
$
integral_X f_n dd(m) <= integral_X f_(n+1) dd(m) <= integral_X f dd(m)
$
が成り立つ。
したがって積分の列$integral_X f_n dd(m)$は単調増加なので収束するか無限大に発散し、その値は$integral_X f dd(m)$以下である。
あとはこれが実際には等しいことを示せばよい。
さらにこのことは$g <= f$を満たす非負値可測単関数$g$に対して$lim_n integral_X f_n dd(m) >= integral_X g dd(m)$を示すことに帰着される。
$g$の標準形を$g = sum_i c_i 1_(A_i)$として$m(A_i) < oo$の場合を考える。
$epsilon > 0$に対して
$
B_(i, n) = A_i cap { f_n >= c_i-epsilon }
$
と設定すると、$f_n <= f_(n+1)$より$B_(i, n) subset B_(i, n+1)$で$g <= f = sup_n f_n$より$union.big_n B_(i, n) = A_i$である。
さらに
$
integral_X f_n dd(m)
>= sum_i integral_(B_(i, n)) f_n dd(m)
>= sum_i (c_i-epsilon) m(B_(i, n))
>= sum_i c_i m (B_(i, n))-epsilon sum_i c_i m (A_i).
$
よって
$
integral_X g dd(m)
= sum_i c_i m(A_i)
// = sum_i c_i m(union.big_n B_(i, n))
= lim_n sum_i c_i m(B_(i, n))
<= lim_n integral_X f_n dd(m)+epsilon sum_i c_i m(A_i)
$
なので、
$epsilon -> 0$として$integral_X g dd(m) <= lim_n integral_X f_n dd(m)$を得る。
$m(A_i) = oo$となる$A_i$がある場合も同様の議論をすることで$lim_n integral_X f_n dd(m) = integral_X g dd(m) = oo$がわかる。
以上より単調収束定理が証明された。
]

ファトゥの補題は単調収束定理において単調性の仮定を外した時に得られる片側の不等式を保証する定理である。
内容はある意味で（ルベーグ）積分が下半連続になっているというものと解釈できる。

#theorem([ファトゥの補題])[
測度空間$(X, m)$上の非負値可測関数の列$f_n$に対して、その各点下極限
$
f(x) := liminf_(n -> oo) f_n (x) in macron(RR)_+
$
も非負値可測関数であり
$
liminf_(n -> oo) integral_X f_n dd(m) >= integral_X f dd(m)
$
が成り立つ。
]

#proof[
可測関数であることは前に示したとおりである。
自然数$n$に対して$g_n = inf_(k >= n) f_k$とおくと、$g_n$は単調増大して$f$に各点収束する。
ここですべての$k >= n$に対して$g_n <= f_k$なので、$integral_X g_n dd(m) <= integral_X f_k dd(m)$で$integral_X g_n dd(m) <= inf_(k >= n) integral_X f_k dd(m)$である。
ここで$n -> oo$とすることで単調収束定理から
$
integral_X f dd(m)
= lim_(n -> oo) integral_X g_n dd(m)
<= lim_(n -> oo) inf_(k >= n) integral_X f_k dd(m)
= liminf_(n -> oo) integral_X f_n dd(m)
$
となる。
]

== 積分の性質

#proposition([積分の線形性])[
測度空間$(X, m)$上の複素数値ルベーグ積分可能関数$f, g$と複素数$c$に対して、和$f+g$と定数倍$c f$もルベーグ積分可能であり
$
integral_X (f+g) dd(m) = integral_X f dd(m)+integral_X g dd(m),
quad integral_X c f dd(m) = c integral_X f dd(m)
$
が成り立つ。
]

#proof[
まず$f, g$が拡張非負値で$c$が非負の時を示す。
定数倍はすぐわかる。
和は$f, g$を単調単関数近似して$f_n, g_n$を取ると、$f_n+g_n$は$f+g$の単調単関数近似になっていて
$
integral_X (f_n+g_n) dd(m) = integral_X f_n dd(m)+integral_X g_n dd(m)
$
なので従う。

次に$f, g$が拡張実数値で$c$が実数の時を示す。
定数倍は$c$の符号で場合分けしてすぐわかる。
和も$f, g$の符号で四つの可測集合
$
A_(+ +) = { f >= 0, g >= 0 },
quad A_(+ -) = { f >= 0, g < 0 },
quad A_(- +) = { f < 0, g >= 0 },
quad A_(- -) = { f < 0, g < 0 }
$
に分けて考える。
このうち$A_(+ +)$と$A_(- -)$の部分は同符号なので先の非負値関数の和に帰着される。
あとは$A_(+ -)$を考えるとさらに$f+g$の符号で分けて
$
A_(+-+) = { f >= 0, g < 0, f+g >= 0 },
quad A_(+--) = { f >= 0, g < 0, f+g < 0 }
$
とする。
$A_(+-+)$においては$f = (f+g)+(-g)$で$f+g$と$-g$が非負より
$
integral_(A_(+-+)) f dd(m)
= integral_(A_(+-+)) (f+g) dd(m)+integral_(A_(+-+)) (-g) dd(m)
= integral_(A_(+-+)) (f+g) dd(m)-integral_(A_(+-+)) g dd(m)
$
で、同様にして$A_(+--)$においては$f+(-f-g) = -g$で$f$と$-f-g$が非負より
$
integral_(A_(+--)) f dd(m)+integral_(A_(+--)) (-f-g) dd(m)
= integral_(A_(+--)) f dd(m)-integral_(A_(+--)) (f+g) dd(m)
= integral_(A_(+--)) (-g) dd(m)
= -integral_(A_(+--)) g dd(m)
$
である。
したがってどちらの場合でも
$
integral_(A_(+ -)) (f+g) dd(m) = integral_(A_(+ -)) f dd(m)+integral_(A_(+ -)) g dd(m)
$
となる。 $A_(- +)$においても同様にすることで、和の積分の公式が示される。

最後に$f, g$が複素数値で$c$が複素数の時は実部虚部に分けると実数の場合に帰着されて示される。
]

#proposition([積分の単調性（実数値）])[
測度空間$(X, m)$上の拡張実数値ルベーグ積分可能な関数$f_1, f_2$に対して、$f_1 <= f_2$のとき
$
integral_X f_1 dd(m) <= integral_X f_2 dd(m)
$
が成り立つ。
特に拡張実数値ルベーグ積分可能な関数$f$に対して
$
abs(integral_X f dd(m)) <= integral_X abs(f) dd(m)
$
が成り立つ。
さらには可算個の拡張実数値ルベーグ積分可能な関数$f$に対して、
$integral_X sup_n f_n dd(m) < +oo$ならば
$
sup_n integral_X f_n dd(m) <= integral_X sup_n f_n dd(m)
$
が成り立ち、
$integral_X inf_n f_n dd(m) > -oo$ならば
$
inf_n integral_X f_n dd(m) >= integral_X inf_n f_n dd(m)
$
が成り立つ。
]

#proof[
$f_1 = f_2 = plus.minus oo$となる集合は測度零でないと積分可能にならないのでこれらの集合は無視できる。
ここで差$g = f_2-f_1$は非負値関数なので非負値に対する積分の単調性より、
$
integral_X g dd(m) = integral_X f_2 dd(m)-integral_X f_1 dd(m) >= 0.
$
よって前半部分は示された。
ルベーグ積分可能関数$f$に対して$-abs(f) <= f <= abs(f)$より
$
-integral_X abs(f) dd(m) <= integral_X f dd(m) <= integral_X abs(f) dd(m)
$
なので、後半部分も成立する。
]

#proposition([積分の単調性（複素数値）])[
測度空間$(X, m)$上の複素数値ルベーグ積分可能な関数$f$に対して
$
abs(integral_X f dd(m)) <= integral_X abs(f) dd(m)
$
が成り立つ。
]

#proof[
$a$を$abs(a) <= 1$を満たす実部と虚部がともに有理数な複素数とすると、
任意の複素数$z$に対して$abs(z) = sup_(abs(a) <= 1) Re a z$である。
よって、
$
integral_X abs(f) dd(m)
= integral_X sup_(abs(a) <= 1) Re a f dd(m)
>= sup_(abs(a) <= 1) integral_X Re a f dd(m)
= sup_(abs(a) <= 1) Re a integral_X f dd(m)
= abs(integral_X f dd(m))
$
である。
]

#proposition([マルコフの不等式])[
測度空間$(X, m)$上の拡張実数値あるいは複素数値ルベーグ積分可能な関数$f$と$t > 0$に対して
$
m({ abs(f) >= t }) <= 1/t integral_X abs(f) dd(m)
$
が成り立つ。
]

#proof[
非負値関数のルベーグ積分の定義より$T > 0$に対して
$
integral_X abs(f) dd(m)
= integral_0^oo m({ abs(f) >= t }) dd(t)
>= integral_0^T m({ abs(f) >= t }) dd(t)
>= integral_0^T m({ abs(f) >= T }) dd(t)
= T m({ abs(f) >= T })
$
である。
]

== ルベーグの優収束定理

単調収束定理やファトゥの補題の内容は拡張実数値関数の列$f_n$にも拡張できるが、
$f_n >= g$, $integral_X g dd(m) > -oo$である$g$の存在の仮定が必要になる。
この仮定がない場合は$integral_X f_n dd(m) = -oo$だが$integral_X f dd(m) > -oo$となる反例が構成できてしまう。
証明は$f_n-g$が非負値なのでそれに対して単調収束定理やファトゥの補題を適用して$g$の積分を足すという議論になるため、実質的に$f_n$は非負値である。

#theorem([実数版ファトゥの補題])[
測度空間$(X, m)$上の拡張実数値可測関数の列$f_n$に対して次が成り立つ。

- （ファトゥの補題）
  $integral_X inf_n f_n dd(m) > -oo$ならば
  $
  liminf_n integral_X f_n dd(m) >= integral_X liminf_n f_n dd(m)
  $
  が成り立つ。
- （逆ファトゥの補題）
  $integral_X sup_n f_n dd(m) < +oo$ならば
  $
  limsup_n integral_X f_n dd(m) <= integral_X limsup_n f_n dd(m)
  $
  が成り立つ。
]

証明は先述の方法でできる。

#theorem([優収束定理])[
測度空間$(X, m)$上の複素数値可測関数の列$f_n$が$f$に各点収束するとする。
ここで差の絶対値の各点上限がルベーグ可積分である、つまり
$
integral_X sup_n abs(f_n-f) dd(m) < oo
$
を仮定するとき、
$
lim_n integral_X abs(f_n-f) dd(m) = 0
$
が成り立つ。
また、このことは
$
lim_n integral_X f_n dd(m) = integral_X f dd(m)
$
を意味する。
]

#proof[
前半部分は逆ファトゥの補題より直ちに従う。
後半部分は積分の大小関係で示したことから
$
abs(integral_X f_n dd(m)-integral_X f dd(m))
= abs(integral_X (f_n-f) dd(m))
<= integral_X abs(f_n-f) dd(m)
$
なので、すぐわかる。
]
