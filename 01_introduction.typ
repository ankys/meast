
#import "deps/theorem.typ": thmrules, theorem, proposition, definition, example, remark, proof
#show: thmrules.with()

#import "@preview/physica:0.9.4": dd

= 導入

== 積分と測度

積分とは究極的に何であろうか。
積分といえば不定積分と定積分あるいは重積分などがあるが、ここでは定積分や重積分を対象に考える。
積分の登場人物といえば集合から数への対応である関数（被積分関数）であり、定積分や重積分ではそこ（と積分領域）から何らかの数（積分値）を対応させる。
被積分関数を$f(x)$で積分領域を$A$としてその積分値はしばしば次のように記述される。
$
integral_A f(x) dd(x)
$
積分の定義は複雑であるが、得られるのは一次元非負関数の定積分なら被積分関数が定める集合の面積、二次元重積分なら体積になることが期待される。

一方で測度とは面積や体積を抽象化した概念であって、集合に対して面積などを対応させることとみなせる。
そのため、線分の長さや集合の元の個数（濃度、数え上げ）や標本空間における確率も測度とみなせる。

このように説明すると積分とは測度を求めることと考えられるかもしれない。
しかしながらそれは半分正しく半分的を射ていない表現である。
一つあるのは積分値は何らかの測度の値であることが多いが、（リーマン）積分の定義をよく見ると被積分関数の定義域である被積分領域の方でも測度が現れる。
そのため積分は測度$m$を明示して
$
integral_A f(x) m(dd(x))
$
あるいはその省略形
$
integral_A f dd(m)
$
と書かれ、本テキストではこの記法を採用する。
この測度を念頭に置いた積分の理論を測度論的積分論という。
利点は数列の和
$
sum_n a_n
$
や確率論での期待値
$
EE[X]
$
も測度が特殊な積分とみなせるということである。

その上で積分はある意味で一つ次数の高い測度を計算するのに使われていると言える。
面積や体積、期待値などは現実世界でも重要な意味を持つ量であり、その計算をするために積分の理論を進めることが必要不可欠である。
次節ではその積分の計算のために積分がどのような性質を持つべきかについて述べる。

== 積分の性質

ここでは復習を兼ねて、積分の要件としての性質を考える。

まず、積分の計算は最終的には次の微分積分学の基本定理により微分して被積分関数になる関数、いわゆる原始関数を求めることに帰着される。
$
integral_a^b F'(x) dd(x) = F(b)-F(a).
$

#example[
二次関数$f(x) = x^2$の原始関数として三次関数$F(x) = 1/3 x^3$があるので、
$
integral_0^1 x^2 dd(x) = F(1)-F(0) = 1/3
$
と計算される。
]

線形性
$
integral (f+g) dd(x) = integral f dd(x)+integral g dd(x),
quad integral c f dd(x) = c integral f dd(x)
$

単調性
$
f <= g 
==> integral f dd(x) <= integral g dd(x)
$

#example[
ガウス関数$f(x) = e^(-x^2/2)$を$[0, 1]$上で考えると、$f$はこの範囲で凹関数なので
$
integral_0^1 e^(-x^2/2) dd(x)
>= integral_0^1 (1+(e^(- 1/2)-1) x) dd(x)
= 1/2 (1+e^(-1/2)) $
となる。
ここで左辺は$0.855624 dots$なのに対して、右辺は$0.803265 dots$なのであまり良い近似ではないかもしれないが、
簡易的に計算ができる。
]

置換積分とは合成関数の微分法$(F(phi(t)))' = F'(phi(x))phi'(x)$に基づく積分の計算法で、
$
integral f(phi(t))phi'(t) dd(t) = integral f(x) dd(x)
$
のことをいう。
積分区間（領域）は変わるので注意する。
特に$phi(t) = a t+b$に対して適用すると
$
integral f(a t+b) dd(t) = 1/a integral f(x) dd(x)
$
を得る。

#example[
$x = phi(t) = t^2$として適用すると
$
integral_0^1 t e^(t^2) = integral_0^1 1/2 e^x dd(x) = 1/2 (e-1)
$
と計算される。
]

上記の例では左辺を右辺に変形することで積分を単純な形にしているが、
右辺をあえて左辺のような形にすることで積分が計算できる形にすることがある。

#example[
区間$[-a, +a]$上の関数$f(x) = 2 sqrt(a^2-x^2)$の積分について$x = a sin theta$と置換すると
$
integral_(-a)^(+a) 2 sqrt(a^2-x^2) dd(x)
= integral_(-pi/2)^(+pi/2) 2 a^2 cos^2 theta dd(theta)
= integral_(-pi/2)^(+pi/2) a^2 (1+cos 2 theta) dd(theta)
= pi a^2
$
と計算され、これは円の面積を表す。
]

非負値関数の積分は次のようにしても計算できる。
$
integral f dd(x)
= integral f abs(dd(x))
= integral_0^oo abs({ f >= t }) dd(t).
$
これは囲まれる部分の切り方を縦から横に切り替えても同じ面積が得られることを意味する。

#example[
$[0, 1]$上の$f(x) = x^2$に対して${ f >= t } = [sqrt(t), 1]$なので、
$
integral_0^1 x^2 dd(x)
= integral_0^oo (1-sqrt(t))_(+) dd(t)
= integral_0^1 (1-t^(1/2)) dd(t)
= 1-2/3 = 1/3
$
である。
]

二変数関数の場合は積分の順序によらずに積分値が等しくなってほしい。
$
integral (integral f(x, y) dd(x)) dd(y)
= integral (integral f(x, y) dd(y)) dd(x)
= integral f(x, y) dd((x, y)).
$
この式のうち最初の二つを累次積分と言い、最後のものを重積分という。
またこの式によって重積分を次数の低い積分に帰着することができる。

#example[
正方形$[0, 1]^2$上の二変数関数$f(x, y) = x y e^(x y^2)$の重積分について、$y$で先に積分することで
$
integral.double_([0, 1]^2) x y e^(x y^2) dd((x, y))
= integral_0^1 (integral_0^1 x y e^(x y^2) dd(y)) dd(x)
= integral_0^1 1/2 (e^x-1) dd(x)
= (e-2)/2
$
と計算される。
なお$x$で先に積分しても同じ値が得られるが、計算量が増える。
]

変数変換の公式は置換積分の重積分版ともいうべき計算法で、$x = Phi(u)$と変数変換することで
$
integral f(x) dd(x) = integral f(Phi(u)) abs(J Phi(u)) dd(u)
$
とできる。
ここで$abs(J Phi(u))$はヤコビアンと呼ばれる微分で計算される量である。
具体的な変換に対して変数変換の公式を書き下すと、一次変換$x = a u+b v, y = c u+d v$に対しては
$
integral.double f(x, y) dd((x, y))
= integral.double f(a u+b v, c u+d v) abs(a d-b c) dd((u, v))
$
となり、極座標変換$x = r cos theta, y = r sin theta$に対しては
$
integral.double f(x, y) dd((x, y))
= integral.double f(r cos theta, r sin theta) r dd((r, theta))
$
となる。

#example[
円板$B_a = { (x, y) mid(|) x^2+y^2 <= a^2 }$上の関数$f(x, y) = e^(-x^2-y^2)$の積分について、
$
integral.double_(B_a) e^(-x^2-y^2) dd((x, y))
= integral_0^a (integral_0^(2 pi) e^(-r^2) r dd(theta)) dd(r)
= 2 pi integral_0^a r e^(-r^2) dd(r)
= pi (1-e^(-a^2))
$
を得る。
さらに$a -> oo$とすることを考えると、$B_a$は平面全体$RR^2$を埋め尽くすと考えて
$
integral.double_(RR^2) e^(-x^2-y^2) dd((x, y)) = pi
$
となってほしくて、さらに累次積分の考え方から
$
integral_(-oo)^(+oo) e^(-x^2) dd(x) = sqrt(pi)
$
も成り立ってほしい。
最後の積分のことをガウス積分という。
]

以上の事柄はこれまでに学んだリーマン積分の範囲でも成立することであるが、問題は次の積分と極限の順序交換である。
つまり関数列$f_n$に対して
$
lim_n integral f_n (x) dd(x) = integral lim_n f_n (x) dd(x)
$
が成り立ってほしい。
もちろんリーマン積分の範囲でも$f_n$が有界閉集合上一様収束すればこれは正当化できるが、実際にはもっと様々な場合で成立すべきである。

#example[
$n = 1, 2, 3, dots$に対して区間$[0, 1]$上の関数列$f_n (x) = x^n$を考えるとこれは$f(x) = 0$に$x = 1$を除いて各点収束する。
一方で積分の列の方は
$
integral_0^1 x^n dd(x) = 1/(n+1) -> 0 = integral_0^1 f(x) dd(x)
$
なので、これは積分と極限の順序交換ができる場合である。
]

その一方で順序交換は必ずできるわけではない。

#example[
実軸全体$RR$上の関数$f_n (x) = 1/n e^(-x^2/n^2)$は$f(x) = 0$に一様収束するが、
$
integral_(RR) 1/n e^(-x^2/n^2) dd(x) = integral_(RR) e^(-x^2) dd(x) = sqrt(pi) > 0
$
である。
]

== ルベーグ積分の展開

本テキストでは前節で挙げた積分の満たすべき要件をなるべく広い範囲で成り立たせる積分としてルベーグ積分について議論する。

リーマン積分が関数のグラフを縦に切っていたのに対して、ルベーグ積分の定義のアイデアは横に切ることにある。
基礎的な性質（線形性と単調性）は定義から従うとして、TODO
