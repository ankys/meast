
#import "deps/theorem.typ": thmrules, theorem, proposition, definition, example, remark, proof
#show: thmrules.with()

#import "@preview/physica:0.9.4": dd

= 微分定理

== 測度距離空間

（完備可分な）距離空間$(X, d)$に対して$m$をボレル正則な測度であって任意の閉球
$
B(x, r) := { y in X mid(|) d(x, y) <= r }
quad (x in X, r > 0)
$
の測度が有限かつ非零であるとする。
このとき$(X, d, m)$を_測度距離空間_という。

ユークリッド空間$RR^N$に通常のユークリッド距離とルベーグ測度を入れたものは測度距離空間である。

#block[
測度距離空間$(X, d, m)$が_ダブリング_条件を満たすとはある定数$C$が存在して、任意の$x in X$と$r > 0$に対して
$
m(B(x, 2 r)) <= C m(B(x, r))$
が成り立つことをいう。
]

== ルベーグの微分定理

#theorem([ルベーグの微分定理])[
$(X, d, m)$をダブリング条件を満たす測度距離空間として$f$を$X$上の複素数値局所積分可能関数とする。
このとき$m$についてほとんどすべての$x in X$で
$
lim_(r -> 0) 1/(m(B(x, r))) integral_(B(x, r)) f dd(m) = f(x)
$
が成り立つ。
]

測度が有限かつ非零な可測集合$A$上で積分可能関数$f$に対して、
$
integral.dash_A f dd(m) = 1/(m(A)) integral_A f dd(m)
$
と定めて平均化積分という。
ここで証明の前に、
$
abs(integral.dash_(B(x, r)) f dd(m)-f(x))
= abs(integral.dash_(B(x, r)) (f(y)-f(x)) dd(m)(y))
<= integral.dash_(B(x, r)) abs(f(y)-f(x)) dd(m)(y)
$
であるので、この最右辺が$0$に収束することを示せば十分であることに注意する。

#proof[
積分可能な関数$f$と点$x in X$と半径$r > 0$に対して
$
T_r f(x) = integral.dash_(B(x, r)) abs(f(y)-f(x)) dd(m)(y)
$
とおく。
示すべきことは$T f(x) = limsup_(r -> 0) T_r f(x)$として、ほとんどすべての$x in X$に対して$T f(x) = 0$である。
]
