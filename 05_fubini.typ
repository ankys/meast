
#import "deps/theorem.typ": thmrules, theorem, proposition, definition, example, remark, proof
#show: thmrules.with()

#import "@preview/physica:0.9.4": dd

= 積空間

== 直積測度

#definition([直積測度空間])[
$N = 1, 2, 3, dots$個の可測空間$(X_1, cal(F)_1), dots, (X_N, cal(F)_N)$に対して_直積可測空間_$(X, cal(F))$を次のようにして導入する。

- 集合としては直積集合$X = X_1 times dots times X_N$である。
- すべての直積集合$A_1 times dots times A_N$ ($A_i in cal(F)_i$)が可測になるようにそれらで生成される完全加法族を$cal(F)$とする。

さらに測度空間$(X_1, cal(F)_1, m_1), dots, (X_N, cal(F)_N, m_N)$に対して次の条件を満たす測度$m$を_直積測度_と呼ぶ。

- すべての直積集合$A_1 times dots times A_N$ ($A_i in cal(F)_i$)に対して
  $
  m(A_1 times dots times A_N) = m_1 (A_1) dots m_N (A_N)
  $
  が成り立つ。

このような測度空間$(X, cal(F), m)$は測度空間$(X_1, cal(F)_1, m_1), dots, (X_N, cal(F)_N, m_N)$の_直積測度空間_という。
]

以降ではそのような直積測度をどうやって構築するかおよびどのような場合に一意性が保証できるかを考える。
簡単のために$N = 2$として記述する。

#example[
$X = Y = [0, 1]$としてともにボレル集合族を考え$X$にはルベーグ測度$m_X$を$Y$には数え上げ測度$m_Y$を入れる。

]
#theorem([極大直積測度])[
測度空間$(X, cal(F)_X, m_X), (Y, cal(F)_Y, m_Y)$
]

この定理で構成された測度を_極大直積測度_といい$m = m_1 times.circle dots times.circle m_N$と表す。

== フビニの定理

#theorem([フビニの定理])[
完備測度空間$(X, cal(F)_X, m_X)$と$(Y, cal(F)_Y, m_Y)$に対して、$(X times Y, cal(F), m)$を極大積測度空間とする。
ここで複素数値可測関数$f(x, y)$が$X times Y$上で積分可能であるならば、
$
integral.double_(X times Y) f(x, y) m(dd(x, y))
= integral_X (integral_Y f(x, y) m_Y(dd(y))) m_X(dd(x))
= integral_Y (integral_X f(x, y) m_X(dd(x))) m_Y(dd(y))
$
が成り立つ。
]

== トネリの定理

#theorem([トネリの定理])[
シグマ有限測度空間$(X, cal(F)_X, m_X)$と$(Y, cal(F)_Y, m_Y)$に対して、$(X times Y, cal(F), m)$を極大積測度空間とする。
ここで拡張非負値可測関数$f (x, y)$に対して、
$
integral.double_(X times Y) f(x, y) m(dd(x, y))
= integral_X (integral_Y f(x, y) m_Y(dd(y))) m_X(dd(x))
= integral_Y (integral_X f(x, y) m_X(dd(x))) m_Y(dd(y))
$
が成り立つ。
]

つまり、三辺のうちどれかが無限大なら他も無限大である。
