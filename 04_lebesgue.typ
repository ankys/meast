
= ルベーグ測度

== ルベーグ外測度とルベーグ測度

これまで抽象的に扱ってきた測度であるが、ユークリッド空間$RR^N$で$N$次元面積に相当する測度がルベーグ測度である。
リーマン積分においてジョルダン測度がリーマン積分を通して定義されていたのに対して、ルベーグ積分は集合$A subset RR^N$に対して被覆を用いて直接定義する。
まず、測度の候補として開矩形$(a_1, b_1) times dots times (a_N, b_N)$に対しては
$
tilde(cal(L))^N ((a_1, b_1) times dots times (a_N, b_N)) = (b_1-a_1) dots (b_N-a_N)
$
とするのが妥当であろう。

#definition([ルベーグ外測度])[
部分集合$A subset RR^N$に対して、可算個の開矩形$R_i = (a^i_1, b^i_1) times dots times (a^i_N, b^i_N)$で被覆することで
$
macron(cal(L))^N (A)
= inf{ sum_i (b^i_1-a^i_1) dots (b^i_N-a^i_N) mid(|) bigcup_i (a^i_1, b^i_1) times dots times (a^i_N, b^i_N) supset A }
$
と定義する。
この$macron(cal(L))^N$は$N$次元_ルベーグ外測度_と呼ばれる。
]

こうして定義されたルベーグ外測度は残念ながら測度にはなっていない。
測度にするにはいくらかの病的な集合を可測集合から除く必要がある。
アイデアとしては補集合の情報を入れるため、全体集合$RR^N$を二つの集合$A$と$A^c$に分割すると四つめの性質から
$
macron(cal(L))^N (B sect A)+macron(cal(L))^N (B sect A^c) >= macron(cal(L))^N (B)
$
が成り立つが、等号が成立する場合が（ルベーグ）可測集合である。

#definition([ルベーグ測度])[
部分集合$A subset RR^N$が、任意の部分集合$B subset RR^N$に対して
$
macron(cal(L))^N (B sect A)+macron(cal(L))^N (B sect A^c) = macron(cal(L))^N (B)
$
を満たす時、$A$を_ルベーグ可測集合_といい、ルベーグ可測集合全体を$cal(B L)(RR^N)$で表す。
また、ルベーグ可測集合$A in cal(B L)(RR^N)$に対して
$
cal(L)^N (A) = macron(cal(L))^N (A)
$
と定義して、
$cal(L)^N$を$N$次元_ルベーグ測度_と呼ぶ。
]

こうして標準的な測度空間が得られる。

#theorem([ルベーグ測度])[
$(RR^N, cal(B L)(RR^N), cal(L)^N)$は測度空間になっている。
]

以上のことはより一般の設定で示すことができるので後の節で証明する。

== リーマン積分とルベーグ積分の関係

話をルベーグ測度に戻すと、ルベーグ測度空間$(RR^N, cal(B L)(RR^N), cal(L)^N)$上のルベーグ積分$integral f dd(cal(L)^N)$は別に定義した（リーマン）積分$integral f (x) dd(x)$と一致してほしい。
この節ではそのことについて追及する。

まず、$N = 1$の場合において区間のルベーグ外測度はその長さに一致することを示す。

#proposition[
有界閉区間$[a, b]$のルベーグ外測度は
$
macron(cal(L))^1 ([a, b]) = b-a
$
となる。
]

#proof[
$epsilon > 0$に対して$(a-epsilon, b+epsilon)$は$[a, b]$を被覆するので
$
macron(cal(L))^1 ([a, b]) <= b-a+2 epsilon
$
である。
可算個の開区間$(a_i, b_i)$で$[a, b]$を被覆する時、$[a, b]$はコンパクトなので有限個で被覆でき、さらに$a_i$が小さい順に並べ替えて$(a_(i_1), b_(i_1)), dots, (a_(i_n), b_(i_n))$を得ることができる。
この時$a_(i_1) < a$, $a_(i_(j+1)) < b_(i_j)$, $b < b_(i_n)$でないと被覆できないことに注意する。
ここから
$
sum_i (b_i-a_i)
>= sum_(j = 1)^n (b_(i_j)-a_(i_j))
> sum_(j = 1)^(n-1) (a_(i_(j+1))-a_(i_j))+(b_(i_n)-a_(i_n))
= b_(i_n)-a_(i_1)
> b-a
$
である。
以上より$macron(cal(L))^1 ([a, b]) = b-a$が成り立つ。
]

== カラテオドリの拡張定理

#definition([外測度])[
集合$X$の部分集合$A$に対して$macron(m)(A)$が次を満たすとき、$macron(m)$を$X$の_外測度_という。

+ 任意の部分集合$A subset X$に対して$macron(m)(A) in macron(RR)_+$である。
+ 空集合について$macron(m)(nothing) = 0$が成り立つ。
+ 任意の二つの部分集合$A, B subset X$に対して$A subset B$ならば$macron(m)(A) <= macron(m)(B)$が成り立つ。
+ 任意の可算個の部分集合$A_i subset X$に対して$macron(m)(union.big_i A_i) <= sum_i macron(m)(A_i)$が成り立つ。
]

#proposition[
集合$X$のいくつかの部分集合$D$（その集合を$cal(D)$とおく）に拡張非負値$tilde(m)(D) in macron(RR)_+$を対応させる。
ここで$tilde(m)(nothing) = 0$と$X in cal(D)$を仮定して、
$X$の部分集合$A$に対して可算個の$D_i in cal(D)$で被覆することで
$
macron(m)(A) = inf{ sum_i tilde(m)(D_i) mid bigcup_i D_i supset A }
$
と定義すると、$macron(m)$は$X$の外測度になる。
]

#proof[
+ 部分集合$A subset X$に対して被覆は存在するので$macron(m)(A) in macron(RR)_+$である。
+ 空集合$nothing$について$nothing in cal(D)$で被覆されるので$macron(m)(nothing) <= tilde(m) (nothing) = 0$である。
+ $A subset B$のとき$B$の被覆は$A$の被覆でもあるので$macron(m)(A) <= macron(m)(B)$が成り立つ。
+ 可算個の部分集合$A_i subset X$に対して、それぞれに可算被覆をとってそれら全ては$union.big_i A_i$の可算被覆なので$macron(m)(union.big_i A_i) <= sum_i macron(m)(A_i)$が成り立つ。
]

#theorem([カラテオドリの拡張定理])[
集合$X$とその外測度$macron(m)$を考える。
ここで部分集合$A subset X$が、任意の部分集合$B subset X$に対して
$
macron(m)(B sect A)+macron(m)(B sect A^c) = macron(m)(B)
$
を満たす時、そのような$A$全体を$cal(F)$として$m$を$macron(m)$の$cal(F)$への制限とする時、
$(X, cal(F), m)$は測度空間になっていて、さらに$m(A) = 0$となる測度零集合$A in cal(F)$に対して任意の部分集合$C subset A$は$cal(F)$に属する可測集合である。
]

測度空間を示した後の後半部分の条件を測度空間の完備性といい、後の節で詳しく見る。

#proof[
空集合$A = nothing$について、
$
macron(m)(B sect A)+macron(m)(B sect A^c) = macron(m)(nothing)+macron(m)(B) = macron(m)(B)
$
なので$nothing in cal(F)$であり、$m(nothing) = macron(m)(nothing) = 0$である。

集合$A in cal(F)$について、
$
macron(m)(B sect A^c)+macron(m)(B sect A) = macron(m)(B sect A)+macron(m)(B sect A^c)
$
より$A^c in cal(F)$である。

可算個の前に二つの集合$A_1, A_2 in cal(F)$に対して
$
macron(m)(B sect (A_1 union A_2))+macron(m)(B sect (A_1 union A_2)^c)
&= macron(m)((B sect A_1) union (B sect A_1^c sect A_2))+macron(m)(B sect A_1^c sect A_2^c) \
&<= macron(m)(B sect A_1)+macron(m)(B sect A_1^c sect A_2)+macron(m)(B sect A_1^c sect A_2^c)
= macron(m)(B).
$
よって$A_1 union A_2 in cal(F)$である。
可算個の集合$A_1, A_2, A_3, dots in cal(F)$に対して、互いに交わりがない場合は$A = union.big_i A_i$について
$
macron(m)(B)
&= macron(m)(B sect A_1)+macron(m)(B sect A_1^c)
= macron(m)(B sect A_1)+macron(m)(B sect A_2)+macron(m)(B sect A_1^c sect A_2^c) \
&= dots = macron(m)(B sect A_1)+dots+macron(m)(B sect A_n)+macron(m)(B sect A_1^c sect dots sect A_n^c) \
&>= macron(m)(B sect A_1)+dots+macron(m)(B sect A_n)+macron(m)(B sect A^c)
$
で$n -> oo$として
$
macron(m)(B)
>= sum_i macron(m)(B sect A_i)+macron(m)(B sect A^c)
>= macron(m)(union.big_i B sect A_i)+macron(m)(B sect A^c)
>= macron(m)(B sect A)+macron(m)(B sect A^c)
$
なので、$union.big_i A_i in cal(F)$である。
交わりがあるかもしれない場合も
$
union.big_i A_i = union.big_i (A_i sect A_1^c sect dots sect A_(i-1)^c)
$
であり、以上の内容から$cal(F)$は補集合、有限合併、可算直和について閉じているので可算合併についても閉じている。

最後に$m$が測度になることについては、
互いに交わらない可算個の集合$A_i in cal(F)$について$B = A = union.big_i A_i$として
$
m(A) = macron(m)(A) >= sum_i macron(m)(A_i)+macron(m)(nothing) = sum_i m(A_i).
$
一方で外測度の要件より不等号は等号として成立するので、$m$は測度である。

完備性について$m(A) = 0$, $C subset A$とすると、$B subset X$に対して
$
macron(m)(B sect C)+macron(m)(B sect C^c)
<= macron(m)(B sect A)+macron(m)(B sect C^c)
<= macron(m)(A)+macron(m)(B)
= macron(m)(B).
$
よって$C in cal(F)$で、定理の証明が完成する。
]

== 生成された加法族

集合$X$とその集合族（$X$のいくつかの部分集合からなる集合）$cal(C)$が与えられた時、
そこにさらに$X$の部分集合を最小限追加して完全加法族$sigma(cal(C))$を作る。

#proposition([生成された完全加法族])[
集合$X$とその集合族$cal(C)$に対して$cal(F)$を$cal(C)$を包含する$X$の完全加法族として、
$
sigma(cal(C)) = sect.big_(cal(F) supset cal(C)) cal(F)
$
は$X$の完全加法族であり、
$cal(C)$を包含する完全加法族の中で最小のものである。
]

この$sigma(cal(C))$を集合族$cal(C)$が_生成する完全加法族_という。

#proof[
最小性は定義からすぐわかるので$sigma(cal(C))$が完全加法族を示す。

+ 空集合$nothing$は完全加法族$cal(F)$に共通して属しているので、$nothing in sigma(cal(C))$である。
+ 集合$A in sigma(cal(C))$の補集合$A^c$について、$A in sigma(cal(C)) subset cal(F)$ならば$A^c in cal(F)$より$A^c in sigma(cal(C))$である。
+ 可算個の集合$A_n in sigma(cal(C))$の合併$A = union.big_n A_n$について、$A_n in sigma(cal(C)) subset cal(F)$ならば$A in cal(F)$より$A in sigma(cal(C))$である。

以上より証明された。
]

多くの場合、完全加法族はこのようにして構成される。
その中でも特に重要なのが位相空間におけるボレル集合族である。

#definition([ボレル可測])[
位相空間$(X, cal(O))$において、開集合系$cal(O)$が生成する$X$の完全加法族を$(X, cal(O))$の_ボレル集合族_といい$cal(B)(X, cal(O))$と表す。
また、ボレル集合族に属する可測集合を$(X, cal(O))$の_ボレル可測集合_といい、$(X, cal(B)(X, cal(O)))$を_ボレル可測空間_という。
]

距離空間やユークリッド空間$RR^N$などの標準的な開集合系がある対象においては$cal(O)$は省略される。
また、前章で定義した可測関数はボレル可測空間$(RR, cal(B)(RR))$への可測写像と見なすことができる。

== 完備測度

ボレル可測集合は開集合や閉集合をはじめとして様々な集合を集めている。
しかしながら、それでもルベーグ可測集合とは少し差がある。
その差こそが完備性の有無である。

#definition([完備測度空間])[
測度空間$(X, cal(F), m)$が完備であるとは、$m(A) = 0$となる測度零集合$A in cal(F)$に対して任意の部分集合$B subset A$は$cal(F)$に属する可測集合（であり測度零）であることをいう。
]

#theorem([完備化])[
]

== ホップの拡張定理

ジョルダン測度のような可算加法的ではないが有限加法的ではある場合にそれを可算加法的な測度に拡張することを保証するのがホップの拡張定理である。

#theorem([ホップの拡張定理])[
有限加法的測度空間$(X, cal(A), m_0)$が完全加法的、つまり可算個の任意の互いに交わりを持たない可算集合$A_i in cal(A)$であって$union.big_i A_i in cal(A)$であるものに対して
$
m_0 (union.big_i A_i) = sum_i m_0 (A_i)
$
が成り立つとき、
完全加法族$sigma(cal(A))$上の完全加法的な測度$m$であって任意の$A in cal(A)$に対して$m(A) = m_0 (A)$となるものが存在する。
]

#remark[
この定理の逆のこと、つまり有限加法的測度が完全加法的に拡張できるなら空間が完全加法的であることはすぐわかる。
]

#proof[
まず、外測度$macron(m)$を、部分集合$A subset X$に対して可算個の可測集合$A_i in cal(A)$で被覆することで
$
macron(m)(A) = inf{ sum_i m_0 (A_i) mid(|) A_i in cal(A), union.big_i A_i supset A }
$
と定める。
これが実際に外測度になることはすでに示した命題による。
ここからカラテオドリの拡張定理により完備測度空間$(X, cal(F), m)$が構成できる。
あとは$cal(F) supset cal(A)$と任意の$A in cal(A)$に対して$macron(m)(A) = m_0 (A)$を示せば定理が証明される。

このうち$cal(F) supset cal(A)$は$A in cal(A)$が$A in cal(F)$つまり$B subset X$に対して
$
macron(m)(B sect A)+macron(m)(B sect A^c) <= macron(m)(B)
$
を示せばよい。
$macron(m)(B) = oo$ならば直ちに従うので、$macron(m)(B) < oo$の場合を考える。
正の数$epsilon > 0$に対して外測度の定義より$B_i in cal(A)$が存在して$union.big_i B_i supset B$かつ
$
sum_i m_0 (B_i) <= macron(m)(B)+epsilon
$
となる。
ここで$B sect A subset union.big_i (B_i sect A)$と$B sect A^c subset union.big_i (B_i sect A^c)$より
$
macron(m)(B sect A)+macron(m)(B sect A^c)
<= sum_i m_0 (B_i sect A)+sum_i m_0 (B_i sect A^c)
= sum_i (m_0 (B_i sect A)+m_0 (B_i sect A^c)).
$
ここで$m_0$は有限加法性を持っているので、
$
macron(m)(B sect A)+macron(m)(B sect A^c) <= sum_i m_0 (B_i) <= macron(m)(B)+epsilon.
$
したがって$cal(F) supset cal(A)$がわかる。

続いて$A in cal(A)$に対して$macron(m)(A) = m_0 (A)$を示すが、外測度の定義から$macron(m)(A) <= m_0 (A)$は自明なので$m_0 (A) <= macron(m)(A)$を示す。
これは$A_i in cal(A)$で$union.big_i A_i supset A$となるものに対して
$
m_0 (A) <= sum_i m_0 (A_i)
$
を示せばよい。
ここで$B_n = A_n sect (sect.big_(i < n) A_i^c) sect A in cal(A)$とおくと$B_n$は互いに交わりを持たないで$union.big_i B_i = A$なので完全加法性より、
$
m_0 (A) = sum_i m_0 (B_i).
$
各$n$に対して$B_n subset A_n$なので、ほしい不等式が成立する。

以上より定理が証明された。
]

また、この拡張は一意的である。

#definition([シグマ有限])[
有限加法的測度空間$(X, cal(A), m_0)$に対して可算個の測度有限$m_0 (A_i) < oo$な可測集合$A_i in cal(A)$であって$X$を被覆するつまり$union.big_i A_i = X$となるものが存在するとき、$(X, cal(A), m_0)$は_シグマ有限_であるという。
]

#remark[
$X_n = union.big_(i <= n) A_i$とおけば単調性$X_n subset X_(n+1)$を満たす。
]

#theorem([ホップの拡張定理の一意性])[
有限加法的測度空間$(X, cal(A), m_0)$がシグマ有限のとき、ホップの拡張定理での測度$m$は一意である。
]

証明のために次の単調族定理を用意する。

#definition([単調族])[
集合$X$の集合族$cal(M)$が次の条件をみたすとき_単調族_という。

+ $A_i in cal(M)$が$A_n subset A_(n+1)$をみたすとき、$union.big_i A_i in cal(M)$となる。
+ $A_i in cal(M)$が$A_n supset A_(n+1)$をみたすとき、$sect.big_i A_i in cal(M)$となる。

さらに集合$X$の集合族$cal(C)$に対して、$cal(C)$を含む中で最小の単調族が存在し$M(cal(C))$と表す。
]

#theorem([単調族定理])[
集合$X$の有限加法族$cal(A)$に対して$M(cal(A)) = sigma(cal(A))$が成り立つ。
]

#proof[
完全加法族は単調族なので、$M(cal(A)) subset sigma(cal(A))$は自明であり、あとは$M(cal(A))$が完全加法族になることを示せばよい。

+ $cal(A)$は有限加法族なので、$nothing in cal(A) subset M(cal(A))$である。
+ TODO
]

#proof([ホップの拡張定理の一意性の証明])[
有限加法的測度$m_0$の$cal(F) = sigma(cal(A))$への拡張$m_1, m_2$が$m_1 = m_2$をみたすことを示す。
シグマ有限性より$X_n in cal(A)$であって$m_0 (X_n) < oo$, $X_n subset X_(n+1)$, $union.big_n X_n = X$をみたすものが取れる。
この$X_n$をもとにして集合族
$
cal(C) = { A in cal(F) mid m_1 (A sect X_n) = m_2 (A sect X_n) forall n in NN }
$
を定める。
有限加法族$cal(A)$上では$m = m_1 = m_2$なので、$cal(A) subset cal(C)$である。
よって$cal(C)$が単調族であることを示せば、単調族定理より$cal(F) = sigma(cal(A)) subset cal(C)$なので、すべての$A in cal(F)$に対して$m_1 (A sect X_n) = m_2 (A sect X_n)$で$n -> oo$として$m_1 (A) = m_2 (A)$を得る。
したがってあとは$cal(C)$が単調族であることを示せばよいが、これは測度の単調性より容易に示される。
ただし、単調減少列について測度の有限性が必要になってくるが、これは$m_1 (X_n) = m_2 (X_n) = m_0 (X_n) < oo$から従う（詳細省略）。
]
