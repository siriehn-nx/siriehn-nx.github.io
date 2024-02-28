#import "@preview/lemmify:0.1.5": *
#import "@preview/i-figured:0.2.3"


#let conf(
  title: none,
  date: none,
  authors: (
    (
      name: "siriehn_nx",
      affiliation: "Tsinghua University",
      email: "siriehn_nx@outlook.com",
    ),
  ),
  abstract: [],
  doc,
) = {
  // Set and show rules from before.
  show math.equation.where(block: false): it => {
    if it.has("label") and it.label == label("displayed-inline-math-equation") {
      it
    } else {
      [$display(it)$<displayed-inline-math-equation>]
    }
  }
  set text(
		font: "Linux Libertine",
		size: 12pt,
	)
  set page(
		paper: "us-letter",
		header: align(
			right)[
			],
		numbering: "(1/1)",
		margin: (x: 1.8cm, y: 1.5cm),
	)
	set heading(numbering: "1.1")
  show heading: i-figured.reset-counters
  set align(center)
  text(17pt, title)
  let count = authors.len()
  let ncols = calc.min(count, 3)
  grid(
    columns: (1fr,) * ncols,
    row-gutter: 24pt,
    ..authors.map(author => [
      #author.name \
      #author.affiliation \
      #link("mailto:" + author.email) \
      #date
    ]),
  )

  //par(justify: false)[
  //  *Abstract* \
  //  #abstract
  //]

  set align(left)
  columns(1, doc)
}

#let (
  theorem, lemma, corollary, definition,
  proposition, example,
  rules: thm-rules
) = default-theorems("thm-group", lang: "en")


// memset0-course
#let reset_indent = [#text()[#v(0pt, weak: true)];#text()[#h(0em)]]

#let named_block(it, name: "", color: red, inset: 11pt) = {block(
  below: 1em, stroke: 0.5pt + color, radius: 3pt,
  width: 100%, inset: inset
)[
  #place(
    top + left,
    dy: -6pt - inset, // Account for inset of block
    dx: 8pt - inset,
    block(fill: white, inset: 2pt)[
			#set text(font: "Noto Sans", fill: color)
			#strong[#name]
		]
  )
  #let fontcolor = color.darken(20%)
  #set text(fill: fontcolor)
  #set par(justify: true, first-line-indent: 0em)
  #it
];reset_indent}

#let problem(it) = named_block(it, name: "Problem",color:green.darken(20%))
#let proof(it) = named_block(it, name: "Proof", color: gray.darken(30%))

#let solution(it) = named_block(it, name: "Solution", color: orange.darken(30%))
#let remark(it) = named_block(it, name: "Remark", color: blue.darken(30%))
// OK

#let seq(x,l,r) = [$#x _#l,...,#x _#r$]
#let xx(l,r) = [$x_#l,...,x_#r$] // a seq like "x_l,...,x_r"
#let xx(l,a,r) = [$x_#l,x_#a,...,x_#r$] // a seq like "x_l,x_(l+1),...,x_r"
#let RS(x) = [$bb(R)^#x$] // R_space ^ x
#let ST(x, y,arguments:none) = [$lr({#x mid(|) #y ,#arguments})$] // a set like "{x|y}"
#let alim(x,y) = [$lim _(#x arrow #y)$]
#let oplus = [$plus.circle$]
#let ne = [$eq.not$]
#let lrarrowd = [$arrow.l.r.double$]
#let lrarrowdl = [$arrow.l.r.double.long$]
#let phia = [$phi.alt$]


#show: doc => conf(
  title: [
    Analysis2
  ],
  date: "February 26, 2024",
  // a date
  //abstract: none,
  doc,
)
#show: thm-rules

// apply the show rules (these can be customized)
#show math.equation: i-figured.show-equation.with(
  level: 2,
  zero-fill: false,
  leading-zero: false,
  numbering: "(1.1)",
  prefix: "eqt:",
  only-labeled: false,  // numbering all block equations implicitly
  unnumbered-label: "-",
)


#counter(heading).update(6)

= 多变量函数的连续性

== $RR$ 中的拓扑

#definition[
$RR ^n = lr({x = (x ^ 1, ... x ^ n) mid(|) x ^ i in RR , i = 1, ..., n })$, 称 $x$ 为 $n$ 元有序数组,为  $RS(n)$ 中的点,通常的加法和数乘,$RS(n)$ 为线性空间.
]

=== 度量

#definition[
映射 $d: RS(n) times RS(n) arrow RR (x, y) arrow.bar d(x, y)$,其中 $d(x, y) = [sum_(i=1)^n (x ^ i - y ^ i) ^ 2] ^ (1/2)$.
]

则 $d$ 满足:

+ 正定性,$forall x, y in RS(n), d(x, y) >= 0, \"=\" lrarrowdl x = y$.
+ 对称性, $d(x, y) = d(y, x)$.
+ 三角不等式, $forall x, y, z in RS(n), d(x, y) <= d(x, z) + d(z, y)$

若 $d$ 满足三条性质,称  $d$ 为  $RS(n)$ 的度量.

#remark[
#definition[

  $p >= 1, d_p :RS(n) times RS(n) arrow RR_+,(x,y) arrow.bar d_p (x,y) = (sum_(i=1)^n |x ^ i - y^i| ^ p) ^ (1/p)$,
  $d_infinity: RS(n) times RS(n) arrow RR_+,(x,y) arrow.bar d_infinity (x,y) = max_(1<=i<=n)|x ^ i -y ^ i|$
]
可以验证,$d_p,d_infinity$ 均为 $RS(n)$ 上的度量.
]


#proposition(name:"Minkowski 不等式")[
$d_infinity (x, y) <= d(x, y) <= n d_infinity (x, y)$
$C_(p, 1) d(x, y)<= d_p (x, y) <= C_(p, 2) d(x, y) $,其中 $C_(p, 1), C_(p, 2)$ 均为依赖  $p$ 的常数.
]

=== 开集,闭集,拓扑空间

#definition[
设 $a in RS(n), delta > 0, B(a;delta) = lr({x in RS(n) mid(|) d(a, x) < delta})$ 称为以 $a$ 为中心,$delta$ 为半径的球 / $delta$ 邻域.
]
#definition[
设 $U subset RS(n), forall a in U, exists delta > 0, "s,t." B(a; delta) subset U$,则称 $U$ 为开集.
]
#example[$B(a; r)$ 为开集(r > 0).]
#proposition[
+ $RS(n), emptyset$ 为开集.
+ 无穷多个开集的并还是开集.
+ 有限多个开集的交还是开集.
]
#definition[
$RS(n)$ 中的开集满足以上三条性质,那么称 $RS(n)$ 为拓扑空间.
]

$RS(n)$ 中的拓扑空间是由 $d$ 诱导的.

一般而言,有以下定义.

#definition(name:[拓扑空间])[
设 $X$ 为集合, $tau$ 为 $X$ 的子集簇,满足:
+ $phi,X in tau$
+ $forall tau_alpha , alpha in Lambda, union.big_{alpha in Lambda} tau_alpha in tau$
+ 设 $seq(tau, 1, m) in tau$ 则 $sect.big _{i = 1} ^m tau_i in tau$
那么称 $(X, tau)$ 为拓扑空间.
]
#definition[
  设 $A subset RS(n)$,若 $A ^ c  = RR ^ n backslash A$ 为开集,那么称 $A$ 为闭集.
]

#example[
- $forall x, y in RS(n),A = {x, y}$ 闭集
- $overline(B)(a;r) = lr({x in RS(n) mid(|) d (a; x) <= r})$ 闭集
- $cal(S ) ^ (n - 1) (a, r) = lr({x in RS(n) mid(|) d(a; x) = r})$ 为闭集
]

记 $cal(S) ^ (n - 1) = cal(S) ^ (n - 1) (0, 1)$

由 $"De Morgan"$ 定理可知:

#proposition[
+ $RS(n), emptyset$ 是闭集
+ 无穷多个闭集的交仍然是闭集
+ 有限多个闭集的并仍然是闭集
]

=== 邻域,内点,边界点,聚点

#definition(name:[邻域,内点,边界点])[
+ 设 $x in RS(n)$,任一包含 $x$ 的开集  $U$ 称为 $x$ 的邻域,$circle(U) = U backslash {x}$ 称为 $x$ 的去心邻域
+ 设 $D subset RS(n)$,若 $x in D, exists x$ 的邻域 $U,"s.t." U subset D$, 称 $x$ 为 $D$ 的内点.对应的,若 $x$ 是 $D ^ c$ 的内点,则 $x$ 为 $D$ 的内点.
+ 设 $D subset RS(n)$, $x$ 即非内点也非外点,则 $x$ 为 $D$ 的边界点. $diff D = lr({x in RS(n) mid(|) x "为" D "的边界点"})$,称 $diff D$ 为 $D$ 的边界,也可定义为 $diff D = lr({x in RS(n) mid(|) x "的任一领域" U, U sect D ne emptyset, U sect D ^ c ne emptyset})$
]

#definition(name:[聚点])[
设 $D subset RS(n)$,若 $D$ 的任一邻域均含有 $D$ 中的无穷多个点, 称 $x$ 为 $D$ 的一个聚点. $lrarrowdl x$ 的任意邻域 $U, circle(U) union D ne emptyset$
]

$D' = lr({x in RS(n) mid(|)  x "为" D "聚点"})$,称其为 $D$ 的导集

称 $overline(D) = D union D'$ 为 $D$ 的闭包.


#theorem[
  $D subset RS(n)$ 为闭集 $lrarrowdl D' subset D$.
]


#proof[
  "$arrow.long.double$" $forall a in D'$ 要证明 $a in D$.
  
  (反证法): 若 $a in.not D$ 则 $a in D ^ c$, 由于 $D$ 闭集,则 $D ^ c$ 开集,$exists delta > 0, B(a; delta ) subset D ^ c, B(a; delta) sect D = emptyset$ ,这与 $a$ 为聚点矛盾,则 $a in D, "i.e." D' subset D$.

  "$arrow.l.long.double$" $D' subset D$ 要证明 $D ^ c$ 为开集.
  
  $forall a in D ^ c, a$ 不是聚点,则 $exists delta > 0, "s.t." B(a;delta) sect D = emptyset$,则 $B(a; delta) subset D ^ c$,从而 $D ^ c$ 为开集.
]

== $RS(n)$ 中的紧(致)集

#definition(name:[紧集])[
设 $A subset RS(n)$ 若 $A$ 的任意开覆盖都有有限字符该,称 $A$ 为 $RS(n)$ 的紧集(compet set).
]

由 Heine-Bored 定理可知 $RR$ 中闭区间为紧集.

#definition(name:[长方体])[
  设 $a, b in RS(n), a = (a ^ 1, ..., a ^ n), b = (b ^ 1, ..., b ^ n), a ^ i <= b ^ i, i = 1,...,n, I_(a, b) = lr({x in RS(n) mid(|) a  ^ i <= x ^ i <= b ^ i})$ 其为长方体.
]
#proposition[
$I_(a, b)$   为  $RS(n)$ 中的紧集.
]
#proof[
(反证法): 设 ${U_alpha}_(alpha in Lambda)$ 为 $I_(a, b)$ 的开覆盖,不存在其的有限子覆盖,令 $I_1$ 分成 $2 ^ n$ 个长方体,则至少有一个长方体没有有限子覆盖,记为 $I_2$,继续其过程,记为 $I_3,...,I_n,...$,满足 $I_1 supset I_2 supset ... supset I_k supset ...$.

$I_k = lr({x in RS(n) mid(|) a_k ^ i <= x ^ i <= b_k ^ i, i = 1, ..., n})$

由 Cauchy-Cantor 闭区间套定理,$exists ! x _0 ^i  in sect.big _{k = 1} ^ infinity [a_k ^ i, b_k ^ i]$,令 $x_0 = (x_0 ^ 1, ... x_0 ^ n)$ ,则 $exists alpha_0 in Lambda , "s.t." x_0 in U_(alpha_0)$ ,令 $"diam" I_k = sup_{x, y in I_k} d(x, y)$

则  $lim _(k arrow infinity) "diam" I_k = 0$,$exists k in NN ^ *, "s.t." k >= K, x_0 in I_k subset U _(alpha_0)$,从而与构造矛盾! $ballot$
]