# Graceful labelings of trees with a degree-4 and a degree-3 branch vertex

**Theorem.** Every finite tree with exactly two branch vertices, one of degree 4 and one of
degree 3, is graceful.

**Status:** proved and machine-checked. `proof/Main.lean` passes `conjectures verify` for task
`fc-4b69a7dc-math15catalog-source10-a324196efa-formalized-v1` (accepted, reason `VERIFIED`, exit 0,
2026-10-08, local development sandbox).

The proof is constructive. It builds explicit labelings from a small toolkit of α-labeling
operations, plus a finite number of explicit labelings found by computer and checked in Lean.

## 0. Setting and notation

A *graceful labeling* of a tree $T$ with $m$ edges is an injection $f:V(T)\to\{0,\dots,m\}$ such
that the edge labels $|f(x)-f(y)|$ over the edges $xy$ are exactly $\{1,\dots,m\}$.

Every tree with exactly two branch vertices, of degrees 4 and 3, is isomorphic to

$$T = T(a,b,c\mid d\mid e,f),\qquad a,b,c,d,e,f\ge 1,$$

which consists of:
- a vertex $u$ (degree 4) with pendant paths ("arms") of $a,b,c$ vertices;
- a vertex $v$ (degree 3) with arms of $e,f$ vertices;
- a $u$–$v$ path with $d$ edges (the "$d$-path"); its interior vertices are $d_1,\dots,d_{d-1}$,
  where $d_i$ is at distance $i$ from $u$.

By symmetry we may assume $a\le b\le c$ and $e\le f$. Arm vertices are written $x_k$ (the $k$-th
vertex of arm $x$, counted from its root).

**α-labelings.** An α-labeling is a graceful labeling with a threshold $\lambda$ such that every
edge joins a label $\le\lambda$ ("low") to a label $>\lambda$ ("high"). The low vertices form one
colour class of the bipartition. For a vertex $x$ define:
- $\varepsilon(x)=f(x)$ if $x$ is low, and $m-f(x)$ if $x$ is high (distance to the extreme label);
- $\tau(x)=\lambda-f(x)$ if low, and $f(x)-\lambda-1$ if high (distance to the threshold).

Then $\varepsilon(x)+\tau(x)$ is constant on each colour class.

**Notation.** $\mathrm{OK}(n,t)$ means: $n\ge1$, $0\le t\le\lfloor (n-1)/2\rfloor$, and
**not** ($n\equiv1\pmod 4$, $n>1$, $4t=n-1$).

## 1. Tools

**Lemma 1.1 (complement).** If $f$ is graceful then so is $m-f$. If $f$ is α, so is $m-f$, with
$\varepsilon$ and $\tau$ unchanged.

**Lemma 1.2 (reflection).** If $f$ is α with threshold $\lambda$, define
$g(x)=\lambda-f(x)$ for low $x$ and $g(x)=m+\lambda+1-f(x)$ for high $x$. Then $g$ is α with the
same threshold and the same low set, and $g$ swaps $\varepsilon$ and $\tau$ at every vertex.
(An edge label $h-l$ becomes $m+1-(h-l)$.)

**Lemma 1.3 (gluing).** Let $A$ be α-labeled ($m_A$ edges, threshold $\lambda$), $x\in A$, and
let $B$ be gracefully labeled by $g$ ($m_B$ edges), $w\in B$. Join them by the edge $xw$. Put
$F=f_A$ on the low part of $A$, $F=f_A+m_B+1$ on the high part, and $F=\lambda+1+g$ on $B$.
Then $F$ is graceful iff $g(w)=\tau(x)$ (if $x$ is high) or $g(w)=m_B-\tau(x)$ (if $x$ is low).
If moreover $g$ is α and $w$ lies in the colour class opposite to $x$, then $F$ is α, $\varepsilon$
is unchanged on $A$, and $\tau$ is unchanged on $B$.

**Lemma 1.4 (end invariant).** In any α-labeling of a path $z_1\dots z_n$ with $z_1$ low,
$\tau(z_n)=f(z_1)$.

**Theorem 1.5 (α-EPL).** The path on $n$ vertices has an α-labeling with threshold
$\lfloor (n-1)/2\rfloor$ whose first vertex is low with label $t$ whenever $\mathrm{OK}(n,t)$
holds. (Brute force shows the excluded cases are genuine for $n\le14$; this is not used.)

*Construction*, by strong induction on $n$:
- $t=0$: the zigzag $0,m,1,m-1,\dots$
- $2t>\lambda$: reflect a labeling for $\lambda-t$.
- $2t=\lambda$: pattern C, $t,3t,t+1,3t-1,\dots,2t,\;m,0,m-1,1,\dots,m-t$.
- $2t<\lambda$: pattern E or E2. A zigzag head ends at an extreme label, and a smaller α-EPL
  instance is shifted into the remaining box.

**Corollary 1.6 (attaching an α segment).** Let $A$ be α, $x\in A$, and attach at $x$ a new path
of $L$ vertices with $\mathrm{OK}(L,\tau(x))$. Then (Lemma 1.3 with Theorem 1.5) the result $A'$
is α. Moreover:
- $\varepsilon$ is unchanged on the old vertices;
- for every old $z$, $\tau(z)$ grows by $\lfloor (L+\delta)/2\rfloor$, where $\delta=1$ iff $z$ and
  $x$ lie in different colour classes;
- the far end of the new path has $\tau=\tau_A(x)$, by Lemma 1.4.

**Corollary 1.7 (final segment).** If $A$ is α, $x\in A$ and $\tau(x)\le L-1$, then attaching a
path of $L$ vertices at $x$ gives a graceful labeling $G$ with $G(z)\in\{\varepsilon(z),
m-\varepsilon(z)\}$ for every old $z$. (Glue a graceful path whose end has label $\tau(x)$.)

**Lemma 1.8 (leaf chain).** If $G$ is graceful and $G(x)\in\{0,m\}$, then attaching a path of
$L\ge0$ new vertices at $x$ keeps the tree graceful. (Give each new leaf the label $m+1$, then
complement.)

**Lemma 1.9 (join).** Let $A$ be α, $B$ graceful, and suppose the only tree edge between them is
$xw$. If $B(w)\in\{\tau_A(x),\,m_B-\tau_A(x)\}$ and $\tau_A(x)\le m_B$, then the union is graceful
(Lemma 1.3, complementing $B$ if needed).

## 2. Pieces

Below, "$X$ at $r$" names an arm $X$ hanging at the vertex $r$. A *program* is a sequence of
the operations of §1: start with an explicit α-path, attach α segments (Cor. 1.6), reflect
(Lemma 1.2), and finish with a final segment (Cor. 1.7) or a join (Lemma 1.9). Each program's
side conditions are $\mathrm{OK}(\cdot,\cdot)$ constraints, computed by the $\varepsilon/\tau$
bookkeeping of Cor. 1.6.

**Lemma 2.1 (IVL0).** For all $(x,y)\neq(2,2)$, the path $P(x,y)$ (arms $x,y$ at a root $r$) has
an α-labeling with $\varepsilon(r)=0$ and $\tau(r)=\lfloor x/2\rfloor+\lfloor y/2\rfloor$.
Assume $x\le y$:
- (a) zigzag along $x$ from $r$, then attach $y$ at $r$; needs $\mathrm{OK}(y,\lfloor x/2\rfloor)$;
- the explicit core for $(6,6)$;
- (b) $x_1$, $y_1$ at $r$, then the two tails; for $x\ge4$, $x\ne6$;
- the programs s1 (for $(3,5)$) and s0 (for $(2,5)$, $(6,13)$) on the swapped pair.

A short case analysis shows that every pair is covered.

**Lemma 2.2 (SP0).** For every $a\le b\le c$, the spider $S(a,b,c)$ has a graceful labeling with
the centre $u$ at label $0$ (or $m$):
- generic: IVL0$(a,b)$ at $u$, then a final segment $c$; needs
  $\lfloor a/2\rfloor+\lfloor b/2\rfloor\le c-1$, which holds unless $a=b=c$ is even;
- $(2,2,c)$: for $c\ge9$, an explicit α-core $S(2,2,5)$ plus a final segment; for $c\le8$, tables;
- $(2k,2k,2k)$: for $k\ge8$, explicit α-cores ($S(7,1,1)$, or $S(7,3,1)$ when $k=12$) plus α
  tails and a final segment; for $k\le7$, tables.

**Lemma 2.3 (SPσ, σ = 1, 2).** A graceful spider at $u$ with $u$ at label $\sigma$ or $m-\sigma$
can be built by any of these programs on an ordering $(x,y,z)$ of the arms:
- spA: α-EPL from $u$ along $x$ with $u$ at $\sigma$, then $y$ at $u$, then a final $z$. Needs
  $\mathrm{OK}(x+1,\sigma)$, $\mathrm{OK}(y,\lfloor x/2\rfloor-\sigma)$, and
  $\lfloor x/2\rfloor-\sigma+\lfloor y/2\rfloor\le z-1$.
- sw1 ($\sigma=1$): IVL0$(x,y)$, reflect, $z_1z_2$, reflect, final rest of $z$. Needs
  $(x,y)\ne(2,2)$ and $\lfloor x/2\rfloor+\lfloor y/2\rfloor+4\le z$.
- sw2 ($\sigma=1$): zigzag $x$, reflect, $y_1y_2$, reflect, $y$ tail, final $z$. Needs $y\ge3$,
  $\mathrm{OK}(y-2,\lfloor x/2\rfloor+1)$, and $\lfloor x/2\rfloor+\lfloor y/2\rfloor\le z$.

**Lemma 2.4 (SP1 coverage).** Every $a\le b\le c$ except the 13 spiders

$$F_1=\{(1,1,1),(1,4,4),(4,4,4),(4,4,6),(4,4,7),(4,6,6),(4,6,7),(4,6,8),(4,7,7),(4,7,8),(4,8,8),(5,5,5),(6,9,9)\}$$

has an SP1 program:
- spA on $(a,b,c)$ whenever $a\ge2$, $a\ne4$, and $b$ is not exceptional, where exceptional means
  $b\equiv1\ (4)$ and $b=4\lfloor a/2\rfloor-3$;
- $a=1$: by $b$ — sw1, spA$(c,a,b)$, spA$(b,a,c)$, sw2$(a,b,c)$, or sw2$(a,c,b)$;
- $a=4$: sw2 for $b\ge9$, $b\ne15$; otherwise sw1 when $c\ge\lfloor b/2\rfloor+6$;
- exceptional $b$: sw1 when $c\ge\lfloor a/2\rfloor+\lfloor b/2\rfloor+4$;
- the 12 remaining spiders, (4,4,5), (4,5,5–7), (4,8,9), (5,5,6–7), (6,9,10), (7,9,9–10),
  (8,13,13) and (9,13,13): each gets an explicit choice of program.

**Lemma 2.5 (v-side pieces, $e=f=2$).** Let $\mathrm{VSP}(D,\sigma)$ be an α-labeling of the
subtree made of $v$, its arms of length 2, and the $D$ path vertices $d_{d-1},\dots,d_{d-D}$, with
$\tau=\sigma$ at its last vertex ($v$ itself when $D=0$). It exists:
- for $\sigma=1$: when $D\in\{0,1,5\}$ or $\mathrm{OK}(D,1)$, i.e. for every $D\ne2$
  (graceful $P(2,2)=(0,4,1,3,2)$ plus a chain, or explicit cores);
- for $\sigma=2$: when $D\in\{3,4\}$, or $D>3$ and $\mathrm{OK}(D-3,2)$, or $D>4$ and
  $\mathrm{OK}(D-4,2)$ (explicit cores plus a chain). In particular for $D\in\{3,4\}\cup[8,\infty)$.

## 3. Family A: $(e,f)\neq(2,2)$

Take IVL0$(e,f)$ at $v$ and reflect, so $\tau(v)=0$. If $d\ge2$, attach the $d-1$ interior
$d$-path vertices at $v$; this is allowed since $\mathrm{OK}(d-1,0)$ always holds, and the new end
$d_1$ has $\tau=0$. Join with SP0$(a,b,c)$ at $u$ (Lemma 1.9, condition $u\mapsto 0$ or $m$).

## 4. Family C: $e=f=2$

There are five templates.
- **V($\sigma$)**: VSP$(d-1,\sigma)$ joined to an SPσ spider at the edge $d_1u$ (Lemma 1.9).
- **cut**: VSP$(d-2,1)$, joined at $d_2d_1$ to a graceful piece containing $d_1$, $u$ and the
  spider with $d_1$ at label $1$. That piece is: the α-path $d_1,u,x_1$ labelled $1,2,0$; the
  α tail of $x$; α $y$ at $u$; and a final $z$. It needs $\mathrm{OK}(x-1,1)$,
  $\mathrm{OK}(y,\lfloor x/2\rfloor)$ and $\lfloor x/2\rfloor+\lfloor y/2\rfloor\le z-1$.
- **U**: an α piece on the $u$-side, joined to a graceful $P(2,2)$ at $v$. The α piece is: zigzag
  $x$ from $u$; the $d$-path from $u$; reflect; α $y$ and $z$ at $u$; reflect. Its junction
  $d_{d-1}$ has $\tau=\lfloor x/2\rfloor$, and the $P(2,2)$ has $v$ at $\rho$ or $4-\rho$ for
  $\rho\in\{0,1,3,4\}$. It needs $\lfloor x/2\rfloor\in\{0,1,3,4\}$, $d=1$ or
  $\mathrm{OK}(d-1,\lfloor x/2\rfloor)$, and $\mathrm{OK}(z,\lfloor y/2\rfloor)$.
- **Π ($d=3$)**: an explicit α-path $f_2f_1\,v\,d_2d_1\,u\,(a_1\dots)$ with $v$ at label $0$, then
  α $b$ at $u$, a final $c$ at $u$, and a leaf chain for arm $e$ at $v$ (Lemma 1.8). The starts
  are:

  | $a$ | start labels | $\tau(u)$ |
  |---|---|---|
  | $1$ | $1,5,0,6,3,4,2$ | $0$ |
  | $2$ | $1,6,0,7,3,4,2,5$ | $0$ |
  | $3$ | $1,8,0,6,4,5,2,7,3$ | $0$ |
  | $4$ | $1,8,0,9,3,5,4,7,2,6$ | $0$ |
  | $a\ge5$, $a\ne7$ | the $a=2$ start plus an α tail at $a_2$ | $\lfloor (a-2)/2\rfloor$ |
  | Π′ | $f_2..u$ labelled $1,5,0,3,2,4$ plus α $a$ at $u$ | $1+\lfloor a/2\rfloor$ |
- **cores**: explicit graceful labelings with $u$ at $0$, extended by a leaf chain at $u$ (Lemma 1.8):
  - $T(4,4,\cdot\mid d\mid2,2)$ and $T(\cdot,4,4\mid d\mid2,2)$ for $d\in\{1,2,6,7,8\}$;
  - $T(6,9,\cdot\mid d\mid2,2)$ for $d\in\{2,6,7\}$;
  - plus one table, $T(5,5,5\mid1\mid2,2)$.

**Coverage.**
- **$d=3$**, any $a\le b\le c$. Use Π for $a\in\{1,2,3,4\}$, and Π for $a\ge5$, $a\ne7$, unless
  $b\equiv1\ (4)$ and $4\lfloor (a-2)/2\rfloor=b-1$. Otherwise use cut, or Π′ when $(a,b)=(7,13)$
  or $a=6$.
- **$d\ne3$, spider not in $F_1$**: V(1). VSP$(d-1,1)$ exists since $d-1\ne2$, and SP1 exists
  by Lemma 2.4.
- **$d\ne3$, spider in $F_1$**:
  - $(1,1,1)$: U.
  - $(1,4,4)$ and $(4,4,c)$: cores for $d\in\{1,2,6,7,8\}$, V(2) otherwise.
  - $(4,b,c)$ with $6\le b\le c\le 8$: U for $d=1$, V(2) for $d=4$, cut otherwise.
  - $(5,5,5)$: the table for $d=1$, V(2) for $d=4$, cut otherwise.
  - $(6,9,9)$: U for $d\in\{1,8\}$, cores for $d\in\{2,6,7\}$, V(2) otherwise.

## 5. Formalization

The whole argument is formalized in Lean 4 / Mathlib in `proof/Main.lean`, which concatenates
`proof/A1…F8`, as `theorem target : Math15.Graceful.Target10`.
- **Structure theorem** (C1–C9): every tree with branch vertices of degrees 4 and 3 is isomorphic
  to a canonical $T(a,b,c\mid d\mid e,f)$ on natural-number names ($u=0$, $v=1$, arm $X$
  position $k$ = $X+8k$). This reduces the target to `CanonGraceful a b c d e f` for sorted
  parameters.
- **α-piece API** (D1–E1): pieces carry their α threshold and the $\varepsilon/\tau$
  bookkeeping. Attach, final-segment, join and leaf-chain lemmas are proved once, with symbolic
  arm lengths.
- **Explicit labelings** are checked by `decide +kernel` on a Boolean tree-and-labeling checker.
  `native_decide` is not used.
- **Coverage** (F1–F8) is proved by `omega` case splits that mirror §3–§4.

Search scripts that found the cores and tables are in `search/` (`search/tf`, `search/tab`).
