/-! ## α-pieces of the canonical tree with ε/τ bookkeeping -/

/-- depth parity of a canonical name (tree rooted at `u = 0`, `v` at depth `d`) -/
def par (d z : ℕ) : ℕ :=
  if z = 0 then 0 else if z = 1 then d % 2 else if 6 ≤ z % 8 then (z / 8 + d) % 2 else (z / 8) % 2

theorem par_le_one (d z : ℕ) : par d z ≤ 1 := by
  unfold par; split_ifs <;> omega

/-- distance of a label to the extreme label of its class -/
noncomputable def Pc.eps (P : Pc) (th z : ℕ) : ℕ :=
  if P.f z < th then P.f z else P.E.card - P.f z

/-- distance of a label to the threshold -/
noncomputable def Pc.tau (P : Pc) (th z : ℕ) : ℕ :=
  if P.f z < th then th - 1 - P.f z else P.f z - th

/-- an α-piece of `T(·|d|·)`: adjacency `Tadj d`, low class = parity class `q` -/
structure APc (d q : ℕ) where
  P : Pc
  th : ℕ
  hR : P.R = Tadj d
  hA : P.Alpha th
  hlow : ∀ z ∈ P.S, (P.f z < th ↔ par d z = q)
  hq : q ≤ 1

/-- reflection of a labeling with threshold `th`: lows `l ↦ th-1-l`, highs `h ↦ m+th-h` -/
noncomputable def Pc.reflP (P : Pc) (th : ℕ) : Pc where
  S := P.S
  R := P.R
  f := fun z => if P.f z < th then th - 1 - P.f z else P.E.card + th - P.f z

theorem Pc.reflP_E (P : Pc) (th : ℕ) : (P.reflP th).E = P.E := rfl

theorem Pc.reflP_f (P : Pc) (th z : ℕ) :
    (P.reflP th).f z = if P.f z < th then th - 1 - P.f z else P.E.card + th - P.f z := rfl

theorem Pc.reflP_edge {P : Pc} {th : ℕ} (hP : P.Alpha th) {x y : ℕ} (hx : x ∈ P.S) (hy : y ∈ P.S)
    (hr : P.R x y) :
    Nat.dist ((P.reflP th).f x) ((P.reflP th).f y) + Nat.dist (P.f x) (P.f y) = P.E.card + 1 := by
  have c := hP.2.2 x hx y hy hr
  have h1 := hP.1.2.2.2.1 x hx
  have h2 := hP.1.2.2.2.1 y hy
  rw [Pc.reflP_f, Pc.reflP_f]
  by_cases hl : P.f x < th
  · have hh : th ≤ P.f y := c.mp hl
    rw [if_pos hl, if_neg (by omega)]
    simp only [Nat.dist]; omega
  · have hh : P.f y < th := by
      by_contra hc
      exact hl (c.mpr (by omega))
    rw [if_neg hl, if_pos hh]
    simp only [Nat.dist]; omega

theorem Pc.reflP_alpha {P : Pc} {th : ℕ} (hP : P.Alpha th) : (P.reflP th).Alpha th := by
  have hP' := hP
  obtain ⟨⟨hsym, hcard, hinj, hle, hedge⟩, hth, halt⟩ := hP
  have hE := Pc.reflP_E P th
  refine ⟨⟨hsym, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [hE]; exact hcard
  · intro x hx y hy h
    have := hle x hx; have := hle y hy
    apply hinj x hx y hy
    rw [Pc.reflP_f, Pc.reflP_f] at h
    by_cases h1 : P.f x < th <;> by_cases h2 : P.f y < th
    · rw [if_pos h1, if_pos h2] at h; omega
    · rw [if_pos h1, if_neg h2] at h; omega
    · rw [if_neg h1, if_pos h2] at h; omega
    · rw [if_neg h1, if_neg h2] at h; omega
  · intro x hx
    rw [hE, Pc.reflP_f]; have := hle x hx
    split_ifs <;> omega
  · intro e he e' he' h
    rw [hE] at he he'
    apply hedge e he e' he'
    obtain ⟨a1, a2, _, a4⟩ := Pc.mem_E.mp he
    obtain ⟨b1, b2, _, b4⟩ := Pc.mem_E.mp he'
    have c1 := Pc.reflP_edge hP' a1 a2 a4
    have c2 := Pc.reflP_edge hP' b1 b2 b4
    omega
  · rw [hE]; exact hth
  · intro x hx y hy hr
    have c := halt x hx y hy hr
    have := hle x hx; have := hle y hy
    rw [Pc.reflP_f, Pc.reflP_f]
    by_cases h1 : P.f x < th
    · rw [if_pos h1, if_neg (by have := c.mp h1; omega)]; omega
    · have h2 : P.f y < th := by by_contra hc; exact h1 (c.mpr (by omega))
      rw [if_neg h1, if_pos h2]; omega

namespace APc
variable {d q : ℕ}

noncomputable def eps (A : APc d q) (z : ℕ) : ℕ := A.P.eps A.th z
noncomputable def tau (A : APc d q) (z : ℕ) : ℕ := A.P.tau A.th z

theorem f_le (A : APc d q) {z : ℕ} (hz : z ∈ A.P.S) : A.P.f z ≤ A.P.E.card :=
  A.hA.1.2.2.2.1 z hz

/-- `ε + τ` depends only on the class -/
theorem eps_tau (A : APc d q) {z : ℕ} (hz : z ∈ A.P.S) :
    A.eps z + A.tau z = if par d z = q then A.th - 1 else A.P.E.card - A.th := by
  have hle := A.f_le hz
  have hl := A.hlow z hz
  unfold eps tau Pc.eps Pc.tau
  by_cases h : A.P.f z < A.th
  · rw [if_pos h, if_pos h, if_pos (hl.mp h)]; omega
  · rw [if_neg h, if_neg h, if_neg (fun e => h (hl.mpr e))]; omega

theorem eps_tau_same (A : APc d q) {z y : ℕ} (hz : z ∈ A.P.S) (hy : y ∈ A.P.S)
    (h : par d z = par d y) : A.eps z + A.tau z = A.eps y + A.tau y := by
  rw [A.eps_tau hz, A.eps_tau hy, h]

/-- reflection (same vertex set, same threshold, `ε ↔ τ`) -/
noncomputable def refl (A : APc d q) : APc d q where
  P := A.P.reflP A.th
  th := A.th
  hR := A.hR
  hA := Pc.reflP_alpha A.hA
  hlow := by
    intro z hz
    have := A.hlow z hz
    have := A.hA.2.1
    have := A.f_le hz
    rw [Pc.reflP_f]
    split_ifs <;> omega
  hq := A.hq

theorem refl_S (A : APc d q) : A.refl.P.S = A.P.S := rfl
theorem refl_card (A : APc d q) : A.refl.P.E.card = A.P.E.card := rfl

theorem refl_eps (A : APc d q) {z : ℕ} (hz : z ∈ A.P.S) : A.refl.eps z = A.tau z := by
  have := A.f_le hz
  have := A.hA.2.1
  show (A.P.reflP A.th).eps A.th z = A.P.tau A.th z
  unfold Pc.eps Pc.tau
  rw [Pc.reflP_E, Pc.reflP_f]
  split_ifs <;> omega

theorem refl_tau (A : APc d q) {z : ℕ} (hz : z ∈ A.P.S) : A.refl.tau z = A.eps z := by
  have := A.f_le hz
  have := A.hA.2.1
  show (A.P.reflP A.th).tau A.th z = A.P.eps A.th z
  unfold Pc.eps Pc.tau
  rw [Pc.reflP_f]
  split_ifs <;> omega

/-- complement: labels `x ↦ m - x`; the low class switches -/
noncomputable def cmp (A : APc d q) : APc d (1 - q) where
  P := A.P.cmp
  th := A.P.E.card + 1 - A.th
  hR := A.hR
  hA := Pc.cmp_alpha A.hA
  hlow := by
    intro z hz
    have := A.hlow z hz
    have := A.f_le hz
    have := A.hA.2.1
    have := par_le_one d z
    have := A.hq
    show A.P.E.card - A.P.f z < A.P.E.card + 1 - A.th ↔ par d z = 1 - q
    constructor <;> intro h <;> omega
  hq := by omega

theorem cmp_S (A : APc d q) : A.cmp.P.S = A.P.S := rfl
theorem cmp_card (A : APc d q) : A.cmp.P.E.card = A.P.E.card := rfl

theorem cmp_eps (A : APc d q) {z : ℕ} (hz : z ∈ A.P.S) : A.cmp.eps z = A.eps z := by
  have := A.f_le hz
  have := A.hA.2.1
  show A.P.cmp.eps (A.P.E.card + 1 - A.th) z = A.P.eps A.th z
  unfold Pc.eps
  rw [Pc.cmp_E]
  show (if A.P.E.card - A.P.f z < A.P.E.card + 1 - A.th then A.P.E.card - A.P.f z
    else A.P.E.card - (A.P.E.card - A.P.f z)) = _
  split_ifs <;> omega

theorem cmp_tau (A : APc d q) {z : ℕ} (hz : z ∈ A.P.S) : A.cmp.tau z = A.tau z := by
  have := A.f_le hz
  have := A.hA.2.1
  show A.P.cmp.tau (A.P.E.card + 1 - A.th) z = A.P.tau A.th z
  unfold Pc.tau
  show (if A.P.E.card - A.P.f z < A.P.E.card + 1 - A.th then A.P.E.card + 1 - A.th - 1 - (A.P.E.card - A.P.f z)
    else A.P.E.card - A.P.f z - (A.P.E.card + 1 - A.th)) = _
  split_ifs <;> omega

/-- the label of a vertex is `ε` or `m - ε` -/
theorem f_eps (A : APc d q) {z : ℕ} (hz : z ∈ A.P.S) :
    A.P.f z = A.eps z ∨ A.P.f z = A.P.E.card - A.eps z := by
  have := A.f_le hz
  unfold eps Pc.eps
  split_ifs <;> omega

end APc
