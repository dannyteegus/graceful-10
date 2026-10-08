/-! ## Attaching an α-EPL segment to an α-piece -/

/-- `nm 0, …, nm (L-1)` is an induced path of `Tadj d`, attached to `x` by the edge `x - nm 0`,
with alternating depth parities. -/
structure Seg (d x L : ℕ) (nm pos : ℕ → ℕ) : Prop where
  hL : 1 ≤ L
  inj : ∀ i j, i < L → j < L → nm i = nm j → i = j
  hpos : ∀ i, i < L → pos (nm i) = i
  cons : ∀ i, i + 1 < L → Tadj d (nm i) (nm (i + 1))
  chord : ∀ i j, i < L → j < L → Tadj d (nm i) (nm j) → i = j + 1 ∨ j = i + 1
  xw : Tadj d x (nm 0)
  par0 : par d (nm 0) + par d x = 1
  parI : ∀ i, i < L → par d (nm i) = (par d (nm 0) + i) % 2

theorem ipathPc_card_S {R : ℕ → ℕ → Prop} {n : ℕ} {nm pos L : ℕ → ℕ}
    (hinj : ∀ i j, i < n → j < n → nm i = nm j → i = j) :
    (ipathPc R n nm pos L).S.card = n := by
  classical
  show ((Finset.range n).image nm).card = n
  rw [Finset.card_image_of_injOn, Finset.card_range]
  intro i hi j hj h
  simp only [Finset.coe_range, Set.mem_Iio] at hi hj
  exact hinj _ _ hi hj h

theorem ipathPc_mem {R : ℕ → ℕ → Prop} {n : ℕ} {nm pos L : ℕ → ℕ} {z : ℕ} :
    z ∈ (ipathPc R n nm pos L).S ↔ ∃ i, i < n ∧ nm i = z := by
  simp [ipathPc, Finset.mem_image]

theorem Pc.tau_cmp {P : Pc} {th z : ℕ} (hz : P.f z ≤ P.E.card) (hth : th ≤ P.E.card + 1) :
    P.cmp.tau (P.E.card + 1 - th) z = P.tau th z := by
  unfold Pc.tau
  show (if P.E.card - P.f z < P.E.card + 1 - th then P.E.card + 1 - th - 1 - (P.E.card - P.f z)
    else P.E.card - P.f z - (P.E.card + 1 - th)) = _
  split_ifs <;> omega

/-- `τ` of index `i` in an α-path labeling with threshold `(L-1)/2` -/
def ptau (L : ℕ) (Lab : ℕ → ℕ) (i : ℕ) : ℕ :=
  if Lab i ≤ (L - 1) / 2 then (L - 1) / 2 - Lab i else Lab i - (L - 1) / 2 - 1

theorem ptau_last {L : ℕ} {Lab : ℕ → ℕ} (hLab : PathAlpha L Lab ((L - 1) / 2)) (hL : 1 ≤ L)
    (h0 : Lab 0 ≤ (L - 1) / 2) : ptau L Lab (L - 1) = Lab 0 := by
  have hend := path_end_inv hLab hL rfl h0
  unfold ptau
  split_ifs with h
  · exact hend.1 h
  · exact hend.2 (by omega)

namespace APc
variable {d q : ℕ}

/-- attach a segment labeled by a given α-path labeling whose first label is `τ(x)` -/
theorem attachP (A : APc d q) {x L : ℕ} {nm pos : ℕ → ℕ} (hs : Seg d x L nm pos)
    (hx : x ∈ A.P.S) (hfresh : ∀ i, i < L → nm i ∉ A.P.S)
    (hcross : ∀ p ∈ A.P.S, ∀ i, i < L → Tadj d p (nm i) → p = x ∧ i = 0)
    (Lab : ℕ → ℕ) (hLab : PathAlpha L Lab ((L - 1) / 2)) (hLab0 : Lab 0 = A.tau x)
    (hlow0 : Lab 0 ≤ (L - 1) / 2) :
    ∃ B : APc d q, (∀ z, z ∈ B.P.S ↔ z ∈ A.P.S ∨ ∃ i, i < L ∧ nm i = z) ∧
      B.P.E.card = A.P.E.card + L ∧
      (∀ z ∈ A.P.S, B.eps z = A.eps z) ∧
      (∀ z ∈ A.P.S, B.tau z = A.tau z + (L + (par d z + par d x) % 2) / 2) ∧
      (∀ i, i < L → B.tau (nm i) = ptau L Lab i) := by
  classical
  have hL1 := hs.hL
  set t := A.tau x with ht
  set lam := (L - 1) / 2 with hlam
  have hok2 : t ≤ lam := by rw [← hLab0]; exact hlow0
  have hsym : ∀ p q', Tadj d p q' → Tadj d q' p := Tadj_symm d
  have hB0 := ipathPc_alpha (R := Tadj d) (pos := pos) hs.hL hsym hs.inj hs.hpos hs.cons hs.chord
    hLab (by omega)
  set B0 := ipathPc (Tadj d) L nm pos Lab with hB0def
  have hB0S : B0.S.card = L := ipathPc_card_S hs.inj
  have hB0E : B0.E.card = L - 1 := by have := hB0.1.2.1; omega
  have hmemB0 : ∀ z, z ∈ B0.S ↔ ∃ i, i < L ∧ nm i = z := fun z => ipathPc_mem
  have hfB0 : ∀ i, i < L → B0.f (nm i) = Lab i := by
    intro i hi; show Lab (pos (nm i)) = Lab i; rw [hs.hpos i hi]
  have hxS := A.hlow x hx
  have hfx := A.f_le hx
  have hth := A.hA.2.1
  have htdef : t = if A.P.f x < A.th then A.th - 1 - A.P.f x else A.P.f x - A.th := rfl
  -- the attached piece: complemented iff `x` is low
  obtain ⟨B, thB, hBA, hBR, hBS, hBE, hBf, hthB, hBlow, hBtau, hthBv⟩ : ∃ (B : Pc) (thB : ℕ),
      B.Alpha thB ∧ B.R = Tadj d ∧ (∀ z, z ∈ B.S ↔ ∃ i, i < L ∧ nm i = z) ∧ B.E.card = L - 1 ∧
      ((A.P.f x < A.th ∧ B.f (nm 0) + (A.th - 1 - A.P.f x) = B.E.card) ∨
        (A.th ≤ A.P.f x ∧ B.f (nm 0) + A.th = A.P.f x)) ∧
      (A.P.f x < A.th ↔ thB ≤ B.f (nm 0)) ∧
      (∀ i, i < L → (B.f (nm i) < thB ↔ par d (nm i) = q)) ∧
      (∀ i, i < L → B.tau thB (nm i) = ptau L Lab i) ∧
      thB = (if A.P.f x < A.th then L / 2 else (L + 1) / 2) := by
    have hlowi := path_low_iff hLab
    have hLle := hLab.2.1
    have hq := A.hq
    have hp0 := hs.par0
    have hpI := hs.parI
    have hplx := par_le_one d x
    by_cases hxl : A.P.f x < A.th
    · -- complement
      refine ⟨B0.cmp, B0.E.card + 1 - (lam + 1), Pc.cmp_alpha hB0, rfl, hmemB0, hB0E, ?_, ?_, ?_, ?_,
        by rw [if_pos hxl, hB0E]; have := hs.hL; omega⟩
      · left; refine ⟨hxl, ?_⟩
        show B0.E.card - B0.f (nm 0) + _ = B0.E.card
        rw [hfB0 0 (by have := hs.hL; omega), hLab0, hB0E, htdef, if_pos hxl]
        rw [htdef, if_pos hxl] at hok2
        omega
      · show _ ↔ _ ≤ B0.E.card - B0.f (nm 0)
        rw [hfB0 0 (by have := hs.hL; omega), hLab0, hB0E]
        omega
      · intro i hi
        show B0.E.card - B0.f (nm i) < _ ↔ _
        rw [hfB0 i hi, hB0E]
        have a := hlowi i hi
        rw [hLab0] at a
        have := hLle i hi
        have hpxq : par d x = q := hxS.mp hxl
        rw [hpI i hi]
        constructor
        · intro h
          have : ¬ Lab i ≤ lam := by omega
          have : ¬ (t ≤ lam ↔ i % 2 = 0) := fun e => this (a.mpr e)
          omega
        · intro h
          have : ¬ (i % 2 = 0) := by omega
          have : ¬ Lab i ≤ lam := fun e => this ((a.mp e).mp (by omega))
          omega
      · intro i hi
        rw [Pc.tau_cmp (by rw [hfB0 i hi, hB0E]; exact hLle i hi) (by rw [hB0E]; omega)]
        unfold Pc.tau ptau
        rw [hfB0 i hi]
        have := hLle i hi
        by_cases hll : Lab i ≤ lam
        · rw [if_pos (by omega), if_pos hll]; omega
        · rw [if_neg (by omega), if_neg hll]; omega
    · -- as is
      refine ⟨B0, lam + 1, hB0, rfl, hmemB0, hB0E, ?_, ?_, ?_, ?_, by rw [if_neg hxl]; omega⟩
      · right; refine ⟨by omega, ?_⟩
        rw [hfB0 0 (by have := hs.hL; omega), hLab0, htdef, if_neg hxl]
        omega
      · rw [hfB0 0 (by have := hs.hL; omega), hLab0]
        omega
      · intro i hi
        rw [hfB0 i hi]
        have a := hlowi i hi
        rw [hLab0] at a
        have hpxq : par d x ≠ q := fun e => hxl (hxS.mpr e)
        rw [hpI i hi]
        constructor
        · intro h
          have := (a.mp (by omega)).mp (by omega)
          omega
        · intro h
          have : i % 2 = 0 := by omega
          have := a.mpr (by constructor <;> intro _ <;> omega)
          omega
      · intro i hi
        unfold Pc.tau ptau
        rw [hfB0 i hi]
        have := hLle i hi
        by_cases hll : Lab i ≤ lam
        · rw [if_pos (by omega), if_pos hll]; omega
        · rw [if_neg (by omega), if_neg hll]; omega
  -- glue
  have hR : A.P.R = B.R := by rw [A.hR, hBR]
  have hd : Disjoint A.P.S B.S := by
    rw [Finset.disjoint_left]
    intro z hzA hzB
    obtain ⟨i, hi, rfl⟩ := (hBS z).mp hzB
    exact hfresh i hi hzA
  have hw : nm 0 ∈ B.S := (hBS _).mpr ⟨0, by have := hs.hL; omega, rfl⟩
  have hxw : A.P.R x (nm 0) := by rw [A.hR]; exact hs.xw
  have hcr : ∀ p ∈ A.P.S, ∀ q' ∈ B.S, A.P.R p q' → p = x ∧ q' = nm 0 := by
    intro p hp q' hq' hr
    obtain ⟨i, hi, rfl⟩ := (hBS q').mp hq'
    rw [A.hR] at hr
    obtain ⟨h1, h2⟩ := hcross p hp i hi hr
    exact ⟨h1, by rw [h2]⟩
  have hJ := Pc.ifgl_alpha A.hA hBA hR hd hx hw hxw hcr hBf hthB
  have hJE := Pc.ijoin_card_E (th := A.th) hR A.hA.1.1 hd hx hw hxw hcr
  rw [hBE] at hJE
  set J := Pc.ijoin A.P B A.th x (nm 0) with hJdef
  have hJS : ∀ z, z ∈ J.S ↔ z ∈ A.P.S ∨ ∃ i, i < L ∧ nm i = z := by
    intro z
    show z ∈ A.P.S ∪ B.S ↔ _
    rw [Finset.mem_union, hBS]
  have hJfA : ∀ z ∈ A.P.S, J.f z = if A.P.f z < A.th then A.P.f z else A.P.f z + L := by
    intro z hz
    show (Pc.join A.P B A.th x (nm 0)).f z = _
    by_cases hl : A.P.f z < A.th
    · rw [Pc.join_f_lowA hz hl, if_pos hl]
    · rw [Pc.join_f_highA hz (by omega), if_neg hl, hBE]; have := hs.hL; omega
  have hJfB : ∀ z ∈ B.S, J.f z = A.th + B.f z := by
    intro z hz
    show (Pc.join A.P B A.th x (nm 0)).f z = _
    exact Pc.join_f_B hd hz
  have hthB_le : thB ≤ L := by have := hBA.2.1; omega
  have hBle : ∀ z ∈ B.S, B.f z ≤ L - 1 := by
    intro z hz; have := hBA.1.2.2.2.1 z hz; omega
  refine ⟨⟨J, A.th + thB, A.hR, hJ, ?_, A.hq⟩, hJS, by rw [hJE]; omega, ?_, ?_, ?_⟩
  · -- lowness
    intro z hz
    rcases (hJS z).mp hz with hzA | ⟨i, hi, rfl⟩
    · rw [hJfA z hzA]
      have hl' := A.hlow z hzA
      have := A.f_le hzA
      by_cases hl : A.P.f z < A.th
      · rw [if_pos hl]
        exact ⟨fun _ => hl'.mp hl, fun _ => by omega⟩
      · rw [if_neg hl]
        exact ⟨fun h => by omega, fun h => absurd (hl'.mpr h) hl⟩
    · have hzB : nm i ∈ B.S := (hBS _).mpr ⟨i, hi, rfl⟩
      rw [hJfB _ hzB]
      have := hBlow i hi
      constructor
      · intro h; exact this.mp (by omega)
      · intro h; have := this.mpr h; omega
  · -- eps of old vertices
    intro z hz
    have hle := A.f_le hz
    show J.eps (A.th + thB) z = A.P.eps A.th z
    unfold Pc.eps
    rw [hJfA z hz, hJE]
    by_cases hl : A.P.f z < A.th
    · simp only [if_pos hl]
      rw [if_pos (show A.P.f z < A.th + thB by omega)]
    · simp only [if_neg hl]
      rw [if_neg (show ¬ A.P.f z + L < A.th + thB by omega)]; omega
  · -- tau of old vertices
    intro z hz
    have hle := A.f_le hz
    have hlz := A.hlow z hz
    have hq := A.hq
    have hpz := par_le_one d z
    have hpx := par_le_one d x
    show J.tau (A.th + thB) z = A.P.tau A.th z + _
    unfold Pc.tau
    rw [hJfA z hz]
    by_cases hl : A.P.f z < A.th <;> by_cases hxl : A.P.f x < A.th
    · simp only [if_pos hl]
      rw [if_pos (show A.P.f z < A.th + thB by omega)]
      rw [if_pos hxl] at hthBv
      have := hlz.mp hl; have := hxS.mp hxl
      have e : (par d z + par d x) % 2 = 0 := by omega
      rw [e]; omega
    · simp only [if_pos hl]
      rw [if_pos (show A.P.f z < A.th + thB by omega)]
      rw [if_neg hxl] at hthBv
      have := hlz.mp hl; have : par d x ≠ q := fun e => hxl (hxS.mpr e)
      have e : (par d z + par d x) % 2 = 1 := by omega
      rw [e]; omega
    · simp only [if_neg hl]
      rw [if_neg (show ¬ A.P.f z + L < A.th + thB by omega)]
      rw [if_pos hxl] at hthBv
      have : par d z ≠ q := fun e => hl (hlz.mpr e); have := hxS.mp hxl
      have e : (par d z + par d x) % 2 = 1 := by omega
      rw [e]; omega
    · simp only [if_neg hl]
      rw [if_neg (show ¬ A.P.f z + L < A.th + thB by omega)]
      rw [if_neg hxl] at hthBv
      have : par d z ≠ q := fun e => hl (hlz.mpr e); have : par d x ≠ q := fun e => hxl (hxS.mpr e)
      have e : (par d z + par d x) % 2 = 0 := by omega
      rw [e]; omega
  · -- tau of the new segment
    intro i hi
    have hzB : nm i ∈ B.S := (hBS _).mpr ⟨i, hi, rfl⟩
    have := hBle _ hzB
    show J.tau (A.th + thB) (nm i) = _
    rw [← hBtau i hi]
    unfold Pc.tau
    rw [hJfB _ hzB]
    by_cases hb : B.f (nm i) < thB
    · rw [if_pos (by omega), if_pos hb]; omega
    · rw [if_neg (by omega), if_neg hb]; omega

/-- attach an α-EPL segment: needs `AeplOK L τ(x)`; the new end gets `τ = τ(x)` -/
theorem attach (A : APc d q) {x L : ℕ} {nm pos : ℕ → ℕ} (hs : Seg d x L nm pos)
    (hx : x ∈ A.P.S) (hfresh : ∀ i, i < L → nm i ∉ A.P.S)
    (hcross : ∀ p ∈ A.P.S, ∀ i, i < L → Tadj d p (nm i) → p = x ∧ i = 0)
    (hok : AeplOK L (A.tau x)) :
    ∃ B : APc d q, (∀ z, z ∈ B.P.S ↔ z ∈ A.P.S ∨ ∃ i, i < L ∧ nm i = z) ∧
      B.P.E.card = A.P.E.card + L ∧
      (∀ z ∈ A.P.S, B.eps z = A.eps z) ∧
      (∀ z ∈ A.P.S, B.tau z = A.tau z + (L + (par d z + par d x) % 2) / 2) ∧
      B.tau (nm (L - 1)) = A.tau x := by
  obtain ⟨Lab, hLab, hLab0⟩ := aepl L (A.tau x) hok
  have hl0 : Lab 0 ≤ (L - 1) / 2 := by rw [hLab0]; exact hok.2.1
  obtain ⟨B, h1, h2, h3, h4, h5⟩ := A.attachP hs hx hfresh hcross Lab hLab hLab0 hl0
  refine ⟨B, h1, h2, h3, h4, ?_⟩
  rw [h5 _ (by have := hs.hL; omega), ptau_last hLab hs.hL hl0, hLab0]

end APc
