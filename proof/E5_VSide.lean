/-! ## The v-side for `e = f = 2`: α-pieces on `v`, its two 2-arms and part of the `d`-path -/

/-- names: `v, e1, e2, f1, f2`, then the `d`-path from `v` inward -/
def vnm (d i : ℕ) : ℕ := if i < 5 then [1, 14, 22, 15, 23].getD i 0 else 5 + 8 * (d + 4 - i)

/-- parents in the v-spider -/
def vpa (i : ℕ) : ℕ := if i < 5 then [0, 0, 1, 0, 3].getD i 0 else if i = 5 then 0 else i - 1

theorem vnm_small (d i : ℕ) (hi : i < 5) :
    vnm d i = if i = 0 then 1 else if i = 1 then 14 else if i = 2 then 22 else if i = 3 then 15 else 23 := by
  unfold vnm; rw [if_pos hi]; interval_cases i <;> rfl

theorem vpa_small (i : ℕ) (hi : i < 5) :
    vpa i = if i = 2 then 1 else if i = 4 then 3 else 0 := by
  unfold vpa; rw [if_pos hi]; interval_cases i <;> rfl

theorem vnm_big (d i : ℕ) (hi : 5 ≤ i) : vnm d i = 5 + 8 * (d + 4 - i) := by
  unfold vnm; rw [if_neg (by omega)]

theorem vSpider_adj (d jl : ℕ) (hd : jl + 1 ≤ d) (hd2 : 2 ≤ d) :
    ∀ i k, i < 5 + jl → k < 5 + jl →
      (Tadj d (vnm d i) (vnm d k) ↔ (i ≠ 0 ∧ vpa i = k) ∨ (k ≠ 0 ∧ vpa k = i)) := by
  have h5 : 2 ≤ 5 ∧ 5 ≤ 7 := by omega
  have small : ∀ i k, i < 5 → k < 5 →
      (Tadj d (vnm d i) (vnm d k) ↔ (i ≠ 0 ∧ vpa i = k) ∨ (k ≠ 0 ∧ vpa k = i)) := by
    intro i k hi hk
    rw [vnm_small d i hi, vnm_small d k hk, vpa_small i hi, vpa_small k hk]
    unfold Tadj Tpar dEnd armRoot
    interval_cases i <;> interval_cases k <;> simp <;> (try split_ifs) <;> omega
  have mixed : ∀ i k, i < 5 → 5 ≤ k → k < 5 + jl →
      (Tadj d (vnm d i) (vnm d k) ↔ (i = 0 ∧ k = 5)) := by
    intro i k hi hk1 hk2
    rw [vnm_big d k hk1, Tadj_arm_iff d 5 (d + 4 - k) _ h5 (by omega), vnm_small d i hi,
      show armRoot 5 = 0 from rfl]
    constructor
    · rintro (h | h | ⟨_, h1, h2⟩)
      · split_ifs at h <;> omega
      · split_ifs at h <;> omega
      · split_ifs at h2 <;> omega
    · rintro ⟨rfl, rfl⟩
      right; right; exact ⟨rfl, by omega, rfl⟩
  intro i k hi hk
  by_cases hi5 : i < 5 <;> by_cases hk5 : k < 5
  · exact small i k hi5 hk5
  · rw [mixed i k hi5 (by omega) hk]
    rw [vpa_small i hi5]
    unfold vpa; rw [if_neg hk5]
    constructor
    · rintro ⟨rfl, rfl⟩; right; simp
    · rintro (⟨_, h⟩ | ⟨_, h⟩)
      · split_ifs at h <;> omega
      · split_ifs at h <;> omega
  · constructor
    · intro h
      have := (mixed k i hk5 (by omega) hi).mp (Tadj_symm d _ _ h)
      obtain ⟨rfl, rfl⟩ := this
      left; unfold vpa; simp
    · intro h
      apply Tadj_symm
      apply (mixed k i hk5 (by omega) hi).mpr
      rw [vpa_small k hk5] at h
      unfold vpa at h; rw [if_neg hi5] at h
      rcases h with ⟨_, h⟩ | ⟨_, h⟩
      · split_ifs at h <;> omega
      · split_ifs at h <;> omega
  · have hi' : 5 ≤ i := by omega
    have hk' : 5 ≤ k := by omega
    rw [vnm_big d i hi', vnm_big d k hk', Tadj_arm_iff d 5 (d + 4 - k) _ h5 (by omega),
      show armRoot 5 = 0 from rfl]
    have vi : vpa i = if i = 5 then 0 else i - 1 := by unfold vpa; rw [if_neg hi5]
    have vk : vpa k = if k = 5 then 0 else k - 1 := by unfold vpa; rw [if_neg hk5]
    rw [vi, vk]
    constructor
    · rintro (h | h | ⟨_, _, h⟩)
      · by_cases hm : d + 4 - k = 1
        · rw [if_pos hm] at h; omega
        · rw [if_neg hm] at h
          left; refine ⟨by omega, ?_⟩; rw [if_neg (by omega)]; omega
      · right; refine ⟨by omega, ?_⟩; rw [if_neg (by omega)]; omega
      · omega
    · rintro (⟨_, h⟩ | ⟨_, h⟩)
      · by_cases h6 : i = 5
        · rw [if_pos h6] at h; omega
        · rw [if_neg h6] at h
          left; rw [if_neg (by omega)]; omega
      · by_cases h6 : k = 5
        · rw [if_pos h6] at h; omega
        · rw [if_neg h6] at h
          right; left; omega

/-- the v-side piece: `v`, its two 2-arms, and `d`-path positions `d-D … d-1`, with
`τ` at the junction vertex (`v` if `D = 0`, else position `d-D`) equal to `σ` -/
def VSP (d D σ : ℕ) : Prop :=
  ∃ q, ∃ A : APc d q, (∀ z, z ∈ A.P.S ↔ z = 1 ∨ z = 14 ∨ z = 22 ∨ z = 15 ∨ z = 23 ∨
      (z % 8 = 5 ∧ d - D ≤ z / 8 ∧ z / 8 ≤ d - 1 ∧ 1 ≤ D)) ∧
    A.P.E.card = 4 + D ∧ A.tau (if D = 0 then 1 else 5 + 8 * (d - D)) = σ

/-- depth of the `i`-th v-spider vertex below `v` -/
def vdepth (i : ℕ) : ℕ := if i < 5 then [0, 1, 2, 1, 2].getD i 0 else i - 4

theorem par_vnm (d j i : ℕ) (hd : j + 1 ≤ d) (hi : i < 5 + j) :
    par d (vnm d i) = (d + vdepth i) % 2 := by
  by_cases h5 : i < 5
  · rw [vnm_small d i h5]
    unfold vdepth; rw [if_pos h5]
    interval_cases i <;> simp [par] <;> omega
  · rw [vnm_big d i (by omega), par_arm d 5 _ (by omega) (by omega)]
    unfold vdepth; rw [if_neg h5]
    simp only [show ¬ 6 ≤ 5 by omega, if_false]
    omega

theorem vnm_inj (d j : ℕ) (hd : j + 1 ≤ d) :
    ∀ i k, i < 5 + j → k < 5 + j → vnm d i = vnm d k → i = k := by
  intro i k hi hk e
  by_cases hi5 : i < 5 <;> by_cases hk5 : k < 5
  · rw [vnm_small d i hi5, vnm_small d k hk5] at e
    interval_cases i <;> interval_cases k <;> simp at e ⊢
  · rw [vnm_small d i hi5, vnm_big d k (by omega)] at e
    split_ifs at e <;> omega
  · rw [vnm_big d i (by omega), vnm_small d k hk5] at e
    split_ifs at e <;> omega
  · rw [vnm_big d i (by omega), vnm_big d k (by omega)] at e
    omega

/-- an explicit α-labeled v-spider core with the `d`-path leg of length `j` -/
theorem vCore (d j th c : ℕ) (labs : List ℕ) (hd : j + 1 ≤ d) (hd2 : 2 ≤ d) (hj : 1 ≤ j)
    (hc : treeCheck (5 + j) th true vpa (fun i => labs.getD i 0) = true)
    (hlowc : ∀ i, i < 5 + j → (labs.getD i 0 < th ↔ (vdepth i + c) % 2 = 0)) (hc1 : c ≤ 1) :
    ∃ A : APc d ((d + c) % 2), (∀ z, z ∈ A.P.S ↔ z = 1 ∨ z = 14 ∨ z = 22 ∨ z = 15 ∨ z = 23 ∨
        (z % 8 = 5 ∧ d - j ≤ z / 8 ∧ z / 8 ≤ d - 1)) ∧
      A.P.E.card = 4 + j ∧
      A.tau (5 + 8 * (d - j)) = (if labs.getD (4 + j) 0 < th then th - 1 - labs.getD (4 + j) 0
        else labs.getD (4 + j) 0 - th) := by
  obtain ⟨A, hS, hE, _, ht⟩ := startTree d (5 + j) th ((d + c) % 2) (vnm d)
    (fun z => if z = 1 then 0 else if z = 14 then 1 else if z = 22 then 2 else if z = 15 then 3
      else if z = 23 then 4 else d + 4 - z / 8) vpa (fun i => labs.getD i 0) (by omega)
    (vnm_inj d j hd)
    (by
      intro i hi
      by_cases h5 : i < 5
      · rw [vnm_small d i h5]; interval_cases i <;> simp
      · rw [vnm_big d i (by omega)]; split_ifs <;> omega)
    (vSpider_adj d j hd hd2) hc
    (by
      intro i hi
      rw [hlowc i hi, par_vnm d j i hd hi]
      omega)
    (by omega)
  refine ⟨A, ?_, by rw [hE]; omega, ?_⟩
  · intro z
    rw [hS]
    constructor
    · rintro ⟨i, hi, rfl⟩
      by_cases h5 : i < 5
      · rw [vnm_small d i h5]; interval_cases i <;> simp
      · rw [vnm_big d i (by omega)]; right; right; right; right; right; omega
    · rintro (rfl | rfl | rfl | rfl | rfl | h)
      · exact ⟨0, by omega, by rw [vnm_small d 0 (by omega)]; simp⟩
      · exact ⟨1, by omega, by rw [vnm_small d 1 (by omega)]; simp⟩
      · exact ⟨2, by omega, by rw [vnm_small d 2 (by omega)]; simp⟩
      · exact ⟨3, by omega, by rw [vnm_small d 3 (by omega)]; simp⟩
      · exact ⟨4, by omega, by rw [vnm_small d 4 (by omega)]; simp⟩
      · exact ⟨d + 4 - z / 8, by omega, by rw [vnm_big d _ (by omega)]; omega⟩
  · have := ht (4 + j) (by omega)
    rw [vnm_big d (4 + j) (by omega), show d + 4 - (4 + j) = d - j by omega] at this
    exact this

theorem arms_v : Arms2 1 6 7 := ⟨by omega, by omega, by omega, by omega, by omega, rfl, rfl⟩

def labP22 (i : ℕ) : ℕ := [0, 4, 1, 3, 2].getD i 0

theorem labP22_alpha : PathAlpha 5 labP22 2 := by
  apply pathAlpha_of <;> decide

/-- the α-labelled `P(2,2)` at `v` with `τ(v) = 1` -/
theorem p22_piece (d : ℕ) (hd : 1 ≤ d) :
    ∃ q, ∃ A : APc d q, (∀ z, z ∈ A.P.S ↔ z = 1 ∨ z = 14 ∨ z = 22 ∨ z = 15 ∨ z = 23) ∧
      A.P.E.card = 4 ∧ A.tau 1 = 1 := by
  obtain ⟨A, hS, hE, _, ht⟩ := startThrough d 1 6 7 2 2 hd arms_v (by omega) (by omega) labP22
    (by simpa using labP22_alpha) (by decide)
  refine ⟨_, A, fun z => by rw [hS]; unfold Sh2; omega, hE, ?_⟩
  have := ht 2 (by omega)
  simp only [tnm, lt_irrefl, if_false, if_true] at this
  rw [this]; decide

theorem vsp_p22 (d : ℕ) (hd : 1 ≤ d) : VSP d 0 1 := by
  obtain ⟨q, A, hS, hE, ht⟩ := p22_piece d hd
  exact ⟨q, A, fun z => by rw [hS]; omega, by rw [hE], by rw [if_pos rfl]; exact ht⟩

theorem vsp_chain1 (d D : ℕ) (hD : 1 ≤ D) (hDd : D + 1 ≤ d) (hok : AeplOK D 1) : VSP d D 1 := by
  obtain ⟨q, A, hS, hE, ht⟩ := p22_piece d (by omega)
  obtain ⟨B, hS', hE', _, _, ht'⟩ := A.attachDV D hD hDd (by rw [hS]; left; rfl)
    (by intro i hi h; rw [hS] at h; omega) (by intro _ h; rw [hS] at h; omega)
    (by intro _ h; rw [hS] at h; omega) (by intro h; rw [hS] at h; omega)
    (by rw [ht]; exact hok)
  refine ⟨q, B, fun z => by rw [hS', hS]; omega, by rw [hE', hE], ?_⟩
  rw [if_neg (by omega), ht', ht]

theorem vsp_core11 (d : ℕ) (hd : 2 ≤ d) : VSP d 1 1 := by
  obtain ⟨A, hS, hE, ht⟩ := vCore d 1 3 0 [1, 3, 2, 5, 0, 4] (by omega) hd (by omega)
    (by decide +kernel) (by decide +kernel) (by omega)
  exact ⟨_, A, fun z => by rw [hS]; omega, hE, by rw [if_neg (by omega), ht]; decide⟩

theorem vsp_core51 (d : ℕ) (hd : 6 ≤ d) : VSP d 5 1 := by
  obtain ⟨A, hS, hE, ht⟩ := vCore d 5 5 0 [1, 7, 2, 9, 0, 8, 4, 5, 3, 6] (by omega) (by omega)
    (by omega) (by decide +kernel) (by decide +kernel) (by omega)
  exact ⟨_, A, fun z => by rw [hS]; omega, hE, by rw [if_neg (by omega), ht]; decide⟩

/-- σ = 2 cores with a chain toward `u` -/
theorem vsp_core2 (d j L : ℕ) (hj : j = 3 ∨ j = 4) (hd : j + L + 1 ≤ d)
    (hok : L = 0 ∨ AeplOK L 2) : VSP d (j + L) 2 := by
  obtain ⟨c, A, hS, hE, ht⟩ : ∃ c, ∃ A : APc d ((d + c) % 2),
      (∀ z, z ∈ A.P.S ↔ z = 1 ∨ z = 14 ∨ z = 22 ∨ z = 15 ∨ z = 23 ∨
        (z % 8 = 5 ∧ d - j ≤ z / 8 ∧ z / 8 ≤ d - 1)) ∧
      A.P.E.card = 4 + j ∧ A.tau (5 + 8 * (d - j)) = 2 := by
    rcases hj with rfl | rfl
    · obtain ⟨A, hS, hE, ht⟩ := vCore d 3 4 0 [2, 4, 3, 5, 1, 7, 0, 6] (by omega) (by omega)
        (by omega) (by decide +kernel) (by decide +kernel) (by omega)
      exact ⟨0, A, hS, hE, by rw [ht]; decide⟩
    · obtain ⟨A, hS, hE, ht⟩ := vCore d 4 4 1 [5, 3, 4, 2, 7, 1, 8, 0, 6] (by omega) (by omega)
        (by omega) (by decide +kernel) (by decide +kernel) (by omega)
      exact ⟨1, A, hS, hE, by rw [ht]; decide⟩
  rcases hok with rfl | hok
  · exact ⟨_, A, fun z => by rw [hS]; omega, by rw [hE]; rfl, by rw [if_neg (by omega), Nat.add_zero, ht]⟩
  · have hL : 1 ≤ L := hok.1
    obtain ⟨B, hS', hE', _, _, ht'⟩ := A.attachDD (d - j - 1) L hL (by omega) (by omega)
      (by rw [hS, show d - j - 1 + 1 = d - j by omega]; right; right; right; right; right; omega)
      (by intro i hi h; rw [hS] at h; omega) (by intro _ h; rw [hS] at h; omega)
      (by intro _ h; rw [hS] at h; omega)
      (by rw [show d - j - 1 + 1 = d - j by omega, ht]; exact hok)
    refine ⟨_, B, fun z => by rw [hS', hS]; omega, by rw [hE', hE]; omega, ?_⟩
    rw [if_neg (by omega), show d - (j + L) = d - j - 1 + 1 - L by omega, ht',
      show d - j - 1 + 1 = d - j by omega, ht]

theorem vsp1 (d D : ℕ) (hD : D + 1 ≤ d) (h : D = 0 ∨ AeplOK D 1 ∨ D = 1 ∨ D = 5) : VSP d D 1 := by
  rcases h with rfl | h | rfl | rfl
  · exact vsp_p22 d (by omega)
  · exact vsp_chain1 d D h.1 hD h
  · exact vsp_core11 d (by omega)
  · exact vsp_core51 d (by omega)

theorem vsp2 (d D : ℕ) (hD : D + 1 ≤ d)
    (h : D = 3 ∨ D = 4 ∨ (3 < D ∧ AeplOK (D - 3) 2) ∨ (4 < D ∧ AeplOK (D - 4) 2)) : VSP d D 2 := by
  rcases h with rfl | rfl | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact vsp_core2 d 3 0 (Or.inl rfl) (by omega) (Or.inl rfl)
  · exact vsp_core2 d 4 0 (Or.inr rfl) (by omega) (Or.inl rfl)
  · have := vsp_core2 d 3 (D - 3) (Or.inl rfl) (by omega) (Or.inr h2)
    rwa [show 3 + (D - 3) = D by omega] at this
  · have := vsp_core2 d 4 (D - 4) (Or.inr rfl) (by omega) (Or.inr h2)
    rwa [show 4 + (D - 4) = D by omega] at this
