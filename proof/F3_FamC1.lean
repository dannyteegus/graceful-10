/-! ## Family C (`e = f = 2`): templates V, cut, U -/

theorem tset22_iff {a b c d s : ℕ} (hd : 1 ≤ d) :
    s ∈ Tset a b c d 2 2 ↔ ShU a b c s ∨ s = 1 ∨ s = 14 ∨ s = 22 ∨ s = 15 ∨ s = 23 ∨
      (s % 8 = 5 ∧ 1 ≤ s / 8 ∧ s / 8 ≤ d - 1) := by
  rw [mem_Tset_iff hd]; unfold ShU
  constructor
  · rintro (h | h | h | h | h | h | h | h) <;> omega
  · rintro ((h | h | h | h) | h | h | h | h | h | h) <;> omega

theorem dnode_one {d : ℕ} (hd : 1 ≤ d) :
    (if d - 1 = 0 then 1 else 5 + 8 * (d - (d - 1))) = dnode d (0 + 1) := by
  unfold dnode
  by_cases h1 : d = 1
  · subst h1; simp
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]; omega

theorem dnode_two {d : ℕ} (hd : 2 ≤ d) :
    (if d - 2 = 0 then 1 else 5 + 8 * (d - (d - 2))) = dnode d (1 + 1) := by
  unfold dnode
  by_cases h1 : d = 2
  · subst h1; simp
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]; omega

/-- template V: the v-side (with the whole `d`-path) α, junction `τ = σ`, and a σ-spider -/
theorem famC_V {a b c d σ : ℕ} (hd : 1 ≤ d) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hσ : σ ≤ 2)
    (hV : VSP d (d - 1) σ) (hS : SPG d σ a b c) : CanonGraceful a b c d 2 2 := by
  obtain ⟨q, A, hSA, _, htA⟩ := hV
  obtain ⟨G, hG, hGR, hGS, hGE, hGf⟩ := hS
  rw [dnode_one hd] at htA
  have hw : dnode d 0 = 0 := by unfold dnode; simp
  refine join_vu (j := 0) hd (by omega) A G hG hGR
    (by intro z hz; rw [hSA] at hz; unfold vPart; omega)
    (by intro z hz; rw [hGS] at hz; unfold ShU at hz; unfold uPart; omega)
    (by rw [← dnode_one hd, hSA]; split_ifs <;> omega)
    (by rw [hw, hGS]; left; rfl)
    (by rw [hw, htA]; exact hGf)
    (by rw [htA, hGE]; omega)
    (by
      intro s; rw [hSA, hGS, tset22_iff hd]
      constructor
      · rintro ((h | h | h | h | h | h) | h)
        · omega
        · omega
        · omega
        · omega
        · omega
        · omega
        · left; exact h
      · rintro (h | h | h | h | h | h | h)
        · right; exact h
        all_goals left; omega)

/-- the piece for the cut template: `d1, u` and the three arms, `d1` at label `1` -/
theorem cutB_prog {d X Y Z x y z : ℕ} (hd : 2 ≤ d) (h : Arms3 X Y Z) (hx : 2 ≤ x) (hy : 1 ≤ y)
    (hz : 1 ≤ z) (hok1 : AeplOK (x - 1) 1) (hok2 : AeplOK y (x / 2))
    (hok3 : x / 2 + y / 2 ≤ z - 1) :
    ∃ G : Pc, G.Grace ∧ G.R = Tadj d ∧ (∀ w, w ∈ G.S ↔ w = 13 ∨ ShXYZ X x Y y Z z w) ∧
      G.E.card = 1 + x + y + z ∧ (G.f 13 = 1 ∨ G.f 13 = G.E.card - 1) := by
  obtain ⟨hX, hY, hZ, hXY, hXZ, hYZ⟩ := h
  have hrX := armRoot_u hX
  have hrY := armRoot_u hY
  have hrZ := armRoot_u hZ
  have pX1 : par d (X + 8 * 1) = 1 := by
    rw [par_arm_root d X 1 (by omega) (by omega), hrX, par_zero]
  have p13 : par d 13 = 1 := by rw [show (13 : ℕ) = 5 + 8 * 1 by rfl, par_arm d 5 1 (by omega) (by omega)]; simp
  have a130 : Tadj d 13 0 := by rw [tadjB_iff, tadjB_indep d _ _ (by omega) (by omega)]; decide
  have a0X : Tadj d 0 (X + 8 * 1) := by
    apply (Tadj_arm_iff d X 1 0 (by omega) (by omega)).mpr; left; rw [if_pos rfl, hrX]
  have n13X : ¬ Tadj d 13 (X + 8 * 1) := by
    intro h'
    rcases (Tadj_arm_iff d X 1 13 (by omega) (by omega)).mp h' with e | e | ⟨e, _⟩ <;> [skip; omega; omega]
    rw [if_pos rfl, hrX] at e; omega
  -- the start path `13, 0, X1` labelled `1, 2, 0`
  have hL : PathAlpha 3 (fun i => [1, 2, 0].getD i 0) 1 := by apply pathAlpha_of <;> decide
  obtain ⟨A0, hS0, hE0, he0, ht0⟩ := startPath d 3 (fun i => [13, 0, X + 8 * 1].getD i 0)
    (fun w => if w = 13 then 0 else if w = 0 then 1 else 2) (fun i => [1, 2, 0].getD i 0) (by omega)
    (by intro i j hi hj e; interval_cases i <;> interval_cases j <;> simp at e ⊢ <;> omega)
    (by intro i hi; interval_cases i <;> simp <;> omega)
    (by intro i hi
        have : i < 2 := by omega
        interval_cases i
        · exact a130
        · exact a0X)
    (by
      intro i j hi hj e
      interval_cases i <;> interval_cases j <;> simp at e ⊢
      · exact absurd e (Tadj_irrefl d 13 (by omega))
      · exact n13X e
      · exact absurd e (Tadj_irrefl d 0 (by omega))
      · exact n13X (Tadj_symm d _ _ e)
      · exact absurd e (Tadj_irrefl d _ (by omega)))
    (by intro i hi; interval_cases i <;> simp [p13, pX1, par_zero])
    hL (by decide)
  have hS0' : ∀ w, w ∈ A0.P.S ↔ w = 13 ∨ w = 0 ∨ (w % 8 = X ∧ w / 8 = 1) := by
    intro w; rw [hS0]
    constructor
    · rintro ⟨i, hi, rfl⟩; interval_cases i <;> simp <;> omega
    · rintro (rfl | rfl | h')
      · exact ⟨0, by omega, rfl⟩
      · exact ⟨1, by omega, rfl⟩
      · exact ⟨2, by omega, by simp; omega⟩
  have e13 : A0.eps 13 = 1 := by have := he0 0 (by omega); simpa [peps] using this
  have t0 : A0.tau 0 = 0 := by have := ht0 1 (by omega); simpa [ptau] using this
  have tX1 : A0.tau (X + 8 * 1) = 1 := by have := ht0 2 (by omega); simpa [ptau] using this
  have m13 : (13 : ℕ) ∈ A0.P.S := by rw [hS0']; left; rfl
  have m0 : (0 : ℕ) ∈ A0.P.S := by rw [hS0']; right; left; rfl
  have mX1 : X + 8 * 1 ∈ A0.P.S := by rw [hS0']; omega
  -- X tail
  obtain ⟨A1, hS1, hE1, he1, ht1, _⟩ := A0.attachArm X 1 (x - 1) (by omega) (by omega) (by omega) mX1
    (by intro i hi hm; rw [hS0'] at hm; omega) (by intro hm; rw [hS0'] at hm; omega)
    (fun e => by omega) (fun e => by omega) (by rw [tX1]; exact hok1)
  have hS1' : ∀ w, w ∈ A1.P.S ↔ w = 13 ∨ w = 0 ∨ (w % 8 = X ∧ 1 ≤ w / 8 ∧ w / 8 ≤ x) := by
    intro w; rw [hS1, hS0']; omega
  have t1 : A1.tau 0 = x / 2 := by rw [ht1 _ m0, t0, pX1, par_zero]; omega
  have m0' : (0 : ℕ) ∈ A1.P.S := by rw [hS1']; right; left; rfl
  -- Y at the root
  obtain ⟨A2, hS2, hE2, he2, ht2, _⟩ := A1.attachRoot Y y (by omega) hy (by rw [hrY]; exact m0')
    (by intro i hi hm; rw [hS1'] at hm; omega) (by intro hm; rw [hS1'] at hm; omega)
    (fun e => by omega) (fun e => by omega) (by rw [hrY, t1]; exact hok2)
  have hS2' : ∀ w, w ∈ A2.P.S ↔ w = 13 ∨ w = 0 ∨ (w % 8 = X ∧ 1 ≤ w / 8 ∧ w / 8 ≤ x) ∨
      (w % 8 = Y ∧ 1 ≤ w / 8 ∧ w / 8 ≤ y) := by
    intro w; rw [hS2, hS1']; omega
  have t2 : A2.tau 0 = x / 2 + y / 2 := by
    rw [ht2 _ m0', t1, hrY, show (par d 0 + par d 0) % 2 = 0 by rw [par_zero]]; omega
  have m0'' : (0 : ℕ) ∈ A2.P.S := by rw [hS2']; right; left; rfl
  -- final Z
  obtain ⟨G, hG, hR, hSG, hEG, hf⟩ := A2.attachGRoot Z z (by omega) hz (by rw [hrZ]; exact m0'')
    (by intro i hi hm; rw [hS2'] at hm; omega) (by intro hm; rw [hS2'] at hm; omega)
    (fun e => by omega) (fun e => by omega) (by rw [hrZ, t2]; exact hok3)
  have m13' : (13 : ℕ) ∈ A1.P.S := by rw [hS1']; left; rfl
  have m13'' : (13 : ℕ) ∈ A2.P.S := by rw [hS2']; left; rfl
  refine ⟨G, hG, hR, fun w => by rw [hSG, hS2']; unfold ShXYZ; omega,
    by rw [hEG, hE2, hE1, hE0]; omega, ?_⟩
  rcases hf 13 m13'' with e | e <;> rw [he2 _ m13', he1 _ m13, e13] at e
  · left; exact e
  · right; exact e

/-- template cut: the v-side down to position 2, the u-side with `d1` -/
theorem famC_cut {a b c d X Y Z x y z : ℕ} (hd : 2 ≤ d) (h : Arms3 X Y Z)
    (ha : a = if X = 2 then x else if Y = 2 then y else z)
    (hb : b = if X = 3 then x else if Y = 3 then y else z)
    (hc : c = if X = 4 then x else if Y = 4 then y else z)
    (hx : 2 ≤ x) (hy : 1 ≤ y) (hz : 1 ≤ z) (hok1 : AeplOK (x - 1) 1) (hok2 : AeplOK y (x / 2))
    (hok3 : x / 2 + y / 2 ≤ z - 1) (hV : VSP d (d - 2) 1) : CanonGraceful a b c d 2 2 := by
  obtain ⟨q, A, hSA, _, htA⟩ := hV
  obtain ⟨G, hG, hGR, hGS, hGE, hGf⟩ := cutB_prog (d := d) (by omega) h hx hy hz hok1 hok2 hok3
  rw [dnode_two hd] at htA
  have hw : dnode d 1 = 13 := by unfold dnode; rw [if_neg (by omega), if_neg (by omega)]
  have hperm := fun w => shU_perm (w := w) h ha hb hc
  refine join_vu (j := 1) (by omega) (by omega) A G hG hGR
    (by intro w hw'; rw [hSA] at hw'; unfold vPart; omega)
    (by
      intro w hw'; rw [hGS] at hw'
      rcases hw' with hw' | hw'
      · unfold uPart; omega
      · unfold ShXYZ at hw'; rw [hperm w] at hw'; unfold ShU at hw'; unfold uPart; omega)
    (by rw [← dnode_two hd, hSA]; split_ifs <;> omega)
    (by rw [hw, hGS]; left; rfl)
    (by rw [hw, htA]; exact hGf)
    (by rw [htA, hGE]; omega)
    (by
      intro s; rw [hSA, hGS, tset22_iff (by omega)]
      unfold ShXYZ; rw [hperm s]; unfold ShU
      constructor
      · rintro ((h | h | h | h | h | h) | (h | h | h | h | h)) <;> omega
      · rintro ((h | h | h | h) | h | h | h | h | h | h) <;> omega)
