/-! ## Explicit start paths through a root (`X`-arm inward, root, `Y`-arm outward) -/

/-- names along the path: `X`-arm positions `p, …, 1`, the root, `Y`-arm positions `1, 2, …` -/
def tnm (r X Y p i : ℕ) : ℕ :=
  if i < p then X + 8 * (p - i) else if i = p then r else Y + 8 * (i - p)

theorem startThrough (d r X Y p s : ℕ) (hd : 1 ≤ d) (h : Arms2 r X Y) (hp : 1 ≤ p) (hs : 1 ≤ s)
    (Lab : ℕ → ℕ) (hLab : PathAlpha (p + s + 1) Lab ((p + s) / 2)) (h0 : Lab 0 ≤ (p + s) / 2) :
    ∃ A : APc d ((par d r + p) % 2), (∀ z, z ∈ A.P.S ↔ Sh2 r X p Y s z) ∧ A.P.E.card = p + s ∧
      (∀ i, i ≤ p + s → A.eps (tnm r X Y p i) = peps (p + s + 1) Lab i) ∧
      (∀ i, i ≤ p + s → A.tau (tnm r X Y p i) = ptau (p + s + 1) Lab i) := by
  obtain ⟨hX, hY, hXY, hX5, hY5, hrX, hrY⟩ := h
  have hr2 : r < 2 := by rw [← hrX]; exact armRoot_lt X
  have pXk : ∀ k, 1 ≤ k → par d (X + 8 * k) = (par d r + k) % 2 := by
    intro k hk; rw [par_arm_root d X k hX hk, hrX]
  have pYk : ∀ k, 1 ≤ k → par d (Y + 8 * k) = (par d r + k) % 2 := by
    intro k hk; rw [par_arm_root d Y k hY hk, hrY]
  have pr := par_le_one d r
  -- adjacency facts
  have adjX : ∀ k p', 1 ≤ k → (Tadj d p' (X + 8 * k) ↔
      p' = (if k = 1 then r else X + 8 * (k - 1)) ∨ p' = X + 8 * (k + 1)) := by
    intro k p' hk
    rw [Tadj_arm_iff d X k p' hX hk, hrX]
    constructor
    · rintro (h1 | h1 | ⟨h5, _, _⟩)
      · exact Or.inl h1
      · exact Or.inr h1
      · exact absurd h5 hX5
    · rintro (h1 | h1)
      · exact Or.inl h1
      · exact Or.inr (Or.inl h1)
  have adjY : ∀ k p', 1 ≤ k → (Tadj d p' (Y + 8 * k) ↔
      p' = (if k = 1 then r else Y + 8 * (k - 1)) ∨ p' = Y + 8 * (k + 1)) := by
    intro k p' hk
    rw [Tadj_arm_iff d Y k p' hY hk, hrY]
    constructor
    · rintro (h1 | h1 | ⟨h5, _, _⟩)
      · exact Or.inl h1
      · exact Or.inr h1
      · exact absurd h5 hY5
    · rintro (h1 | h1)
      · exact Or.inl h1
      · exact Or.inr (Or.inl h1)
  have hrr : ¬ Tadj d r r := Tadj_irrefl d r hd
  obtain ⟨A, hS, hE, he, ht⟩ := startPath d (p + s + 1) (tnm r X Y p)
    (fun z => if z = r then p else if z % 8 = X then p - z / 8 else p + z / 8) Lab (by omega)
    (by intro i j _ _ e; unfold tnm at e; split_ifs at e <;> omega)
    (by intro i _; unfold tnm; split_ifs <;> omega)
    (by
      intro i hi
      unfold tnm
      by_cases h1 : i + 1 < p
      · rw [if_pos (by omega), if_pos h1]
        exact (adjX (p - (i + 1)) _ (by omega)).mpr
          (Or.inr (by rw [show p - (i + 1) + 1 = p - i by omega]))
      · by_cases h2 : i + 1 = p
        · rw [if_pos (by omega), if_neg (by omega), if_pos h2]
          exact Tadj_symm d _ _ ((adjX (p - i) _ (by omega)).mpr (Or.inl (by rw [if_pos (by omega)])))
        · by_cases h3 : i = p
          · rw [if_neg (by omega), if_pos h3, if_neg (by omega), if_neg (by omega)]
            exact (adjY (i + 1 - p) _ (by omega)).mpr (Or.inl (by rw [if_pos (by omega)]))
          · rw [if_neg (by omega), if_neg h3, if_neg (by omega), if_neg (by omega)]
            exact (adjY (i + 1 - p) _ (by omega)).mpr (Or.inl (by rw [if_neg (by omega)]; congr 1; omega)))
    (by
      intro i j hi hj hadj
      unfold tnm at hadj
      by_cases hj1 : j < p
      · rw [if_pos hj1] at hadj
        rcases (adjX (p - j) _ (by omega)).mp hadj with e | e
        · split_ifs at hadj e <;> omega
        · split_ifs at hadj e <;> omega
      · by_cases hj2 : j = p
        · rw [if_neg hj1, if_pos hj2] at hadj
          by_cases hi1 : i < p
          · rw [if_pos hi1] at hadj
            rcases (adjX (p - i) _ (by omega)).mp (Tadj_symm d _ _ hadj) with e | e
            · split_ifs at e <;> omega
            · omega
          · by_cases hi2 : i = p
            · rw [if_neg hi1, if_pos hi2] at hadj; exact absurd hadj hrr
            · rw [if_neg hi1, if_neg hi2] at hadj
              rcases (adjY (i - p) _ (by omega)).mp (Tadj_symm d _ _ hadj) with e | e
              · split_ifs at e <;> omega
              · omega
        · rw [if_neg hj1, if_neg hj2] at hadj
          rcases (adjY (j - p) _ (by omega)).mp hadj with e | e
          · split_ifs at hadj e <;> omega
          · split_ifs at hadj e <;> omega)
    (by
      intro i hi
      unfold tnm
      rw [if_pos (by omega : 0 < p), Nat.sub_zero, pXk p hp]
      split_ifs with h1 h2
      · rw [pXk _ (by omega)]; omega
      · omega
      · rw [pYk _ (by omega)]; omega)
    hLab (by rw [show p + s + 1 - 1 = p + s by omega]; exact h0)
  have hq : par d (tnm r X Y p 0) = (par d r + p) % 2 := by
    unfold tnm; rw [if_pos (by omega), Nat.sub_zero, pXk p hp]
  refine ⟨A.recast hq, ?_, ?_, ?_, ?_⟩
  · intro z
    rw [APc.recast_P, hS]
    unfold Sh2 tnm
    constructor
    · rintro ⟨i, hi, rfl⟩
      split_ifs <;> omega
    · rintro (rfl | h | h)
      · exact ⟨p, by omega, by simp⟩
      · exact ⟨p - z / 8, by omega, by rw [if_pos (by omega)]; omega⟩
      · exact ⟨p + z / 8, by omega, by rw [if_neg (by omega), if_neg (by omega)]; omega⟩
  · rw [APc.recast_P, hE]; omega
  · intro i hi; rw [APc.recast_eps, he i (by omega)]
  · intro i hi; rw [APc.recast_tau, ht i (by omega)]

/-- the explicit core `IVL0(6,6)` -/
def lab66 (i : ℕ) : ℕ := [2, 7, 6, 8, 5, 9, 0, 12, 1, 11, 3, 10, 4].getD i 0

/-- a decidable form of `PathAlpha` -/
theorem pathAlpha_of {n lam : ℕ} {L : ℕ → ℕ}
    (h1 : ∀ i, i < n → ∀ j, j < n → L i = L j → i = j) (h2 : ∀ i, i < n → L i ≤ n - 1)
    (h3 : ∀ i, i < n - 1 → ∀ j, j < n - 1 →
      Nat.dist (L i) (L (i + 1)) = Nat.dist (L j) (L (j + 1)) → i = j)
    (h4 : ∀ i, i < n - 1 → (L i ≤ lam ↔ lam < L (i + 1))) : PathAlpha n L lam :=
  ⟨fun i j hi hj => h1 i hi j hj, h2, fun i j hi hj => h3 i (by omega) j (by omega),
    fun i hi => h4 i (by omega)⟩

theorem lab66_alpha : PathAlpha 13 lab66 6 := by
  apply pathAlpha_of
  · decide
  · decide
  · decide
  · decide

theorem ivl0_66 {d r X Y : ℕ} (hd : 1 ≤ d) (h : Arms2 r X Y) : IVL0P d r X Y 6 6 := by
  obtain ⟨A, hS, hE, he, ht⟩ := startThrough d r X Y 6 6 hd h (by omega) (by omega) lab66
    (by simpa using lab66_alpha) (by decide)
  have hq : (par d r + 6) % 2 = par d r := by have := par_le_one d r; omega
  refine ⟨A.recast hq, hS, hE, ?_, ?_⟩
  · rw [APc.recast_eps]
    have := he 6 (by omega)
    simp only [tnm, lt_irrefl, if_false, if_true] at this
    rw [this]; decide
  · rw [APc.recast_tau]
    have := ht 6 (by omega)
    simp only [tnm, lt_irrefl, if_false, if_true] at this
    rw [this]; decide

/-- **IVL0 for all pairs except `(2,2)`** -/
theorem ivl0_all {d r X Y x y : ℕ} (hd : 1 ≤ d) (h : Arms2 r X Y) (hx : 1 ≤ x) (hy : 1 ≤ y)
    (h22 : ¬ (x = 2 ∧ y = 2)) : IVL0P d r X Y x y := by
  have key : ∀ X Y x y, Arms2 r X Y → 1 ≤ x → x ≤ y → ¬ (x = 2 ∧ y = 2) → IVL0P d r X Y x y := by
    intro X Y x y h hx hxy h22
    by_cases ha : AeplOK y (x / 2)
    · exact ivl0_a hd h hx (by omega) ha
    by_cases h66 : x = 6 ∧ y = 6
    · obtain ⟨rfl, rfl⟩ := h66; exact ivl0_66 hd h
    unfold AeplOK at ha
    by_cases hb : 4 ≤ x ∧ x ≠ 6
    · exact ivl0_b hd h (by omega) (by omega) ⟨by omega, by omega, by omega⟩
        ⟨by omega, by omega, by omega⟩
    by_cases hs1 : x = 3
    · subst hs1
      have hy5 : y = 5 := by omega
      subst hy5
      exact ivl0_symm (ivl0_s1 hd h.symm (by omega) (by omega) ⟨by omega, by omega, by omega⟩
        ⟨by omega, by omega, by omega⟩)
    · have hy' : (x = 2 ∧ y = 5) ∨ (x = 6 ∧ y = 13) := by omega
      exact ivl0_symm (ivl0_s0 hd h.symm (by omega) (by omega)
        ⟨by omega, by omega, by omega⟩)
  rcases le_total x y with hxy | hxy
  · exact key X Y x y h hx hxy h22
  · exact ivl0_symm (key Y X y x h.symm hy hxy (by omega))
