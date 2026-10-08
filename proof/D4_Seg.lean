/-! ## Segments along arms, and start pieces -/

theorem par_arm (d X j : ℕ) (hX : 2 ≤ X ∧ X ≤ 7) (hj : 1 ≤ j) :
    par d (X + 8 * j) = if 6 ≤ X then (j + d) % 2 else j % 2 := by
  unfold par
  have h1 : X + 8 * j ≠ 0 := by omega
  have h2 : X + 8 * j ≠ 1 := by omega
  have h3 : (X + 8 * j) % 8 = X := by omega
  have h4 : (X + 8 * j) / 8 = j := by omega
  rw [if_neg h1, if_neg h2, h3, h4]

theorem par_zero (d : ℕ) : par d 0 = 0 := by simp [par]
theorem par_one (d : ℕ) : par d 1 = d % 2 := by simp [par]

/-- neighbours of an arm vertex `X + 8j` -/
theorem Tadj_arm_iff (d X j p : ℕ) (hX : 2 ≤ X ∧ X ≤ 7) (hj : 1 ≤ j) :
    Tadj d p (X + 8 * j) ↔ p = (if j = 1 then armRoot X else X + 8 * (j - 1)) ∨
      p = X + 8 * (j + 1) ∨ (X = 5 ∧ j + 1 = d ∧ p = 1) := by
  unfold Tadj
  have hq := Tpar_arm d X j hX hj
  constructor
  · rintro (⟨hp0, hp⟩ | ⟨_, hp⟩)
    · -- p has parent X + 8j
      unfold Tpar at hp
      rw [if_neg hp0] at hp
      by_cases hp1 : p = 1
      · subst hp1
        rw [if_pos rfl] at hp
        unfold dEnd at hp
        split_ifs at hp with hd
        · right; right; refine ⟨by omega, by omega, rfl⟩
        · omega
      · rw [if_neg hp1] at hp
        split_ifs at hp with h2
        · right; left; omega
        · unfold armRoot at hp; split_ifs at hp <;> omega
    · left
      rw [hq] at hp
      split_ifs at hp ⊢ <;> omega
  · rintro (h | h | ⟨h5, hd, rfl⟩)
    · right
      refine ⟨by omega, ?_⟩
      rw [hq, h]
      split_ifs <;> omega
    · left
      refine ⟨by omega, ?_⟩
      rw [h, show X + 8 * (j + 1) = X + 8 * (j + 1) from rfl, Tpar_arm d X (j + 1) hX (by omega)]
      rw [if_pos (by omega)]; congr 1
    · left
      refine ⟨by omega, ?_⟩
      unfold Tpar dEnd
      rw [if_neg (by omega), if_pos rfl, if_pos (by omega)]
      omega

/-- outward segment on arm `X`: positions `k0+1, …, k0+L`, attached at position `k0` (or the root) -/
theorem segOut (d X k0 L : ℕ) (hX : 2 ≤ X ∧ X ≤ 7) (hL : 1 ≤ L) :
    Seg d (if k0 = 0 then armRoot X else X + 8 * k0) L (fun i => X + 8 * (k0 + 1 + i))
      (fun z => z / 8 - (k0 + 1)) := by
  refine ⟨hL, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j _ _ h; omega
  · intro i _; omega
  · intro i _
    show Tadj d (X + 8 * (k0 + 1 + i)) (X + 8 * (k0 + 1 + (i + 1)))
    rw [show X + 8 * (k0 + 1 + (i + 1)) = X + 8 * (k0 + 1 + i + 1) by ring]
    exact (Tadj_arm_iff d X (k0 + 1 + i + 1) _ hX (by omega)).mpr
      (Or.inl (by rw [if_neg (by omega)]; congr 1))
  · intro i j _ _ h
    rcases (Tadj_arm_iff d X (k0 + 1 + j) _ hX (by omega)).mp h with h1 | h1 | ⟨_, _, h1⟩
    · split_ifs at h1
      · unfold armRoot at h1; split_ifs at h1 <;> omega
      · right; omega
    · left; omega
    · omega
  · show Tadj d _ (X + 8 * (k0 + 1 + 0))
    apply (Tadj_arm_iff d X (k0 + 1 + 0) _ hX (by omega)).mpr
    left
    by_cases hk : k0 = 0
    · rw [if_pos hk, if_pos (by omega)]
    · rw [if_neg hk, if_neg (by omega)]; congr 1
  · show par d (X + 8 * (k0 + 1 + 0)) + _ = 1
    rw [par_arm d X _ hX (by omega)]
    by_cases hk : k0 = 0
    · rw [if_pos hk]
      unfold armRoot
      split_ifs with h1 h2 h2
      · omega
      · rw [par_one]; omega
      · rw [par_zero]; omega
      · omega
    · rw [if_neg hk, par_arm d X _ hX (by omega)]
      split_ifs <;> omega
  · intro i _
    show par d (X + 8 * (k0 + 1 + i)) = (par d (X + 8 * (k0 + 1 + 0)) + i) % 2
    rw [par_arm d X _ hX (by omega), par_arm d X _ hX (by omega)]
    split_ifs <;> omega

/-- inward segment on the `d`-path: positions `k0, k0-1, …, k0-L+1`, attached at position `k0+1`
(or at `v` when `k0 + 1 = d`) -/
theorem segIn (d k0 L : ℕ) (hL : 1 ≤ L) (hk : L ≤ k0) (hkd : k0 + 1 ≤ d) :
    Seg d (if k0 + 1 = d then 1 else 5 + 8 * (k0 + 1)) L (fun i => 5 + 8 * (k0 - i))
      (fun z => k0 - z / 8) := by
  have h5 : 2 ≤ 5 ∧ 5 ≤ 7 := by omega
  refine ⟨hL, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j _ _ h; omega
  · intro i _; omega
  · intro i _
    show Tadj d (5 + 8 * (k0 - i)) (5 + 8 * (k0 - (i + 1)))
    have := (Tadj_arm_iff d 5 (k0 - (i + 1)) (5 + 8 * (k0 - i)) h5 (by omega)).mpr
      (Or.inr (Or.inl (by congr 1; omega)))
    exact this
  · intro i j _ _ h
    rcases (Tadj_arm_iff d 5 (k0 - j) _ h5 (by omega)).mp h with h1 | h1 | ⟨_, _, h1⟩
    · split_ifs at h1
      · unfold armRoot at h1; split_ifs at h1 <;> omega
      · left; omega
    · right; omega
    · omega
  · show Tadj d _ (5 + 8 * (k0 - 0))
    apply (Tadj_arm_iff d 5 (k0 - 0) _ h5 (by omega)).mpr
    by_cases hv : k0 + 1 = d
    · rw [if_pos hv]; right; right; exact ⟨rfl, by omega, rfl⟩
    · rw [if_neg hv]; right; left; congr 1
  · show par d (5 + 8 * (k0 - 0)) + _ = 1
    rw [par_arm d 5 _ h5 (by omega)]
    by_cases hv : k0 + 1 = d
    · rw [if_pos hv, par_one]; simp only [show ¬ 6 ≤ 5 by omega, if_false]; omega
    · rw [if_neg hv, par_arm d 5 _ h5 (by omega)]
      simp only [show ¬ 6 ≤ 5 by omega, if_false]; omega
  · intro i _
    show par d (5 + 8 * (k0 - i)) = (par d (5 + 8 * (k0 - 0)) + i) % 2
    rw [par_arm d 5 _ h5 (by omega), par_arm d 5 _ h5 (by omega)]
    simp only [show ¬ 6 ≤ 5 by omega, if_false]
    omega

/-- `ε` of index `i` in an α-path labeling with threshold `(n-1)/2` -/
def peps (n : ℕ) (Lab : ℕ → ℕ) (i : ℕ) : ℕ :=
  if Lab i ≤ (n - 1) / 2 then Lab i else (n - 1) - Lab i

/-- a start piece: an induced path of `Tadj d` with an α-labeling whose first vertex is low -/
theorem startPath (d n : ℕ) (nm pos Lab : ℕ → ℕ) (hn : 1 ≤ n)
    (hinj : ∀ i j, i < n → j < n → nm i = nm j → i = j) (hpos : ∀ i, i < n → pos (nm i) = i)
    (hcons : ∀ i, i + 1 < n → Tadj d (nm i) (nm (i + 1)))
    (hchord : ∀ i j, i < n → j < n → Tadj d (nm i) (nm j) → i = j + 1 ∨ j = i + 1)
    (hpar : ∀ i, i < n → par d (nm i) = (par d (nm 0) + i) % 2)
    (hLab : PathAlpha n Lab ((n - 1) / 2)) (h0 : Lab 0 ≤ (n - 1) / 2) :
    ∃ A : APc d (par d (nm 0)), (∀ z, z ∈ A.P.S ↔ ∃ i, i < n ∧ nm i = z) ∧ A.P.E.card = n - 1 ∧
      (∀ i, i < n → A.eps (nm i) = peps n Lab i) ∧ (∀ i, i < n → A.tau (nm i) = ptau n Lab i) := by
  have hA := ipathPc_alpha (R := Tadj d) (pos := pos) hn (Tadj_symm d) hinj hpos hcons hchord hLab
    (by omega)
  set P := ipathPc (Tadj d) n nm pos Lab with hP
  have hS : P.S.card = n := ipathPc_card_S hinj
  have hE : P.E.card = n - 1 := by have := hA.1.2.1; omega
  have hf : ∀ i, i < n → P.f (nm i) = Lab i := by
    intro i hi; show Lab (pos (nm i)) = Lab i; rw [hpos i hi]
  have hlow := path_low_iff hLab
  have hle := hLab.2.1
  refine ⟨⟨P, (n - 1) / 2 + 1, rfl, hA, ?_, par_le_one d _⟩, fun z => ipathPc_mem, hE, ?_, ?_⟩
  · intro z hz
    obtain ⟨i, hi, rfl⟩ := ipathPc_mem.mp hz
    rw [hf i hi, hpar i hi]
    have a := hlow i hi
    have := par_le_one d (nm 0)
    constructor
    · intro h; have := (a.mp (by omega)).mp h0; omega
    · intro h; have := a.mpr (by constructor <;> intro _ <;> omega); omega
  · intro i hi
    show P.eps ((n - 1) / 2 + 1) (nm i) = _
    unfold Pc.eps peps
    rw [hf i hi, hE]
    have := hle i hi
    split_ifs <;> omega
  · intro i hi
    show P.tau ((n - 1) / 2 + 1) (nm i) = _
    unfold Pc.tau ptau
    rw [hf i hi]
    have := hle i hi
    split_ifs <;> omega
