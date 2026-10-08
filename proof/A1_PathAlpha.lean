/-- `L` is an α-labeling (threshold `lam`) of the path `0 - 1 - ⋯ - (n-1)`. -/
def PathAlpha (n : ℕ) (L : ℕ → ℕ) (lam : ℕ) : Prop :=
  (∀ i j, i < n → j < n → L i = L j → i = j) ∧
  (∀ i, i < n → L i ≤ n - 1) ∧
  (∀ i j, i + 1 < n → j + 1 < n →
      Nat.dist (L i) (L (i + 1)) = Nat.dist (L j) (L (j + 1)) → i = j) ∧
  (∀ i, i + 1 < n → (L i ≤ lam ↔ lam < L (i + 1)))

/-- the standard zigzag `0, n-1, 1, n-2, …` -/
def zz (n : ℕ) (i : ℕ) : ℕ := if i % 2 = 0 then i / 2 else n - 1 - i / 2

theorem zz_alpha (n : ℕ) (hn : 1 ≤ n) : PathAlpha n (zz n) ((n - 1) / 2) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j hi hj h
    unfold zz at h
    split_ifs at h <;> omega
  · intro i hi
    unfold zz
    split_ifs <;> omega
  · intro i j hi hj h
    unfold zz at h
    simp only [Nat.dist] at h
    split_ifs at h <;> omega
  · intro i hi
    unfold zz
    split_ifs <;> omega

/-- reflection of an α-labeling: lows `l ↦ lam - l`, highs `h ↦ n + lam - h`. -/
def refl (n lam : ℕ) (L : ℕ → ℕ) (i : ℕ) : ℕ :=
  if L i ≤ lam then lam - L i else n + lam - L i

theorem refl_edge {n lam : ℕ} {L : ℕ → ℕ} (h : PathAlpha n L lam) (i : ℕ) (hi : i + 1 < n) :
    Nat.dist (refl n lam L i) (refl n lam L (i + 1)) + Nat.dist (L i) (L (i + 1)) = n := by
  obtain ⟨_, hle, _, halt⟩ := h
  have a1 := halt i hi
  have b1 := hle i (by omega)
  have b2 := hle (i + 1) hi
  unfold refl
  simp only [Nat.dist]
  by_cases hl : L i ≤ lam
  · have hh : lam < L (i + 1) := a1.mp hl
    rw [if_pos hl, if_neg (by omega)]
    omega
  · have hh : ¬ lam < L (i + 1) := fun h' => hl (a1.mpr h')
    rw [if_neg hl, if_pos (by omega)]
    omega

theorem refl_alpha {n lam : ℕ} {L : ℕ → ℕ} (h : PathAlpha n L lam) (hlam : lam < n) :
    PathAlpha n (refl n lam L) lam := by
  have hedgeR := refl_edge h
  obtain ⟨hinj, hle, hedge, halt⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j hi hj hij
    apply hinj i j hi hj
    have := hle i hi
    have := hle j hj
    unfold refl at hij
    split_ifs at hij <;> omega
  · intro i hi
    have := hle i hi
    unfold refl
    split_ifs <;> omega
  · intro i j hi hj hij
    apply hedge i j hi hj
    have e1 := hedgeR i hi
    have e2 := hedgeR j hj
    omega
  · intro i hi
    have a1 := halt i hi
    have b1 := hle i (by omega)
    have b2 := hle (i + 1) hi
    unfold refl
    split_ifs <;> omega

/-- complement `x ↦ n - 1 - x`, threshold `n - 2 - lam`. -/
def comp (n : ℕ) (L : ℕ → ℕ) (i : ℕ) : ℕ := n - 1 - L i

theorem comp_alpha {n lam : ℕ} {L : ℕ → ℕ} (h : PathAlpha n L lam) (hlam : lam + 2 ≤ n) :
    PathAlpha n (comp n L) (n - 2 - lam) := by
  obtain ⟨hinj, hle, hedge, halt⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j hi hj hij
    apply hinj i j hi hj
    have := hle i hi
    have := hle j hj
    unfold comp at hij
    omega
  · intro i _
    unfold comp
    omega
  · intro i j hi hj hij
    apply hedge i j hi hj
    have b1 := hle i (by omega)
    have b2 := hle (i + 1) hi
    have b3 := hle j (by omega)
    have b4 := hle (j + 1) hj
    have c1 : Nat.dist (comp n L i) (comp n L (i + 1)) = Nat.dist (L i) (L (i + 1)) := by
      unfold comp; simp only [Nat.dist]; omega
    have c2 : Nat.dist (comp n L j) (comp n L (j + 1)) = Nat.dist (L j) (L (j + 1)) := by
      unfold comp; simp only [Nat.dist]; omega
    omega
  · intro i hi
    have a1 := halt i hi
    have b1 := hle i (by omega)
    have b2 := hle (i + 1) hi
    unfold comp
    omega
