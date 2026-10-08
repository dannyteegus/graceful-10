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

/-- head of pattern E -/
def hdE (n t i : ℕ) : ℕ := if i % 2 = 0 then t - i / 2 else n - 1 - t + i / 2

/-- pattern E: head `t, n-1-t, t-1, n-t, …, 0, n-1`, then the box path shifted by `t+1`. -/
def patE (n t : ℕ) (L : ℕ → ℕ) (i : ℕ) : ℕ :=
  if i ≤ 2 * t + 1 then hdE n t i else t + 1 + L (i - (2 * t + 2))

theorem patE_head {n t : ℕ} {L : ℕ → ℕ} {i : ℕ} (h : i ≤ 2 * t + 1) :
    patE n t L i = hdE n t i := by
  unfold patE; exact if_pos h

theorem patE_box {n t : ℕ} {L : ℕ → ℕ} {i : ℕ} (h : 2 * t + 2 ≤ i) :
    patE n t L i = t + 1 + L (i - (2 * t + 2)) := by
  unfold patE; exact if_neg (by omega)

theorem hdE_range {n t i : ℕ} (h : i ≤ 2 * t + 1) :
    (i % 2 = 0 ∧ hdE n t i = t - i / 2 ∧ i / 2 ≤ t) ∨
    (i % 2 = 1 ∧ hdE n t i = n - 1 - t + i / 2 ∧ i / 2 ≤ t) := by
  unfold hdE
  split_ifs with hp
  · left; exact ⟨hp, rfl, by omega⟩
  · right; exact ⟨by omega, rfl, by omega⟩

theorem patE_alpha {k t mu : ℕ} {L : ℕ → ℕ} (h : PathAlpha k L mu) (hk : 1 ≤ k)
    (h0 : L 0 = t) (ht : t ≤ mu) (hmu : mu < k) :
    PathAlpha (k + 2 * t + 2) (patE (k + 2 * t + 2) t L) (t + 1 + mu) := by
  obtain ⟨hinj, hle, hedge, halt⟩ := h
  set n := k + 2 * t + 2 with hn
  have eHead : ∀ i, i + 1 ≤ 2 * t + 1 →
      Nat.dist (patE n t L i) (patE n t L (i + 1)) = n - 1 - 2 * t + i := by
    intro i hi
    rw [patE_head (by omega), patE_head hi]
    simp only [Nat.dist]
    rcases hdE_range (n := n) (t := t) (i := i) (by omega) with ⟨p1, q1, r1⟩ | ⟨p1, q1, r1⟩ <;>
    rcases hdE_range (n := n) (t := t) (i := i + 1) hi with ⟨p2, q2, r2⟩ | ⟨p2, q2, r2⟩ <;>
    omega
  have eJunc : Nat.dist (patE n t L (2 * t + 1)) (patE n t L (2 * t + 1 + 1)) = n - 2 * t - 2 := by
    rw [patE_head (le_refl _), patE_box (by omega)]
    have : 2 * t + 1 + 1 - (2 * t + 2) = 0 := by omega
    rw [this, h0]
    rcases hdE_range (n := n) (t := t) (i := 2 * t + 1) (le_refl _) with ⟨p1, q1, r1⟩ | ⟨p1, q1, r1⟩ <;>
    simp only [Nat.dist] <;> omega
  have eBox : ∀ i, 2 * t + 2 ≤ i →
      Nat.dist (patE n t L i) (patE n t L (i + 1)) =
        Nat.dist (L (i - (2 * t + 2))) (L (i - (2 * t + 2) + 1)) := by
    intro i hi
    rw [patE_box hi, patE_box (by omega)]
    have : i + 1 - (2 * t + 2) = i - (2 * t + 2) + 1 := by omega
    rw [this]
    simp only [Nat.dist]
    omega
  have boxPos : ∀ j, j + 1 < k → 1 ≤ Nat.dist (L j) (L (j + 1)) := by
    intro j hj
    simp only [Nat.dist]
    by_contra hc
    have : L j = L (j + 1) := by omega
    exact absurd (hinj j (j + 1) (by omega) hj this) (by omega)
  have boxLe : ∀ j, j + 1 < k → Nat.dist (L j) (L (j + 1)) ≤ k - 1 := by
    intro j hj
    have := hle j (by omega)
    have := hle (j + 1) hj
    simp only [Nat.dist]
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j hi hj hij
    by_cases hi' : i ≤ 2 * t + 1 <;> by_cases hj' : j ≤ 2 * t + 1
    · rw [patE_head hi', patE_head hj'] at hij
      rcases hdE_range (n := n) (t := t) (i := i) hi' with ⟨p1, q1, r1⟩ | ⟨p1, q1, r1⟩ <;>
      rcases hdE_range (n := n) (t := t) (i := j) hj' with ⟨p2, q2, r2⟩ | ⟨p2, q2, r2⟩ <;>
      omega
    · rw [patE_head hi', patE_box (by omega)] at hij
      have := hle (j - (2 * t + 2)) (by omega)
      rcases hdE_range (n := n) (t := t) (i := i) hi' with ⟨p1, q1, r1⟩ | ⟨p1, q1, r1⟩ <;>
      omega
    · rw [patE_box (by omega), patE_head hj'] at hij
      have := hle (i - (2 * t + 2)) (by omega)
      rcases hdE_range (n := n) (t := t) (i := j) hj' with ⟨p1, q1, r1⟩ | ⟨p1, q1, r1⟩ <;>
      omega
    · rw [patE_box (by omega), patE_box (by omega)] at hij
      have := hinj (i - (2 * t + 2)) (j - (2 * t + 2)) (by omega) (by omega) (by omega)
      omega
  · intro i hi
    by_cases hi' : i ≤ 2 * t + 1
    · rw [patE_head hi']
      rcases hdE_range (n := n) (t := t) (i := i) hi' with ⟨p1, q1, r1⟩ | ⟨p1, q1, r1⟩ <;>
      omega
    · rw [patE_box (by omega)]
      have := hle (i - (2 * t + 2)) (by omega)
      omega
  · intro i j hi hj hij
    have cls : ∀ x, x + 1 < n →
        (x + 1 ≤ 2 * t + 1 ∧ Nat.dist (patE n t L x) (patE n t L (x + 1)) = n - 1 - 2 * t + x) ∨
        (x = 2 * t + 1 ∧ Nat.dist (patE n t L x) (patE n t L (x + 1)) = n - 2 * t - 2) ∨
        (2 * t + 2 ≤ x ∧ 1 ≤ Nat.dist (patE n t L x) (patE n t L (x + 1)) ∧
          Nat.dist (patE n t L x) (patE n t L (x + 1)) ≤ k - 1) := by
      intro x hx
      by_cases c1 : x + 1 ≤ 2 * t + 1
      · exact Or.inl ⟨c1, eHead x c1⟩
      · by_cases c2 : x = 2 * t + 1
        · subst c2; exact Or.inr (Or.inl ⟨rfl, eJunc⟩)
        · refine Or.inr (Or.inr ⟨by omega, ?_, ?_⟩)
          · rw [eBox x (by omega)]; exact boxPos _ (by omega)
          · rw [eBox x (by omega)]; exact boxLe _ (by omega)
    rcases cls i hi with ⟨a1, a2⟩ | ⟨a1, a2⟩ | ⟨a1, a2, a3⟩ <;>
    rcases cls j hj with ⟨b1, b2⟩ | ⟨b1, b2⟩ | ⟨b1, b2, b3⟩
    all_goals first
      | omega
      | (rw [eBox i (by omega), eBox j (by omega)] at hij
         have := hedge (i - (2 * t + 2)) (j - (2 * t + 2)) (by omega) (by omega) hij
         omega)
  · intro i hi
    by_cases c1 : i + 1 ≤ 2 * t + 1
    · rw [patE_head (by omega), patE_head c1]
      rcases hdE_range (n := n) (t := t) (i := i) (by omega) with ⟨p1, q1, r1⟩ | ⟨p1, q1, r1⟩ <;>
      rcases hdE_range (n := n) (t := t) (i := i + 1) c1 with ⟨p2, q2, r2⟩ | ⟨p2, q2, r2⟩ <;>
      omega
    · by_cases c2 : i = 2 * t + 1
      · subst c2
        rw [patE_head (le_refl _), patE_box (by omega)]
        have : 2 * t + 1 + 1 - (2 * t + 2) = 0 := by omega
        rw [this, h0]
        rcases hdE_range (n := n) (t := t) (i := 2 * t + 1) (le_refl _) with ⟨p1, q1, r1⟩ | ⟨p1, q1, r1⟩ <;>
        omega
      · rw [patE_box (by omega), patE_box (by omega)]
        have a := halt (i - (2 * t + 2)) (by omega)
        have : i + 1 - (2 * t + 2) = i - (2 * t + 2) + 1 := by omega
        rw [this]
        omega

/-- head of pattern E2: `t, n-t, t-1, n-t+1, …, 1, n-1, 0` (positions `0..2t`). -/
def hdE2 (n t i : ℕ) : ℕ := if i % 2 = 0 then t - i / 2 else n - t + i / 2

/-- pattern E2: head, then the complemented box path shifted by `t+1`. -/
def patE2 (n k t : ℕ) (L : ℕ → ℕ) (i : ℕ) : ℕ :=
  if i ≤ 2 * t then hdE2 n t i else t + 1 + (k - 1 - L (i - (2 * t + 1)))

theorem patE2_head {n k t : ℕ} {L : ℕ → ℕ} {i : ℕ} (h : i ≤ 2 * t) :
    patE2 n k t L i = hdE2 n t i := by
  unfold patE2; exact if_pos h

theorem patE2_box {n k t : ℕ} {L : ℕ → ℕ} {i : ℕ} (h : 2 * t + 1 ≤ i) :
    patE2 n k t L i = t + 1 + (k - 1 - L (i - (2 * t + 1))) := by
  unfold patE2; exact if_neg (by omega)

theorem hdE2_range {n t i : ℕ} (h : i ≤ 2 * t) :
    (i % 2 = 0 ∧ hdE2 n t i = t - i / 2 ∧ i / 2 ≤ t) ∨
    (i % 2 = 1 ∧ hdE2 n t i = n - t + i / 2 ∧ i / 2 + 1 ≤ t) := by
  unfold hdE2
  split_ifs with hp
  · left; exact ⟨hp, rfl, by omega⟩
  · right; exact ⟨by omega, rfl, by omega⟩

theorem patE2_alpha {k t mu : ℕ} {L : ℕ → ℕ} (h : PathAlpha k L mu) (hk : 2 ≤ k)
    (h0 : L 0 = t) (ht : t ≤ mu) (hmu : mu + 2 ≤ k) :
    PathAlpha (k + 2 * t + 1) (patE2 (k + 2 * t + 1) k t L) (t + k - 1 - mu) := by
  obtain ⟨hinj, hle, hedge, halt⟩ := h
  set n := k + 2 * t + 1 with hn
  have eHead : ∀ i, i + 1 ≤ 2 * t →
      Nat.dist (patE2 n k t L i) (patE2 n k t L (i + 1)) = n - 2 * t + i := by
    intro i hi
    rw [patE2_head (by omega), patE2_head hi]
    simp only [Nat.dist]
    rcases hdE2_range (n := n) (t := t) (i := i) (by omega) with ⟨p1, q1, r1⟩ | ⟨p1, q1, r1⟩ <;>
    rcases hdE2_range (n := n) (t := t) (i := i + 1) hi with ⟨p2, q2, r2⟩ | ⟨p2, q2, r2⟩ <;>
    omega
  have eJunc : Nat.dist (patE2 n k t L (2 * t)) (patE2 n k t L (2 * t + 1)) = k := by
    rw [patE2_head (le_refl _), patE2_box (le_refl _)]
    have : 2 * t + 1 - (2 * t + 1) = 0 := by omega
    rw [this, h0]
    rcases hdE2_range (n := n) (t := t) (i := 2 * t) (le_refl _) with ⟨p1, q1, r1⟩ | ⟨p1, q1, r1⟩ <;>
    simp only [Nat.dist] <;> omega
  have eBox : ∀ i, 2 * t + 1 ≤ i → i + 1 < n →
      Nat.dist (patE2 n k t L i) (patE2 n k t L (i + 1)) =
        Nat.dist (L (i - (2 * t + 1))) (L (i - (2 * t + 1) + 1)) := by
    intro i hi hi2
    rw [patE2_box hi, patE2_box (by omega)]
    have : i + 1 - (2 * t + 1) = i - (2 * t + 1) + 1 := by omega
    rw [this]
    have := hle (i - (2 * t + 1)) (by omega)
    have := hle (i - (2 * t + 1) + 1) (by omega)
    simp only [Nat.dist]
    omega
  have boxPos : ∀ j, j + 1 < k → 1 ≤ Nat.dist (L j) (L (j + 1)) := by
    intro j hj
    simp only [Nat.dist]
    by_contra hc
    have : L j = L (j + 1) := by omega
    exact absurd (hinj j (j + 1) (by omega) hj this) (by omega)
  have boxLe : ∀ j, j + 1 < k → Nat.dist (L j) (L (j + 1)) ≤ k - 1 := by
    intro j hj
    have := hle j (by omega)
    have := hle (j + 1) hj
    simp only [Nat.dist]
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j hi hj hij
    by_cases hi' : i ≤ 2 * t <;> by_cases hj' : j ≤ 2 * t
    · rw [patE2_head hi', patE2_head hj'] at hij
      rcases hdE2_range (n := n) (t := t) (i := i) hi' with ⟨p1, q1, r1⟩ | ⟨p1, q1, r1⟩ <;>
      rcases hdE2_range (n := n) (t := t) (i := j) hj' with ⟨p2, q2, r2⟩ | ⟨p2, q2, r2⟩ <;>
      omega
    · rw [patE2_head hi', patE2_box (by omega)] at hij
      have := hle (j - (2 * t + 1)) (by omega)
      rcases hdE2_range (n := n) (t := t) (i := i) hi' with ⟨p1, q1, r1⟩ | ⟨p1, q1, r1⟩ <;>
      omega
    · rw [patE2_box (by omega), patE2_head hj'] at hij
      have := hle (i - (2 * t + 1)) (by omega)
      rcases hdE2_range (n := n) (t := t) (i := j) hj' with ⟨p1, q1, r1⟩ | ⟨p1, q1, r1⟩ <;>
      omega
    · rw [patE2_box (by omega), patE2_box (by omega)] at hij
      have := hle (i - (2 * t + 1)) (by omega)
      have := hle (j - (2 * t + 1)) (by omega)
      have := hinj (i - (2 * t + 1)) (j - (2 * t + 1)) (by omega) (by omega) (by omega)
      omega
  · intro i hi
    by_cases hi' : i ≤ 2 * t
    · rw [patE2_head hi']
      rcases hdE2_range (n := n) (t := t) (i := i) hi' with ⟨p1, q1, r1⟩ | ⟨p1, q1, r1⟩ <;>
      omega
    · rw [patE2_box (by omega)]
      have := hle (i - (2 * t + 1)) (by omega)
      omega
  · intro i j hi hj hij
    have cls : ∀ x, x + 1 < n →
        (x + 1 ≤ 2 * t ∧ Nat.dist (patE2 n k t L x) (patE2 n k t L (x + 1)) = n - 2 * t + x) ∨
        (x = 2 * t ∧ Nat.dist (patE2 n k t L x) (patE2 n k t L (x + 1)) = k) ∨
        (2 * t + 1 ≤ x ∧ 1 ≤ Nat.dist (patE2 n k t L x) (patE2 n k t L (x + 1)) ∧
          Nat.dist (patE2 n k t L x) (patE2 n k t L (x + 1)) ≤ k - 1) := by
      intro x hx
      by_cases c1 : x + 1 ≤ 2 * t
      · exact Or.inl ⟨c1, eHead x c1⟩
      · by_cases c2 : x = 2 * t
        · subst c2; exact Or.inr (Or.inl ⟨rfl, eJunc⟩)
        · refine Or.inr (Or.inr ⟨by omega, ?_, ?_⟩)
          · rw [eBox x (by omega) hx]; exact boxPos _ (by omega)
          · rw [eBox x (by omega) hx]; exact boxLe _ (by omega)
    rcases cls i hi with ⟨a1, a2⟩ | ⟨a1, a2⟩ | ⟨a1, a2, a3⟩ <;>
    rcases cls j hj with ⟨b1, b2⟩ | ⟨b1, b2⟩ | ⟨b1, b2, b3⟩
    all_goals first
      | omega
      | (rw [eBox i (by omega) hi, eBox j (by omega) hj] at hij
         have := hedge (i - (2 * t + 1)) (j - (2 * t + 1)) (by omega) (by omega) hij
         omega)
  · intro i hi
    by_cases c1 : i + 1 ≤ 2 * t
    · rw [patE2_head (by omega), patE2_head c1]
      rcases hdE2_range (n := n) (t := t) (i := i) (by omega) with ⟨p1, q1, r1⟩ | ⟨p1, q1, r1⟩ <;>
      rcases hdE2_range (n := n) (t := t) (i := i + 1) c1 with ⟨p2, q2, r2⟩ | ⟨p2, q2, r2⟩ <;>
      omega
    · by_cases c2 : i = 2 * t
      · subst c2
        rw [patE2_head (le_refl _), patE2_box (le_refl _)]
        have : 2 * t + 1 - (2 * t + 1) = 0 := by omega
        rw [this, h0]
        rcases hdE2_range (n := n) (t := t) (i := 2 * t) (le_refl _) with ⟨p1, q1, r1⟩ | ⟨p1, q1, r1⟩ <;>
        omega
      · rw [patE2_box (by omega), patE2_box (by omega)]
        have a := halt (i - (2 * t + 1)) (by omega)
        have b1 := hle (i - (2 * t + 1)) (by omega)
        have b2 := hle (i - (2 * t + 1) + 1) (by omega)
        have : i + 1 - (2 * t + 1) = i - (2 * t + 1) + 1 := by omega
        rw [this]
        omega

/-- pattern C for `n = 4t+2`: `t, 3t, t+1, 3t-1, …, 2t, 4t+1, 0, 4t, 1, …, 3t+1`. -/
def patC (t i : ℕ) : ℕ :=
  if i ≤ 2 * t then (if i % 2 = 0 then t + i / 2 else 3 * t - i / 2)
  else (if (i - (2 * t + 1)) % 2 = 0 then 4 * t + 1 - (i - (2 * t + 1)) / 2
        else (i - (2 * t + 1)) / 2)

theorem patC_val (t i : ℕ) :
    (i ≤ 2 * t ∧ i % 2 = 0 ∧ patC t i = t + i / 2) ∨
    (i ≤ 2 * t ∧ i % 2 = 1 ∧ patC t i = 3 * t - i / 2) ∨
    (2 * t + 1 ≤ i ∧ (i - (2 * t + 1)) % 2 = 0 ∧ patC t i = 4 * t + 1 - (i - (2 * t + 1)) / 2) ∨
    (2 * t + 1 ≤ i ∧ (i - (2 * t + 1)) % 2 = 1 ∧ patC t i = (i - (2 * t + 1)) / 2) := by
  unfold patC
  split_ifs with h1 h2 h3
  · exact Or.inl ⟨h1, h2, rfl⟩
  · exact Or.inr (Or.inl ⟨h1, by omega, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨by omega, h3, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega, rfl⟩))

/-- the edge labels of pattern C: `2t, 2t-1, …, 1`, then `2t+1`, then `4t+1, 4t, …, 2t+2` -/
theorem patC_edge (t i : ℕ) (hi : i + 1 < 4 * t + 2) :
    Nat.dist (patC t i) (patC t (i + 1)) =
      if i < 2 * t then 2 * t - i else if i = 2 * t then 2 * t + 1 else 6 * t + 2 - i := by
  unfold Nat.dist
  rcases patC_val t i with ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩ <;>
  rcases patC_val t (i + 1) with ⟨b1, b2, b3⟩ | ⟨b1, b2, b3⟩ | ⟨b1, b2, b3⟩ | ⟨b1, b2, b3⟩ <;>
  rw [a3, b3] <;> split_ifs <;> omega

theorem patC_alpha (t : ℕ) (ht : 1 ≤ t) : PathAlpha (4 * t + 2) (patC t) (2 * t) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j hi hj hij
    rcases patC_val t i with ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩ <;>
    rcases patC_val t j with ⟨b1, b2, b3⟩ | ⟨b1, b2, b3⟩ | ⟨b1, b2, b3⟩ | ⟨b1, b2, b3⟩ <;>
    omega
  · intro i hi
    rcases patC_val t i with ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩ <;> omega
  · intro i j hi hj hij
    rw [patC_edge t i hi, patC_edge t j hj] at hij
    split_ifs at hij <;> omega
  · intro i hi
    rcases patC_val t i with ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩ <;>
    rcases patC_val t (i + 1) with ⟨b1, b2, b3⟩ | ⟨b1, b2, b3⟩ | ⟨b1, b2, b3⟩ | ⟨b1, b2, b3⟩ <;>
    omega

/-- Feasibility of α-EPL: `t ≤ (n-1)/2` and not the exceptional middle label. -/
def AeplOK (n t : ℕ) : Prop := 1 ≤ n ∧ t ≤ (n - 1) / 2 ∧ ¬ (n % 4 = 1 ∧ 1 < n ∧ 4 * t = n - 1)

/-- **α-EPL.** The path on `n` vertices has an α-labeling (threshold `(n-1)/2`) whose first
vertex has label `t`, unless `n ≡ 1 (mod 4)`, `n > 1`, `4t = n-1`. -/
theorem aepl : ∀ n t, AeplOK n t → ∃ L : ℕ → ℕ, PathAlpha n L ((n - 1) / 2) ∧ L 0 = t := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro t ⟨hn, ht, hex⟩
  -- labelings with small first label
  have small : ∀ s, AeplOK n s → 2 * s ≤ (n - 1) / 2 →
      ∃ L : ℕ → ℕ, PathAlpha n L ((n - 1) / 2) ∧ L 0 = s := by
    intro s ⟨_, hs, hexs⟩ h2
    by_cases s0 : s = 0
    · subst s0
      exact ⟨zz n, zz_alpha n hn, by simp [zz]⟩
    by_cases heq : 2 * s = (n - 1) / 2
    · -- n = 4s + 2
      have hn' : n = 4 * s + 2 := by omega
      subst hn'
      refine ⟨patC s, ?_, ?_⟩
      · have : (4 * s + 2 - 1) / 2 = 2 * s := by omega
        rw [this]; exact patC_alpha s (by omega)
      · simp [patC]
    · -- 2s < (n-1)/2, so n ≥ 4s+3
      have hbig : 4 * s + 3 ≤ n := by omega
      by_cases hk : (n - 2 * s - 2) % 4 = 1 ∧ 1 < n - 2 * s - 2 ∧ 4 * s = n - 2 * s - 2 - 1
      · -- box exceptional: k = 4s+1; use pattern E2 with box 4s+2 (pattern C)
        have hn' : n = 6 * s + 3 := by omega
        have hC := patC_alpha s (by omega)
        have hE2 := patE2_alpha (k := 4 * s + 2) (t := s) (mu := 2 * s) (L := patC s) hC
          (by omega) (by simp [patC]) (by omega) (by omega)
        refine ⟨patE2 (4 * s + 2 + 2 * s + 1) (4 * s + 2) s (patC s), ?_, ?_⟩
        · have e1 : n = 4 * s + 2 + 2 * s + 1 := by omega
          have e2 : (n - 1) / 2 = s + (4 * s + 2) - 1 - 2 * s := by omega
          rw [e2, e1]; exact hE2
        · simp [patE2, hdE2]
      · -- pattern E with box k = n - 2s - 2
        set k := n - 2 * s - 2 with hkdef
        have hkpos : 2 * s + 1 ≤ k := by omega
        obtain ⟨L, hL, hL0⟩ := ih k (by omega) s ⟨by omega, by omega, hk⟩
        have hE := patE_alpha (k := k) (t := s) (mu := (k - 1) / 2) hL (by omega) hL0
          (by omega) (by omega)
        refine ⟨patE (k + 2 * s + 2) s L, ?_, ?_⟩
        · have e1 : n = k + 2 * s + 2 := by omega
          have e2 : (n - 1) / 2 = s + 1 + (k - 1) / 2 := by omega
          rw [e2, e1]; exact hE
        · simp [patE, hdE]
  by_cases h2 : 2 * t ≤ (n - 1) / 2
  · exact small t ⟨hn, ht, hex⟩ h2
  · -- reflect a labeling with first label (n-1)/2 - t
    set lam := (n - 1) / 2 with hlam
    obtain ⟨L, hL, hL0⟩ := small (lam - t) ⟨hn, by omega, by omega⟩ (by omega)
    refine ⟨refl n lam L, refl_alpha hL (by omega), ?_⟩
    unfold refl
    rw [hL0, if_pos (by omega)]
    omega

/-! ## Labeled pieces over ℕ-named vertices -/

/-- A labeled piece: finite vertex set `S`, symmetric adjacency `R` (only meaningful on `S`),
labeling `f`. -/
structure Pc where
  S : Finset ℕ
  R : ℕ → ℕ → Prop
  f : ℕ → ℕ

/-- oriented edge set (pairs `x < y`) of a piece -/
noncomputable def Pc.E (P : Pc) : Finset (ℕ × ℕ) := by
  classical
  exact (P.S ×ˢ P.S).filter (fun e => e.1 < e.2 ∧ P.R e.1 e.2)

theorem Pc.mem_E {P : Pc} {e : ℕ × ℕ} :
    e ∈ P.E ↔ e.1 ∈ P.S ∧ e.2 ∈ P.S ∧ e.1 < e.2 ∧ P.R e.1 e.2 := by
  classical
  unfold Pc.E
  simp [Finset.mem_filter, Finset.mem_product, and_assoc]

/-- graceful piece: tree-sized, labels injective in `[0,m]`, edge labels injective. -/
def Pc.Grace (P : Pc) : Prop :=
  (∀ x y, P.R x y → P.R y x) ∧
  P.S.card = P.E.card + 1 ∧
  (∀ x ∈ P.S, ∀ y ∈ P.S, P.f x = P.f y → x = y) ∧
  (∀ x ∈ P.S, P.f x ≤ P.E.card) ∧
  (∀ e ∈ P.E, ∀ e' ∈ P.E,
      Nat.dist (P.f e.1) (P.f e.2) = Nat.dist (P.f e'.1) (P.f e'.2) → e = e')

/-- α-piece with `th` low labels (`x` is low iff `f x < th`). -/
def Pc.Alpha (P : Pc) (th : ℕ) : Prop :=
  P.Grace ∧ th ≤ P.E.card + 1 ∧
  ∀ x ∈ P.S, ∀ y ∈ P.S, P.R x y → (P.f x < th ↔ th ≤ P.f y)

/-! ## Flexible gluing (FGL) -/

/-- join `A` (α, threshold `th`) and `B` by the edge `x - w`. -/
noncomputable def Pc.join (A B : Pc) (th x w : ℕ) : Pc where
  S := A.S ∪ B.S
  R := fun p q => (p ∈ A.S ∧ q ∈ A.S ∧ A.R p q) ∨ (p ∈ B.S ∧ q ∈ B.S ∧ B.R p q) ∨
    (p = x ∧ q = w) ∨ (p = w ∧ q = x)
  f := fun z => if z ∈ A.S then (if A.f z < th then A.f z else A.f z + B.E.card + 1)
    else th + B.f z

/-- ordered version of an unordered pair -/
def opair (x w : ℕ) : ℕ × ℕ := (min x w, max x w)

theorem Pc.join_E {A B : Pc} {th x w : ℕ} (hd : Disjoint A.S B.S) (hx : x ∈ A.S) (hw : w ∈ B.S) :
    (Pc.join A B th x w).E = A.E ∪ B.E ∪ {opair x w} := by
  classical
  have hxw : x ≠ w := fun h => Finset.disjoint_left.mp hd hx (h ▸ hw)
  ext ⟨p, q⟩
  simp only [Pc.mem_E, Finset.mem_union, Finset.mem_singleton, Pc.join, opair, Prod.mk.injEq]
  constructor
  · rintro ⟨hp, hq, hpq, hr⟩
    rcases hr with ⟨a1, a2, a3⟩ | ⟨b1, b2, b3⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl (Or.inl ⟨a1, a2, hpq, a3⟩)
    · exact Or.inl (Or.inr ⟨b1, b2, hpq, b3⟩)
    · right; constructor <;> omega
    · right; constructor <;> omega
  · rintro ((⟨a1, a2, a3, a4⟩ | ⟨b1, b2, b3, b4⟩) | ⟨h1, h2⟩)
    · exact ⟨Or.inl a1, Or.inl a2, a3, Or.inl ⟨a1, a2, a4⟩⟩
    · exact ⟨Or.inr b1, Or.inr b2, b3, Or.inr (Or.inl ⟨b1, b2, b4⟩)⟩
    · have hne : x < w ∨ w < x := by omega
      rcases hne with h | h
      · have e1 : p = x := by omega
        have e2 : q = w := by omega
        subst e1; subst e2
        exact ⟨Or.inl hx, Or.inr hw, h, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
      · have e1 : p = w := by omega
        have e2 : q = x := by omega
        subst e1; subst e2
        exact ⟨Or.inr hw, Or.inl hx, h, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩

theorem Pc.join_card_E {A B : Pc} {th x w : ℕ} (hd : Disjoint A.S B.S) (hx : x ∈ A.S)
    (hw : w ∈ B.S) : (Pc.join A B th x w).E.card = A.E.card + B.E.card + 1 := by
  classical
  rw [Pc.join_E hd hx hw]
  have d1 : Disjoint A.E B.E := by
    rw [Finset.disjoint_left]
    intro e he he'
    exact Finset.disjoint_left.mp hd (Pc.mem_E.mp he).1 (Pc.mem_E.mp he').1
  have d2 : Disjoint (A.E ∪ B.E) {opair x w} := by
    rw [Finset.disjoint_singleton_right, Finset.mem_union]
    rintro (h | h)
    · have := Pc.mem_E.mp h
      simp only [opair] at this
      rcases le_total x w with hl | hl
      · rw [max_eq_right hl] at this
        exact Finset.disjoint_left.mp hd this.2.1 hw
      · rw [min_eq_right hl] at this
        exact Finset.disjoint_left.mp hd this.1 hw
    · have := Pc.mem_E.mp h
      simp only [opair] at this
      rcases le_total x w with hl | hl
      · rw [min_eq_left hl] at this
        exact Finset.disjoint_left.mp hd hx this.1
      · rw [max_eq_left hl] at this
        exact Finset.disjoint_left.mp hd hx this.2.1
  rw [Finset.card_union_of_disjoint d2, Finset.card_union_of_disjoint d1, Finset.card_singleton]

theorem Pc.join_f_lowA {A B : Pc} {th x w z : ℕ} (hz : z ∈ A.S) (hl : A.f z < th) :
    (Pc.join A B th x w).f z = A.f z := by
  simp [Pc.join, hz, hl]

theorem Pc.join_f_highA {A B : Pc} {th x w z : ℕ} (hz : z ∈ A.S) (hl : th ≤ A.f z) :
    (Pc.join A B th x w).f z = A.f z + B.E.card + 1 := by
  have : ¬ A.f z < th := by omega
  simp [Pc.join, hz, this]

theorem Pc.join_f_B {A B : Pc} {th x w z : ℕ} (hd : Disjoint A.S B.S) (hz : z ∈ B.S) :
    (Pc.join A B th x w).f z = th + B.f z := by
  have : z ∉ A.S := fun h => Finset.disjoint_left.mp hd h hz
  simp [Pc.join, this]

theorem Pc.Grace.dist_pos {P : Pc} (hP : P.Grace) {e : ℕ × ℕ} (he : e ∈ P.E) :
    1 ≤ Nat.dist (P.f e.1) (P.f e.2) := by
  obtain ⟨_, _, hinj, _, _⟩ := hP
  obtain ⟨h1, h2, h3, _⟩ := Pc.mem_E.mp he
  have hne : P.f e.1 ≠ P.f e.2 := fun h => absurd (hinj _ h1 _ h2 h) (by omega)
  simp only [Nat.dist]; omega

theorem Pc.Grace.dist_le {P : Pc} (hP : P.Grace) {e : ℕ × ℕ} (he : e ∈ P.E) :
    Nat.dist (P.f e.1) (P.f e.2) ≤ P.E.card := by
  obtain ⟨_, _, _, hle, _⟩ := hP
  obtain ⟨h1, h2, _, _⟩ := Pc.mem_E.mp he
  have := hle _ h1
  have := hle _ h2
  simp only [Nat.dist]; omega

theorem Pc.fgl {A B : Pc} {th x w : ℕ} (hA : A.Alpha th) (hB : B.Grace) (hd : Disjoint A.S B.S)
    (hx : x ∈ A.S) (hw : w ∈ B.S)
    (hc : (A.f x < th ∧ B.f w + (th - 1 - A.f x) = B.E.card) ∨ (th ≤ A.f x ∧ B.f w + th = A.f x)) :
    (Pc.join A B th x w).Grace := by
  classical
  have hAg := hA.1
  obtain ⟨hAsym, hAcard, hAinj, hAle, hAedge⟩ := hA.1
  have hth := hA.2.1
  have hAalt := hA.2.2
  obtain ⟨hBsym, hBcard, hBinj, hBle, hBedge⟩ := hB
  have hBg : B.Grace := ⟨hBsym, hBcard, hBinj, hBle, hBedge⟩
  have hcardE := Pc.join_card_E (th := th) hd hx hw
  have hE := Pc.join_E (th := th) hd hx hw
  set J := Pc.join A B th x w with hJ
  set mB := B.E.card with hmB
  have notB : ∀ z ∈ A.S, z ∉ B.S := fun z hz hzB => Finset.disjoint_left.mp hd hz hzB
  -- label of an A-edge
  have eA : ∀ e ∈ A.E, Nat.dist (J.f e.1) (J.f e.2) = Nat.dist (A.f e.1) (A.f e.2) + mB + 1 := by
    intro e he
    obtain ⟨h1, h2, _, hr⟩ := Pc.mem_E.mp he
    have alt := hAalt _ h1 _ h2 hr
    by_cases hl : A.f e.1 < th
    · have hh : th ≤ A.f e.2 := alt.mp hl
      rw [Pc.join_f_lowA h1 hl, Pc.join_f_highA h2 hh]
      simp only [Nat.dist]; omega
    · have hh : A.f e.2 < th := by
        by_contra hc'; exact hl (alt.mpr (by omega))
      rw [Pc.join_f_highA h1 (by omega), Pc.join_f_lowA h2 hh]
      simp only [Nat.dist]; omega
  have eB : ∀ e ∈ B.E, Nat.dist (J.f e.1) (J.f e.2) = Nat.dist (B.f e.1) (B.f e.2) := by
    intro e he
    obtain ⟨h1, h2, _, _⟩ := Pc.mem_E.mp he
    rw [Pc.join_f_B hd h1, Pc.join_f_B hd h2]
    simp only [Nat.dist]; omega
  have eJ : Nat.dist (J.f (opair x w).1) (J.f (opair x w).2) = mB + 1 := by
    have key : Nat.dist (J.f x) (J.f w) = mB + 1 := by
      rw [Pc.join_f_B hd hw]
      rcases hc with ⟨hl, hc⟩ | ⟨hh, hc⟩
      · rw [Pc.join_f_lowA hx hl]; simp only [Nat.dist]; omega
      · rw [Pc.join_f_highA hx hh]; simp only [Nat.dist]; omega
    simp only [opair]
    rcases le_total x w with hl | hl
    · rw [min_eq_left hl, max_eq_right hl]; exact key
    · rw [min_eq_right hl, max_eq_left hl, Nat.dist_comm]; exact key
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro p q h
    simp only [J, Pc.join] at h ⊢
    rcases h with ⟨a1, a2, a3⟩ | ⟨b1, b2, b3⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨a2, a1, hAsym _ _ a3⟩
    · exact Or.inr (Or.inl ⟨b2, b1, hBsym _ _ b3⟩)
    · exact Or.inr (Or.inr (Or.inr ⟨h2, h1⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨h2, h1⟩))
  · rw [hcardE]
    simp only [J, Pc.join]
    rw [Finset.card_union_of_disjoint hd]
    omega
  · intro p hp q hq hpq
    simp only [J, Pc.join, Finset.mem_union] at hp hq
    rcases hp with hp | hp <;> rcases hq with hq | hq
    · by_cases l1 : A.f p < th <;> by_cases l2 : A.f q < th
      · rw [Pc.join_f_lowA hp l1, Pc.join_f_lowA hq l2] at hpq; exact hAinj _ hp _ hq hpq
      · rw [Pc.join_f_lowA hp l1, Pc.join_f_highA hq (by omega)] at hpq; omega
      · rw [Pc.join_f_highA hp (by omega), Pc.join_f_lowA hq l2] at hpq; omega
      · rw [Pc.join_f_highA hp (by omega), Pc.join_f_highA hq (by omega)] at hpq
        exact hAinj _ hp _ hq (by omega)
    · rw [Pc.join_f_B hd hq] at hpq
      have := hBle _ hq
      by_cases l1 : A.f p < th
      · rw [Pc.join_f_lowA hp l1] at hpq; omega
      · rw [Pc.join_f_highA hp (by omega)] at hpq; omega
    · rw [Pc.join_f_B hd hp] at hpq
      have := hBle _ hp
      by_cases l1 : A.f q < th
      · rw [Pc.join_f_lowA hq l1] at hpq; omega
      · rw [Pc.join_f_highA hq (by omega)] at hpq; omega
    · rw [Pc.join_f_B hd hp, Pc.join_f_B hd hq] at hpq
      exact hBinj _ hp _ hq (by omega)
  · intro p hp
    rw [hcardE]
    simp only [J, Pc.join, Finset.mem_union] at hp
    rcases hp with hp | hp
    · have := hAle _ hp
      by_cases l1 : A.f p < th
      · rw [Pc.join_f_lowA hp l1]; omega
      · rw [Pc.join_f_highA hp (by omega)]; omega
    · rw [Pc.join_f_B hd hp]
      have := hBle _ hp
      omega
  · intro e he e' he' heq
    rw [hE] at he he'
    simp only [Finset.mem_union, Finset.mem_singleton] at he he'
    rcases he with (he | he) | he <;> rcases he' with (he' | he') | he'
    · rw [eA e he, eA e' he'] at heq; exact hAedge e he e' he' (by omega)
    · rw [eA e he, eB e' he'] at heq
      have := hBg.dist_le he'; omega
    · rw [eA e he, he', eJ] at heq
      have := hAg.dist_pos he; omega
    · rw [eB e he, eA e' he'] at heq
      have := hBg.dist_le he; omega
    · rw [eB e he, eB e' he'] at heq; exact hBedge e he e' he' heq
    · rw [eB e he, he', eJ] at heq
      have := hBg.dist_le he; omega
    · rw [he, eJ, eA e' he'] at heq
      have := hAg.dist_pos he'; omega
    · rw [he, eJ, eB e' he'] at heq
      have := hBg.dist_le he'; omega
    · rw [he, he']

theorem Pc.fgl_alpha {A B : Pc} {th thB x w : ℕ} (hA : A.Alpha th) (hB : B.Alpha thB)
    (hd : Disjoint A.S B.S) (hx : x ∈ A.S) (hw : w ∈ B.S)
    (hc : (A.f x < th ∧ B.f w + (th - 1 - A.f x) = B.E.card) ∨ (th ≤ A.f x ∧ B.f w + th = A.f x))
    (hcls : A.f x < th ↔ thB ≤ B.f w) :
    (Pc.join A B th x w).Alpha (th + thB) := by
  classical
  have hG := Pc.fgl hA hB.1 hd hx hw hc
  refine ⟨hG, ?_, ?_⟩
  · rw [Pc.join_card_E hd hx hw]
    have := hA.2.1
    have := hB.2.1
    omega
  · have hAalt := hA.2.2
    have hBalt := hB.2.2
    have hthA := hA.2.1
    have hthB := hB.2.1
    intro p hp q hq hr
    simp only [Pc.join, Finset.mem_union] at hp hq hr
    rcases hr with ⟨a1, a2, a3⟩ | ⟨b1, b2, b3⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have alt := hAalt _ a1 _ a2 a3
      by_cases l1 : A.f p < th
      · have h2 : th ≤ A.f q := alt.mp l1
        rw [Pc.join_f_lowA a1 l1, Pc.join_f_highA a2 h2]
        omega
      · have h2 : A.f q < th := by
          by_contra hc'; exact l1 (alt.mpr (by omega))
        rw [Pc.join_f_highA a1 (by omega), Pc.join_f_lowA a2 h2]
        omega
    · have alt := hBalt _ b1 _ b2 b3
      rw [Pc.join_f_B hd b1, Pc.join_f_B hd b2]
      omega
    · subst h1; subst h2
      rw [Pc.join_f_B hd hw]
      by_cases l1 : A.f p < th
      · rw [Pc.join_f_lowA hx l1]; have := hcls.mp l1; omega
      · rw [Pc.join_f_highA hx (by omega)]
        have : ¬ thB ≤ B.f q := fun h => l1 (hcls.mpr h)
        omega
    · subst h1; subst h2
      rw [Pc.join_f_B hd hw]
      by_cases l1 : A.f q < th
      · rw [Pc.join_f_lowA hx l1]; have := hcls.mp l1; omega
      · rw [Pc.join_f_highA hx (by omega)]
        have : ¬ thB ≤ B.f p := fun h => l1 (hcls.mpr h)
        omega

/-- complement of a piece's labeling -/
noncomputable def Pc.cmp (P : Pc) : Pc where
  S := P.S
  R := P.R
  f := fun z => P.E.card - P.f z

theorem Pc.cmp_E (P : Pc) : P.cmp.E = P.E := rfl

theorem Pc.cmp_grace {P : Pc} (hP : P.Grace) : P.cmp.Grace := by
  obtain ⟨hsym, hcard, hinj, hle, hedge⟩ := hP
  refine ⟨hsym, hcard, ?_, ?_, ?_⟩
  · intro x hx y hy h
    simp only [Pc.cmp] at h
    have := hle x hx; have := hle y hy
    exact hinj x hx y hy (by omega)
  · intro x _
    show P.E.card - P.f x ≤ P.cmp.E.card
    rw [Pc.cmp_E]; omega
  · intro e he e' he' h
    rw [Pc.cmp_E] at he he'
    apply hedge e he e' he'
    obtain ⟨a1, a2, _, _⟩ := Pc.mem_E.mp he
    obtain ⟨b1, b2, _, _⟩ := Pc.mem_E.mp he'
    have := hle _ a1; have := hle _ a2; have := hle _ b1; have := hle _ b2
    simp only [Pc.cmp, Nat.dist] at h ⊢
    omega

theorem Pc.cmp_alpha {P : Pc} {th : ℕ} (hP : P.Alpha th) : P.cmp.Alpha (P.E.card + 1 - th) := by
  refine ⟨Pc.cmp_grace hP.1, ?_, ?_⟩
  · rw [Pc.cmp_E]; omega
  · intro x hx y hy hr
    have alt := hP.2.2 x hx y hy hr
    have := hP.1.2.2.2.1 x hx
    have := hP.1.2.2.2.1 y hy
    have := hP.2.1
    simp only [Pc.cmp]
    omega

/-! ## Path pieces -/

/-- the path piece `nm 0 - nm 1 - ⋯ - nm (n-1)` labelled by `L ∘ pos`. -/
noncomputable def pathPc (n : ℕ) (nm pos L : ℕ → ℕ) : Pc where
  S := (Finset.range n).image nm
  R := fun p q => ∃ i, i + 1 < n ∧ ((p = nm i ∧ q = nm (i + 1)) ∨ (p = nm (i + 1) ∧ q = nm i))
  f := fun z => L (pos z)

theorem pathPc_mem_S {n : ℕ} {nm pos L : ℕ → ℕ} {z : ℕ} :
    z ∈ (pathPc n nm pos L).S ↔ ∃ i, i < n ∧ nm i = z := by
  simp [pathPc, Finset.mem_image]

theorem pathPc_E {n : ℕ} {nm pos L : ℕ → ℕ} (hinj : ∀ i j, i < n → j < n → nm i = nm j → i = j) :
    (pathPc n nm pos L).E = (Finset.range (n - 1)).image (fun i => opair (nm i) (nm (i + 1))) := by
  classical
  ext ⟨p, q⟩
  rw [Pc.mem_E, Finset.mem_image]
  simp only [pathPc_mem_S, Finset.mem_range, opair, Prod.mk.injEq]
  constructor
  · rintro ⟨_, _, hpq, i, hi, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩
    · exact ⟨i, by omega, min_eq_left (le_of_lt hpq), max_eq_right (le_of_lt hpq)⟩
    · exact ⟨i, by omega, min_eq_right (le_of_lt hpq), max_eq_left (le_of_lt hpq)⟩
  · rintro ⟨i, hi, h1, h2⟩
    have hne : nm i ≠ nm (i + 1) := fun h => absurd (hinj _ _ (by omega) (by omega) h) (by omega)
    rcases lt_or_gt_of_ne hne with hl | hl
    · rw [min_eq_left (le_of_lt hl)] at h1
      rw [max_eq_right (le_of_lt hl)] at h2
      subst h1; subst h2
      exact ⟨⟨i, by omega, rfl⟩, ⟨i + 1, by omega, rfl⟩, hl, i, by omega, Or.inl ⟨rfl, rfl⟩⟩
    · rw [min_eq_right (le_of_lt hl)] at h1
      rw [max_eq_left (le_of_lt hl)] at h2
      subst h1; subst h2
      exact ⟨⟨i + 1, by omega, rfl⟩, ⟨i, by omega, rfl⟩, hl, i, by omega, Or.inr ⟨rfl, rfl⟩⟩

theorem opair_inj_path {n : ℕ} {nm : ℕ → ℕ} (hinj : ∀ i j, i < n → j < n → nm i = nm j → i = j)
    {i j : ℕ} (hi : i + 1 < n) (hj : j + 1 < n)
    (h : opair (nm i) (nm (i + 1)) = opair (nm j) (nm (j + 1))) : i = j := by
  simp only [opair, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  -- the unordered pairs agree
  have key : (nm i = nm j ∧ nm (i + 1) = nm (j + 1)) ∨ (nm i = nm (j + 1) ∧ nm (i + 1) = nm j) := by
    rcases le_total (nm i) (nm (i + 1)) with a | a <;>
    rcases le_total (nm j) (nm (j + 1)) with b | b
    · rw [min_eq_left a, min_eq_left b] at h1; rw [max_eq_right a, max_eq_right b] at h2
      exact Or.inl ⟨h1, h2⟩
    · rw [min_eq_left a, min_eq_right b] at h1; rw [max_eq_right a, max_eq_left b] at h2
      exact Or.inr ⟨h1, h2⟩
    · rw [min_eq_right a, min_eq_left b] at h1; rw [max_eq_left a, max_eq_right b] at h2
      exact Or.inr ⟨h2, h1⟩
    · rw [min_eq_right a, min_eq_right b] at h1; rw [max_eq_left a, max_eq_left b] at h2
      exact Or.inl ⟨h2, h1⟩
  rcases key with ⟨k1, _⟩ | ⟨k1, k2⟩
  · exact hinj _ _ (by omega) (by omega) k1
  · have e1 := hinj _ _ (by omega) (by omega) k1
    have e2 := hinj _ _ (by omega) (by omega) k2
    omega

theorem pathPc_card_E {n : ℕ} {nm pos L : ℕ → ℕ} (hinj : ∀ i j, i < n → j < n → nm i = nm j → i = j) :
    (pathPc n nm pos L).E.card = n - 1 := by
  classical
  rw [pathPc_E hinj, Finset.card_image_of_injOn, Finset.card_range]
  intro i hi j hj h
  simp only [Finset.coe_range, Set.mem_Iio] at hi hj
  exact opair_inj_path hinj (by omega) (by omega) h

theorem pathPc_card_S {n : ℕ} {nm pos L : ℕ → ℕ} (hinj : ∀ i j, i < n → j < n → nm i = nm j → i = j) :
    (pathPc n nm pos L).S.card = n := by
  classical
  show ((Finset.range n).image nm).card = n
  rw [Finset.card_image_of_injOn, Finset.card_range]
  intro i hi j hj h
  simp only [Finset.coe_range, Set.mem_Iio] at hi hj
  exact hinj _ _ hi hj h

theorem pathPc_alpha {n lam : ℕ} {nm pos L : ℕ → ℕ} (hn : 1 ≤ n)
    (hinj : ∀ i j, i < n → j < n → nm i = nm j → i = j) (hpos : ∀ i, i < n → pos (nm i) = i)
    (hL : PathAlpha n L lam) (hlam : lam < n) :
    (pathPc n nm pos L).Alpha (lam + 1) := by
  classical
  obtain ⟨Linj, Lle, Ledge, Lalt⟩ := hL
  have hE := pathPc_card_E (pos := pos) (L := L) hinj
  have fval : ∀ i, i < n → (pathPc n nm pos L).f (nm i) = L i := by
    intro i hi; simp [pathPc, hpos i hi]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rintro p q ⟨i, hi, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩
    · exact ⟨i, hi, Or.inr ⟨rfl, rfl⟩⟩
    · exact ⟨i, hi, Or.inl ⟨rfl, rfl⟩⟩
  · rw [pathPc_card_S hinj, hE]; omega
  · intro x hx y hy hxy
    obtain ⟨i, hi, rfl⟩ := pathPc_mem_S.mp hx
    obtain ⟨j, hj, rfl⟩ := pathPc_mem_S.mp hy
    rw [fval i hi, fval j hj] at hxy
    rw [Linj i j hi hj hxy]
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := pathPc_mem_S.mp hx
    rw [fval i hi, hE]; exact Lle i hi
  · intro e he e' he' h
    rw [pathPc_E hinj, Finset.mem_image] at he he'
    obtain ⟨i, hi, rfl⟩ := he
    obtain ⟨j, hj, rfl⟩ := he'
    simp only [Finset.mem_range] at hi hj
    have d1 : Nat.dist ((pathPc n nm pos L).f (opair (nm i) (nm (i + 1))).1)
        ((pathPc n nm pos L).f (opair (nm i) (nm (i + 1))).2) = Nat.dist (L i) (L (i + 1)) := by
      simp only [opair]
      rcases le_total (nm i) (nm (i + 1)) with a | a
      · rw [min_eq_left a, max_eq_right a, fval i (by omega), fval (i + 1) (by omega)]
      · rw [min_eq_right a, max_eq_left a, fval i (by omega), fval (i + 1) (by omega), Nat.dist_comm]
    have d2 : Nat.dist ((pathPc n nm pos L).f (opair (nm j) (nm (j + 1))).1)
        ((pathPc n nm pos L).f (opair (nm j) (nm (j + 1))).2) = Nat.dist (L j) (L (j + 1)) := by
      simp only [opair]
      rcases le_total (nm j) (nm (j + 1)) with a | a
      · rw [min_eq_left a, max_eq_right a, fval j (by omega), fval (j + 1) (by omega)]
      · rw [min_eq_right a, max_eq_left a, fval j (by omega), fval (j + 1) (by omega), Nat.dist_comm]
    rw [d1, d2] at h
    rw [Ledge i j (by omega) (by omega) h]
  · rw [hE]; omega
  · intro x _ y _ hr
    obtain ⟨i, hi, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩ := hr
    · rw [fval i (by omega), fval (i + 1) hi]
      have := Lalt i hi
      omega
    · rw [fval (i + 1) hi, fval i (by omega)]
      have := Lalt i hi
      omega

/-! ## Induced pieces: all pieces share one global symmetric adjacency `R` -/

theorem Pc.E_congr {P Q : Pc} (hS : P.S = Q.S)
    (hR : ∀ x ∈ P.S, ∀ y ∈ P.S, P.R x y ↔ Q.R x y) : P.E = Q.E := by
  classical
  ext e
  rw [Pc.mem_E, Pc.mem_E, ← hS]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨h1, h2, h3, (hR _ h1 _ h2).mp h4⟩
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨h1, h2, h3, (hR _ h1 _ h2).mpr h4⟩

theorem Pc.grace_congr {P Q : Pc} (hP : P.Grace) (hS : P.S = Q.S)
    (hR : ∀ x ∈ P.S, ∀ y ∈ P.S, P.R x y ↔ Q.R x y) (hf : ∀ x ∈ P.S, P.f x = Q.f x)
    (hsym : ∀ x y, Q.R x y → Q.R y x) : Q.Grace := by
  obtain ⟨_, hcard, hinj, hle, hedge⟩ := hP
  have hE := Pc.E_congr hS hR
  refine ⟨hsym, ?_, ?_, ?_, ?_⟩
  · rw [← hS, ← hE]; exact hcard
  · intro x hx y hy h
    rw [← hS] at hx hy
    rw [← hf x hx, ← hf y hy] at h
    exact hinj x hx y hy h
  · intro x hx
    rw [← hS] at hx
    rw [← hf x hx, ← hE]; exact hle x hx
  · intro e he e' he' h
    rw [← hE] at he he'
    obtain ⟨a1, a2, _, _⟩ := Pc.mem_E.mp he
    obtain ⟨b1, b2, _, _⟩ := Pc.mem_E.mp he'
    rw [← hf _ a1, ← hf _ a2, ← hf _ b1, ← hf _ b2] at h
    exact hedge e he e' he' h

theorem Pc.alpha_congr {P Q : Pc} {th : ℕ} (hP : P.Alpha th) (hS : P.S = Q.S)
    (hR : ∀ x ∈ P.S, ∀ y ∈ P.S, P.R x y ↔ Q.R x y) (hf : ∀ x ∈ P.S, P.f x = Q.f x)
    (hsym : ∀ x y, Q.R x y → Q.R y x) : Q.Alpha th := by
  refine ⟨Pc.grace_congr hP.1 hS hR hf hsym, ?_, ?_⟩
  · rw [← Pc.E_congr hS hR]; exact hP.2.1
  · intro x hx y hy hr
    rw [← hS] at hx hy
    rw [← hf x hx, ← hf y hy]
    exact hP.2.2 x hx y hy ((hR x hx y hy).mpr hr)

/-- the induced join: same global `R`, labeling as in `Pc.join`. -/
noncomputable def Pc.ijoin (A B : Pc) (th x w : ℕ) : Pc where
  S := A.S ∪ B.S
  R := A.R
  f := (Pc.join A B th x w).f

theorem Pc.ijoin_R {A B : Pc} {th x w : ℕ} (hR : A.R = B.R) (hsym : ∀ p q, A.R p q → A.R q p)
    (hd : Disjoint A.S B.S) (hxw : A.R x w)
    (hcross : ∀ p ∈ A.S, ∀ q ∈ B.S, A.R p q → p = x ∧ q = w) :
    ∀ p ∈ (Pc.join A B th x w).S, ∀ q ∈ (Pc.join A B th x w).S,
      (Pc.join A B th x w).R p q ↔ (Pc.ijoin A B th x w).R p q := by
  intro p hp q hq
  simp only [Pc.join, Pc.ijoin, Finset.mem_union] at hp hq ⊢
  constructor
  · rintro (⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact h
    · rw [hR]; exact h
    · exact hxw
    · exact hsym _ _ hxw
  · intro h
    rcases hp with hp | hp <;> rcases hq with hq | hq
    · exact Or.inl ⟨hp, hq, h⟩
    · obtain ⟨rfl, rfl⟩ := hcross p hp q hq h
      exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
    · obtain ⟨rfl, rfl⟩ := hcross q hq p hp (hsym _ _ h)
      exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))
    · exact Or.inr (Or.inl ⟨hp, hq, by rw [← hR]; exact h⟩)

theorem Pc.ifgl {A B : Pc} {th x w : ℕ} (hA : A.Alpha th) (hB : B.Grace) (hR : A.R = B.R)
    (hd : Disjoint A.S B.S) (hx : x ∈ A.S) (hw : w ∈ B.S) (hxw : A.R x w)
    (hcross : ∀ p ∈ A.S, ∀ q ∈ B.S, A.R p q → p = x ∧ q = w)
    (hc : (A.f x < th ∧ B.f w + (th - 1 - A.f x) = B.E.card) ∨ (th ≤ A.f x ∧ B.f w + th = A.f x)) :
    (Pc.ijoin A B th x w).Grace :=
  Pc.grace_congr (Pc.fgl hA hB hd hx hw hc) rfl
    (Pc.ijoin_R hR hA.1.1 hd hxw hcross) (fun _ _ => rfl) hA.1.1

theorem Pc.ifgl_alpha {A B : Pc} {th thB x w : ℕ} (hA : A.Alpha th) (hB : B.Alpha thB)
    (hR : A.R = B.R) (hd : Disjoint A.S B.S) (hx : x ∈ A.S) (hw : w ∈ B.S) (hxw : A.R x w)
    (hcross : ∀ p ∈ A.S, ∀ q ∈ B.S, A.R p q → p = x ∧ q = w)
    (hc : (A.f x < th ∧ B.f w + (th - 1 - A.f x) = B.E.card) ∨ (th ≤ A.f x ∧ B.f w + th = A.f x))
    (hcls : A.f x < th ↔ thB ≤ B.f w) :
    (Pc.ijoin A B th x w).Alpha (th + thB) :=
  Pc.alpha_congr (Pc.fgl_alpha hA hB hd hx hw hc hcls) rfl
    (Pc.ijoin_R hR hA.1.1 hd hxw hcross) (fun _ _ => rfl) hA.1.1

theorem Pc.ijoin_card_E {A B : Pc} {th x w : ℕ} (hR : A.R = B.R) (hsym : ∀ p q, A.R p q → A.R q p)
    (hd : Disjoint A.S B.S) (hx : x ∈ A.S) (hw : w ∈ B.S) (hxw : A.R x w)
    (hcross : ∀ p ∈ A.S, ∀ q ∈ B.S, A.R p q → p = x ∧ q = w) :
    (Pc.ijoin A B th x w).E.card = A.E.card + B.E.card + 1 := by
  have h := Pc.E_congr (P := Pc.join A B th x w) (Q := Pc.ijoin A B th x w) rfl
    (Pc.ijoin_R hR hsym hd hxw hcross)
  rw [← h, Pc.join_card_E hd hx hw]

/-- an induced path piece with global adjacency `R`. -/
noncomputable def ipathPc (R : ℕ → ℕ → Prop) (n : ℕ) (nm pos L : ℕ → ℕ) : Pc where
  S := (Finset.range n).image nm
  R := R
  f := fun z => L (pos z)

theorem ipathPc_alpha {R : ℕ → ℕ → Prop} {n lam : ℕ} {nm pos L : ℕ → ℕ} (hn : 1 ≤ n)
    (hsym : ∀ p q, R p q → R q p)
    (hinj : ∀ i j, i < n → j < n → nm i = nm j → i = j) (hpos : ∀ i, i < n → pos (nm i) = i)
    (hcons : ∀ i, i + 1 < n → R (nm i) (nm (i + 1)))
    (hchord : ∀ i j, i < n → j < n → R (nm i) (nm j) → i = j + 1 ∨ j = i + 1)
    (hL : PathAlpha n L lam) (hlam : lam < n) :
    (ipathPc R n nm pos L).Alpha (lam + 1) := by
  refine Pc.alpha_congr (pathPc_alpha hn hinj hpos hL hlam) rfl ?_ (fun _ _ => rfl) hsym
  intro x hx y hy
  obtain ⟨i, hi, rfl⟩ := pathPc_mem_S.mp hx
  obtain ⟨j, hj, rfl⟩ := pathPc_mem_S.mp hy
  simp only [pathPc, ipathPc]
  constructor
  · rintro ⟨k, hk, (⟨h1, h2⟩ | ⟨h1, h2⟩)⟩
    · rw [h1, h2]; exact hcons k hk
    · rw [h1, h2]; exact hsym _ _ (hcons k hk)
  · intro h
    rcases hchord i j hi hj h with e | e
    · exact ⟨j, by omega, Or.inr ⟨by rw [e], rfl⟩⟩
    · exact ⟨i, by omega, Or.inl ⟨rfl, by rw [e]⟩⟩

/-! ## Rooted-tree facts via distances -/

section TreeFacts
variable {V : Type} {G : SimpleGraph V}

theorem tree_par_exists (hT : G.IsTree) (u x : V) (hx : x ≠ u) :
    ∃ y, G.Adj y x ∧ G.dist u y + 1 = G.dist u x := by
  obtain ⟨p, hp⟩ := hT.isConnected.preconnected u x |>.exists_walk_length_eq_dist
  cases hq : p.reverse with
  | nil => exact absurd rfl hx
  | cons h q =>
    rename_i y
    refine ⟨y, h.symm, ?_⟩
    have hlen : q.length + 1 = G.dist u x := by
      have := p.length_reverse
      rw [hq, SimpleGraph.Walk.length_cons] at this
      omega
    have h1 : G.dist u y ≤ q.length := by
      have := SimpleGraph.dist_le q.reverse
      rw [SimpleGraph.Walk.length_reverse] at this
      exact this
    have h2 := hT.dist_eq_dist_add_one_of_adj u h
    omega


theorem tree_not_mem_support_of_far (hT : G.IsTree) {u y x : V} (p : G.Walk u y)
    (hp : p.length = G.dist u y) (hfar : G.dist u y < G.dist u x) : x ∉ p.support := by
  classical
  intro hx
  have h1 := SimpleGraph.dist_le (p.takeUntil x hx)
  have h2 := p.length_takeUntil_le hx
  omega

theorem tree_par_unique (hT : G.IsTree) {u x y₁ y₂ : V} (h₁ : G.Adj y₁ x) (h₂ : G.Adj y₂ x)
    (d₁ : G.dist u y₁ + 1 = G.dist u x) (d₂ : G.dist u y₂ + 1 = G.dist u x) : y₁ = y₂ := by
  classical
  obtain ⟨p₁, hp₁, hl₁⟩ := hT.isConnected.exists_path_of_dist u y₁
  obtain ⟨p₂, hp₂, hl₂⟩ := hT.isConnected.exists_path_of_dist u y₂
  have n₁ := tree_not_mem_support_of_far hT p₁ hl₁ (by omega : G.dist u y₁ < G.dist u x)
  have n₂ := tree_not_mem_support_of_far hT p₂ hl₂ (by omega : G.dist u y₂ < G.dist u x)
  have q₁ := hp₁.concat n₁ h₁
  have q₂ := hp₂.concat n₂ h₂
  have heq : p₁.concat h₁ = p₂.concat h₂ :=
    congrArg Subtype.val (hT.IsAcyclic.path_unique ⟨_, q₁⟩ ⟨_, q₂⟩)
  have := congrArg SimpleGraph.Walk.penultimate heq
  simpa [SimpleGraph.Walk.penultimate_concat] using this


/-- parent of `x` in the tree rooted at `u` (`u` itself for `x = u`). -/
noncomputable def tpar (hT : G.IsTree) (u x : V) : V := by
  classical
  exact if h : x = u then u else Classical.choose (tree_par_exists hT u x h)

theorem tpar_spec (hT : G.IsTree) (u x : V) (hx : x ≠ u) :
    G.Adj (tpar hT u x) x ∧ G.dist u (tpar hT u x) + 1 = G.dist u x := by
  classical
  unfold tpar
  simp only [dif_neg hx]
  exact Classical.choose_spec (tree_par_exists hT u x hx)

theorem tpar_eq (hT : G.IsTree) {u x y : V} (hx : x ≠ u) (hadj : G.Adj y x)
    (hd : G.dist u y + 1 = G.dist u x) : tpar hT u x = y :=
  tree_par_unique hT (tpar_spec hT u x hx).1 hadj (tpar_spec hT u x hx).2 hd

theorem dist_pos_of_ne (hT : G.IsTree) {u x : V} (hx : x ≠ u) : 1 ≤ G.dist u x := by
  have := hT.isConnected.pos_dist_of_ne (Ne.symm hx)
  omega

theorem eq_of_dist_zero (hT : G.IsTree) {u x : V} (h : G.dist u x = 0) : x = u :=
  ((hT.isConnected.dist_eq_zero_iff).mp h).symm

/-- adjacency is exactly the parent relation -/
theorem adj_iff_par (hT : G.IsTree) (u : V) {x y : V} (hadj : G.Adj x y) :
    (y ≠ u ∧ tpar hT u y = x ∧ G.dist u y = G.dist u x + 1) ∨
    (x ≠ u ∧ tpar hT u x = y ∧ G.dist u x = G.dist u y + 1) := by
  rcases hT.dist_eq_dist_add_one_of_adj u hadj with h | h
  · right
    have hx : x ≠ u := by
      intro e; subst e; simp at h
    exact ⟨hx, tpar_eq hT hx hadj.symm (by omega), h⟩
  · left
    have hy : y ≠ u := by
      intro e; subst e; simp at h
    exact ⟨hy, tpar_eq hT hy hadj (by omega), h⟩

theorem iter_tpar_dist (hT : G.IsTree) (u x : V) :
    ∀ i, i ≤ G.dist u x → G.dist u ((tpar hT u)^[i] x) = G.dist u x - i := by
  intro i
  induction i with
  | zero => intro _; simp
  | succ i ih =>
    intro hi
    rw [Function.iterate_succ_apply']
    have h1 := ih (by omega)
    have hne : (tpar hT u)^[i] x ≠ u := by
      intro e; rw [e] at h1; simp at h1; omega
    have := (tpar_spec hT u _ hne).2
    omega

/-- ancestor of `x` at depth `j` -/
noncomputable def anc (hT : G.IsTree) (u x : V) (j : ℕ) : V := (tpar hT u)^[G.dist u x - j] x

theorem anc_dist (hT : G.IsTree) (u x : V) {j : ℕ} (hj : j ≤ G.dist u x) :
    G.dist u (anc hT u x j) = j := by
  unfold anc
  rw [iter_tpar_dist hT u x _ (by omega)]
  omega

theorem anc_self (hT : G.IsTree) (u x : V) : anc hT u x (G.dist u x) = x := by
  simp [anc]

theorem anc_tpar (hT : G.IsTree) (u x : V) (hx : x ≠ u) {j : ℕ} (hj : j < G.dist u x) :
    anc hT u (tpar hT u x) j = anc hT u x j := by
  unfold anc
  have hd := (tpar_spec hT u x hx).2
  have e : G.dist u x - j = (G.dist u (tpar hT u x) - j) + 1 := by omega
  rw [e, Function.iterate_succ_apply]

theorem anc_anc (hT : G.IsTree) (u x : V) {i j : ℕ} (hji : j ≤ i) (hi : i ≤ G.dist u x) :
    anc hT u (anc hT u x i) j = anc hT u x j := by
  have hd := anc_dist hT u x hi
  unfold anc at hd ⊢
  rw [hd, ← Function.iterate_add_apply]
  congr 1
  omega

end TreeFacts

/-! ## Chains: one vertex per depth in a low-degree branch -/

section Chain
variable {n : ℕ} {G : SimpleGraph (Fin n)}

theorem deg_ge_three {q a b c : Fin n} (ha : G.Adj q a) (hb : G.Adj q b) (hc : G.Adj q c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : 3 ≤ Math15.Graceful.degree G q := by
  classical
  unfold Math15.Graceful.degree
  have hsub : ({a, b, c} : Finset (Fin n)) ⊆ (Finset.univ : Finset (Fin n)).filter (G.Adj q) := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hz with rfl | rfl | rfl <;> assumption
  have hcard : ({a, b, c} : Finset (Fin n)).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair hbc]
    simp [hab, hac]
  calc 3 = ({a, b, c} : Finset (Fin n)).card := hcard.symm
    _ ≤ _ := Finset.card_le_card hsub

theorem chain_uniq (hT : G.IsTree) (u w : Fin n) (K : ℕ) (hw : 1 ≤ G.dist u w)
    (hdeg : ∀ q, G.dist u w ≤ G.dist u q → G.dist u q < K →
      anc hT u q (G.dist u w) = w → Math15.Graceful.degree G q ≤ 2) :
    ∀ x y, G.dist u w ≤ G.dist u x → G.dist u x ≤ K →
      anc hT u x (G.dist u w) = w → anc hT u y (G.dist u w) = w →
      G.dist u x = G.dist u y → x = y := by
  intro x y
  induction' h : G.dist u x - G.dist u w with j ih generalizing x y
  · intro hx _ ax ay hxy
    have e1 : G.dist u x = G.dist u w := by omega
    have e2 : G.dist u y = G.dist u w := by omega
    have hx' : w = x := by
      have h1 := anc_self hT u x
      rw [e1, ax] at h1
      exact h1
    have hy' : w = y := by
      have h1 := anc_self hT u y
      rw [e2, ay] at h1
      exact h1
    exact hx'.symm.trans hy'
  · intro hx hK ax ay hxy
    have hxu : x ≠ u := by
      intro e; rw [e, SimpleGraph.dist_self] at hx; omega
    have hyu : y ≠ u := by
      intro e; rw [e, SimpleGraph.dist_self] at hxy; omega
    obtain ⟨hpx, dpx⟩ := tpar_spec hT u x hxu
    obtain ⟨hpy, dpy⟩ := tpar_spec hT u y hyu
    have apx : anc hT u (tpar hT u x) (G.dist u w) = w := by
      rw [anc_tpar hT u x hxu (by omega)]; exact ax
    have apy : anc hT u (tpar hT u y) (G.dist u w) = w := by
      rw [anc_tpar hT u y hyu (by omega)]; exact ay
    have heq : tpar hT u x = tpar hT u y :=
      ih (tpar hT u x) (tpar hT u y) (by omega) (by omega) (by omega) apx apy (by omega)
    by_contra hne
    set q := tpar hT u x with hq
    have hqu : q ≠ u := fun e => by rw [e] at dpx; simp at dpx; omega
    obtain ⟨hpq, dpq⟩ := tpar_spec hT u q hqu
    have h3 : 3 ≤ Math15.Graceful.degree G q := by
      refine deg_ge_three (a := tpar hT u q) (b := x) (c := y) hpq.symm hpx (heq ▸ hpy) ?_ ?_ hne
      · intro e; rw [e] at dpq; omega
      · intro e; rw [e] at dpq; omega
    have := hdeg q (by omega) (by omega) apx
    omega

end Chain

/-! ## Transfer: a graceful piece isomorphic to `G` gives `IsGraceful G` -/

section Transfer
variable {n : ℕ} {G : SimpleGraph (Fin n)}

/-- edge labels of a graceful piece cover `[1, |E|]` -/
theorem Pc.Grace.label_surj {P : Pc} (hP : P.Grace) {d : ℕ} (h1 : 1 ≤ d) (h2 : d ≤ P.E.card) :
    ∃ e ∈ P.E, Nat.dist (P.f e.1) (P.f e.2) = d := by
  classical
  set lab : ℕ × ℕ → ℕ := fun e => Nat.dist (P.f e.1) (P.f e.2)
  have hinj : Set.InjOn lab P.E := fun e he e' he' h => hP.2.2.2.2 e he e' he' h
  have hsub : P.E.image lab ⊆ Finset.Icc 1 P.E.card := by
    intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨e, he, rfl⟩ := hz
    rw [Finset.mem_Icc]
    exact ⟨hP.dist_pos he, hP.dist_le he⟩
  have hcard : (P.E.image lab).card = (Finset.Icc 1 P.E.card).card := by
    rw [Finset.card_image_of_injOn hinj, Nat.card_Icc]; omega
  have heq := Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard.symm)
  have hd : d ∈ Finset.Icc 1 P.E.card := Finset.mem_Icc.mpr ⟨h1, h2⟩
  rw [← heq, Finset.mem_image] at hd
  obtain ⟨e, he, hl⟩ := hd
  exact ⟨e, he, hl⟩

theorem graceful_of_piece (P : Pc) (hP : P.Grace) (φ : Fin n → ℕ) (hinj : Function.Injective φ)
    (hmem : ∀ x, φ x ∈ P.S) (hsurj : ∀ s ∈ P.S, ∃ x, φ x = s)
    (hadj : ∀ x y, G.Adj x y ↔ P.R (φ x) (φ y)) : Math15.Graceful.IsGraceful G := by
  classical
  -- the G-edge set and its bijection with P.E
  set EG := (Finset.univ : Finset (Fin n × Fin n)).filter (fun e => e.1 < e.2 ∧ G.Adj e.1 e.2)
    with hEG
  have hcount : Math15.Graceful.edgeCount G = EG.card := by
    unfold Math15.Graceful.edgeCount; rfl
  set g : Fin n × Fin n → ℕ × ℕ := fun e => opair (φ e.1) (φ e.2) with hg
  have g_mem : ∀ e ∈ EG, g e ∈ P.E := by
    intro e he
    simp only [hEG, Finset.mem_filter, Finset.mem_univ, true_and] at he
    rw [Pc.mem_E]
    have hne : φ e.1 ≠ φ e.2 := fun h => absurd (hinj h) (ne_of_lt he.1)
    have hr := (hadj e.1 e.2).mp he.2
    simp only [hg, opair]
    rcases lt_or_gt_of_ne hne with hl | hl
    · rw [min_eq_left (le_of_lt hl), max_eq_right (le_of_lt hl)]
      exact ⟨hmem _, hmem _, hl, hr⟩
    · rw [min_eq_right (le_of_lt hl), max_eq_left (le_of_lt hl)]
      exact ⟨hmem _, hmem _, hl, hP.1 _ _ hr⟩
  have g_inj : Set.InjOn g EG := by
    intro e he e' he' h
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq, hEG] at he he'
    simp only [hg, opair, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have key : (φ e.1 = φ e'.1 ∧ φ e.2 = φ e'.2) ∨ (φ e.1 = φ e'.2 ∧ φ e.2 = φ e'.1) := by
      rcases le_total (φ e.1) (φ e.2) with a | a <;> rcases le_total (φ e'.1) (φ e'.2) with b | b
      · rw [min_eq_left a, min_eq_left b] at h1; rw [max_eq_right a, max_eq_right b] at h2
        exact Or.inl ⟨h1, h2⟩
      · rw [min_eq_left a, min_eq_right b] at h1; rw [max_eq_right a, max_eq_left b] at h2
        exact Or.inr ⟨h1, h2⟩
      · rw [min_eq_right a, min_eq_left b] at h1; rw [max_eq_left a, max_eq_right b] at h2
        exact Or.inr ⟨h2, h1⟩
      · rw [min_eq_right a, min_eq_right b] at h1; rw [max_eq_left a, max_eq_left b] at h2
        exact Or.inl ⟨h2, h1⟩
    rcases key with ⟨k1, k2⟩ | ⟨k1, k2⟩
    · exact Prod.ext (hinj k1) (hinj k2)
    · have a1 : e.1 = e'.2 := hinj k1
      have a2 : e.2 = e'.1 := hinj k2
      have h3 : e.2 < e.1 := by rw [a1, a2]; exact he'.1
      exact absurd he.1 (not_lt.mpr (le_of_lt h3))
  have g_surj : ∀ s ∈ P.E, ∃ e ∈ EG, g e = s := by
    intro s hs
    obtain ⟨h1, h2, h3, h4⟩ := Pc.mem_E.mp hs
    obtain ⟨x, hx⟩ := hsurj _ h1
    obtain ⟨y, hy⟩ := hsurj _ h2
    have hxy : x ≠ y := fun e => by subst e; rw [hx] at hy; omega
    have hadjxy : G.Adj x y := (hadj x y).mpr (by rw [hx, hy]; exact h4)
    rcases lt_or_gt_of_ne hxy with hl | hl
    · refine ⟨(x, y), ?_, ?_⟩
      · simp [hEG, hl, hadjxy]
      · simp only [hg, opair, hx, hy]
        rw [min_eq_left (le_of_lt h3), max_eq_right (le_of_lt h3)]
    · refine ⟨(y, x), ?_, ?_⟩
      · simp [hEG, hl, hadjxy.symm]
      · simp only [hg, opair, hx, hy]
        rw [min_eq_right (le_of_lt h3), max_eq_left (le_of_lt h3)]
  have hcardE : EG.card = P.E.card := by
    have hsub : EG.image g ⊆ P.E := by
      intro s hs; rw [Finset.mem_image] at hs; obtain ⟨e, he, rfl⟩ := hs; exact g_mem e he
    have hsup : P.E ⊆ EG.image g := by
      intro s hs; obtain ⟨e, he, rfl⟩ := g_surj s hs; exact Finset.mem_image_of_mem g he
    rw [← Finset.card_image_of_injOn g_inj, Finset.Subset.antisymm hsub hsup]
  -- label transport
  have lab_eq : ∀ e : Fin n × Fin n,
      Nat.dist (P.f (φ e.1)) (P.f (φ e.2)) = Nat.dist (P.f (g e).1) (P.f (g e).2) := by
    intro e
    simp only [hg, opair]
    rcases le_total (φ e.1) (φ e.2) with a | a
    · rw [min_eq_left a, max_eq_right a]
    · rw [min_eq_right a, max_eq_left a, Nat.dist_comm]
  refine ⟨fun x => P.f (φ x), ?_, ?_, ?_⟩
  · intro x y h
    exact hinj (hP.2.2.1 _ (hmem x) _ (hmem y) h)
  · intro x
    rw [hcount, hcardE]
    exact hP.2.2.2.1 _ (hmem x)
  · intro d h1 h2
    rw [hcount, hcardE] at h2
    obtain ⟨s, hs, hl⟩ := hP.label_surj h1 h2
    obtain ⟨e, he, rfl⟩ := g_surj s hs
    have he' := he
    simp only [hEG, Finset.mem_filter, Finset.mem_univ, true_and] at he'
    refine ⟨e, ⟨he'.1, he'.2, by rw [lab_eq]; exact hl⟩, ?_⟩
    rintro e' ⟨h1', h2', h3'⟩
    have he'm : e' ∈ EG := by simp [hEG, h1', h2']
    rw [lab_eq] at h3'
    have := hP.2.2.2.2 _ (g_mem e' he'm) _ (g_mem e he) (by rw [h3', hl])
    exact g_inj he'm he this

end Transfer

/-! ## Canonical tree T(a,b,c|d|e,f) on ℕ-names

`u = 0`, `v = 1`, arm `X ∈ {2,…,7}` position `k ≥ 1` is `X + 8k`.
Arms: 2,3,4 at `u` (lengths a,b,c), 5 = interior of the u–v path (length d−1), 6,7 at `v`. -/

/-- arm lengths -/
def armLen (a b c d e f X : ℕ) : ℕ :=
  if X = 2 then a else if X = 3 then b else if X = 4 then c else
  if X = 5 then d - 1 else if X = 6 then e else if X = 7 then f else 0

/-- root of arm `X` -/
def armRoot (X : ℕ) : ℕ := if X ≤ 5 then 0 else 1

/-- last vertex of the u–v path before `v` -/
def dEnd (d : ℕ) : ℕ := if 2 ≤ d then 5 + 8 * (d - 1) else 0

/-- canonical parent function (tree rooted at `u = 0`) -/
def Tpar (d : ℕ) (x : ℕ) : ℕ :=
  if x = 0 then 0 else if x = 1 then dEnd d else
  if 2 ≤ x / 8 then x - 8 else armRoot (x % 8)

/-- canonical adjacency (symmetric parent relation) -/
def Tadj (d : ℕ) (x y : ℕ) : Prop := (x ≠ 0 ∧ Tpar d x = y) ∨ (y ≠ 0 ∧ Tpar d y = x)

/-- canonical vertex set -/
def Tset (a b c d e f : ℕ) : Finset ℕ :=
  {0, 1} ∪ (Finset.Icc 2 7).biUnion (fun X => (Finset.Icc 1 (armLen a b c d e f X)).image
    (fun k => X + 8 * k))

theorem mem_Tset {a b c d e f x : ℕ} :
    x ∈ Tset a b c d e f ↔ x = 0 ∨ x = 1 ∨
      ∃ X k, 2 ≤ X ∧ X ≤ 7 ∧ 1 ≤ k ∧ k ≤ armLen a b c d e f X ∧ x = X + 8 * k := by
  unfold Tset
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_biUnion,
    Finset.mem_Icc, Finset.mem_image]
  constructor
  · rintro ((h | h) | ⟨X, ⟨h1, h2⟩, k, ⟨k1, k2⟩, rfl⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨X, k, h1, h2, k1, k2, rfl⟩)
  · rintro (h | h | ⟨X, k, h1, h2, k1, k2, rfl⟩)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr ⟨X, ⟨h1, h2⟩, k, ⟨k1, k2⟩, rfl⟩

theorem Tadj_symm (d : ℕ) : ∀ x y, Tadj d x y → Tadj d y x := by
  intro x y h; rcases h with h | h
  · exact Or.inr h
  · exact Or.inl h

theorem Tpar_arm (d X k : ℕ) (hX : 2 ≤ X ∧ X ≤ 7) (hk : 1 ≤ k) :
    Tpar d (X + 8 * k) = if 2 ≤ k then X + 8 * (k - 1) else armRoot X := by
  unfold Tpar
  have h1 : X + 8 * k ≠ 0 := by omega
  have h2 : X + 8 * k ≠ 1 := by omega
  have h3 : (X + 8 * k) / 8 = k := by omega
  have h4 : (X + 8 * k) % 8 = X := by omega
  rw [if_neg h1, if_neg h2, h3, h4]
  split_ifs <;> omega

theorem armLen_2 (a b c d e f : ℕ) : armLen a b c d e f 2 = a := rfl
theorem armLen_3 (a b c d e f : ℕ) : armLen a b c d e f 3 = b := rfl
theorem armLen_4 (a b c d e f : ℕ) : armLen a b c d e f 4 = c := rfl
theorem armLen_5 (a b c d e f : ℕ) : armLen a b c d e f 5 = d - 1 := rfl
theorem armLen_6 (a b c d e f : ℕ) : armLen a b c d e f 6 = e := rfl
theorem armLen_7 (a b c d e f : ℕ) : armLen a b c d e f 7 = f := rfl

/-! ## Structure of Branch43 trees -/

section Struct
variable {n : ℕ} {G : SimpleGraph (Fin n)}

theorem nbr_root_depth (hT : G.IsTree) {u y : Fin n} (h : G.Adj u y) :
    G.dist u y = 1 ∧ tpar hT u y = u := by
  rcases adj_iff_par hT u h with ⟨_, h2, h3⟩ | ⟨h1, _, _⟩
  · rw [SimpleGraph.dist_self] at h3; exact ⟨by omega, h2⟩
  · exact absurd rfl h1

theorem anc_one_adj (hT : G.IsTree) {u x : Fin n} (hx : x ≠ u) :
    G.Adj u (anc hT u x 1) := by
  have hd : 1 ≤ G.dist u x := dist_pos_of_ne hT hx
  have h1 := anc_dist hT u x hd
  have hne : anc hT u x 1 ≠ u := by
    intro e; rw [e, SimpleGraph.dist_self] at h1; omega
  obtain ⟨hadj, hdd⟩ := tpar_spec hT u (anc hT u x 1) hne
  rw [h1] at hdd
  have : tpar hT u (anc hT u x 1) = u := eq_of_dist_zero hT (by omega)
  rw [this] at hadj
  exact hadj

theorem anc_one_ne_root (hT : G.IsTree) {u x : Fin n} (hx : x ≠ u) : anc hT u x 1 ≠ u := by
  have h1 := anc_dist hT u x (dist_pos_of_ne hT hx)
  intro e; rw [e, SimpleGraph.dist_self] at h1; omega

/-- the branch of a vertex is inherited from its parent -/
theorem anc_one_tpar (hT : G.IsTree) {u x : Fin n} (hx : x ≠ u) (h2 : 2 ≤ G.dist u x) :
    anc hT u (tpar hT u x) 1 = anc hT u x 1 :=
  anc_tpar hT u x hx (by omega)

/-- neighbours of a non-root vertex: its parent and its children -/
theorem nbr_cases (hT : G.IsTree) {u q y : Fin n} (h : G.Adj q y) :
    (tpar hT u y = q ∧ y ≠ u ∧ G.dist u y = G.dist u q + 1) ∨
    (q ≠ u ∧ tpar hT u q = y ∧ G.dist u q = G.dist u y + 1) := by
  rcases adj_iff_par hT u h with ⟨a, b, c⟩ | ⟨a, b, c⟩
  · exact Or.inl ⟨b, a, c⟩
  · exact Or.inr ⟨a, b, c⟩

end Struct

/-! ## Setup data for a Branch43 tree -/

/-- the branch data of a Branch43 tree rooted at `u` -/
structure B43Setup {n : ℕ} (G : SimpleGraph (Fin n)) where
  hT : G.IsTree
  u : Fin n
  v : Fin n
  wa : Fin n
  wb : Fin n
  wc : Fin n
  ce : Fin n
  cf : Fin n
  huv : v ≠ u
  hdeg : ∀ q, q ≠ u → q ≠ v → Math15.Graceful.degree G q ≤ 2
  /-- every non-root vertex lies in exactly one of the four branches -/
  hbr : ∀ x, x ≠ u → anc hT u x 1 = wa ∨ anc hT u x 1 = wb ∨ anc hT u x 1 = wc ∨
    anc hT u x 1 = anc hT u v 1
  hwa : G.Adj u wa
  hwb : G.Adj u wb
  hwc : G.Adj u wc
  hab : wa ≠ wb
  hac : wa ≠ wc
  hbc : wb ≠ wc
  had : wa ≠ anc hT u v 1
  hbd : wb ≠ anc hT u v 1
  hcd : wc ≠ anc hT u v 1
  hce : tpar hT u ce = v ∧ ce ≠ u ∧ G.dist u ce = G.dist u v + 1
  hcf : tpar hT u cf = v ∧ cf ≠ u ∧ G.dist u cf = G.dist u v + 1
  hef : ce ≠ cf
  /-- every vertex below `v` lies in the subtree of `ce` or `cf` -/
  hsub : ∀ x, x ≠ u → anc hT u x 1 = anc hT u v 1 → G.dist u v < G.dist u x →
    anc hT u x (G.dist u v + 1) = ce ∨ anc hT u x (G.dist u v + 1) = cf

namespace B43Setup
variable {n : ℕ} {G : SimpleGraph (Fin n)} (S : B43Setup G)

theorem dist_wa : G.dist S.u S.wa = 1 := (nbr_root_depth S.hT S.hwa).1
theorem dist_wb : G.dist S.u S.wb = 1 := (nbr_root_depth S.hT S.hwb).1
theorem dist_wc : G.dist S.u S.wc = 1 := (nbr_root_depth S.hT S.hwc).1

theorem dv_pos : 1 ≤ G.dist S.u S.v := dist_pos_of_ne S.hT S.huv

theorem ne_root_of_pos {x : Fin n} (h : 1 ≤ G.dist S.u x) : x ≠ S.u := by
  intro e; rw [e, SimpleGraph.dist_self] at h; omega

/-- uniqueness in the three u-arms -/
theorem arm_uniq {w : Fin n} (hw : w = S.wa ∨ w = S.wb ∨ w = S.wc) {x y : Fin n}
    (hx : x ≠ S.u) (hy : y ≠ S.u) (ax : anc S.hT S.u x 1 = w) (ay : anc S.hT S.u y 1 = w)
    (hxy : G.dist S.u x = G.dist S.u y) : x = y := by
  have dw : G.dist S.u w = 1 := by
    rcases hw with rfl | rfl | rfl
    · exact S.dist_wa
    · exact S.dist_wb
    · exact S.dist_wc
  have hwd : w ≠ anc S.hT S.u S.v 1 := by
    rcases hw with rfl | rfl | rfl
    · exact S.had
    · exact S.hbd
    · exact S.hcd
  refine chain_uniq S.hT S.u w (G.dist S.u x + 1) (by omega) ?_ x y (by rw [dw]; exact dist_pos_of_ne S.hT hx)
    (by omega) (by rw [dw]; exact ax) (by rw [dw]; exact ay) hxy
  intro q h1 _ h3
  rw [dw] at h1 h3
  apply S.hdeg q (S.ne_root_of_pos h1)
  intro e; rw [e] at h3; exact hwd h3.symm

/-- uniqueness on the u–v path (depths ≤ dist u v) -/
theorem dpath_uniq {x y : Fin n} (hx : x ≠ S.u) (hy : y ≠ S.u)
    (ax : anc S.hT S.u x 1 = anc S.hT S.u S.v 1) (ay : anc S.hT S.u y 1 = anc S.hT S.u S.v 1)
    (hxv : G.dist S.u x ≤ G.dist S.u S.v) (hxy : G.dist S.u x = G.dist S.u y) : x = y := by
  set wd := anc S.hT S.u S.v 1 with hwd
  have dw : G.dist S.u wd = 1 := anc_dist S.hT S.u S.v S.dv_pos
  refine chain_uniq S.hT S.u wd (G.dist S.u S.v) (by omega) ?_ x y
    (by rw [dw]; exact dist_pos_of_ne S.hT hx) hxv (by rw [dw]; exact ax) (by rw [dw]; exact ay) hxy
  intro q h1 h2 _
  rw [dw] at h1
  apply S.hdeg q (S.ne_root_of_pos h1)
  intro e; rw [e] at h2; omega

/-- below `v`, the ancestor at depth `dist u v` is `v` -/
theorem anc_v {x : Fin n} (hx : x ≠ S.u) (ax : anc S.hT S.u x 1 = anc S.hT S.u S.v 1)
    (hxv : G.dist S.u S.v ≤ G.dist S.u x) : anc S.hT S.u x (G.dist S.u S.v) = S.v := by
  have h1 := anc_dist S.hT S.u x hxv
  refine S.dpath_uniq (S.ne_root_of_pos (by rw [h1]; exact S.dv_pos)) S.huv ?_ rfl (le_of_eq h1) h1
  rw [anc_anc S.hT S.u x (by have := S.dv_pos; omega) hxv]; exact ax

/-- uniqueness in the two v-subtrees -/
theorem sub_uniq {w : Fin n} (hw : w = S.ce ∨ w = S.cf) {x y : Fin n}
    (ax : anc S.hT S.u x (G.dist S.u S.v + 1) = w) (ay : anc S.hT S.u y (G.dist S.u S.v + 1) = w)
    (hx : G.dist S.u S.v + 1 ≤ G.dist S.u x) (hxy : G.dist S.u x = G.dist S.u y) : x = y := by
  have dw : G.dist S.u w = G.dist S.u S.v + 1 := by
    rcases hw with rfl | rfl
    · exact S.hce.2.2
    · exact S.hcf.2.2
  refine chain_uniq S.hT S.u w (G.dist S.u x + 1) (by have := S.dv_pos; omega) ?_ x y
    (by rw [dw]; exact hx) (by omega) (by rw [dw]; exact ax) (by rw [dw]; exact ay) hxy
  intro q h1 _ _
  rw [dw] at h1
  apply S.hdeg q (S.ne_root_of_pos (by have := S.dv_pos; omega))
  intro e; rw [e] at h1; omega

end B43Setup

/-! ## The canonical map φ -/

namespace B43Setup
variable {n : ℕ} {G : SimpleGraph (Fin n)} (S : B43Setup G)

/-- the canonical name of a vertex -/
noncomputable def phi (x : Fin n) : ℕ := by
  classical
  exact if x = S.u then 0 else if x = S.v then 1
  else if anc S.hT S.u x 1 = S.wa then 2 + 8 * G.dist S.u x
  else if anc S.hT S.u x 1 = S.wb then 3 + 8 * G.dist S.u x
  else if anc S.hT S.u x 1 = S.wc then 4 + 8 * G.dist S.u x
  else if G.dist S.u x < G.dist S.u S.v then 5 + 8 * G.dist S.u x
  else if anc S.hT S.u x (G.dist S.u S.v + 1) = S.ce then 6 + 8 * (G.dist S.u x - G.dist S.u S.v)
  else 7 + 8 * (G.dist S.u x - G.dist S.u S.v)

theorem anc_v_one : anc S.hT S.u S.v 1 ≠ S.wa ∧ anc S.hT S.u S.v 1 ≠ S.wb ∧
    anc S.hT S.u S.v 1 ≠ S.wc := ⟨S.had.symm, S.hbd.symm, S.hcd.symm⟩

/-- the categories of vertices, with the value of `phi` -/
theorem phi_cases (x : Fin n) :
    (x = S.u ∧ S.phi x = 0) ∨
    (x = S.v ∧ S.phi x = 1) ∨
    (x ≠ S.u ∧ x ≠ S.v ∧ anc S.hT S.u x 1 = S.wa ∧ S.phi x = 2 + 8 * G.dist S.u x) ∨
    (x ≠ S.u ∧ x ≠ S.v ∧ anc S.hT S.u x 1 = S.wb ∧ S.phi x = 3 + 8 * G.dist S.u x) ∨
    (x ≠ S.u ∧ x ≠ S.v ∧ anc S.hT S.u x 1 = S.wc ∧ S.phi x = 4 + 8 * G.dist S.u x) ∨
    (x ≠ S.u ∧ x ≠ S.v ∧ anc S.hT S.u x 1 = anc S.hT S.u S.v 1 ∧
      G.dist S.u x < G.dist S.u S.v ∧ S.phi x = 5 + 8 * G.dist S.u x) ∨
    (x ≠ S.u ∧ anc S.hT S.u x 1 = anc S.hT S.u S.v 1 ∧ G.dist S.u S.v < G.dist S.u x ∧
      anc S.hT S.u x (G.dist S.u S.v + 1) = S.ce ∧
      S.phi x = 6 + 8 * (G.dist S.u x - G.dist S.u S.v)) ∨
    (x ≠ S.u ∧ anc S.hT S.u x 1 = anc S.hT S.u S.v 1 ∧ G.dist S.u S.v < G.dist S.u x ∧
      anc S.hT S.u x (G.dist S.u S.v + 1) = S.cf ∧
      S.phi x = 7 + 8 * (G.dist S.u x - G.dist S.u S.v)) := by
  classical
  have hv := S.anc_v_one
  by_cases hu : x = S.u
  · left; exact ⟨hu, by simp [phi, hu]⟩
  by_cases hvx : x = S.v
  · right; left; exact ⟨hvx, by simp [phi, hvx, S.huv]⟩
  rcases S.hbr x hu with ha | hb | hc | hd
  · right; right; left; exact ⟨hu, hvx, ha, by simp [phi, hu, hvx, ha]⟩
  · have : anc S.hT S.u x 1 ≠ S.wa := by rw [hb]; exact S.hab.symm
    right; right; right; left; exact ⟨hu, hvx, hb, by simp [phi, hu, hvx, hb, Ne.symm S.hab]⟩
  · have h1 : anc S.hT S.u x 1 ≠ S.wa := by rw [hc]; exact S.hac.symm
    have h2 : anc S.hT S.u x 1 ≠ S.wb := by rw [hc]; exact S.hbc.symm
    right; right; right; right; left
    exact ⟨hu, hvx, hc, by simp [phi, hu, hvx, hc, Ne.symm S.hac, Ne.symm S.hbc]⟩
  · have h1 : anc S.hT S.u x 1 ≠ S.wa := by rw [hd]; exact hv.1
    have h2 : anc S.hT S.u x 1 ≠ S.wb := by rw [hd]; exact hv.2.1
    have h3 : anc S.hT S.u x 1 ≠ S.wc := by rw [hd]; exact hv.2.2
    rcases lt_trichotomy (G.dist S.u x) (G.dist S.u S.v) with hl | he | hg
    · right; right; right; right; right; left
      exact ⟨hu, hvx, hd, hl, by simp [phi, hu, hvx, h1, h2, h3, hl]⟩
    · exact absurd (S.dpath_uniq hu S.huv hd rfl (le_of_eq he) he) hvx
    · have hnl : ¬ G.dist S.u x < G.dist S.u S.v := by omega
      rcases S.hsub x hu hd hg with he' | hf'
      · right; right; right; right; right; right; left
        exact ⟨hu, hd, hg, he', by simp [phi, hu, hvx, h1, h2, h3, hnl, he']⟩
      · have hne : anc S.hT S.u x (G.dist S.u S.v + 1) ≠ S.ce := by rw [hf']; exact S.hef.symm
        right; right; right; right; right; right; right
        exact ⟨hu, hd, hg, hf', by simp [phi, hu, hvx, h1, h2, h3, hnl, hne]⟩

theorem phi_armA {x : Fin n} (hx : x ≠ S.u) (ax : anc S.hT S.u x 1 = S.wa) :
    S.phi x = 2 + 8 * G.dist S.u x := by
  rcases S.phi_cases x with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, _, _, p⟩ | ⟨_, _, a, _⟩ | ⟨_, _, a, _⟩ |
      ⟨_, _, a, _, _⟩ | ⟨_, a, _, _, _⟩ | ⟨_, a, _, _, _⟩
  · exact absurd h hx
  · rw [h] at ax; exact absurd ax S.anc_v_one.1
  · exact p
  · rw [ax] at a; exact absurd a S.hab
  · rw [ax] at a; exact absurd a S.hac
  all_goals (rw [ax] at a; exact absurd a S.had)

theorem phi_armB {x : Fin n} (hx : x ≠ S.u) (ax : anc S.hT S.u x 1 = S.wb) :
    S.phi x = 3 + 8 * G.dist S.u x := by
  rcases S.phi_cases x with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, _, a, _⟩ | ⟨_, _, _, p⟩ | ⟨_, _, a, _⟩ |
      ⟨_, _, a, _, _⟩ | ⟨_, a, _, _, _⟩ | ⟨_, a, _, _, _⟩
  · exact absurd h hx
  · rw [h] at ax; exact absurd ax S.anc_v_one.2.1
  · rw [ax] at a; exact absurd a.symm S.hab
  · exact p
  · rw [ax] at a; exact absurd a S.hbc
  all_goals (rw [ax] at a; exact absurd a S.hbd)

theorem phi_armC {x : Fin n} (hx : x ≠ S.u) (ax : anc S.hT S.u x 1 = S.wc) :
    S.phi x = 4 + 8 * G.dist S.u x := by
  rcases S.phi_cases x with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, _, a, _⟩ | ⟨_, _, a, _⟩ | ⟨_, _, _, p⟩ |
      ⟨_, _, a, _, _⟩ | ⟨_, a, _, _, _⟩ | ⟨_, a, _, _, _⟩
  · exact absurd h hx
  · rw [h] at ax; exact absurd ax S.anc_v_one.2.2
  · rw [ax] at a; exact absurd a.symm S.hac
  · rw [ax] at a; exact absurd a.symm S.hbc
  · exact p
  all_goals (rw [ax] at a; exact absurd a S.hcd)

theorem phi_dpath {x : Fin n} (hx : x ≠ S.u) (ax : anc S.hT S.u x 1 = anc S.hT S.u S.v 1)
    (dx : G.dist S.u x < G.dist S.u S.v) : S.phi x = 5 + 8 * G.dist S.u x := by
  rcases S.phi_cases x with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, _, a, _⟩ | ⟨_, _, a, _⟩ | ⟨_, _, a, _⟩ |
      ⟨_, _, _, _, p⟩ | ⟨_, _, d, _, _⟩ | ⟨_, _, d, _, _⟩
  · exact absurd h hx
  · rw [h] at dx; omega
  · rw [ax] at a; exact absurd a S.anc_v_one.1
  · rw [ax] at a; exact absurd a S.anc_v_one.2.1
  · rw [ax] at a; exact absurd a S.anc_v_one.2.2
  · exact p
  all_goals omega

theorem phi_subE {x : Fin n} (hx : x ≠ S.u) (ax : anc S.hT S.u x 1 = anc S.hT S.u S.v 1)
    (dx : G.dist S.u S.v < G.dist S.u x) (sx : anc S.hT S.u x (G.dist S.u S.v + 1) = S.ce) :
    S.phi x = 6 + 8 * (G.dist S.u x - G.dist S.u S.v) := by
  rcases S.phi_cases x with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, _, a, _⟩ | ⟨_, _, a, _⟩ | ⟨_, _, a, _⟩ |
      ⟨_, _, _, d, _⟩ | ⟨_, _, _, _, p⟩ | ⟨_, _, _, s, _⟩
  · exact absurd h hx
  · rw [h] at dx; omega
  · rw [ax] at a; exact absurd a S.anc_v_one.1
  · rw [ax] at a; exact absurd a S.anc_v_one.2.1
  · rw [ax] at a; exact absurd a S.anc_v_one.2.2
  · omega
  · exact p
  · rw [sx] at s; exact absurd s S.hef

theorem phi_subF {x : Fin n} (hx : x ≠ S.u) (ax : anc S.hT S.u x 1 = anc S.hT S.u S.v 1)
    (dx : G.dist S.u S.v < G.dist S.u x) (sx : anc S.hT S.u x (G.dist S.u S.v + 1) = S.cf) :
    S.phi x = 7 + 8 * (G.dist S.u x - G.dist S.u S.v) := by
  rcases S.phi_cases x with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, _, a, _⟩ | ⟨_, _, a, _⟩ | ⟨_, _, a, _⟩ |
      ⟨_, _, _, d, _⟩ | ⟨_, _, _, s, _⟩ | ⟨_, _, _, _, p⟩
  · exact absurd h hx
  · rw [h] at dx; omega
  · rw [ax] at a; exact absurd a S.anc_v_one.1
  · rw [ax] at a; exact absurd a S.anc_v_one.2.1
  · rw [ax] at a; exact absurd a S.anc_v_one.2.2
  · omega
  · rw [sx] at s; exact absurd s.symm S.hef
  · exact p

theorem phi_inj : Function.Injective S.phi := by
  intro x y h
  rcases S.phi_cases x with ⟨hx, px⟩ | ⟨hx, px⟩ | ⟨xu, xv, ax, px⟩ | ⟨xu, xv, ax, px⟩ |
      ⟨xu, xv, ax, px⟩ | ⟨xu, xv, ax, dx, px⟩ | ⟨xu, ax, dx, sx, px⟩ | ⟨xu, ax, dx, sx, px⟩ <;>
  rcases S.phi_cases y with ⟨hy, py⟩ | ⟨hy, py⟩ | ⟨yu, yv, ay, py⟩ | ⟨yu, yv, ay, py⟩ |
      ⟨yu, yv, ay, py⟩ | ⟨yu, yv, ay, dy, py⟩ | ⟨yu, ay, dy, sy, py⟩ | ⟨yu, ay, dy, sy, py⟩ <;>
  rw [px, py] at h
  all_goals first
    | omega
    | (rw [hx, hy])
    | exact S.arm_uniq (Or.inl rfl) xu yu ax ay (by omega)
    | exact S.arm_uniq (Or.inr (Or.inl rfl)) xu yu ax ay (by omega)
    | exact S.arm_uniq (Or.inr (Or.inr rfl)) xu yu ax ay (by omega)
    | exact S.dpath_uniq xu yu ax ay (le_of_lt dx) (by omega)
    | exact S.sub_uniq (Or.inl rfl) sx sy (by omega) (by omega)
    | exact S.sub_uniq (Or.inr rfl) sx sy (by omega) (by omega)

theorem phi_u : S.phi S.u = 0 := by
  rcases S.phi_cases S.u with ⟨_, p⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩
  · exact p
  · exact absurd h.symm S.huv
  all_goals exact absurd rfl h

theorem phi_v : S.phi S.v = 1 := by
  rcases S.phi_cases S.v with ⟨h, _⟩ | ⟨_, p⟩ | ⟨_, h, _⟩ | ⟨_, h, _⟩ | ⟨_, h, _⟩ | ⟨_, h, _⟩ |
      ⟨_, _, d, _⟩ | ⟨_, _, d, _⟩
  · exact absurd h S.huv
  · exact p
  all_goals first | exact absurd rfl h | omega

theorem tpar_of_depth_one {x : Fin n} (hx : x ≠ S.u) (h1 : G.dist S.u x = 1) :
    tpar S.hT S.u x = S.u := by
  have := (tpar_spec S.hT S.u x hx).2
  exact eq_of_dist_zero S.hT (by omega)

theorem phi_par {x : Fin n} (hx : x ≠ S.u) :
    S.phi (tpar S.hT S.u x) = Tpar (G.dist S.u S.v) (S.phi x) := by
  have dpar := (tpar_spec S.hT S.u x hx).2
  have dv := S.dv_pos
  have dx1 := dist_pos_of_ne S.hT hx
  rcases S.phi_cases x with ⟨h, _⟩ | ⟨hv, px⟩ | ⟨_, _, ax, px⟩ | ⟨_, _, ax, px⟩ |
      ⟨_, _, ax, px⟩ | ⟨_, _, ax, dx, px⟩ | ⟨_, ax, dx, sx, px⟩ | ⟨_, ax, dx, sx, px⟩
  · exact absurd h hx
  · subst hv
    rw [px]
    unfold Tpar dEnd
    rw [if_neg one_ne_zero, if_pos rfl]
    by_cases h2 : 2 ≤ G.dist S.u S.v
    · rw [if_pos h2]
      have hp : tpar S.hT S.u S.v ≠ S.u := S.ne_root_of_pos (by omega)
      rw [S.phi_dpath hp (anc_one_tpar S.hT hx h2) (by omega)]; omega
    · rw [if_neg h2, S.tpar_of_depth_one hx (by omega), S.phi_u]
  · rw [px, Tpar_arm _ 2 _ (by omega) dx1]
    by_cases h2 : 2 ≤ G.dist S.u x
    · rw [if_pos h2]
      have hp : tpar S.hT S.u x ≠ S.u := S.ne_root_of_pos (by omega)
      have ap := anc_one_tpar S.hT hx h2
      rw [ax] at ap
      rw [S.phi_armA hp ap]; omega
    · rw [if_neg h2, S.tpar_of_depth_one hx (by omega), S.phi_u]
      try simp [armRoot]
  · rw [px, Tpar_arm _ 3 _ (by omega) dx1]
    by_cases h2 : 2 ≤ G.dist S.u x
    · rw [if_pos h2]
      have hp : tpar S.hT S.u x ≠ S.u := S.ne_root_of_pos (by omega)
      have ap := anc_one_tpar S.hT hx h2
      rw [ax] at ap
      rw [S.phi_armB hp ap]; omega
    · rw [if_neg h2, S.tpar_of_depth_one hx (by omega), S.phi_u]
      try simp [armRoot]
  · rw [px, Tpar_arm _ 4 _ (by omega) dx1]
    by_cases h2 : 2 ≤ G.dist S.u x
    · rw [if_pos h2]
      have hp : tpar S.hT S.u x ≠ S.u := S.ne_root_of_pos (by omega)
      have ap := anc_one_tpar S.hT hx h2
      rw [ax] at ap
      rw [S.phi_armC hp ap]; omega
    · rw [if_neg h2, S.tpar_of_depth_one hx (by omega), S.phi_u]
      try simp [armRoot]
  · rw [px, Tpar_arm _ 5 _ (by omega) dx1]
    by_cases h2 : 2 ≤ G.dist S.u x
    · rw [if_pos h2]
      have hp : tpar S.hT S.u x ≠ S.u := S.ne_root_of_pos (by omega)
      have ap := anc_one_tpar S.hT hx h2
      rw [ax] at ap
      rw [S.phi_dpath hp ap (by omega)]; omega
    · rw [if_neg h2, S.tpar_of_depth_one hx (by omega), S.phi_u]
      try simp [armRoot]
  · rw [px, Tpar_arm _ 6 _ (by omega) (by omega)]
    have hp : tpar S.hT S.u x ≠ S.u := S.ne_root_of_pos (by omega)
    have ap := anc_one_tpar S.hT hx (by omega)
    rw [ax] at ap
    by_cases h2 : 2 ≤ G.dist S.u x - G.dist S.u S.v
    · rw [if_pos h2]
      have sp := anc_tpar S.hT S.u x hx (j := G.dist S.u S.v + 1) (by omega)
      rw [sx] at sp
      rw [S.phi_subE hp ap (by omega) sp]; omega
    · rw [if_neg h2]
      have : tpar S.hT S.u x = S.v := S.dpath_uniq hp S.huv ap rfl (by omega) (by omega)
      rw [this, S.phi_v]
      try simp [armRoot]
  · rw [px, Tpar_arm _ 7 _ (by omega) (by omega)]
    have hp : tpar S.hT S.u x ≠ S.u := S.ne_root_of_pos (by omega)
    have ap := anc_one_tpar S.hT hx (by omega)
    rw [ax] at ap
    by_cases h2 : 2 ≤ G.dist S.u x - G.dist S.u S.v
    · rw [if_pos h2]
      have sp := anc_tpar S.hT S.u x hx (j := G.dist S.u S.v + 1) (by omega)
      rw [sx] at sp
      rw [S.phi_subF hp ap (by omega) sp]; omega
    · rw [if_neg h2]
      have : tpar S.hT S.u x = S.v := S.dpath_uniq hp S.huv ap rfl (by omega) (by omega)
      rw [this, S.phi_v]
      try simp [armRoot]

end B43Setup

/-! ## The image of φ is the canonical tree -/

namespace B43Setup
variable {n : ℕ} {G : SimpleGraph (Fin n)} (S : B43Setup G)

/-- length of the u-arm through `w` -/
noncomputable def lenU (w : Fin n) : ℕ :=
  ((Finset.univ : Finset (Fin n)).filter (fun x => x ≠ S.u ∧ anc S.hT S.u x 1 = w)).sup
    (fun x => G.dist S.u x)

/-- length of the v-arm through `c` -/
noncomputable def lenV (c : Fin n) : ℕ :=
  ((Finset.univ : Finset (Fin n)).filter (fun x => x ≠ S.u ∧
    anc S.hT S.u x 1 = anc S.hT S.u S.v 1 ∧ G.dist S.u S.v < G.dist S.u x ∧
    anc S.hT S.u x (G.dist S.u S.v + 1) = c)).sup (fun x => G.dist S.u x - G.dist S.u S.v)

theorem le_lenU {w x : Fin n} (hx : x ≠ S.u) (ax : anc S.hT S.u x 1 = w) :
    G.dist S.u x ≤ S.lenU w := by
  unfold lenU
  exact Finset.le_sup (f := fun x => G.dist S.u x) (by simp [hx, ax])

theorem le_lenV {c x : Fin n} (hx : x ≠ S.u) (ax : anc S.hT S.u x 1 = anc S.hT S.u S.v 1)
    (dx : G.dist S.u S.v < G.dist S.u x) (sx : anc S.hT S.u x (G.dist S.u S.v + 1) = c) :
    G.dist S.u x - G.dist S.u S.v ≤ S.lenV c := by
  unfold lenV
  exact Finset.le_sup (f := fun x => G.dist S.u x - G.dist S.u S.v) (by simp [hx, ax, dx, sx])

theorem self_anc_one {w : Fin n} (hw : G.dist S.u w = 1) : anc S.hT S.u w 1 = w := by
  have := anc_self S.hT S.u w
  rw [hw] at this; exact this

theorem lenU_spec {w : Fin n} (hw : G.dist S.u w = 1) :
    1 ≤ S.lenU w ∧ ∃ x, x ≠ S.u ∧ anc S.hT S.u x 1 = w ∧ G.dist S.u x = S.lenU w := by
  have hwu : w ≠ S.u := S.ne_root_of_pos (by omega)
  have hmem : w ∈ (Finset.univ : Finset (Fin n)).filter
      (fun x => x ≠ S.u ∧ anc S.hT S.u x 1 = w) := by
    simp [hwu, S.self_anc_one hw]
  refine ⟨?_, ?_⟩
  · have := S.le_lenU hwu (S.self_anc_one hw); omega
  · obtain ⟨x, hx, hxe⟩ := Finset.exists_mem_eq_sup _ ⟨w, hmem⟩ (fun x => G.dist S.u x)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    exact ⟨x, hx.1, hx.2, by unfold lenU; rw [hxe]⟩

theorem c_props {c : Fin n} (hc : tpar S.hT S.u c = S.v ∧ c ≠ S.u ∧
    G.dist S.u c = G.dist S.u S.v + 1) :
    anc S.hT S.u c 1 = anc S.hT S.u S.v 1 ∧ anc S.hT S.u c (G.dist S.u S.v + 1) = c := by
  obtain ⟨h1, h2, h3⟩ := hc
  refine ⟨?_, ?_⟩
  · have := anc_tpar S.hT S.u c h2 (j := 1) (by have := S.dv_pos; omega)
    rw [h1] at this; exact this.symm
  · have := anc_self S.hT S.u c
    rw [h3] at this; exact this

theorem lenV_spec {c : Fin n} (hc : tpar S.hT S.u c = S.v ∧ c ≠ S.u ∧
    G.dist S.u c = G.dist S.u S.v + 1) :
    1 ≤ S.lenV c ∧ ∃ x, x ≠ S.u ∧ anc S.hT S.u x 1 = anc S.hT S.u S.v 1 ∧
      G.dist S.u S.v < G.dist S.u x ∧ anc S.hT S.u x (G.dist S.u S.v + 1) = c ∧
      G.dist S.u x - G.dist S.u S.v = S.lenV c := by
  obtain ⟨p1, p2⟩ := S.c_props hc
  have hmem : c ∈ (Finset.univ : Finset (Fin n)).filter (fun x => x ≠ S.u ∧
      anc S.hT S.u x 1 = anc S.hT S.u S.v 1 ∧ G.dist S.u S.v < G.dist S.u x ∧
      anc S.hT S.u x (G.dist S.u S.v + 1) = c) := by
    simp [hc.2.1, p1, p2, hc.2.2]
  refine ⟨?_, ?_⟩
  · have := S.le_lenV hc.2.1 p1 (by omega) p2; omega
  · obtain ⟨x, hx, hxe⟩ := Finset.exists_mem_eq_sup _ ⟨c, hmem⟩
      (fun x => G.dist S.u x - G.dist S.u S.v)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    exact ⟨x, hx.1, hx.2.1, hx.2.2.1, hx.2.2.2, by unfold lenV; rw [hxe]⟩

/-- the arm lengths -/
noncomputable def La : ℕ := S.lenU S.wa
noncomputable def Lb : ℕ := S.lenU S.wb
noncomputable def Lc : ℕ := S.lenU S.wc
noncomputable def Le : ℕ := S.lenV S.ce
noncomputable def Lf : ℕ := S.lenV S.cf

theorem phi_mem (x : Fin n) :
    S.phi x ∈ Tset S.La S.Lb S.Lc (G.dist S.u S.v) S.Le S.Lf := by
  rw [mem_Tset]
  rcases S.phi_cases x with ⟨_, px⟩ | ⟨_, px⟩ | ⟨xu, _, ax, px⟩ | ⟨xu, _, ax, px⟩ |
      ⟨xu, _, ax, px⟩ | ⟨xu, _, ax, dx, px⟩ | ⟨xu, ax, dx, sx, px⟩ | ⟨xu, ax, dx, sx, px⟩
  · exact Or.inl px
  · exact Or.inr (Or.inl px)
  · have := S.le_lenU xu ax
    exact Or.inr (Or.inr ⟨2, G.dist S.u x, by omega, by omega, dist_pos_of_ne S.hT xu,
      by rw [armLen_2]; exact this, px⟩)
  · have := S.le_lenU xu ax
    exact Or.inr (Or.inr ⟨3, G.dist S.u x, by omega, by omega, dist_pos_of_ne S.hT xu,
      by rw [armLen_3]; exact this, px⟩)
  · have := S.le_lenU xu ax
    exact Or.inr (Or.inr ⟨4, G.dist S.u x, by omega, by omega, dist_pos_of_ne S.hT xu,
      by rw [armLen_4]; exact this, px⟩)
  · exact Or.inr (Or.inr ⟨5, G.dist S.u x, by omega, by omega, dist_pos_of_ne S.hT xu,
      by rw [armLen_5]; omega, px⟩)
  · have := S.le_lenV xu ax dx sx
    exact Or.inr (Or.inr ⟨6, G.dist S.u x - G.dist S.u S.v, by omega, by omega, by omega,
      by rw [armLen_6]; exact this, px⟩)
  · have := S.le_lenV xu ax dx sx
    exact Or.inr (Or.inr ⟨7, G.dist S.u x - G.dist S.u S.v, by omega, by omega, by omega,
      by rw [armLen_7]; exact this, px⟩)

/-- a u-arm vertex at each depth up to the arm length -/
theorem uarm_at {w : Fin n} (hw : G.dist S.u w = 1) {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ S.lenU w) :
    ∃ y, y ≠ S.u ∧ anc S.hT S.u y 1 = w ∧ G.dist S.u y = k := by
  obtain ⟨_, x, xu, ax, dx⟩ := S.lenU_spec hw
  refine ⟨anc S.hT S.u x k, S.ne_root_of_pos ?_, ?_, ?_⟩
  · rw [anc_dist S.hT S.u x (by omega)]; exact hk1
  · rw [anc_anc S.hT S.u x hk1 (by omega)]; exact ax
  · exact anc_dist S.hT S.u x (by omega)

theorem varm_at {c : Fin n} (hc : tpar S.hT S.u c = S.v ∧ c ≠ S.u ∧
    G.dist S.u c = G.dist S.u S.v + 1) {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ S.lenV c) :
    ∃ y, y ≠ S.u ∧ anc S.hT S.u y 1 = anc S.hT S.u S.v 1 ∧
      G.dist S.u S.v < G.dist S.u y ∧ anc S.hT S.u y (G.dist S.u S.v + 1) = c ∧
      G.dist S.u y = G.dist S.u S.v + k := by
  obtain ⟨_, x, xu, ax, dx, sx, ex⟩ := S.lenV_spec hc
  have dv := S.dv_pos
  have hd : G.dist S.u (anc S.hT S.u x (G.dist S.u S.v + k)) = G.dist S.u S.v + k :=
    anc_dist S.hT S.u x (by omega)
  refine ⟨anc S.hT S.u x (G.dist S.u S.v + k), S.ne_root_of_pos (by omega), ?_, by omega, ?_, hd⟩
  · rw [anc_anc S.hT S.u x (by omega) (by omega)]; exact ax
  · rw [anc_anc S.hT S.u x (by omega) (by omega)]; exact sx

theorem phi_surj (s : ℕ) (hs : s ∈ Tset S.La S.Lb S.Lc (G.dist S.u S.v) S.Le S.Lf) :
    ∃ x, S.phi x = s := by
  rw [mem_Tset] at hs
  rcases hs with rfl | rfl | ⟨X, k, h2, h7, hk1, hk, rfl⟩
  · exact ⟨S.u, S.phi_u⟩
  · exact ⟨S.v, S.phi_v⟩
  have hX : X = 2 ∨ X = 3 ∨ X = 4 ∨ X = 5 ∨ X = 6 ∨ X = 7 := by omega
  rcases hX with rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨y, yu, ay, dy⟩ := S.uarm_at S.dist_wa hk1 (by rw [armLen_2] at hk; exact hk)
    exact ⟨y, by rw [S.phi_armA yu ay, dy]⟩
  · obtain ⟨y, yu, ay, dy⟩ := S.uarm_at S.dist_wb hk1 (by rw [armLen_3] at hk; exact hk)
    exact ⟨y, by rw [S.phi_armB yu ay, dy]⟩
  · obtain ⟨y, yu, ay, dy⟩ := S.uarm_at S.dist_wc hk1 (by rw [armLen_4] at hk; exact hk)
    exact ⟨y, by rw [S.phi_armC yu ay, dy]⟩
  · rw [armLen_5] at hk
    have hkd : k ≤ G.dist S.u S.v := by omega
    have yd := anc_dist S.hT S.u S.v hkd
    refine ⟨anc S.hT S.u S.v k, ?_⟩
    rw [S.phi_dpath (S.ne_root_of_pos (by omega)) (anc_anc S.hT S.u S.v hk1 hkd) (by omega), yd]
  · obtain ⟨y, yu, ay, dy, sy, ey⟩ := S.varm_at S.hce hk1 (by rw [armLen_6] at hk; exact hk)
    exact ⟨y, by rw [S.phi_subE yu ay dy sy, ey]; omega⟩
  · obtain ⟨y, yu, ay, dy, sy, ey⟩ := S.varm_at S.hcf hk1 (by rw [armLen_7] at hk; exact hk)
    exact ⟨y, by rw [S.phi_subF yu ay dy sy, ey]; omega⟩

theorem phi_ne_zero {x : Fin n} (hx : x ≠ S.u) : S.phi x ≠ 0 := by
  intro e; apply hx; apply S.phi_inj; rw [e, S.phi_u]

theorem phi_adj (x y : Fin n) : G.Adj x y ↔ Tadj (G.dist S.u S.v) (S.phi x) (S.phi y) := by
  constructor
  · intro h
    rcases nbr_cases S.hT (u := S.u) h with ⟨hp, hy, _⟩ | ⟨hx, hp, _⟩
    · exact Or.inr ⟨S.phi_ne_zero hy, by rw [← S.phi_par hy, hp]⟩
    · exact Or.inl ⟨S.phi_ne_zero hx, by rw [← S.phi_par hx, hp]⟩
  · rintro (⟨h0, hp⟩ | ⟨h0, hp⟩)
    · have hx : x ≠ S.u := by intro e; rw [e, S.phi_u] at h0; exact h0 rfl
      rw [← S.phi_par hx] at hp
      rw [← S.phi_inj hp]; exact (tpar_spec S.hT S.u x hx).1.symm
    · have hy : y ≠ S.u := by intro e; rw [e, S.phi_u] at h0; exact h0 rfl
      rw [← S.phi_par hy] at hp
      rw [← S.phi_inj hp]; exact (tpar_spec S.hT S.u y hy).1

end B43Setup

/-! ## Building the setup from `Branch43`, and the reduction to canonical trees -/

section Build
variable {n : ℕ} {G : SimpleGraph (Fin n)}

theorem tpar_anc (hT : G.IsTree) (u x : Fin n) {j : ℕ} (hj : 1 ≤ j) (hjx : j ≤ G.dist u x) :
    tpar hT u (anc hT u x j) = anc hT u x (j - 1) := by
  unfold anc
  have e : G.dist u x - (j - 1) = (G.dist u x - j) + 1 := by omega
  rw [e, Function.iterate_succ_apply']

theorem nbr_finset (q : Fin n) :
    ∃ N : Finset (Fin n), N.card = Math15.Graceful.degree G q ∧ ∀ z, z ∈ N ↔ G.Adj q z := by
  classical
  refine ⟨(Finset.univ : Finset (Fin n)).filter (G.Adj q), ?_, fun z => by simp⟩
  unfold Math15.Graceful.degree
  rfl

theorem build_setup (hT : G.IsTree) {u v : Fin n} (hb : Math15.Graceful.Branch43 G u v) :
    Nonempty (B43Setup G) := by
  classical
  obtain ⟨huv, hdu, hdv, hdeg⟩ := hb
  have hvu : v ≠ u := Ne.symm huv
  have dv : 1 ≤ G.dist u v := dist_pos_of_ne hT hvu
  have dwd : G.dist u (anc hT u v 1) = 1 := anc_dist hT u v dv
  -- the three other neighbours of u
  obtain ⟨N, hN, hNm⟩ := nbr_finset (G := G) u
  rw [hdu] at hN
  have wdN : anc hT u v 1 ∈ N := (hNm _).2 (anc_one_adj hT hvu)
  have h3 : (N.erase (anc hT u v 1)).card = 3 := by rw [Finset.card_erase_of_mem wdN, hN]
  obtain ⟨wa, wb, wc, hab, hac, hbc, hE⟩ := Finset.card_eq_three.mp h3
  have memE : ∀ z, z ∈ N.erase (anc hT u v 1) ↔ z = wa ∨ z = wb ∨ z = wc := by
    intro z; rw [hE]; simp
  have ha := (memE wa).2 (Or.inl rfl)
  have hb' := (memE wb).2 (Or.inr (Or.inl rfl))
  have hc := (memE wc).2 (Or.inr (Or.inr rfl))
  rw [Finset.mem_erase] at ha hb' hc
  -- the two children of v
  obtain ⟨M, hM, hMm⟩ := nbr_finset (G := G) v
  rw [hdv] at hM
  have pM : tpar hT u v ∈ M := (hMm _).2 (tpar_spec hT u v hvu).1.symm
  have h2 : (M.erase (tpar hT u v)).card = 2 := by rw [Finset.card_erase_of_mem pM, hM]
  obtain ⟨ce, cf, hef, hE2⟩ := Finset.card_eq_two.mp h2
  have memE2 : ∀ z, z ∈ M.erase (tpar hT u v) ↔ z = ce ∨ z = cf := by
    intro z; rw [hE2]; simp
  have child : ∀ c, c ∈ M.erase (tpar hT u v) →
      tpar hT u c = v ∧ c ≠ u ∧ G.dist u c = G.dist u v + 1 := by
    intro c hc
    rw [Finset.mem_erase] at hc
    rcases adj_iff_par hT u ((hMm c).1 hc.2) with ⟨a1, a2, a3⟩ | ⟨_, a2, _⟩
    · exact ⟨a2, a1, a3⟩
    · exact absurd a2.symm hc.1
  have hdegd : ∀ q, G.dist u (anc hT u v 1) ≤ G.dist u q → G.dist u q < G.dist u v →
      anc hT u q (G.dist u (anc hT u v 1)) = anc hT u v 1 →
      Math15.Graceful.degree G q ≤ 2 := by
    intro q h1 h2 _
    apply hdeg q
    · intro e; rw [e, SimpleGraph.dist_self] at h1; omega
    · intro e; rw [e] at h2; omega
  refine ⟨{
    hT := hT, u := u, v := v, wa := wa, wb := wb, wc := wc, ce := ce, cf := cf,
    huv := hvu, hdeg := fun q h1 h2 => hdeg q h1 h2, hbr := ?_,
    hwa := (hNm wa).1 ha.2, hwb := (hNm wb).1 hb'.2, hwc := (hNm wc).1 hc.2,
    hab := hab, hac := hac, hbc := hbc, had := ha.1, hbd := hb'.1, hcd := hc.1,
    hce := child ce ((memE2 ce).2 (Or.inl rfl)), hcf := child cf ((memE2 cf).2 (Or.inr rfl)),
    hef := hef, hsub := ?_ }⟩
  · intro x hx
    have hN1 := (hNm _).2 (anc_one_adj hT hx)
    by_cases e : anc hT u x 1 = anc hT u v 1
    · exact Or.inr (Or.inr (Or.inr e))
    · have := (memE _).1 (Finset.mem_erase.2 ⟨e, hN1⟩)
      rcases this with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
  · intro x hx ax dx
    have dz : G.dist u (anc hT u x (G.dist u v)) = G.dist u v := anc_dist hT u x (le_of_lt dx)
    have zv : anc hT u x (G.dist u v) = v := by
      refine chain_uniq hT u (anc hT u v 1) (G.dist u v) (by omega) hdegd _ v
        (by rw [dwd, dz]; exact dv) (le_of_eq dz) ?_ (by rw [dwd]) dz
      rw [dwd, anc_anc hT u x dv (le_of_lt dx)]; exact ax
    have dy : G.dist u (anc hT u x (G.dist u v + 1)) = G.dist u v + 1 :=
      anc_dist hT u x (by omega)
    have tpy : tpar hT u (anc hT u x (G.dist u v + 1)) = v := by
      rw [tpar_anc hT u x (by omega) (by omega), Nat.add_sub_cancel]; exact zv
    have yu : anc hT u x (G.dist u v + 1) ≠ u := by
      intro e; rw [e, SimpleGraph.dist_self] at dy; omega
    have hadj := (tpar_spec hT u _ yu).1
    rw [tpy] at hadj
    have yM := (hMm _).2 hadj
    have yp : anc hT u x (G.dist u v + 1) ≠ tpar hT u v := by
      intro e
      have := (tpar_spec hT u v hvu).2
      rw [← e, dy] at this; omega
    exact (memE2 _).1 (Finset.mem_erase.2 ⟨yp, yM⟩)

end Build

namespace B43Setup
variable {n : ℕ} {G : SimpleGraph (Fin n)} (S : B43Setup G)

/-- swap the u-arms a and b -/
def swapAB : B43Setup G :=
  { S with
    wa := S.wb, wb := S.wa,
    hbr := fun x hx => by have := S.hbr x hx; tauto,
    hwa := S.hwb, hwb := S.hwa, hab := S.hab.symm, hac := S.hbc, hbc := S.hac,
    had := S.hbd, hbd := S.had }

/-- swap the u-arms b and c -/
def swapBC : B43Setup G :=
  { S with
    wb := S.wc, wc := S.wb,
    hbr := fun x hx => by have := S.hbr x hx; tauto,
    hwb := S.hwc, hwc := S.hwb, hab := S.hac, hac := S.hab, hbc := S.hbc.symm,
    hbd := S.hcd, hcd := S.hbd }

/-- swap the v-arms -/
def swapEF : B43Setup G :=
  { S with
    ce := S.cf, cf := S.ce, hce := S.hcf, hcf := S.hce, hef := S.hef.symm,
    hsub := fun x hx ax dx => by have := S.hsub x hx ax dx; tauto }

theorem swapAB_L : S.swapAB.La = S.Lb ∧ S.swapAB.Lb = S.La ∧ S.swapAB.Lc = S.Lc ∧
    S.swapAB.Le = S.Le ∧ S.swapAB.Lf = S.Lf := ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem swapBC_L : S.swapBC.La = S.La ∧ S.swapBC.Lb = S.Lc ∧ S.swapBC.Lc = S.Lb ∧
    S.swapBC.Le = S.Le ∧ S.swapBC.Lf = S.Lf := ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem swapEF_L : S.swapEF.La = S.La ∧ S.swapEF.Lb = S.Lb ∧ S.swapEF.Lc = S.Lc ∧
    S.swapEF.Le = S.Lf ∧ S.swapEF.Lf = S.Le := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem sortABC (hef : S.Le ≤ S.Lf) :
    ∃ S' : B43Setup G, S'.La ≤ S'.Lb ∧ S'.Lb ≤ S'.Lc ∧ S'.Le ≤ S'.Lf := by
  have p1 := S.swapAB_L
  have p2 := S.swapBC_L
  have p3 := S.swapAB.swapBC_L
  have p4 := S.swapBC.swapAB_L
  have p5 := S.swapAB.swapBC.swapAB_L
  by_cases h1 : S.La ≤ S.Lb <;> by_cases h2 : S.Lb ≤ S.Lc <;> by_cases h3 : S.La ≤ S.Lc
  · exact ⟨S, h1, h2, hef⟩
  · omega
  · exact ⟨S.swapBC, by omega⟩
  · exact ⟨S.swapBC.swapAB, by omega⟩
  · exact ⟨S.swapAB, by omega⟩
  · exact ⟨S.swapAB.swapBC, by omega⟩
  · omega
  · exact ⟨S.swapAB.swapBC.swapAB, by omega⟩

theorem sorted (S : B43Setup G) : ∃ S' : B43Setup G, S'.La ≤ S'.Lb ∧ S'.Lb ≤ S'.Lc ∧ S'.Le ≤ S'.Lf := by
  by_cases h : S.Le ≤ S.Lf
  · exact S.sortABC h
  · exact S.swapEF.sortABC (by rw [S.swapEF_L.2.2.2.1, S.swapEF_L.2.2.2.2]; omega)

theorem L_pos : 1 ≤ S.La ∧ 1 ≤ S.Lb ∧ 1 ≤ S.Lc ∧ 1 ≤ G.dist S.u S.v ∧ 1 ≤ S.Le ∧ 1 ≤ S.Lf :=
  ⟨(S.lenU_spec S.dist_wa).1, (S.lenU_spec S.dist_wb).1, (S.lenU_spec S.dist_wc).1, S.dv_pos,
    (S.lenV_spec S.hce).1, (S.lenV_spec S.hcf).1⟩

end B43Setup

/-- a canonical tree with a graceful labelling of its names -/
def CanonGraceful (a b c d e f : ℕ) : Prop :=
  ∃ P : Pc, P.Grace ∧ (∀ s, s ∈ P.S ↔ s ∈ Tset a b c d e f) ∧
    (∀ x ∈ P.S, ∀ y ∈ P.S, P.R x y ↔ Tadj d x y)

theorem B43Setup.graceful {n : ℕ} {G : SimpleGraph (Fin n)} (S : B43Setup G)
    (h : CanonGraceful S.La S.Lb S.Lc (G.dist S.u S.v) S.Le S.Lf) :
    Math15.Graceful.IsGraceful G := by
  obtain ⟨P, hP, hS, hR⟩ := h
  refine graceful_of_piece P hP S.phi S.phi_inj (fun x => (hS _).2 (S.phi_mem x))
    (fun s hs => S.phi_surj s ((hS s).1 hs)) (fun x y => ?_)
  rw [S.phi_adj, hR _ ((hS _).2 (S.phi_mem x)) _ ((hS _).2 (S.phi_mem y))]

/-- the reduction: it suffices to label every sorted canonical tree -/
theorem target_of_canon (H : ∀ a b c d e f, 1 ≤ a → a ≤ b → b ≤ c → 1 ≤ d → 1 ≤ e → e ≤ f →
    CanonGraceful a b c d e f) : Math15.Graceful.Target10 := by
  intro n G hT ⟨u, v, hb⟩
  obtain ⟨S⟩ := build_setup hT hb
  obtain ⟨S', h1, h2, h3⟩ := S.sorted
  have hp := S'.L_pos
  exact S'.graceful (H _ _ _ _ _ _ hp.1 h1 h2 hp.2.2.2.1 hp.2.2.2.2.1 h3)

/-! ## α-labeled paths: class alternation and the end invariant -/

theorem path_low_iff {n lam : ℕ} {L : ℕ → ℕ} (h : PathAlpha n L lam) :
    ∀ i, i < n → (L i ≤ lam ↔ (L 0 ≤ lam ↔ i % 2 = 0)) := by
  intro i
  induction i with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    have a := h.2.2.2 k (by omega)
    have b := ih (by omega)
    have a' : L (k + 1) ≤ lam ↔ ¬ (L k ≤ lam) := by
      constructor
      · intro H H2
        have := a.mp H2
        omega
      · intro H
        by_contra H3
        exact H (a.mpr (by omega))
    rw [show (k + 1) % 2 = 0 ↔ ¬ (k % 2 = 0) by omega, a', b]
    tauto

/-- the labels of an α-path fill `[0, n-1]` -/
theorem path_image {n lam : ℕ} {L : ℕ → ℕ} (h : PathAlpha n L lam) :
    (Finset.range n).image L = Finset.range n := by
  apply Finset.eq_of_subset_of_card_le
  · intro v hv
    simp only [Finset.mem_image, Finset.mem_range] at hv ⊢
    obtain ⟨i, hi, rfl⟩ := hv
    have := h.2.1 i hi
    omega
  · rw [Finset.card_image_of_injOn]
    intro i hi j hj hij
    exact h.1 i j (by simpa using hi) (by simpa using hj) hij

/-- the edge labels of an α-path fill `[1, n-1]` -/
theorem path_edge_image {n lam : ℕ} {L : ℕ → ℕ} (h : PathAlpha n L lam) :
    (Finset.range (n - 1)).image (fun i => Nat.dist (L i) (L (i + 1))) = Finset.Icc 1 (n - 1) := by
  apply Finset.eq_of_subset_of_card_le
  · intro v hv
    simp only [Finset.mem_image, Finset.mem_range, Finset.mem_Icc] at hv ⊢
    obtain ⟨i, hi, rfl⟩ := hv
    have h1 := h.2.1 i (by omega)
    have h2 := h.2.1 (i + 1) (by omega)
    have hne : L i ≠ L (i + 1) := fun e => by have := h.1 i (i + 1) (by omega) (by omega) e; omega
    simp only [Nat.dist]
    omega
  · rw [Finset.card_image_of_injOn, Nat.card_Icc, Finset.card_range]
    · omega
    intro i hi j hj hij
    exact h.2.2.1 i j (by simp at hi; omega) (by simp at hj; omega) hij

theorem sum_signed_range (n lam : ℕ) :
    2 * (∑ v ∈ Finset.range n, (if v ≤ lam then -(v : ℤ) else (v : ℤ))) =
      (n : ℤ) * (n - 1) - 2 * (min lam (n - 1) : ℕ) * ((min lam (n - 1) : ℕ) + 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    by_cases hk : k ≤ lam
    · rw [if_pos hk]
      have e1 : min lam (k + 1 - 1) = k := by omega
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · subst h0; simp
      · have e2 : min lam (k - 1) = k - 1 := by omega
        rw [e1, e2]
        have : ((k - 1 : ℕ) : ℤ) = (k : ℤ) - 1 := by omega
        rw [this]; push_cast; ring
    · rw [if_neg hk]
      have e1 : min lam (k + 1 - 1) = lam := by omega
      have e2 : min lam (k - 1) = lam := by omega
      rw [e1, e2]; push_cast; ring

/-- **End invariant.** In an α-path whose first vertex is low, `τ(last) = ε(first)`. -/
theorem path_end_inv {n lam : ℕ} {L : ℕ → ℕ} (h : PathAlpha n L lam) (hn : 1 ≤ n)
    (hlam : lam = (n - 1) / 2) (h0 : L 0 ≤ lam) :
    (L (n - 1) ≤ lam → lam - L (n - 1) = L 0) ∧ (lam < L (n - 1) → L (n - 1) - lam - 1 = L 0) := by
  set φ : ℕ → ℤ := fun v => if v ≤ lam then -(v : ℤ) else (v : ℤ) with hφ
  set g : ℕ → ℤ := fun i => φ (L i) with hg
  have hedge : ∀ i, i + 1 < n → ((Nat.dist (L i) (L (i + 1)) : ℕ) : ℤ) = g i + g (i + 1) := by
    intro i hi
    have a := h.2.2.2 i hi
    simp only [hg, hφ, Nat.dist]
    by_cases hl : L i ≤ lam
    · have := a.mp hl
      rw [if_pos hl, if_neg (by omega)]
      omega
    · have : ¬ lam < L (i + 1) := fun h' => hl (a.mpr h')
      rw [if_neg hl, if_pos (by omega)]
      omega
  set I := ∑ j ∈ Finset.Icc 1 (n - 1), (j : ℤ) with hIdef
  set S := ∑ v ∈ Finset.range n, φ v with hSdef
  have hS1 : ∑ i ∈ Finset.range (n - 1), ((Nat.dist (L i) (L (i + 1)) : ℕ) : ℤ) = I := by
    have := Finset.sum_image (f := fun j : ℕ => (j : ℤ)) (s := Finset.range (n - 1))
      (g := fun i => Nat.dist (L i) (L (i + 1)))
      (fun i hi j hj hij => h.2.2.1 i j (by simp at hi; omega) (by simp at hj; omega) hij)
    rw [path_edge_image h] at this
    rw [hIdef, this]
  have hIcc : ∀ m : ℕ, 2 * ∑ j ∈ Finset.Icc 1 m, (j : ℤ) = (m : ℤ) * (m + 1) := by
    intro m
    induction m with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_Icc_succ_top (by omega), mul_add, ih]
      push_cast; ring
  have hS2 : ∑ i ∈ Finset.range n, g i = S := by
    have := Finset.sum_image (f := φ) (s := Finset.range n) (g := L)
      (fun i hi j hj hij => h.1 i j (by simpa using hi) (by simpa using hj) hij)
    rw [path_image h] at this
    rw [hSdef, this]
  have hT : ∑ i ∈ Finset.range (n - 1), (g i + g (i + 1)) =
      2 * ∑ i ∈ Finset.range n, g i - g 0 - g (n - 1) := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    rw [Finset.sum_add_distrib]
    have h1 := Finset.sum_range_succ g m
    have h2 := Finset.sum_range_succ' g m
    linarith
  have hsum : ∑ i ∈ Finset.range (n - 1), (g i + g (i + 1)) = I := by
    rw [← hS1]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hedge i (by simp at hi; omega)]
  have key := sum_signed_range n lam
  rw [← hφ, ← hSdef] at key
  have hI := hIcc (n - 1)
  rw [← hIdef] at hI
  have hg0 : g 0 = -(L 0 : ℤ) := by simp [hg, hφ, h0]
  have e : 2 * S - g 0 - g (n - 1) = I := by rw [← hS2, ← hT, hsum]
  rw [hg0] at e
  have hlast := path_low_iff h (n - 1) (by omega)
  have hmin : min lam (n - 1) = lam := by omega
  rw [hmin] at key
  have hn1 : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
  rw [hn1] at hI
  rcases Nat.even_or_odd' n with ⟨k, hk | hk⟩
  · -- n = 2k (k ≥ 1): last is high
    have hhigh : lam < L (n - 1) := by
      by_contra hc
      have := (hlast.mp (by omega)).mp h0
      omega
    have hgl : g (n - 1) = (L (n - 1) : ℤ) := by simp [hg, hφ, show ¬ L (n - 1) ≤ lam by omega]
    rw [hgl] at e
    refine ⟨fun hc => by omega, fun _ => ?_⟩
    have hl1 : (lam : ℤ) = (k : ℤ) - 1 := by omega
    have hnk : (n : ℤ) = 2 * k := by omega
    rw [hl1, hnk] at key
    rw [hnk] at hI
    have : (L (n - 1) : ℤ) = (L 0 : ℤ) + k := by nlinarith
    omega
  · -- n = 2k+1: last is low
    have hlow : L (n - 1) ≤ lam := hlast.mpr (by constructor <;> intro _ <;> omega)
    have hgl : g (n - 1) = -(L (n - 1) : ℤ) := by simp [hg, hφ, hlow]
    rw [hgl] at e
    refine ⟨fun _ => ?_, fun hc => by omega⟩
    have hl1 : (lam : ℤ) = (k : ℤ) := by omega
    have hnk : (n : ℤ) = 2 * k + 1 := by omega
    rw [hl1, hnk] at key
    rw [hnk] at hI
    have : (L (n - 1) : ℤ) = (k : ℤ) - L 0 := by nlinarith
    omega

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

/-! ## Attaching segments along arms (side conditions reduced to membership facts) -/

namespace APc
variable {d q : ℕ}

/-- attach an α-EPL segment on arm `X`, positions `k0+1 … k0+L`, at position `k0` / the root -/
theorem attachOut (A : APc d q) (X k0 L : ℕ) (hX : 2 ≤ X ∧ X ≤ 7) (hL : 1 ≤ L)
    (hx : (if k0 = 0 then armRoot X else X + 8 * k0) ∈ A.P.S)
    (hfresh : ∀ i, i < L → X + 8 * (k0 + 1 + i) ∉ A.P.S)
    (hnext : X + 8 * (k0 + L + 1) ∉ A.P.S)
    (hd5 : X = 5 → k0 + L + 1 ≤ d) (hv : X = 5 → k0 + L + 1 = d → 1 ∉ A.P.S)
    (hok : AeplOK L (A.tau (if k0 = 0 then armRoot X else X + 8 * k0))) :
    ∃ B : APc d q, (∀ z, z ∈ B.P.S ↔ z ∈ A.P.S ∨ ∃ i, i < L ∧ X + 8 * (k0 + 1 + i) = z) ∧
      B.P.E.card = A.P.E.card + L ∧
      (∀ z ∈ A.P.S, B.eps z = A.eps z) ∧
      (∀ z ∈ A.P.S, B.tau z = A.tau z +
        (L + (par d z + par d (if k0 = 0 then armRoot X else X + 8 * k0)) % 2) / 2) ∧
      B.tau (X + 8 * (k0 + L)) = A.tau (if k0 = 0 then armRoot X else X + 8 * k0) := by
  have hs := segOut d X k0 L hX hL
  have hcross : ∀ p ∈ A.P.S, ∀ i, i < L → Tadj d p (X + 8 * (k0 + 1 + i)) →
      p = (if k0 = 0 then armRoot X else X + 8 * k0) ∧ i = 0 := by
    intro p hp i hi h
    rcases (Tadj_arm_iff d X (k0 + 1 + i) p hX (by omega)).mp h with h1 | h1 | ⟨h5, hd, rfl⟩
    · by_cases hi0 : i = 0
      · subst hi0
        refine ⟨?_, rfl⟩
        rw [h1]
        by_cases hk : k0 = 0
        · rw [if_pos (by omega), if_pos hk]
        · rw [if_neg (by omega), if_neg hk]; congr 1
      · exfalso
        rw [if_neg (by omega)] at h1
        exact hfresh (i - 1) (by omega)
          (by rw [show X + 8 * (k0 + 1 + (i - 1)) = p by omega]; exact hp)
    · exfalso
      by_cases hiL : i + 1 < L
      · exact hfresh (i + 1) hiL (by rw [show X + 8 * (k0 + 1 + (i + 1)) = p by omega]; exact hp)
      · exact hnext (by rw [show X + 8 * (k0 + L + 1) = p by omega]; exact hp)
    · exfalso
      have := hd5 h5
      exact hv h5 (by omega) hp
  obtain ⟨B, h1, h2, h3, h4, h5⟩ := A.attach hs hx hfresh hcross hok
  refine ⟨B, h1, h2, h3, h4, ?_⟩
  rw [show k0 + 1 + (L - 1) = k0 + L by omega] at h5
  exact h5

/-- attach an α-EPL segment on the `d`-path going toward `u`: positions `k0, …, k0-L+1`,
at position `k0+1` (or at `v` if `k0 + 1 = d`) -/
theorem attachIn (A : APc d q) (k0 L : ℕ) (hL : 1 ≤ L) (hk : L ≤ k0) (hkd : k0 + 1 ≤ d)
    (hx : (if k0 + 1 = d then 1 else 5 + 8 * (k0 + 1)) ∈ A.P.S)
    (hfresh : ∀ i, i < L → 5 + 8 * (k0 - i) ∉ A.P.S)
    (hnext0 : k0 = L → 0 ∉ A.P.S) (hnext : L < k0 → 5 + 8 * (k0 - L) ∉ A.P.S)
    (hbeyond : k0 + 1 = d → 5 + 8 * d ∉ A.P.S)
    (hok : AeplOK L (A.tau (if k0 + 1 = d then 1 else 5 + 8 * (k0 + 1)))) :
    ∃ B : APc d q, (∀ z, z ∈ B.P.S ↔ z ∈ A.P.S ∨ ∃ i, i < L ∧ 5 + 8 * (k0 - i) = z) ∧
      B.P.E.card = A.P.E.card + L ∧
      (∀ z ∈ A.P.S, B.eps z = A.eps z) ∧
      (∀ z ∈ A.P.S, B.tau z = A.tau z +
        (L + (par d z + par d (if k0 + 1 = d then 1 else 5 + 8 * (k0 + 1))) % 2) / 2) ∧
      B.tau (5 + 8 * (k0 + 1 - L)) = A.tau (if k0 + 1 = d then 1 else 5 + 8 * (k0 + 1)) := by
  have hs := segIn d k0 L hL hk hkd
  have h5 : 2 ≤ 5 ∧ 5 ≤ 7 := by omega
  have hcross : ∀ p ∈ A.P.S, ∀ i, i < L → Tadj d p (5 + 8 * (k0 - i)) →
      p = (if k0 + 1 = d then 1 else 5 + 8 * (k0 + 1)) ∧ i = 0 := by
    intro p hp i hi h
    rcases (Tadj_arm_iff d 5 (k0 - i) p h5 (by omega)).mp h with h1 | h1 | ⟨_, hd, rfl⟩
    · exfalso
      by_cases hiL : i + 1 < L
      · rw [if_neg (by omega)] at h1
        exact hfresh (i + 1) hiL (by rw [show 5 + 8 * (k0 - (i + 1)) = p by omega]; exact hp)
      · by_cases h1' : k0 - i = 1
        · rw [if_pos h1'] at h1
          unfold armRoot at h1
          rw [if_pos (by omega)] at h1
          exact hnext0 (by omega) (by rw [← h1]; exact hp)
        · rw [if_neg h1'] at h1
          exact hnext (by omega) (by rw [show 5 + 8 * (k0 - L) = p by omega]; exact hp)
    · by_cases hi0 : i = 0
      · subst hi0
        refine ⟨?_, rfl⟩
        by_cases hv : k0 + 1 = d
        · exfalso; exact hbeyond hv (by rw [show 5 + 8 * d = p by omega]; exact hp)
        · rw [if_neg hv]; omega
      · exfalso
        exact hfresh (i - 1) (by omega)
          (by rw [show 5 + 8 * (k0 - (i - 1)) = p by omega]; exact hp)
    · by_cases hi0 : i = 0
      · subst hi0
        exact ⟨by rw [if_pos (by omega)], rfl⟩
      · omega
  obtain ⟨B, h1, h2, h3, h4, h5'⟩ := A.attach hs hx hfresh hcross hok
  refine ⟨B, h1, h2, h3, h4, ?_⟩
  rw [show k0 - (L - 1) = k0 + 1 - L by omega] at h5'
  exact h5'

end APc

/-! ## Explicit labeled trees, checked by computation -/

/-- `pa` is a parent function (`pa i < i` for `1 ≤ i < n`), `lab` is injective into `[0,n-1]`
with distinct edge labels `|lab i - lab (pa i)|`; with `alpha`, every edge crosses threshold `th`. -/
def treeCheck (n th : ℕ) (alpha : Bool) (pa lab : ℕ → ℕ) : Bool :=
  ((List.range n).all fun i => decide (lab i < n)) &&
  ((List.range n).all fun i => (List.range n).all fun j => decide (i = j) || decide (lab i ≠ lab j)) &&
  ((List.range n).all fun i => decide (i = 0) || decide (pa i < i)) &&
  ((List.range n).all fun i => (List.range n).all fun j =>
      decide (i = 0) || decide (j = 0) || decide (i = j) ||
      decide (Nat.dist (lab i) (lab (pa i)) ≠ Nat.dist (lab j) (lab (pa j)))) &&
  (!alpha || (decide (th ≤ n) && (List.range n).all fun i =>
      decide (i = 0) || (decide (lab i < th) != decide (lab (pa i) < th))))

theorem treeCheck_spec {n th : ℕ} {alpha : Bool} {pa lab : ℕ → ℕ}
    (h : treeCheck n th alpha pa lab = true) :
    (∀ i, i < n → lab i < n) ∧
    (∀ i j, i < n → j < n → lab i = lab j → i = j) ∧
    (∀ i, i < n → i ≠ 0 → pa i < i) ∧
    (∀ i j, i < n → j < n → i ≠ 0 → j ≠ 0 →
      Nat.dist (lab i) (lab (pa i)) = Nat.dist (lab j) (lab (pa j)) → i = j) ∧
    (alpha = true → th ≤ n ∧ ∀ i, i < n → i ≠ 0 → (lab i < th ↔ ¬ lab (pa i) < th)) := by
  unfold treeCheck at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    decide_eq_true_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨h1, ?_, ?_, ?_, ?_⟩
  · intro i j hi hj e
    rcases h2 i hi j hj with h | h
    · exact h
    · exact absurd e h
  · intro i hi h0
    rcases h3 i hi with h | h
    · exact absurd h h0
    · exact h
  · intro i j hi hj hi0 hj0 e
    rcases h4 i hi j hj with ((h | h) | h) | h
    · exact absurd h hi0
    · exact absurd h hj0
    · exact h
    · exact absurd e h
  · intro ha
    rcases h5 with h | ⟨hth, h⟩
    · rw [ha] at h; exact absurd h (by decide)
    · refine ⟨hth, fun i hi hi0 => ?_⟩
      rcases h i hi with h' | h'
      · exact absurd h' hi0
      · have h'' : ¬ (lab i < th ↔ lab (pa i) < th) := by
          intro e
          by_cases a : lab i < th
          · have b := e.mp a
            simp [a, b] at h'
          · have b : ¬ lab (pa i) < th := fun b => a (e.mpr b)
            simp [a, b] at h'
        tauto

/-- the piece of an explicit tree on names `nm i` with labels `lab i` -/
noncomputable def treePc (d n : ℕ) (nm pos lab : ℕ → ℕ) : Pc where
  S := (Finset.range n).image nm
  R := Tadj d
  f := fun z => lab (pos z)

theorem treePc_mem {d n : ℕ} {nm pos lab : ℕ → ℕ} {z : ℕ} :
    z ∈ (treePc d n nm pos lab).S ↔ ∃ i, i < n ∧ nm i = z := by
  simp [treePc, Finset.mem_image]

theorem treePc_props (d n th : ℕ) (alpha : Bool) (nm pos pa lab : ℕ → ℕ) (hn : 1 ≤ n)
    (hinj : ∀ i j, i < n → j < n → nm i = nm j → i = j) (hpos : ∀ i, i < n → pos (nm i) = i)
    (hadj : ∀ i j, i < n → j < n →
      (Tadj d (nm i) (nm j) ↔ (i ≠ 0 ∧ pa i = j) ∨ (j ≠ 0 ∧ pa j = i)))
    (hc : treeCheck n th alpha pa lab = true) :
    (treePc d n nm pos lab).Grace ∧ (treePc d n nm pos lab).E.card = n - 1 ∧
      (alpha = true → (treePc d n nm pos lab).Alpha th) := by
  classical
  obtain ⟨c1, c2, c3, c4, c5⟩ := treeCheck_spec hc
  set P := treePc d n nm pos lab with hP
  have hf : ∀ i, i < n → P.f (nm i) = lab i := by
    intro i hi; show lab (pos (nm i)) = lab i; rw [hpos i hi]
  -- edges are exactly the parent pairs
  have hEmem : ∀ e, e ∈ P.E ↔ ∃ i, i < n ∧ i ≠ 0 ∧ e = opair (nm i) (nm (pa i)) := by
    intro e
    rw [Pc.mem_E]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      obtain ⟨i, hi, hie⟩ := treePc_mem.mp h1
      obtain ⟨j, hj, hje⟩ := treePc_mem.mp h2
      have h4' : Tadj d (nm i) (nm j) := by rw [hie, hje]; exact h4
      rcases (hadj i j hi hj).mp h4' with ⟨hi0, hp⟩ | ⟨hj0, hp⟩
      · refine ⟨i, hi, hi0, ?_⟩
        rw [hp, hie, hje]
        unfold opair
        rw [min_eq_left (le_of_lt h3), max_eq_right (le_of_lt h3)]
      · refine ⟨j, hj, hj0, ?_⟩
        rw [hp, hie, hje]
        unfold opair
        rw [min_eq_right (le_of_lt h3), max_eq_left (le_of_lt h3)]
    · rintro ⟨i, hi, hi0, rfl⟩
      have hpi := c3 i hi hi0
      have hne : nm i ≠ nm (pa i) := fun e => by have := hinj _ _ hi (by omega) e; omega
      have hadj' := (hadj i (pa i) hi (by omega)).mpr (Or.inl ⟨hi0, rfl⟩)
      have m1 : nm i ∈ P.S := treePc_mem.mpr ⟨i, hi, rfl⟩
      have m2 : nm (pa i) ∈ P.S := treePc_mem.mpr ⟨pa i, by omega, rfl⟩
      unfold opair
      rcases lt_or_gt_of_ne hne with hl | hl
      · rw [min_eq_left (le_of_lt hl), max_eq_right (le_of_lt hl)]
        exact ⟨m1, m2, hl, hadj'⟩
      · rw [min_eq_right (le_of_lt hl), max_eq_left (le_of_lt hl)]
        exact ⟨m2, m1, hl, Tadj_symm d _ _ hadj'⟩
  have hEimg : P.E = ((Finset.range n).filter (fun i => i ≠ 0)).image
      (fun i => opair (nm i) (nm (pa i))) := by
    ext e
    rw [hEmem, Finset.mem_image]
    constructor
    · rintro ⟨i, hi, hi0, rfl⟩; exact ⟨i, by simp [hi, hi0], rfl⟩
    · rintro ⟨i, hi, rfl⟩; simp at hi; exact ⟨i, hi.1, hi.2, rfl⟩
  have hcard : P.E.card = n - 1 := by
    rw [hEimg, Finset.card_image_of_injOn]
    · have : (Finset.range n).filter (fun i => i ≠ 0) = (Finset.range n).erase 0 := by
        ext i; simp [and_comm]
      rw [this, Finset.card_erase_of_mem (by simp; omega), Finset.card_range]
    · intro i hi j hj e
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hi hj
      simp only [opair, Prod.mk.injEq] at e
      have hpi := c3 i hi.1 hi.2
      have hpj := c3 j hj.1 hj.2
      obtain ⟨e1, e2⟩ := e
      have key : (nm i = nm j ∧ nm (pa i) = nm (pa j)) ∨ (nm i = nm (pa j) ∧ nm (pa i) = nm j) := by
        rcases le_total (nm i) (nm (pa i)) with a | a <;>
          rcases le_total (nm j) (nm (pa j)) with b | b
        · rw [min_eq_left a, min_eq_left b] at e1; rw [max_eq_right a, max_eq_right b] at e2
          exact Or.inl ⟨e1, e2⟩
        · rw [min_eq_left a, min_eq_right b] at e1; rw [max_eq_right a, max_eq_left b] at e2
          exact Or.inr ⟨e1, e2⟩
        · rw [min_eq_right a, min_eq_left b] at e1; rw [max_eq_left a, max_eq_right b] at e2
          exact Or.inr ⟨e2, e1⟩
        · rw [min_eq_right a, min_eq_right b] at e1; rw [max_eq_left a, max_eq_left b] at e2
          exact Or.inl ⟨e2, e1⟩
      rcases key with ⟨k1, _⟩ | ⟨k1, k2⟩
      · exact hinj _ _ hi.1 hj.1 k1
      · have := hinj _ _ hi.1 (by omega) k1
        have := hinj _ _ (by omega) hj.1 k2
        omega
  have hScard : P.S.card = n := by
    show ((Finset.range n).image nm).card = n
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro i hi j hj e
    exact hinj i j (by simpa using hi) (by simpa using hj) e
  have hG : P.Grace := by
    refine ⟨Tadj_symm d, by rw [hScard, hcard]; omega, ?_, ?_, ?_⟩
    · intro x hx y hy e
      obtain ⟨i, hi, rfl⟩ := treePc_mem.mp hx
      obtain ⟨j, hj, rfl⟩ := treePc_mem.mp hy
      rw [hf i hi, hf j hj] at e
      rw [c2 i j hi hj e]
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := treePc_mem.mp hx
      rw [hf i hi, hcard]
      have := c1 i hi; omega
    · intro e he e' he' h
      obtain ⟨i, hi, hi0, rfl⟩ := (hEmem e).mp he
      obtain ⟨j, hj, hj0, rfl⟩ := (hEmem e').mp he'
      have hpi := c3 i hi hi0
      have hpj := c3 j hj hj0
      have dist_op : ∀ k, k < n → k ≠ 0 →
          Nat.dist (P.f (opair (nm k) (nm (pa k))).1) (P.f (opair (nm k) (nm (pa k))).2) =
            Nat.dist (lab k) (lab (pa k)) := by
        intro k hk hk0
        have := c3 k hk hk0
        unfold opair
        rcases le_total (nm k) (nm (pa k)) with a | a
        · rw [min_eq_left a, max_eq_right a, hf k hk, hf (pa k) (by omega)]
        · rw [min_eq_right a, max_eq_left a, hf k hk, hf (pa k) (by omega), Nat.dist_comm]
      rw [dist_op i hi hi0, dist_op j hj hj0] at h
      rw [c4 i j hi hj hi0 hj0 h]
  refine ⟨hG, hcard, fun ha => ⟨hG, ?_, ?_⟩⟩
  · rw [hcard]; have := (c5 ha).1; omega
  · intro x hx y hy hr
    obtain ⟨i, hi, rfl⟩ := treePc_mem.mp hx
    obtain ⟨j, hj, rfl⟩ := treePc_mem.mp hy
    rw [hf i hi, hf j hj]
    have hr' : Tadj d (nm i) (nm j) := hr
    have alt := (c5 ha).2
    rcases (hadj i j hi hj).mp hr' with ⟨hi0, hp⟩ | ⟨hj0, hp⟩
    · have := alt i hi hi0; rw [hp] at this; omega
    · have := alt j hj hj0; rw [hp] at this; omega

/-- an explicit α-tree as a start piece -/
theorem startTree (d n th q : ℕ) (nm pos pa lab : ℕ → ℕ) (hn : 1 ≤ n)
    (hinj : ∀ i j, i < n → j < n → nm i = nm j → i = j) (hpos : ∀ i, i < n → pos (nm i) = i)
    (hadj : ∀ i j, i < n → j < n →
      (Tadj d (nm i) (nm j) ↔ (i ≠ 0 ∧ pa i = j) ∨ (j ≠ 0 ∧ pa j = i)))
    (hc : treeCheck n th true pa lab = true)
    (hlow : ∀ i, i < n → (lab i < th ↔ par d (nm i) = q)) (hq : q ≤ 1) :
    ∃ A : APc d q, (∀ z, z ∈ A.P.S ↔ ∃ i, i < n ∧ nm i = z) ∧ A.P.E.card = n - 1 ∧
      (∀ i, i < n → A.eps (nm i) = if lab i < th then lab i else n - 1 - lab i) ∧
      (∀ i, i < n → A.tau (nm i) = if lab i < th then th - 1 - lab i else lab i - th) := by
  obtain ⟨_, hcard, hal⟩ := treePc_props d n th true nm pos pa lab hn hinj hpos hadj hc
  have hA := hal rfl
  have hf : ∀ i, i < n → (treePc d n nm pos lab).f (nm i) = lab i := by
    intro i hi; show lab (pos (nm i)) = lab i; rw [hpos i hi]
  refine ⟨⟨treePc d n nm pos lab, th, rfl, hA, ?_, hq⟩, fun z => treePc_mem, hcard, ?_, ?_⟩
  · intro z hz
    obtain ⟨i, hi, rfl⟩ := treePc_mem.mp hz
    rw [hf i hi]; exact hlow i hi
  · intro i hi
    show (treePc d n nm pos lab).eps th (nm i) = _
    unfold Pc.eps; rw [hf i hi, hcard]
  · intro i hi
    show (treePc d n nm pos lab).tau th (nm i) = _
    unfold Pc.tau; rw [hf i hi]

/-! ## Graceful (not necessarily α) pieces: EPL, final segments, joins, leaf chains -/

/-- `L` is a graceful labeling of the path `0 - 1 - ⋯ - (n-1)` -/
def PathGrace (n : ℕ) (L : ℕ → ℕ) : Prop :=
  (∀ i j, i < n → j < n → L i = L j → i = j) ∧
  (∀ i, i < n → L i ≤ n - 1) ∧
  (∀ i j, i + 1 < n → j + 1 < n →
      Nat.dist (L i) (L (i + 1)) = Nat.dist (L j) (L (j + 1)) → i = j)

theorem PathAlpha.grace {n lam : ℕ} {L : ℕ → ℕ} (h : PathAlpha n L lam) : PathGrace n L :=
  ⟨h.1, h.2.1, h.2.2.1⟩

theorem pathPc_grace {n : ℕ} {nm pos L : ℕ → ℕ} (hn : 1 ≤ n)
    (hinj : ∀ i j, i < n → j < n → nm i = nm j → i = j) (hpos : ∀ i, i < n → pos (nm i) = i)
    (hL : PathGrace n L) : (pathPc n nm pos L).Grace := by
  classical
  obtain ⟨Linj, Lle, Ledge⟩ := hL
  have hE := pathPc_card_E (pos := pos) (L := L) hinj
  have fval : ∀ i, i < n → (pathPc n nm pos L).f (nm i) = L i := by
    intro i hi; simp [pathPc, hpos i hi]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro p q ⟨i, hi, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩
    · exact ⟨i, hi, Or.inr ⟨rfl, rfl⟩⟩
    · exact ⟨i, hi, Or.inl ⟨rfl, rfl⟩⟩
  · rw [pathPc_card_S hinj, hE]; omega
  · intro x hx y hy hxy
    obtain ⟨i, hi, rfl⟩ := pathPc_mem_S.mp hx
    obtain ⟨j, hj, rfl⟩ := pathPc_mem_S.mp hy
    rw [fval i hi, fval j hj] at hxy
    rw [Linj i j hi hj hxy]
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := pathPc_mem_S.mp hx
    rw [fval i hi, hE]; exact Lle i hi
  · intro e he e' he' h
    rw [pathPc_E hinj, Finset.mem_image] at he he'
    obtain ⟨i, hi, rfl⟩ := he
    obtain ⟨j, hj, rfl⟩ := he'
    simp only [Finset.mem_range] at hi hj
    have dd : ∀ k, k + 1 < n → Nat.dist ((pathPc n nm pos L).f (opair (nm k) (nm (k + 1))).1)
        ((pathPc n nm pos L).f (opair (nm k) (nm (k + 1))).2) = Nat.dist (L k) (L (k + 1)) := by
      intro k hk
      simp only [opair]
      rcases le_total (nm k) (nm (k + 1)) with a | a
      · rw [min_eq_left a, max_eq_right a, fval k (by omega), fval (k + 1) (by omega)]
      · rw [min_eq_right a, max_eq_left a, fval k (by omega), fval (k + 1) (by omega), Nat.dist_comm]
    rw [dd i (by omega), dd j (by omega)] at h
    rw [Ledge i j (by omega) (by omega) h]

theorem ipathPc_grace {R : ℕ → ℕ → Prop} {n : ℕ} {nm pos L : ℕ → ℕ} (hn : 1 ≤ n)
    (hsym : ∀ p q, R p q → R q p)
    (hinj : ∀ i j, i < n → j < n → nm i = nm j → i = j) (hpos : ∀ i, i < n → pos (nm i) = i)
    (hcons : ∀ i, i + 1 < n → R (nm i) (nm (i + 1)))
    (hchord : ∀ i j, i < n → j < n → R (nm i) (nm j) → i = j + 1 ∨ j = i + 1)
    (hL : PathGrace n L) :
    (ipathPc R n nm pos L).Grace := by
  refine Pc.grace_congr (pathPc_grace hn hinj hpos hL) rfl ?_ (fun _ _ => rfl) hsym
  intro x hx y hy
  obtain ⟨i, hi, rfl⟩ := pathPc_mem_S.mp hx
  obtain ⟨j, hj, rfl⟩ := pathPc_mem_S.mp hy
  simp only [pathPc, ipathPc]
  constructor
  · rintro ⟨k, hk, (⟨h1, h2⟩ | ⟨h1, h2⟩)⟩
    · rw [h1, h2]; exact hcons k hk
    · rw [h1, h2]; exact hsym _ _ (hcons k hk)
  · intro h
    rcases hchord i j hi hj h with e | e
    · exact ⟨j, by omega, Or.inr ⟨by rw [e], rfl⟩⟩
    · exact ⟨i, by omega, Or.inl ⟨rfl, by rw [e]⟩⟩

/-- complement of a graceful path labeling -/
theorem PathGrace.comp {n : ℕ} {L : ℕ → ℕ} (h : PathGrace n L) : PathGrace n (fun i => n - 1 - L i) := by
  obtain ⟨hinj, hle, hedge⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro i j hi hj e
    have := hle i hi; have := hle j hj
    have e' : n - 1 - L i = n - 1 - L j := e
    exact hinj i j hi hj (by omega)
  · intro i _; show n - 1 - L i ≤ n - 1; omega
  · intro i j hi hj e
    apply hedge i j hi hj
    have := hle i (by omega); have := hle (i + 1) hi; have := hle j (by omega); have := hle (j + 1) hj
    simp only [Nat.dist] at e ⊢
    omega

/-- **EPL.** The path on `n` vertices has a graceful labeling with first label `t`, `t ≤ n-1`. -/
theorem epl (n t : ℕ) (hn : 1 ≤ n) (ht : t ≤ n - 1) : ∃ L : ℕ → ℕ, PathGrace n L ∧ L 0 = t := by
  classical
  by_cases h1 : AeplOK n t
  · obtain ⟨L, hL, h0⟩ := aepl n t h1
    exact ⟨L, hL.grace, h0⟩
  by_cases h2 : AeplOK n (n - 1 - t)
  · obtain ⟨L, hL, h0⟩ := aepl n (n - 1 - t) h2
    exact ⟨fun i => n - 1 - L i, hL.grace.comp, by show n - 1 - L 0 = t; omega⟩
  -- exceptional: n = 4q+1, t ∈ {q, 3q}
  have hex : ∃ q, 1 ≤ q ∧ n = 4 * q + 1 ∧ (t = q ∨ t = 3 * q) := by
    unfold AeplOK at h1 h2
    refine ⟨(n - 1) / 4, ?_, ?_, ?_⟩ <;> omega
  obtain ⟨q, hq, hn', ht'⟩ := hex
  -- the case t = q, by FGL of α-EPL(3q, q) and a zigzag of q+1 vertices
  have main : ∃ L : ℕ → ℕ, PathGrace n L ∧ L 0 = q := by
    have hok : AeplOK (3 * q) q := ⟨by omega, by omega, by omega⟩
    obtain ⟨L1, hL1, h10⟩ := aepl (3 * q) q hok
    set lam1 := (3 * q - 1) / 2 with hlam1
    have hl0 : L1 0 ≤ lam1 := by rw [h10]; omega
    have hlast := ptau_last hL1 (by omega) hl0
    set A := pathPc (3 * q) id id L1 with hA
    have hAa := pathPc_alpha (pos := id) (nm := id) (by omega) (fun i j _ _ e => e) (fun i _ => rfl) hL1
      (by omega)
    have hAE : A.E.card = 3 * q - 1 := pathPc_card_E (fun i j _ _ e => e)
    -- second piece
    set g : ℕ → ℕ := if L1 (3 * q - 1) ≤ lam1 then zz (q + 1) else fun i => q - zz (q + 1) i with hg
    have hgG : PathGrace (q + 1) g := by
      rw [hg]
      split_ifs
      · exact (zz_alpha (q + 1) (by omega)).grace
      · have := (zz_alpha (q + 1) (by omega)).grace.comp
        simpa using this
    set B := pathPc (q + 1) (fun i => i + 3 * q) (fun z => z - 3 * q) g with hB
    have hBinj : ∀ i j, i < q + 1 → j < q + 1 → i + 3 * q = j + 3 * q → i = j := by
      intro i j _ _ e; omega
    have hBg := pathPc_grace (nm := fun i => i + 3 * q) (pos := fun z => z - 3 * q) (by omega) hBinj
      (fun i _ => by simp) hgG
    have hBE : B.E.card = q := by rw [hB, pathPc_card_E hBinj]; omega
    have hd : Disjoint A.S B.S := by
      rw [Finset.disjoint_left]
      intro z hzA hzB
      obtain ⟨i, hi, rfl⟩ := pathPc_mem_S.mp hzA
      obtain ⟨j, hj, e⟩ := pathPc_mem_S.mp hzB
      simp only [id] at e; omega
    have hx : 3 * q - 1 ∈ A.S := pathPc_mem_S.mpr ⟨3 * q - 1, by omega, rfl⟩
    have hw : 3 * q ∈ B.S := pathPc_mem_S.mpr ⟨0, by omega, by simp⟩
    have hfx : A.f (3 * q - 1) = L1 (3 * q - 1) := rfl
    have hfw : B.f (3 * q) = g 0 := by show g (3 * q - 3 * q) = g 0; simp
    have hle1 := hL1.2.1 (3 * q - 1) (by omega)
    have hc : (A.f (3 * q - 1) < lam1 + 1 ∧ B.f (3 * q) + (lam1 + 1 - 1 - A.f (3 * q - 1)) = B.E.card) ∨
        (lam1 + 1 ≤ A.f (3 * q - 1) ∧ B.f (3 * q) + (lam1 + 1) = A.f (3 * q - 1)) := by
      rw [hfx, hfw, hBE]
      unfold ptau at hlast
      by_cases hl : L1 (3 * q - 1) ≤ lam1
      · left
        rw [if_pos hl] at hlast
        refine ⟨by omega, ?_⟩
        rw [hg, if_pos hl]; simp [zz]; omega
      · right
        rw [if_neg hl] at hlast
        refine ⟨by omega, ?_⟩
        rw [hg, if_neg hl]; simp [zz]; omega
    have hJ := Pc.fgl hAa hBg hd hx hw hc
    set J := Pc.join A B (lam1 + 1) (3 * q - 1) (3 * q) with hJdef
    have hJE : J.E.card = 3 * q - 1 + q + 1 := by
      rw [hJdef, Pc.join_card_E hd hx hw, hAE, hBE]
    have hJS : ∀ i, i ∈ J.S ↔ i < n := by
      intro i
      show i ∈ A.S ∪ B.S ↔ _
      rw [Finset.mem_union, pathPc_mem_S, pathPc_mem_S]
      constructor
      · rintro (⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩)
        · show id j < n; simp only [id]; omega
        · omega
      · intro hi
        by_cases h : i < 3 * q
        · exact Or.inl ⟨i, h, rfl⟩
        · exact Or.inr ⟨i - 3 * q, by omega, by omega⟩
    have hJR : ∀ i, i + 1 < n → J.R i (i + 1) := by
      intro i hi
      show (i ∈ A.S ∧ i + 1 ∈ A.S ∧ A.R i (i + 1)) ∨ (i ∈ B.S ∧ i + 1 ∈ B.S ∧ B.R i (i + 1)) ∨
        (i = 3 * q - 1 ∧ i + 1 = 3 * q) ∨ (i = 3 * q ∧ i + 1 = 3 * q - 1)
      by_cases h : i + 1 < 3 * q
      · left
        exact ⟨pathPc_mem_S.mpr ⟨i, by omega, rfl⟩, pathPc_mem_S.mpr ⟨i + 1, h, rfl⟩,
          ⟨i, h, Or.inl ⟨rfl, rfl⟩⟩⟩
      · by_cases h' : i + 1 = 3 * q
        · right; right; left; omega
        · right; left
          refine ⟨pathPc_mem_S.mpr ⟨i - 3 * q, by omega, by omega⟩,
            pathPc_mem_S.mpr ⟨i + 1 - 3 * q, by omega, by omega⟩, ⟨i - 3 * q, by omega, ?_⟩⟩
          left; constructor <;> simp <;> omega
    obtain ⟨_, _, Jinj, Jle, Jedge⟩ := hJ
    refine ⟨fun i => J.f i, ⟨?_, ?_, ?_⟩, ?_⟩
    · intro i j hi hj e
      exact Jinj i ((hJS i).mpr hi) j ((hJS j).mpr hj) e
    · intro i hi
      have := Jle i ((hJS i).mpr hi)
      show J.f i ≤ n - 1
      omega
    · intro i j hi hj e
      have mi : opair i (i + 1) ∈ J.E := by
        rw [Pc.mem_E]; simp only [opair, min_eq_left (Nat.le_succ i), max_eq_right (Nat.le_succ i)]
        exact ⟨(hJS i).mpr (by omega), (hJS (i + 1)).mpr hi, by omega, hJR i hi⟩
      have mj : opair j (j + 1) ∈ J.E := by
        rw [Pc.mem_E]; simp only [opair, min_eq_left (Nat.le_succ j), max_eq_right (Nat.le_succ j)]
        exact ⟨(hJS j).mpr (by omega), (hJS (j + 1)).mpr hj, by omega, hJR j hj⟩
      have := Jedge _ mi _ mj (by
        simp only [opair, min_eq_left (Nat.le_succ i), max_eq_right (Nat.le_succ i),
          min_eq_left (Nat.le_succ j), max_eq_right (Nat.le_succ j)]
        exact e)
      simp only [opair, min_eq_left (Nat.le_succ i), max_eq_right (Nat.le_succ i),
        min_eq_left (Nat.le_succ j), max_eq_right (Nat.le_succ j), Prod.mk.injEq] at this
      exact this.1
    · have h0' : A.f 0 < lam1 + 1 := by show L1 (id 0) < lam1 + 1; simp only [id]; omega
      show J.f 0 = q
      have := Pc.join_f_lowA (B := B) (x := 3 * q - 1) (w := 3 * q)
        (pathPc_mem_S.mpr ⟨0, by omega, rfl⟩ : (0 : ℕ) ∈ A.S) h0'
      rw [hJdef, this]
      show L1 (id 0) = q
      exact h10
  rcases ht' with rfl | rfl
  · exact main
  · obtain ⟨L, hL, h0⟩ := main
    exact ⟨fun i => n - 1 - L i, hL.comp, by show n - 1 - L 0 = 3 * q; omega⟩

/-! ## Final steps: graceful segments, joins, leaf chains, assembly -/

theorem Tadj_irrefl (d y : ℕ) (hd : 1 ≤ d) : ¬ Tadj d y y := by
  unfold Tadj Tpar dEnd armRoot
  intro h
  rcases h with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> split_ifs at h1 <;> omega

/-- the cross condition for an outward segment on arm `X` -/
theorem cross_out {d X k0 L : ℕ} {S : Finset ℕ} (hX : 2 ≤ X ∧ X ≤ 7)
    (hfresh : ∀ i, i < L → X + 8 * (k0 + 1 + i) ∉ S)
    (hnext : X + 8 * (k0 + L + 1) ∉ S)
    (hd5 : X = 5 → k0 + L + 1 ≤ d) (hv : X = 5 → k0 + L + 1 = d → 1 ∉ S) :
    ∀ p ∈ S, ∀ i, i < L → Tadj d p (X + 8 * (k0 + 1 + i)) →
      p = (if k0 = 0 then armRoot X else X + 8 * k0) ∧ i = 0 := by
  intro p hp i hi h
  rcases (Tadj_arm_iff d X (k0 + 1 + i) p hX (by omega)).mp h with h1 | h1 | ⟨h5, hd, rfl⟩
  · by_cases hi0 : i = 0
    · subst hi0
      refine ⟨?_, rfl⟩
      rw [h1]
      by_cases hk : k0 = 0
      · rw [if_pos (by omega), if_pos hk]
      · rw [if_neg (by omega), if_neg hk]; congr 1
    · exfalso
      rw [if_neg (by omega)] at h1
      exact hfresh (i - 1) (by omega)
        (by rw [show X + 8 * (k0 + 1 + (i - 1)) = p by omega]; exact hp)
  · exfalso
    by_cases hiL : i + 1 < L
    · exact hfresh (i + 1) hiL (by rw [show X + 8 * (k0 + 1 + (i + 1)) = p by omega]; exact hp)
    · exact hnext (by rw [show X + 8 * (k0 + L + 1) = p by omega]; exact hp)
  · exfalso
    have := hd5 h5
    exact hv h5 (by omega) hp

namespace APc
variable {d q : ℕ}

/-- final step: attach a graceful segment on arm `X` (needs only `τ(x) ≤ L - 1`) -/
theorem attachGOut (A : APc d q) (X k0 L : ℕ) (hX : 2 ≤ X ∧ X ≤ 7) (hL : 1 ≤ L)
    (hx : (if k0 = 0 then armRoot X else X + 8 * k0) ∈ A.P.S)
    (hfresh : ∀ i, i < L → X + 8 * (k0 + 1 + i) ∉ A.P.S)
    (hnext : X + 8 * (k0 + L + 1) ∉ A.P.S)
    (hd5 : X = 5 → k0 + L + 1 ≤ d) (hv : X = 5 → k0 + L + 1 = d → 1 ∉ A.P.S)
    (hep : A.tau (if k0 = 0 then armRoot X else X + 8 * k0) ≤ L - 1) :
    ∃ G : Pc, G.Grace ∧ G.R = Tadj d ∧
      (∀ z, z ∈ G.S ↔ z ∈ A.P.S ∨ ∃ i, i < L ∧ X + 8 * (k0 + 1 + i) = z) ∧
      G.E.card = A.P.E.card + L ∧
      (∀ z ∈ A.P.S, G.f z = A.eps z ∨ G.f z = G.E.card - A.eps z) := by
  classical
  set x := (if k0 = 0 then armRoot X else X + 8 * k0) with hxdef
  have hs := segOut d X k0 L hX hL
  have hcross := cross_out (d := d) hX hfresh hnext hd5 hv
  have hfx := A.f_le hx
  have hth := A.hA.2.1
  set tg := if A.P.f x < A.th then L - 1 - A.tau x else A.tau x with htg
  obtain ⟨g, hg, hg0⟩ := epl L tg hL (by rw [htg]; split_ifs <;> omega)
  set nm : ℕ → ℕ := fun i => X + 8 * (k0 + 1 + i) with hnm
  set B := ipathPc (Tadj d) L nm (fun z => z / 8 - (k0 + 1)) g with hB
  have hBg : B.Grace := ipathPc_grace (R := Tadj d) (nm := nm) (pos := fun z => z / 8 - (k0 + 1)) hL
    (Tadj_symm d) hs.inj hs.hpos hs.cons hs.chord hg
  have hBS : ∀ z, z ∈ B.S ↔ ∃ i, i < L ∧ nm i = z := fun z => ipathPc_mem
  have hBE : B.E.card = L - 1 := by
    have h1 := hBg.2.1
    have h2 : B.S.card = L := ipathPc_card_S hs.inj
    omega
  have hBf0 : B.f (nm 0) = g 0 := by
    show g ((X + 8 * (k0 + 1 + 0)) / 8 - (k0 + 1)) = g 0
    congr 1; omega
  have hR : A.P.R = B.R := A.hR
  have hd : Disjoint A.P.S B.S := by
    rw [Finset.disjoint_left]
    intro z hzA hzB
    obtain ⟨i, hi, rfl⟩ := (hBS z).mp hzB
    exact hfresh i hi hzA
  have hw : nm 0 ∈ B.S := (hBS _).mpr ⟨0, by omega, rfl⟩
  have hxw : A.P.R x (nm 0) := by rw [A.hR]; exact hs.xw
  have hcr : ∀ p ∈ A.P.S, ∀ q' ∈ B.S, A.P.R p q' → p = x ∧ q' = nm 0 := by
    intro p hp q' hq' hr
    obtain ⟨i, hi, rfl⟩ := (hBS q').mp hq'
    rw [A.hR] at hr
    obtain ⟨h1, h2⟩ := hcross p hp i hi hr
    exact ⟨h1, by rw [h2]⟩
  have htau : A.tau x = if A.P.f x < A.th then A.th - 1 - A.P.f x else A.P.f x - A.th := rfl
  have hc : (A.P.f x < A.th ∧ B.f (nm 0) + (A.th - 1 - A.P.f x) = B.E.card) ∨
      (A.th ≤ A.P.f x ∧ B.f (nm 0) + A.th = A.P.f x) := by
    rw [hBf0, hg0, hBE, htg]
    by_cases hl : A.P.f x < A.th
    · left; rw [if_pos hl]; rw [htau, if_pos hl] at hep ⊢; omega
    · right; rw [if_neg hl]; rw [htau, if_neg hl]; omega
  have hG := Pc.ifgl A.hA hBg hR hd hx hw hxw hcr hc
  have hGE := Pc.ijoin_card_E (th := A.th) hR A.hA.1.1 hd hx hw hxw hcr
  rw [hBE] at hGE
  refine ⟨Pc.ijoin A.P B A.th x (nm 0), hG, A.hR, ?_, by rw [hGE]; omega, ?_⟩
  · intro z
    show z ∈ A.P.S ∪ B.S ↔ _
    rw [Finset.mem_union, hBS]
  · intro z hz
    have hle := A.f_le hz
    show (Pc.join A.P B A.th x (nm 0)).f z = _ ∨ (Pc.join A.P B A.th x (nm 0)).f z = _
    rw [hGE]
    unfold eps Pc.eps
    by_cases hl : A.P.f z < A.th
    · rw [Pc.join_f_lowA hz hl, if_pos hl]; left; rfl
    · rw [Pc.join_f_highA hz (by omega), if_neg hl, hBE]; right; omega

/-- join an α-piece and a graceful piece along the edge `x - w` -/
theorem joinG (A : APc d q) (B : Pc) (hB : B.Grace) (hBR : B.R = Tadj d) {x w : ℕ}
    (hx : x ∈ A.P.S) (hw : w ∈ B.S) (hxw : Tadj d x w) (hd : Disjoint A.P.S B.S)
    (hcross : ∀ p ∈ A.P.S, ∀ q' ∈ B.S, Tadj d p q' → p = x ∧ q' = w)
    (hlab : B.f w = A.tau x ∨ B.f w = B.E.card - A.tau x) (htb : A.tau x ≤ B.E.card) :
    ∃ G : Pc, G.Grace ∧ G.R = Tadj d ∧ (∀ z, z ∈ G.S ↔ z ∈ A.P.S ∨ z ∈ B.S) ∧
      G.E.card = A.P.E.card + B.E.card + 1 ∧
      (∀ z ∈ A.P.S, G.f z = A.eps z ∨ G.f z = G.E.card - A.eps z) := by
  classical
  have hfx := A.f_le hx
  have hth := A.hA.2.1
  have htau : A.tau x = if A.P.f x < A.th then A.th - 1 - A.P.f x else A.P.f x - A.th := rfl
  have hBw := hB.2.2.2.1 w hw
  -- choose B or its complement
  obtain ⟨B', hB', hB'R, hB'S, hB'E, hc⟩ : ∃ B' : Pc, B'.Grace ∧ B'.R = Tadj d ∧ B'.S = B.S ∧
      B'.E.card = B.E.card ∧
      ((A.P.f x < A.th ∧ B'.f w + (A.th - 1 - A.P.f x) = B'.E.card) ∨
        (A.th ≤ A.P.f x ∧ B'.f w + A.th = A.P.f x)) := by
    by_cases hl : A.P.f x < A.th
    · rw [htau, if_pos hl] at hlab htb
      by_cases h1 : B.f w = B.E.card - (A.th - 1 - A.P.f x)
      · exact ⟨B, hB, hBR, rfl, rfl, Or.inl ⟨hl, by omega⟩⟩
      · have h2 : B.f w = A.th - 1 - A.P.f x := by tauto
        refine ⟨B.cmp, Pc.cmp_grace hB, hBR, rfl, rfl, Or.inl ⟨hl, ?_⟩⟩
        show B.E.card - B.f w + _ = B.cmp.E.card
        rw [Pc.cmp_E]; omega
    · rw [htau, if_neg hl] at hlab htb
      by_cases h1 : B.f w = A.P.f x - A.th
      · exact ⟨B, hB, hBR, rfl, rfl, Or.inr ⟨by omega, by omega⟩⟩
      · have h2 : B.f w = B.E.card - (A.P.f x - A.th) := by tauto
        refine ⟨B.cmp, Pc.cmp_grace hB, hBR, rfl, rfl, Or.inr ⟨by omega, ?_⟩⟩
        show B.E.card - B.f w + _ = _
        omega
  have hR : A.P.R = B'.R := by rw [A.hR, hB'R]
  have hd' : Disjoint A.P.S B'.S := by rw [hB'S]; exact hd
  have hw' : w ∈ B'.S := by rw [hB'S]; exact hw
  have hxw' : A.P.R x w := by rw [A.hR]; exact hxw
  have hcr : ∀ p ∈ A.P.S, ∀ q' ∈ B'.S, A.P.R p q' → p = x ∧ q' = w := by
    intro p hp q' hq' hr
    rw [hB'S] at hq'; rw [A.hR] at hr
    exact hcross p hp q' hq' hr
  have hG := Pc.ifgl A.hA hB' hR hd' hx hw' hxw' hcr hc
  have hGE := Pc.ijoin_card_E (th := A.th) hR A.hA.1.1 hd' hx hw' hxw' hcr
  rw [hB'E] at hGE
  refine ⟨Pc.ijoin A.P B' A.th x w, hG, A.hR, ?_, hGE, ?_⟩
  · intro z
    show z ∈ A.P.S ∪ B'.S ↔ _
    rw [Finset.mem_union, hB'S]
  · intro z hz
    have hle := A.f_le hz
    show (Pc.join A.P B' A.th x w).f z = _ ∨ (Pc.join A.P B' A.th x w).f z = _
    rw [hGE]
    unfold eps Pc.eps
    by_cases hl : A.P.f z < A.th
    · rw [Pc.join_f_lowA hz hl, if_pos hl]; left; rfl
    · rw [Pc.join_f_highA hz (by omega), if_neg hl, hB'E]; right; omega

end APc

/-- the one-vertex α-piece -/
noncomputable def singlePc (d y : ℕ) : Pc where
  S := {y}
  R := Tadj d
  f := fun _ => 0

theorem singlePc_E (d y : ℕ) (hd : 1 ≤ d) : (singlePc d y).E = ∅ := by
  classical
  ext e
  rw [Pc.mem_E]
  simp only [singlePc, Finset.mem_singleton, Finset.notMem_empty, iff_false, not_and]
  intro h1 h2 h3
  omega

theorem singlePc_alpha (d y : ℕ) (hd : 1 ≤ d) : (singlePc d y).Alpha 1 := by
  have hE := singlePc_E d y hd
  refine ⟨⟨Tadj_symm d, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [hE]; simp [singlePc]
  · intro a ha b hb _
    simp only [singlePc, Finset.mem_singleton] at ha hb
    rw [ha, hb]
  · intro a _; rw [hE]; simp [singlePc]
  · intro e he; rw [hE] at he; simp at he
  · rw [hE]; simp
  · intro a ha b hb hr
    simp only [singlePc, Finset.mem_singleton] at ha hb
    rw [ha, hb] at hr
    exact absurd hr (Tadj_irrefl d y hd)

/-- one leaf added at a vertex labeled `0` or `m`; the new leaf gets label `0` -/
theorem leafStep {d : ℕ} (hd : 1 ≤ d) (G : Pc) (hG : G.Grace) (hR : G.R = Tadj d) {z y : ℕ}
    (hz : z ∈ G.S) (hy : y ∉ G.S) (hzy : Tadj d z y) (hcr : ∀ p ∈ G.S, Tadj d p y → p = z)
    (hgood : G.f z = 0 ∨ G.f z = G.E.card) :
    ∃ G' : Pc, G'.Grace ∧ G'.R = Tadj d ∧ (∀ s, s ∈ G'.S ↔ s ∈ G.S ∨ s = y) ∧
      G'.E.card = G.E.card + 1 ∧ G'.f y = 0 := by
  classical
  have hzle := hG.2.2.2.1 z hz
  obtain ⟨B, hB, hBR, hBS, hBE, hBz⟩ : ∃ B : Pc, B.Grace ∧ B.R = Tadj d ∧ B.S = G.S ∧
      B.E.card = G.E.card ∧ B.f z = B.E.card := by
    by_cases h : G.f z = G.E.card
    · exact ⟨G, hG, hR, rfl, rfl, h⟩
    · refine ⟨G.cmp, Pc.cmp_grace hG, hR, rfl, rfl, ?_⟩
      have : G.f z = 0 := by tauto
      show G.E.card - G.f z = G.cmp.E.card
      rw [Pc.cmp_E]; omega
  have hA := singlePc_alpha d y hd
  have hAE : (singlePc d y).E.card = 0 := by rw [singlePc_E d y hd]; rfl
  have hRR : (singlePc d y).R = B.R := by rw [hBR]; rfl
  have hdj : Disjoint (singlePc d y).S B.S := by
    rw [hBS]; simp [singlePc, hy]
  have hyA : y ∈ (singlePc d y).S := by simp [singlePc]
  have hzB : z ∈ B.S := by rw [hBS]; exact hz
  have hyz : (singlePc d y).R y z := Tadj_symm d _ _ hzy
  have hcross : ∀ p ∈ (singlePc d y).S, ∀ q' ∈ B.S, (singlePc d y).R p q' → p = y ∧ q' = z := by
    intro p hp q' hq' hr
    simp only [singlePc, Finset.mem_singleton] at hp
    subst hp
    rw [hBS] at hq'
    exact ⟨rfl, hcr q' hq' (Tadj_symm d _ _ hr)⟩
  have hc : ((singlePc d y).f y < 1 ∧ B.f z + (1 - 1 - (singlePc d y).f y) = B.E.card) ∨
      (1 ≤ (singlePc d y).f y ∧ B.f z + 1 = (singlePc d y).f y) := by
    left; refine ⟨by simp [singlePc], ?_⟩; simp [singlePc]; exact hBz
  have hJ := Pc.ifgl hA hB hRR hdj hyA hzB hyz hcross hc
  have hJE := Pc.ijoin_card_E (th := 1) hRR (Tadj_symm d) hdj hyA hzB hyz hcross
  rw [hAE, hBE] at hJE
  refine ⟨Pc.ijoin (singlePc d y) B 1 y z, hJ, rfl, ?_, by rw [hJE]; omega, ?_⟩
  · intro s
    show s ∈ (singlePc d y).S ∪ B.S ↔ _
    rw [Finset.mem_union, hBS]
    simp [singlePc]; tauto
  · show (Pc.join (singlePc d y) B 1 y z).f y = 0
    rw [Pc.join_f_lowA hyA (by simp [singlePc])]
    rfl

/-- a chain of leaves along arm `X` (positions `k0+1 … k0+L`) from a vertex labeled `0` or `m` -/
theorem leafChain {d : ℕ} (hd : 1 ≤ d) (X : ℕ) (hX : 2 ≤ X ∧ X ≤ 7) :
    ∀ L k0 (G : Pc), G.Grace → G.R = Tadj d →
      (if k0 = 0 then armRoot X else X + 8 * k0) ∈ G.S →
      (G.f (if k0 = 0 then armRoot X else X + 8 * k0) = 0 ∨
        G.f (if k0 = 0 then armRoot X else X + 8 * k0) = G.E.card) →
      (∀ i, i < L → X + 8 * (k0 + 1 + i) ∉ G.S) → X + 8 * (k0 + L + 1) ∉ G.S →
      (X = 5 → k0 + L + 1 ≤ d) → (X = 5 → k0 + L + 1 = d → 1 ∉ G.S) →
      ∃ G' : Pc, G'.Grace ∧ G'.R = Tadj d ∧
        (∀ s, s ∈ G'.S ↔ s ∈ G.S ∨ ∃ i, i < L ∧ X + 8 * (k0 + 1 + i) = s) ∧
        G'.E.card = G.E.card + L := by
  intro L
  induction L with
  | zero =>
    intro k0 G hG hR _ _ _ _ _ _
    exact ⟨G, hG, hR, fun s => by simp, rfl⟩
  | succ L ih =>
    intro k0 G hG hR hz hgood hfresh hnext hd5 hv
    set z := (if k0 = 0 then armRoot X else X + 8 * k0) with hzdef
    set y := X + 8 * (k0 + 1) with hy
    have hyS : y ∉ G.S := by have := hfresh 0 (by omega); simpa using this
    have hzy : Tadj d z y := by
      apply (Tadj_arm_iff d X (k0 + 1) z hX (by omega)).mpr
      left
      by_cases hk : k0 = 0
      · rw [hzdef, if_pos hk, if_pos (by omega)]
      · rw [hzdef, if_neg hk, if_neg (by omega)]; congr 1
    have hcr : ∀ p ∈ G.S, Tadj d p y → p = z := by
      intro p hp h
      have := cross_out (d := d) (L := 1) (k0 := k0) (S := G.S) hX
        (fun i hi => by have := hfresh 0 (by omega); rw [show i = 0 by omega]; simpa using this)
        (by intro h'; by_cases hL : L = 0
            · subst hL; exact hnext (by simpa using h')
            · exact hfresh 1 (by omega) (by rw [show X + 8 * (k0 + 1 + 1) = X + 8 * (k0 + 1 + 1) from rfl]; simpa [show k0 + 1 + 1 = k0 + 2 by omega] using h'))
        (fun h5 => by have := hd5 h5; omega)
        (fun h5 h' => hv h5 (by
            have := hd5 h5
            omega) ) p hp 0 (by omega) (by simpa using h)
      exact this.1
    obtain ⟨G1, hG1, hR1, hS1, hE1, hf1⟩ := leafStep hd G hG hR hz hyS hzy hcr hgood
    obtain ⟨G2, hG2, hR2, hS2, hE2⟩ := ih (k0 + 1) G1 hG1 hR1
      (by rw [if_neg (by omega)]; exact (hS1 _).mpr (Or.inr rfl))
      (by rw [if_neg (by omega)]; exact Or.inl hf1)
      (by
        intro i hi h
        rcases (hS1 _).mp h with h' | h'
        · exact hfresh (i + 1) (by omega) (by rw [show X + 8 * (k0 + 1 + (i + 1)) = X + 8 * (k0 + 1 + 1 + i) by ring]; exact h')
        · omega)
      (by
        intro h
        rcases (hS1 _).mp h with h' | h'
        · exact hnext (by rw [show X + 8 * (k0 + (L + 1) + 1) = X + 8 * (k0 + 1 + L + 1) by ring]; exact h')
        · omega)
      (fun h5 => by have := hd5 h5; omega)
      (fun h5 h' h1 => by
        rcases (hS1 _).mp h1 with h'' | h''
        · exact hv h5 (by omega) h''
        · omega)
    refine ⟨G2, hG2, hR2, ?_, by rw [hE2, hE1]; ring⟩
    intro s
    rw [hS2, hS1]
    constructor
    · rintro ((h | rfl) | ⟨i, hi, rfl⟩)
      · exact Or.inl h
      · exact Or.inr ⟨0, by omega, by rw [hy]⟩
      · exact Or.inr ⟨i + 1, by omega, by ring_nf⟩
    · rintro (h | ⟨i, hi, rfl⟩)
      · exact Or.inl (Or.inl h)
      · by_cases hi0 : i = 0
        · subst hi0; exact Or.inl (Or.inr (by rw [hy]))
        · exact Or.inr ⟨i - 1, by omega, by congr 1; omega⟩

/-- the final assembly -/
theorem canon_of_piece {a b c d e f : ℕ} (G : Pc) (hG : G.Grace) (hR : G.R = Tadj d)
    (hS : ∀ s, s ∈ G.S ↔ s ∈ Tset a b c d e f) : CanonGraceful a b c d e f :=
  ⟨G, hG, hS, fun x _ y _ => by rw [hR]⟩

/-! ## Tools for the constructions -/

theorem exists_out_iff (X k0 L z : ℕ) (hX : X < 8) :
    (∃ i, i < L ∧ X + 8 * (k0 + 1 + i) = z) ↔ (z % 8 = X ∧ k0 + 1 ≤ z / 8 ∧ z / 8 ≤ k0 + L) := by
  constructor
  · rintro ⟨i, hi, rfl⟩; omega
  · intro h; exact ⟨z / 8 - (k0 + 1), by omega, by omega⟩

theorem exists_in_iff (k0 L z : ℕ) (hk : L ≤ k0) :
    (∃ i, i < L ∧ 5 + 8 * (k0 - i) = z) ↔ (z % 8 = 5 ∧ k0 + 1 - L ≤ z / 8 ∧ z / 8 ≤ k0) := by
  constructor
  · rintro ⟨i, hi, rfl⟩; omega
  · intro h; exact ⟨k0 - z / 8, by omega, by omega⟩

theorem zz_peps (n i : ℕ) (hi : i < n) : peps n (zz n) i = i / 2 := by
  unfold peps zz; split_ifs <;> omega

theorem zz_ptau (n i : ℕ) (hi : i < n) :
    ptau n (zz n) i = if i % 2 = 0 then (n - 1) / 2 - i / 2 else n - 1 - i / 2 - (n - 1) / 2 - 1 := by
  unfold ptau zz; split_ifs <;> omega

/-- the vertex at position `i` of arm `X` (position `0` = the root) -/
def anode (X i : ℕ) : ℕ := if i = 0 then armRoot X else X + 8 * i

theorem armRoot_le (X : ℕ) : armRoot X ≤ 1 := by unfold armRoot; split_ifs <;> omega

/-- a start piece: root plus arm `X` up to position `x`, labeled by an α-path labeling -/
theorem startArm (d X x : ℕ) (hd : 1 ≤ d) (hX : 2 ≤ X ∧ X ≤ 7) (Lab : ℕ → ℕ)
    (hLab : PathAlpha (x + 1) Lab (x / 2)) (h0 : Lab 0 ≤ x / 2)
    (hd5 : X = 5 → x + 1 ≤ d) :
    ∃ A : APc d (par d (armRoot X)),
      (∀ z, z ∈ A.P.S ↔ z = armRoot X ∨ (z % 8 = X ∧ 1 ≤ z / 8 ∧ z / 8 ≤ x)) ∧ A.P.E.card = x ∧
      (∀ i, i ≤ x → A.eps (anode X i) = peps (x + 1) Lab i) ∧
      (∀ i, i ≤ x → A.tau (anode X i) = ptau (x + 1) Lab i) := by
  have hr := armRoot_le X
  have hnm0 : anode X 0 = armRoot X := by simp [anode]
  have hpar0 : ∀ i, 1 ≤ i → par d (X + 8 * i) = (par d (armRoot X) + i) % 2 := by
    intro i hi
    rw [par_arm d X i hX hi]
    unfold armRoot
    split_ifs with h1 h2 h2
    · omega
    · rw [par_one]; omega
    · rw [par_zero]; omega
    · omega
  have hlab : (x + 1 - 1) / 2 = x / 2 := by omega
  rw [← hlab] at hLab h0
  obtain ⟨A, hS, hE, heps, htau⟩ := startPath d (x + 1) (anode X)
    (fun z => if z = armRoot X then 0 else z / 8) Lab (by omega)
    (by intro i j _ _ e; unfold anode at e; split_ifs at e <;> omega)
    (by
      intro i _
      unfold anode
      split_ifs <;> omega)
    (by
      intro i hi
      unfold anode
      rw [if_neg (show i + 1 ≠ 0 by omega)]
      apply (Tadj_arm_iff d X (i + 1) _ hX (by omega)).mpr
      left
      by_cases h : i = 0
      · rw [if_pos h, if_pos (by omega)]
      · rw [if_neg h, if_neg (by omega)]; congr 1)
    (by
      intro i j hi hj h
      unfold anode at h
      by_cases hj0 : j = 0
      · rw [if_pos hj0] at h
        by_cases hi0 : i = 0
        · rw [if_pos hi0] at h; exact absurd h (Tadj_irrefl d _ hd)
        · rw [if_neg hi0] at h
          rcases (Tadj_arm_iff d X i _ hX (by omega)).mp (Tadj_symm d _ _ h) with h1 | h1 | ⟨h5, _, h1⟩
          · split_ifs at h1 <;> omega
          · unfold armRoot at h1; split_ifs at h1 <;> omega
          · unfold armRoot at h1; rw [if_pos (by omega)] at h1; omega
      · rw [if_neg hj0] at h
        rcases (Tadj_arm_iff d X j _ hX (by omega)).mp h with h1 | h1 | ⟨h5, _, h1⟩
        · split_ifs at h1 with h2 h3 h3
          · omega
          · unfold armRoot at h1; split_ifs at h1 <;> omega
          · unfold armRoot at h1; split_ifs at h1 <;> omega
          · omega
        · split_ifs at h1 <;> [skip; omega]
          unfold armRoot at h1; split_ifs at h1 <;> omega
        · split_ifs at h1
          · unfold armRoot at h1; rw [if_pos (by omega)] at h1; omega
          · omega)
    (by
      intro i hi
      rw [hnm0]
      unfold anode
      by_cases h : i = 0
      · rw [if_pos h, h]; have := par_le_one d (armRoot X); omega
      · rw [if_neg h]; exact hpar0 i (by omega))
    hLab h0
  refine ⟨A, ?_, by rw [hE]; omega, fun i hi => heps i (by omega), fun i hi => htau i (by omega)⟩
  intro z
  rw [hS]
  constructor
  · rintro ⟨i, hi, rfl⟩
    unfold anode
    split_ifs with h
    · left; rfl
    · right; omega
  · rintro (rfl | h)
    · exact ⟨0, by omega, by simp [anode]⟩
    · refine ⟨z / 8, by omega, ?_⟩
      unfold anode
      rw [if_neg (by omega)]
      omega

/-- change the parity index of an α-piece along an equation -/
def APc.recast {d q q' : ℕ} (A : APc d q) (h : q = q') : APc d q' :=
  ⟨A.P, A.th, A.hR, A.hA, fun z hz => by rw [← h]; exact A.hlow z hz, h ▸ A.hq⟩

theorem APc.recast_P {d q q' : ℕ} (A : APc d q) (h : q = q') : (A.recast h).P = A.P := rfl
theorem APc.recast_eps {d q q' : ℕ} (A : APc d q) (h : q = q') (z : ℕ) :
    (A.recast h).eps z = A.eps z := rfl
theorem APc.recast_tau {d q q' : ℕ} (A : APc d q) (h : q = q') (z : ℕ) :
    (A.recast h).tau z = A.tau z := rfl

namespace APc
variable {d q : ℕ}

/-- attach an α-EPL segment along arm `X` at its root -/
theorem attachRoot (A : APc d q) (X L : ℕ) (hX : 2 ≤ X ∧ X ≤ 7) (hL : 1 ≤ L)
    (hx : armRoot X ∈ A.P.S) (hfresh : ∀ i, i < L → X + 8 * (1 + i) ∉ A.P.S)
    (hnext : X + 8 * (L + 1) ∉ A.P.S)
    (hd5 : X = 5 → L + 1 ≤ d) (hv : X = 5 → L + 1 = d → 1 ∉ A.P.S)
    (hok : AeplOK L (A.tau (armRoot X))) :
    ∃ B : APc d q, (∀ z, z ∈ B.P.S ↔ z ∈ A.P.S ∨ (z % 8 = X ∧ 1 ≤ z / 8 ∧ z / 8 ≤ L)) ∧
      B.P.E.card = A.P.E.card + L ∧
      (∀ z ∈ A.P.S, B.eps z = A.eps z) ∧
      (∀ z ∈ A.P.S, B.tau z = A.tau z + (L + (par d z + par d (armRoot X)) % 2) / 2) ∧
      B.tau (X + 8 * L) = A.tau (armRoot X) := by
  obtain ⟨B, h1, h2, h3, h4, h5⟩ := A.attachOut X 0 L hX hL (by rw [if_pos rfl]; exact hx)
    (by intro i hi; rw [show 0 + 1 + i = 1 + i by ring]; exact hfresh i hi)
    (by rw [show 0 + L + 1 = L + 1 by ring]; exact hnext)
    (fun h => by have := hd5 h; omega) (fun h e => hv h (by omega))
    (by rw [if_pos rfl]; exact hok)
  refine ⟨B, fun z => by rw [h1, exists_out_iff X 0 L z (by omega), zero_add, zero_add], h2, h3, ?_, ?_⟩
  · intro z hz; rw [h4 z hz, if_pos rfl]
  · rw [show X + 8 * L = X + 8 * (0 + L) by ring, h5, if_pos rfl]

/-- attach an α-EPL segment along arm `X` at position `k ≥ 1` -/
theorem attachArm (A : APc d q) (X k L : ℕ) (hX : 2 ≤ X ∧ X ≤ 7) (hk : 1 ≤ k) (hL : 1 ≤ L)
    (hx : X + 8 * k ∈ A.P.S) (hfresh : ∀ i, i < L → X + 8 * (k + 1 + i) ∉ A.P.S)
    (hnext : X + 8 * (k + L + 1) ∉ A.P.S)
    (hd5 : X = 5 → k + L + 1 ≤ d) (hv : X = 5 → k + L + 1 = d → 1 ∉ A.P.S)
    (hok : AeplOK L (A.tau (X + 8 * k))) :
    ∃ B : APc d q, (∀ z, z ∈ B.P.S ↔ z ∈ A.P.S ∨ (z % 8 = X ∧ k + 1 ≤ z / 8 ∧ z / 8 ≤ k + L)) ∧
      B.P.E.card = A.P.E.card + L ∧
      (∀ z ∈ A.P.S, B.eps z = A.eps z) ∧
      (∀ z ∈ A.P.S, B.tau z = A.tau z + (L + (par d z + par d (X + 8 * k)) % 2) / 2) ∧
      B.tau (X + 8 * (k + L)) = A.tau (X + 8 * k) := by
  have hk0 : k ≠ 0 := by omega
  obtain ⟨B, h1, h2, h3, h4, h5⟩ := A.attachOut X k L hX hL (by rw [if_neg hk0]; exact hx)
    hfresh hnext hd5 hv (by rw [if_neg hk0]; exact hok)
  refine ⟨B, fun z => by rw [h1, exists_out_iff X k L z (by omega)], h2, h3, ?_, ?_⟩
  · intro z hz; rw [h4 z hz, if_neg hk0]
  · rw [h5, if_neg hk0]

/-- final graceful segment along arm `X` at its root -/
theorem attachGRoot (A : APc d q) (X L : ℕ) (hX : 2 ≤ X ∧ X ≤ 7) (hL : 1 ≤ L)
    (hx : armRoot X ∈ A.P.S) (hfresh : ∀ i, i < L → X + 8 * (1 + i) ∉ A.P.S)
    (hnext : X + 8 * (L + 1) ∉ A.P.S)
    (hd5 : X = 5 → L + 1 ≤ d) (hv : X = 5 → L + 1 = d → 1 ∉ A.P.S)
    (hep : A.tau (armRoot X) ≤ L - 1) :
    ∃ G : Pc, G.Grace ∧ G.R = Tadj d ∧
      (∀ z, z ∈ G.S ↔ z ∈ A.P.S ∨ (z % 8 = X ∧ 1 ≤ z / 8 ∧ z / 8 ≤ L)) ∧
      G.E.card = A.P.E.card + L ∧
      (∀ z ∈ A.P.S, G.f z = A.eps z ∨ G.f z = G.E.card - A.eps z) := by
  obtain ⟨G, h1, h2, h3, h4, h5⟩ := A.attachGOut X 0 L hX hL (by rw [if_pos rfl]; exact hx)
    (by intro i hi; rw [show 0 + 1 + i = 1 + i by ring]; exact hfresh i hi)
    (by rw [show 0 + L + 1 = L + 1 by ring]; exact hnext)
    (fun h => by have := hd5 h; omega) (fun h e => hv h (by omega))
    (by rw [if_pos rfl]; exact hep)
  exact ⟨G, h1, h2, fun z => by rw [h3, exists_out_iff X 0 L z (by omega), zero_add, zero_add], h4, h5⟩

/-- final graceful segment along arm `X` at position `k ≥ 1` -/
theorem attachGArm (A : APc d q) (X k L : ℕ) (hX : 2 ≤ X ∧ X ≤ 7) (hk : 1 ≤ k) (hL : 1 ≤ L)
    (hx : X + 8 * k ∈ A.P.S) (hfresh : ∀ i, i < L → X + 8 * (k + 1 + i) ∉ A.P.S)
    (hnext : X + 8 * (k + L + 1) ∉ A.P.S)
    (hd5 : X = 5 → k + L + 1 ≤ d) (hv : X = 5 → k + L + 1 = d → 1 ∉ A.P.S)
    (hep : A.tau (X + 8 * k) ≤ L - 1) :
    ∃ G : Pc, G.Grace ∧ G.R = Tadj d ∧
      (∀ z, z ∈ G.S ↔ z ∈ A.P.S ∨ (z % 8 = X ∧ k + 1 ≤ z / 8 ∧ z / 8 ≤ k + L)) ∧
      G.E.card = A.P.E.card + L ∧
      (∀ z ∈ A.P.S, G.f z = A.eps z ∨ G.f z = G.E.card - A.eps z) := by
  have hk0 : k ≠ 0 := by omega
  obtain ⟨G, h1, h2, h3, h4, h5⟩ := A.attachGOut X k L hX hL (by rw [if_neg hk0]; exact hx)
    hfresh hnext hd5 hv (by rw [if_neg hk0]; exact hep)
  exact ⟨G, h1, h2, fun z => by rw [h3, exists_out_iff X k L z (by omega)], h4, h5⟩

/-- attach an α-EPL segment on the `d`-path at `v`: positions `d-1, …, d-L` -/
theorem attachDV (A : APc d q) (L : ℕ) (hL : 1 ≤ L) (hLd : L + 1 ≤ d)
    (hx : 1 ∈ A.P.S) (hfresh : ∀ i, i < L → 5 + 8 * (d - 1 - i) ∉ A.P.S)
    (hnext0 : d - 1 = L → 0 ∉ A.P.S) (hnext : L < d - 1 → 5 + 8 * (d - 1 - L) ∉ A.P.S)
    (hbeyond : 5 + 8 * d ∉ A.P.S)
    (hok : AeplOK L (A.tau 1)) :
    ∃ B : APc d q, (∀ z, z ∈ B.P.S ↔ z ∈ A.P.S ∨ (z % 8 = 5 ∧ d - L ≤ z / 8 ∧ z / 8 ≤ d - 1)) ∧
      B.P.E.card = A.P.E.card + L ∧
      (∀ z ∈ A.P.S, B.eps z = A.eps z) ∧
      (∀ z ∈ A.P.S, B.tau z = A.tau z + (L + (par d z + par d 1) % 2) / 2) ∧
      B.tau (5 + 8 * (d - L)) = A.tau 1 := by
  have hv : d - 1 + 1 = d := by omega
  obtain ⟨B, h1, h2, h3, h4, h5⟩ := A.attachIn (d - 1) L hL (by omega) (by omega)
    (by rw [if_pos hv]; exact hx) hfresh hnext0 hnext (fun _ => hbeyond)
    (by rw [if_pos hv]; exact hok)
  refine ⟨B, fun z => by rw [h1, exists_in_iff (d - 1) L z (by omega), show d - 1 + 1 - L = d - L by omega], h2, h3, ?_, ?_⟩
  · intro z hz; rw [h4 z hz, if_pos hv]
  · rw [show d - L = d - 1 + 1 - L by omega, h5, if_pos hv]

/-- attach an α-EPL segment on the `d`-path at position `k+1` going toward `u`:
positions `k, …, k-L+1` -/
theorem attachDD (A : APc d q) (k L : ℕ) (hL : 1 ≤ L) (hk : L ≤ k) (hkd : k + 2 ≤ d)
    (hx : 5 + 8 * (k + 1) ∈ A.P.S) (hfresh : ∀ i, i < L → 5 + 8 * (k - i) ∉ A.P.S)
    (hnext0 : k = L → 0 ∉ A.P.S) (hnext : L < k → 5 + 8 * (k - L) ∉ A.P.S)
    (hok : AeplOK L (A.tau (5 + 8 * (k + 1)))) :
    ∃ B : APc d q, (∀ z, z ∈ B.P.S ↔ z ∈ A.P.S ∨ (z % 8 = 5 ∧ k + 1 - L ≤ z / 8 ∧ z / 8 ≤ k)) ∧
      B.P.E.card = A.P.E.card + L ∧
      (∀ z ∈ A.P.S, B.eps z = A.eps z) ∧
      (∀ z ∈ A.P.S, B.tau z = A.tau z + (L + (par d z + par d (5 + 8 * (k + 1))) % 2) / 2) ∧
      B.tau (5 + 8 * (k + 1 - L)) = A.tau (5 + 8 * (k + 1)) := by
  have hv : k + 1 ≠ d := by omega
  obtain ⟨B, h1, h2, h3, h4, h5⟩ := A.attachIn k L hL hk (by omega)
    (by rw [if_neg hv]; exact hx) hfresh hnext0 hnext (fun h => absurd h hv)
    (by rw [if_neg hv]; exact hok)
  refine ⟨B, fun z => by rw [h1, exists_in_iff k L z hk], h2, h3, ?_, ?_⟩
  · intro z hz; rw [h4 z hz, if_neg hv]
  · rw [h5, if_neg hv]

end APc

/-! ## IVL0: α-labelings of two arms at a root with the root at `ε = 0` -/

theorem par_arm_root (d X k : ℕ) (hX : 2 ≤ X ∧ X ≤ 7) (hk : 1 ≤ k) :
    par d (X + 8 * k) = (par d (armRoot X) + k) % 2 := by
  rw [par_arm d X k hX hk]
  unfold armRoot
  split_ifs with h1 h2 h2
  · omega
  · rw [par_one]; omega
  · rw [par_zero]; omega
  · omega

theorem armRoot_lt (X : ℕ) : armRoot X < 2 := by unfold armRoot; split_ifs <;> omega

/-- shape of a root with two arms -/
def Sh2 (r X x Y y z : ℕ) : Prop :=
  z = r ∨ (z % 8 = X ∧ 1 ≤ z / 8 ∧ z / 8 ≤ x) ∨ (z % 8 = Y ∧ 1 ≤ z / 8 ∧ z / 8 ≤ y)

/-- standing hypotheses: two distinct non-path arms at the root `r` -/
structure Arms2 (r X Y : ℕ) : Prop where
  hX : 2 ≤ X ∧ X ≤ 7
  hY : 2 ≤ Y ∧ Y ≤ 7
  hXY : X ≠ Y
  hX5 : X ≠ 5
  hY5 : Y ≠ 5
  hrX : armRoot X = r
  hrY : armRoot Y = r

theorem Arms2.symm {r X Y : ℕ} (h : Arms2 r X Y) : Arms2 r Y X :=
  ⟨h.hY, h.hX, h.hXY.symm, h.hY5, h.hX5, h.hrY, h.hrX⟩

/-- IVL0: an α-piece on a root and two arms with the root at `ε = 0` -/
def IVL0P (d r X Y x y : ℕ) : Prop :=
  ∃ A : APc d (par d r), (∀ z, z ∈ A.P.S ↔ Sh2 r X x Y y z) ∧
    A.P.E.card = x + y ∧ A.eps r = 0 ∧ A.tau r = x / 2 + y / 2

theorem ivl0_symm {d r X Y x y : ℕ} (H : IVL0P d r X Y x y) : IVL0P d r Y X y x := by
  obtain ⟨A, hS, hE, he, ht⟩ := H
  refine ⟨A, fun z => by rw [hS]; unfold Sh2; tauto, by rw [hE]; ring, he, by rw [ht]; ring⟩

/-- start: zigzag along arm `X` from its root -/
theorem startZZ (d X x : ℕ) (hd : 1 ≤ d) (hX : 2 ≤ X ∧ X ≤ 7) (hX5 : X ≠ 5) (hx : 1 ≤ x) :
    ∃ A : APc d (par d (armRoot X)),
      (∀ z, z ∈ A.P.S ↔ z = armRoot X ∨ (z % 8 = X ∧ 1 ≤ z / 8 ∧ z / 8 ≤ x)) ∧ A.P.E.card = x ∧
      A.eps (armRoot X) = 0 ∧ A.tau (armRoot X) = x / 2 ∧
      (∀ i, 1 ≤ i → i ≤ x → A.eps (X + 8 * i) = i / 2) ∧
      (∀ i, 1 ≤ i → i ≤ x → A.tau (X + 8 * i) =
        if i % 2 = 0 then x / 2 - i / 2 else x - i / 2 - x / 2 - 1) := by
  obtain ⟨A0, hS0, hE0, he0, ht0⟩ := startArm d X x hd hX (zz (x + 1))
    (by have := zz_alpha (x + 1) (by omega); rwa [show (x + 1 - 1) / 2 = x / 2 by omega] at this)
    (by simp [zz]) (fun e => absurd e hX5)
  refine ⟨A0, hS0, hE0, ?_, ?_, ?_, ?_⟩
  · have := he0 0 (by omega); simp only [anode, if_true] at this; rw [this, zz_peps _ _ (by omega)]
  · have := ht0 0 (by omega); simp only [anode, if_true] at this; rw [this, zz_ptau _ _ (by omega)]
    simp
  · intro i hi1 hix
    have := he0 i hix
    simp only [anode, if_neg (show i ≠ 0 by omega)] at this
    rw [this, zz_peps _ _ (by omega)]
  · intro i hi1 hix
    have := ht0 i hix
    simp only [anode, if_neg (show i ≠ 0 by omega)] at this
    rw [this, zz_ptau _ _ (by omega)]
    simp only [show x + 1 - 1 = x by omega]

/-- program a: zigzag along `X`, then `Y` at the root -/
theorem ivl0_a {d r X Y x y : ℕ} (hd : 1 ≤ d) (h : Arms2 r X Y) (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hok : AeplOK y (x / 2)) : IVL0P d r X Y x y := by
  obtain ⟨hX, hY, hXY, hX5, hY5, hrX, hrY⟩ := h
  subst hrX
  have hr2 := armRoot_lt X
  obtain ⟨A0, hS0, hE0, e0, t0, _, _⟩ := startZZ d X x hd hX hX5 hx
  have hrS : armRoot X ∈ A0.P.S := by rw [hS0]; left; rfl
  obtain ⟨B, hS, hE, he, ht, _⟩ := A0.attachRoot Y y hY hy (by rw [hrY]; exact hrS)
    (by intro i hi hm; rw [hS0] at hm; omega)
    (by intro hm; rw [hS0] at hm; omega)
    (fun e => absurd e hY5) (fun e => absurd e hY5)
    (by rw [hrY, t0]; exact hok)
  refine ⟨B, ?_, by rw [hE, hE0], by rw [he _ hrS, e0], ?_⟩
  · intro z; rw [hS, hS0]; unfold Sh2; omega
  · rw [ht _ hrS, t0, hrY]
    have : (par d (armRoot X) + par d (armRoot X)) % 2 = 0 := by omega
    rw [this]; omega

/-- program b: `X1`, then `Y1` at the root, then the two tails -/
theorem ivl0_b {d r X Y x y : ℕ} (hd : 1 ≤ d) (h : Arms2 r X Y) (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hok1 : AeplOK (x - 1) 1) (hok2 : AeplOK (y - 1) ((x - 1) / 2)) : IVL0P d r X Y x y := by
  obtain ⟨hX, hY, hXY, hX5, hY5, hrX, hrY⟩ := h
  subst hrX
  have hr2 := armRoot_lt X
  have pX1 := par_arm_root d X 1 hX (by omega)
  have pY1 := par_arm_root d Y 1 hY (by omega)
  rw [hrY] at pY1
  have pr := par_le_one d (armRoot X)
  obtain ⟨A0, hS0, hE0, e0, t0, _, tX⟩ := startZZ d X 1 hd hX hX5 (by omega)
  have tX1 : A0.tau (X + 8 * 1) = 0 := by rw [tX 1 (by omega) (by omega)]; simp
  have hrS0 : armRoot X ∈ A0.P.S := by rw [hS0]; left; rfl
  have hX1S0 : X + 8 * 1 ∈ A0.P.S := by rw [hS0]; right; omega
  obtain ⟨A1, hS1, hE1, he1, ht1, hY1⟩ := A0.attachRoot Y 1 hY (by omega)
    (by rw [hrY]; exact hrS0)
    (by intro i hi hm; rw [hS0] at hm; omega)
    (by intro hm; rw [hS0] at hm; omega)
    (fun e => absurd e hY5) (fun e => absurd e hY5)
    (by rw [hrY, t0]; exact ⟨by omega, by omega, by omega⟩)
  rw [hrY] at ht1 hY1
  have hS1' : ∀ z, z ∈ A1.P.S ↔ z = armRoot X ∨ (z % 8 = X ∧ z / 8 = 1) ∨ (z % 8 = Y ∧ z / 8 = 1) := by
    intro z; rw [hS1, hS0]; omega
  have hrS1 : armRoot X ∈ A1.P.S := by rw [hS1']; left; rfl
  have hX1S1 : X + 8 * 1 ∈ A1.P.S := by rw [hS1']; right; left; omega
  have hY1S1 : Y + 8 * 1 ∈ A1.P.S := by rw [hS1']; right; right; omega
  have t1r : A1.tau (armRoot X) = 0 := by
    rw [ht1 _ hrS0, t0]; have : (par d (armRoot X) + par d (armRoot X)) % 2 = 0 := by omega
    rw [this]
  have t1X : A1.tau (X + 8 * 1) = 1 := by rw [ht1 _ hX1S0, tX1, pX1]; omega
  have t1Y : A1.tau (Y + 8 * 1) = 0 := by rw [hY1, t0]
  have e1r : A1.eps (armRoot X) = 0 := by rw [he1 _ hrS0, e0]
  obtain ⟨A2, hS2, hE2, he2, ht2, _⟩ := A1.attachArm X 1 (x - 1) hX (by omega) (by omega) hX1S1
    (by intro i hi hm; rw [hS1'] at hm; omega)
    (by intro hm; rw [hS1'] at hm; omega)
    (fun e => absurd e hX5) (fun e => absurd e hX5)
    (by rw [t1X]; exact hok1)
  have hS2' : ∀ z, z ∈ A2.P.S ↔ z = armRoot X ∨ (z % 8 = X ∧ 1 ≤ z / 8 ∧ z / 8 ≤ x) ∨
      (z % 8 = Y ∧ z / 8 = 1) := by
    intro z; rw [hS2, hS1']; omega
  have t2r : A2.tau (armRoot X) = x / 2 := by
    rw [ht2 _ hrS1, t1r, pX1]
    have : (par d (armRoot X) + (par d (armRoot X) + 1) % 2) % 2 = 1 := by omega
    rw [this]; omega
  have t2Y : A2.tau (Y + 8 * 1) = (x - 1) / 2 := by
    rw [ht2 _ hY1S1, t1Y, pX1, pY1]
    have : ((par d (armRoot X) + 1) % 2 + (par d (armRoot X) + 1) % 2) % 2 = 0 := by omega
    rw [this]; omega
  have e2r : A2.eps (armRoot X) = 0 := by rw [he2 _ hrS1, e1r]
  have hrS2 : armRoot X ∈ A2.P.S := by rw [hS2']; left; rfl
  have hY1S2 : Y + 8 * 1 ∈ A2.P.S := by rw [hS2']; right; right; omega
  obtain ⟨A3, hS3, hE3, he3, ht3, _⟩ := A2.attachArm Y 1 (y - 1) hY (by omega) (by omega) hY1S2
    (by intro i hi hm; rw [hS2'] at hm; omega)
    (by intro hm; rw [hS2'] at hm; omega)
    (fun e => absurd e hY5) (fun e => absurd e hY5)
    (by rw [t2Y]; exact hok2)
  refine ⟨A3, ?_, by rw [hE3, hE2, hE1, hE0]; omega, by rw [he3 _ hrS2, e2r], ?_⟩
  · intro z; rw [hS3, hS2']; unfold Sh2; omega
  · rw [ht3 _ hrS2, t2r, pY1]
    have : (par d (armRoot X) + (par d (armRoot X) + 1) % 2) % 2 = 1 := by omega
    rw [this]; omega

/-- program s0: `X1`, then `Y` at the root, then the `X` tail -/
theorem ivl0_s0 {d r X Y x y : ℕ} (hd : 1 ≤ d) (h : Arms2 r X Y) (hx : 2 ≤ x) (hy : 1 ≤ y)
    (hok : AeplOK (x - 1) ((y + 1) / 2)) : IVL0P d r X Y x y := by
  obtain ⟨hX, hY, hXY, hX5, hY5, hrX, hrY⟩ := h
  subst hrX
  have hr2 := armRoot_lt X
  have pX1 := par_arm_root d X 1 hX (by omega)
  have pr := par_le_one d (armRoot X)
  obtain ⟨A0, hS0, hE0, e0, t0, _, tX⟩ := startZZ d X 1 hd hX hX5 (by omega)
  have tX1 : A0.tau (X + 8 * 1) = 0 := by rw [tX 1 (by omega) (by omega)]; simp
  have hrS0 : armRoot X ∈ A0.P.S := by rw [hS0]; left; rfl
  have hX1S0 : X + 8 * 1 ∈ A0.P.S := by rw [hS0]; right; omega
  obtain ⟨A1, hS1, hE1, he1, ht1, _⟩ := A0.attachRoot Y y hY hy
    (by rw [hrY]; exact hrS0)
    (by intro i hi hm; rw [hS0] at hm; omega)
    (by intro hm; rw [hS0] at hm; omega)
    (fun e => absurd e hY5) (fun e => absurd e hY5)
    (by rw [hrY, t0]; exact ⟨by omega, by omega, by omega⟩)
  rw [hrY] at ht1
  have hS1' : ∀ z, z ∈ A1.P.S ↔ z = armRoot X ∨ (z % 8 = X ∧ z / 8 = 1) ∨
      (z % 8 = Y ∧ 1 ≤ z / 8 ∧ z / 8 ≤ y) := by
    intro z; rw [hS1, hS0]; omega
  have t1r : A1.tau (armRoot X) = y / 2 := by
    rw [ht1 _ hrS0, t0]; have : (par d (armRoot X) + par d (armRoot X)) % 2 = 0 := by omega
    rw [this]; omega
  have t1X : A1.tau (X + 8 * 1) = (y + 1) / 2 := by
    rw [ht1 _ hX1S0, tX1, pX1]
    have : ((par d (armRoot X) + 1) % 2 + par d (armRoot X)) % 2 = 1 := by omega
    rw [this]; omega
  have hrS1 : armRoot X ∈ A1.P.S := by rw [hS1']; left; rfl
  have hX1S1 : X + 8 * 1 ∈ A1.P.S := by rw [hS1']; right; left; omega
  obtain ⟨A2, hS2, hE2, he2, ht2, _⟩ := A1.attachArm X 1 (x - 1) hX (by omega) (by omega) hX1S1
    (by intro i hi hm; rw [hS1'] at hm; omega)
    (by intro hm; rw [hS1'] at hm; omega)
    (fun e => absurd e hX5) (fun e => absurd e hX5)
    (by rw [t1X]; exact hok)
  refine ⟨A2, ?_, by rw [hE2, hE1, hE0]; omega, by rw [he2 _ hrS1, he1 _ hrS0, e0], ?_⟩
  · intro z; rw [hS2, hS1']; unfold Sh2; omega
  · rw [ht2 _ hrS1, t1r, pX1]
    have : (par d (armRoot X) + (par d (armRoot X) + 1) % 2) % 2 = 1 := by omega
    rw [this]; omega

/-- program s1: `X1`, `X2`, then `Y` at the root, then the `X` tail -/
theorem ivl0_s1 {d r X Y x y : ℕ} (hd : 1 ≤ d) (h : Arms2 r X Y) (hx : 3 ≤ x) (hy : 1 ≤ y)
    (hok1 : AeplOK y 1) (hok2 : AeplOK (x - 2) (y / 2)) : IVL0P d r X Y x y := by
  obtain ⟨hX, hY, hXY, hX5, hY5, hrX, hrY⟩ := h
  subst hrX
  have hr2 := armRoot_lt X
  have pX1 := par_arm_root d X 1 hX (by omega)
  have pX2 := par_arm_root d X 2 hX (by omega)
  have pr := par_le_one d (armRoot X)
  obtain ⟨A0, hS0, hE0, e0, t0, _, tX⟩ := startZZ d X 1 hd hX hX5 (by omega)
  have tX1 : A0.tau (X + 8 * 1) = 0 := by rw [tX 1 (by omega) (by omega)]; simp
  have hrS0 : armRoot X ∈ A0.P.S := by rw [hS0]; left; rfl
  have hX1S0 : X + 8 * 1 ∈ A0.P.S := by rw [hS0]; right; omega
  obtain ⟨A1, hS1, hE1, he1, ht1, hX2⟩ := A0.attachArm X 1 1 hX (by omega) (by omega) hX1S0
    (by intro i hi hm; rw [hS0] at hm; omega)
    (by intro hm; rw [hS0] at hm; omega)
    (fun e => absurd e hX5) (fun e => absurd e hX5)
    (by rw [tX1]; exact ⟨by omega, by omega, by omega⟩)
  have hS1' : ∀ z, z ∈ A1.P.S ↔ z = armRoot X ∨ (z % 8 = X ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 2) := by
    intro z; rw [hS1, hS0]; omega
  have t1r : A1.tau (armRoot X) = 1 := by
    rw [ht1 _ hrS0, t0, pX1]
    have : (par d (armRoot X) + (par d (armRoot X) + 1) % 2) % 2 = 1 := by omega
    rw [this]
  have t1X2 : A1.tau (X + 8 * 2) = 0 := by
    rw [show X + 8 * 2 = X + 8 * (1 + 1) by ring, hX2, tX1]
  have hrS1 : armRoot X ∈ A1.P.S := by rw [hS1']; left; rfl
  have hX2S1 : X + 8 * 2 ∈ A1.P.S := by rw [hS1']; right; omega
  obtain ⟨A2, hS2, hE2, he2, ht2, _⟩ := A1.attachRoot Y y hY hy
    (by rw [hrY]; exact hrS1)
    (by intro i hi hm; rw [hS1'] at hm; omega)
    (by intro hm; rw [hS1'] at hm; omega)
    (fun e => absurd e hY5) (fun e => absurd e hY5)
    (by rw [hrY, t1r]; exact hok1)
  rw [hrY] at ht2
  have hS2' : ∀ z, z ∈ A2.P.S ↔ z = armRoot X ∨ (z % 8 = X ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 2) ∨
      (z % 8 = Y ∧ 1 ≤ z / 8 ∧ z / 8 ≤ y) := by
    intro z; rw [hS2, hS1']; omega
  have t2r : A2.tau (armRoot X) = 1 + y / 2 := by
    rw [ht2 _ hrS1, t1r]; have : (par d (armRoot X) + par d (armRoot X)) % 2 = 0 := by omega
    rw [this]; omega
  have t2X2 : A2.tau (X + 8 * 2) = y / 2 := by
    rw [ht2 _ hX2S1, t1X2, pX2]
    have : ((par d (armRoot X) + 2) % 2 + par d (armRoot X)) % 2 = 0 := by omega
    rw [this]; omega
  have hrS2 : armRoot X ∈ A2.P.S := by rw [hS2']; left; rfl
  have hX2S2 : X + 8 * 2 ∈ A2.P.S := by rw [hS2']; right; left; omega
  obtain ⟨A3, hS3, hE3, he3, ht3, _⟩ := A2.attachArm X 2 (x - 2) hX (by omega) (by omega) hX2S2
    (by intro i hi hm; rw [hS2'] at hm; omega)
    (by intro hm; rw [hS2'] at hm; omega)
    (fun e => absurd e hX5) (fun e => absurd e hX5)
    (by rw [t2X2]; exact hok2)
  refine ⟨A3, ?_, by rw [hE3, hE2, hE1, hE0]; omega,
    by rw [he3 _ hrS2, he2 _ hrS1, he1 _ hrS0, e0], ?_⟩
  · intro z; rw [hS3, hS2']; unfold Sh2; omega
  · rw [ht3 _ hrS2, t2r, pX2]
    have : (par d (armRoot X) + (par d (armRoot X) + 2) % 2) % 2 = 0 := by omega
    rw [this]; omega

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

/-! ## Explicit trees on numeral names (checked by `decide`) -/

/-- Boolean adjacency of the canonical tree -/
def tadjB (d x y : ℕ) : Bool := (x != 0 && Tpar d x == y) || (y != 0 && Tpar d y == x)

theorem tadjB_iff (d x y : ℕ) : Tadj d x y ↔ tadjB d x y = true := by
  unfold Tadj tadjB
  simp [Bool.or_eq_true, Bool.and_eq_true, bne_iff_ne, beq_iff_eq]

/-- an explicit α-tree on numeral names: lists of names, parents (indices) and labels -/
theorem numTreeA (d th q : ℕ) (names pa lab : List ℕ) (hn : 1 ≤ names.length)
    (hinj : ∀ i, i < names.length → ∀ j, j < names.length →
      names.getD i 0 = names.getD j 0 → i = j)
    (hpos : ∀ i, i < names.length → names.idxOf (names.getD i 0) = i)
    (hadj : ∀ i, i < names.length → ∀ j, j < names.length →
      (tadjB d (names.getD i 0) (names.getD j 0) = true ↔
        (i ≠ 0 ∧ pa.getD i 0 = j) ∨ (j ≠ 0 ∧ pa.getD j 0 = i)))
    (hc : treeCheck names.length th true (fun i => pa.getD i 0) (fun i => lab.getD i 0) = true)
    (hlow : ∀ i, i < names.length → (lab.getD i 0 < th ↔ par d (names.getD i 0) = q))
    (hq : q ≤ 1) :
    ∃ A : APc d q, (∀ z, z ∈ A.P.S ↔ ∃ i, i < names.length ∧ names.getD i 0 = z) ∧
      A.P.E.card = names.length - 1 ∧
      (∀ i, i < names.length → A.eps (names.getD i 0) =
        if lab.getD i 0 < th then lab.getD i 0 else names.length - 1 - lab.getD i 0) ∧
      (∀ i, i < names.length → A.tau (names.getD i 0) =
        if lab.getD i 0 < th then th - 1 - lab.getD i 0 else lab.getD i 0 - th) :=
  startTree d names.length th q (fun i => names.getD i 0) (fun z => names.idxOf z)
    (fun i => pa.getD i 0) (fun i => lab.getD i 0) hn (fun i j hi hj e => hinj i hi j hj e) hpos
    (fun i j hi hj => by rw [tadjB_iff]; exact hadj i hi j hj) hc hlow hq

/-- an explicit graceful tree on numeral names -/
theorem numTreeG (d : ℕ) (names pa lab : List ℕ) (hn : 1 ≤ names.length)
    (hinj : ∀ i, i < names.length → ∀ j, j < names.length →
      names.getD i 0 = names.getD j 0 → i = j)
    (hpos : ∀ i, i < names.length → names.idxOf (names.getD i 0) = i)
    (hadj : ∀ i, i < names.length → ∀ j, j < names.length →
      (tadjB d (names.getD i 0) (names.getD j 0) = true ↔
        (i ≠ 0 ∧ pa.getD i 0 = j) ∨ (j ≠ 0 ∧ pa.getD j 0 = i)))
    (hc : treeCheck names.length 0 false (fun i => pa.getD i 0) (fun i => lab.getD i 0) = true) :
    ∃ G : Pc, G.Grace ∧ G.R = Tadj d ∧ (∀ z, z ∈ G.S ↔ ∃ i, i < names.length ∧ names.getD i 0 = z) ∧
      G.E.card = names.length - 1 ∧ (∀ i, i < names.length → G.f (names.getD i 0) = lab.getD i 0) := by
  obtain ⟨hG, hE, _⟩ := treePc_props d names.length 0 false (fun i => names.getD i 0)
    (fun z => names.idxOf z) (fun i => pa.getD i 0) (fun i => lab.getD i 0) hn
    (fun i j hi hj e => hinj i hi j hj e) hpos
    (fun i j hi hj => by rw [tadjB_iff]; exact hadj i hi j hj) hc
  refine ⟨_, hG, rfl, fun z => treePc_mem, hE, ?_⟩
  intro i hi
  show lab.getD (names.idxOf (names.getD i 0)) 0 = _
  rw [hpos i hi]

/-- membership in a list of numerals as an arithmetic formula, via a bound -/
theorem mem_list_iff {names : List ℕ} {φ : ℕ → Prop} (B : ℕ)
    (h1 : ∀ z, z < B → ((∃ i, i < names.length ∧ names.getD i 0 = z) ↔ φ z))
    (h2 : ∀ i, i < names.length → names.getD i 0 < B) (h3 : ∀ z, B ≤ z → ¬ φ z) :
    ∀ z, (∃ i, i < names.length ∧ names.getD i 0 = z) ↔ φ z := by
  intro z
  by_cases hz : z < B
  · exact h1 z hz
  · constructor
    · rintro ⟨i, hi, rfl⟩; exact absurd (h2 i hi) hz
    · intro h; exact absurd h (h3 z (by omega))

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

/-! ## Spiders at `u` with the centre at label `0` (SP0) -/

theorem Tpar_indep (d x : ℕ) (hx : x ≠ 1) : Tpar d x = Tpar 1 x := by
  unfold Tpar; simp [hx]

theorem tadjB_indep (d x y : ℕ) (hx : x ≠ 1) (hy : y ≠ 1) : tadjB d x y = tadjB 1 x y := by
  unfold tadjB; rw [Tpar_indep d x hx, Tpar_indep d y hy]

theorem par_indep (d z : ℕ) (h1 : z ≠ 1) (h6 : z % 8 < 6) : par d z = par 0 z := by
  unfold par; simp only [h1, if_false]; split_ifs <;> omega

/-- an explicit α-tree on numeral names avoiding `v` and the arms at `v`, for any `d` -/
theorem numTreeAU (d th q : ℕ) (names pa lab : List ℕ) (hn : 1 ≤ names.length)
    (hv : ∀ i, i < names.length → names.getD i 0 ≠ 1 ∧ names.getD i 0 % 8 < 6)
    (hinj : ∀ i, i < names.length → ∀ j, j < names.length →
      names.getD i 0 = names.getD j 0 → i = j)
    (hpos : ∀ i, i < names.length → names.idxOf (names.getD i 0) = i)
    (hadj : ∀ i, i < names.length → ∀ j, j < names.length →
      (tadjB 1 (names.getD i 0) (names.getD j 0) = true ↔
        (i ≠ 0 ∧ pa.getD i 0 = j) ∨ (j ≠ 0 ∧ pa.getD j 0 = i)))
    (hc : treeCheck names.length th true (fun i => pa.getD i 0) (fun i => lab.getD i 0) = true)
    (hlow : ∀ i, i < names.length → (lab.getD i 0 < th ↔ par 0 (names.getD i 0) = q))
    (hq : q ≤ 1) :
    ∃ A : APc d q, (∀ z, z ∈ A.P.S ↔ ∃ i, i < names.length ∧ names.getD i 0 = z) ∧
      A.P.E.card = names.length - 1 ∧
      (∀ i, i < names.length → A.eps (names.getD i 0) =
        if lab.getD i 0 < th then lab.getD i 0 else names.length - 1 - lab.getD i 0) ∧
      (∀ i, i < names.length → A.tau (names.getD i 0) =
        if lab.getD i 0 < th then th - 1 - lab.getD i 0 else lab.getD i 0 - th) :=
  numTreeA d th q names pa lab hn hinj hpos
    (fun i hi j hj => by rw [tadjB_indep d _ _ (hv i hi).1 (hv j hj).1]; exact hadj i hi j hj) hc
    (fun i hi => by rw [par_indep d _ (hv i hi).1 (hv i hi).2]; exact hlow i hi) hq

/-- an explicit graceful tree on numeral names avoiding `v` and the arms at `v`, for any `d` -/
theorem numTreeGU (d : ℕ) (names pa lab : List ℕ) (hn : 1 ≤ names.length)
    (hv : ∀ i, i < names.length → names.getD i 0 ≠ 1)
    (hinj : ∀ i, i < names.length → ∀ j, j < names.length →
      names.getD i 0 = names.getD j 0 → i = j)
    (hpos : ∀ i, i < names.length → names.idxOf (names.getD i 0) = i)
    (hadj : ∀ i, i < names.length → ∀ j, j < names.length →
      (tadjB 1 (names.getD i 0) (names.getD j 0) = true ↔
        (i ≠ 0 ∧ pa.getD i 0 = j) ∨ (j ≠ 0 ∧ pa.getD j 0 = i)))
    (hc : treeCheck names.length 0 false (fun i => pa.getD i 0) (fun i => lab.getD i 0) = true) :
    ∃ G : Pc, G.Grace ∧ G.R = Tadj d ∧ (∀ z, z ∈ G.S ↔ ∃ i, i < names.length ∧ names.getD i 0 = z) ∧
      G.E.card = names.length - 1 ∧ (∀ i, i < names.length → G.f (names.getD i 0) = lab.getD i 0) :=
  numTreeG d names pa lab hn hinj hpos
    (fun i hi j hj => by rw [tadjB_indep d _ _ (hv i hi) (hv j hj)]; exact hadj i hi j hj) hc

/-- shape of the spider at `u` with arms `2, 3, 4` of lengths `a, b, c` -/
def ShU (a b c z : ℕ) : Prop :=
  z = 0 ∨ (z % 8 = 2 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ a) ∨ (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ b) ∨
    (z % 8 = 4 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ c)

/-- a graceful spider at `u` (arms `2,3,4` of lengths `a,b,c`) with `u` at label `σ` or `m - σ` -/
def SPG (d σ a b c : ℕ) : Prop :=
  ∃ G : Pc, G.Grace ∧ G.R = Tadj d ∧ (∀ z, z ∈ G.S ↔ ShU a b c z) ∧ G.E.card = a + b + c ∧
    (G.f 0 = σ ∨ G.f 0 = G.E.card - σ)

/-- standing hypotheses: three distinct arms `X, Y, Z` at `u` -/
structure Arms3 (X Y Z : ℕ) : Prop where
  hX : X = 2 ∨ X = 3 ∨ X = 4
  hY : Y = 2 ∨ Y = 3 ∨ Y = 4
  hZ : Z = 2 ∨ Z = 3 ∨ Z = 4
  hXY : X ≠ Y
  hXZ : X ≠ Z
  hYZ : Y ≠ Z

theorem Arms3.arms2 {X Y Z : ℕ} (h : Arms3 X Y Z) : Arms2 0 X Y := by
  obtain ⟨hX, hY, _, hXY, _, _⟩ := h
  refine ⟨by omega, by omega, hXY, by omega, by omega, ?_, ?_⟩ <;>
    (unfold armRoot; split_ifs <;> omega)

theorem armRoot_u {X : ℕ} (h : X = 2 ∨ X = 3 ∨ X = 4) : armRoot X = 0 := by
  unfold armRoot; split_ifs <;> omega

/-- `ShU` as seen through a permutation of the arms -/
theorem shU_perm {X Y Z x y z a b c w : ℕ} (h : Arms3 X Y Z)
    (ha : a = if X = 2 then x else if Y = 2 then y else z)
    (hb : b = if X = 3 then x else if Y = 3 then y else z)
    (hc : c = if X = 4 then x else if Y = 4 then y else z) :
    (w = 0 ∨ (w % 8 = X ∧ 1 ≤ w / 8 ∧ w / 8 ≤ x) ∨ (w % 8 = Y ∧ 1 ≤ w / 8 ∧ w / 8 ≤ y) ∨
      (w % 8 = Z ∧ 1 ≤ w / 8 ∧ w / 8 ≤ z)) ↔ ShU a b c w := by
  obtain ⟨hX, hY, hZ, hXY, hXZ, hYZ⟩ := h
  unfold ShU
  rcases hX with rfl | rfl | rfl <;> rcases hY with rfl | rfl | rfl <;>
    rcases hZ with rfl | rfl | rfl <;> simp_all <;> omega

/-- SP0, generic program: IVL0 on `X, Y`, then a final graceful segment on `Z` -/
theorem sp0_gen {d X Y Z x y z : ℕ} (h : Arms3 X Y Z) (H : IVL0P d 0 X Y x y)
    (hz : 1 ≤ z) (hK : x / 2 + y / 2 ≤ z - 1) :
    ∃ G : Pc, G.Grace ∧ G.R = Tadj d ∧
      (∀ w, w ∈ G.S ↔ w = 0 ∨ (w % 8 = X ∧ 1 ≤ w / 8 ∧ w / 8 ≤ x) ∨
        (w % 8 = Y ∧ 1 ≤ w / 8 ∧ w / 8 ≤ y) ∨ (w % 8 = Z ∧ 1 ≤ w / 8 ∧ w / 8 ≤ z)) ∧
      G.E.card = x + y + z ∧ (G.f 0 = 0 ∨ G.f 0 = G.E.card) := by
  obtain ⟨hX, hY, hZ, hXY, hXZ, hYZ⟩ := h
  obtain ⟨A, hS, hE, he, ht⟩ := H
  have hZr := armRoot_u hZ
  have h0 : (0 : ℕ) ∈ A.P.S := by rw [hS]; left; rfl
  obtain ⟨G, hG, hR, hSG, hEG, hf⟩ := A.attachGRoot Z z (by omega) hz (by rw [hZr]; exact h0)
    (by intro i hi hm; rw [hS] at hm; unfold Sh2 at hm; omega)
    (by intro hm; rw [hS] at hm; unfold Sh2 at hm; omega)
    (fun e => by omega) (fun e => by omega)
    (by rw [hZr, ht]; exact hK)
  refine ⟨G, hG, hR, fun w => by rw [hSG, hS]; unfold Sh2; omega, by rw [hEG, hE], ?_⟩
  rcases hf 0 h0 with e | e <;> rw [he] at e
  · left; exact e
  · right; rw [e]; rfl


theorem sp0_t22_2 (d : ℕ) : SPG d 0 2 2 2 := by
  obtain ⟨G, hG, hR, hS, hE, hf⟩ := numTreeGU d [0, 10, 18, 11, 19, 12, 20]
    [0, 0, 1, 0, 3, 0, 5]
    [0, 6, 2, 5, 4, 3, 1] (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  have hm := mem_list_iff (names := [0, 10, 18, 11, 19, 12, 20]) (φ := fun z => z = 0 ∨ (z % 8 = 2 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 2) ∨ (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 2) ∨ (z % 8 = 4 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 2)) 24
    (by decide +kernel) (by decide +kernel) (by intro z hz; omega)
  refine ⟨G, hG, hR, fun z => by rw [hS, hm z]; rfl, by rw [hE]; rfl, Or.inl ?_⟩
  have := hf 0 (by decide)
  simpa using this


theorem sp0_t22_3 (d : ℕ) : SPG d 0 2 2 3 := by
  obtain ⟨G, hG, hR, hS, hE, hf⟩ := numTreeGU d [0, 10, 18, 11, 19, 12, 20, 28]
    [0, 0, 1, 0, 3, 0, 5, 6]
    [0, 7, 3, 6, 4, 5, 2, 1] (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  have hm := mem_list_iff (names := [0, 10, 18, 11, 19, 12, 20, 28]) (φ := fun z => z = 0 ∨ (z % 8 = 2 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 2) ∨ (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 2) ∨ (z % 8 = 4 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 3)) 32
    (by decide +kernel) (by decide +kernel) (by intro z hz; omega)
  refine ⟨G, hG, hR, fun z => by rw [hS, hm z]; rfl, by rw [hE]; rfl, Or.inl ?_⟩
  have := hf 0 (by decide)
  simpa using this


theorem sp0_t22_4 (d : ℕ) : SPG d 0 2 2 4 := by
  obtain ⟨G, hG, hR, hS, hE, hf⟩ := numTreeGU d [0, 10, 18, 11, 19, 12, 20, 28, 36]
    [0, 0, 1, 0, 3, 0, 5, 6, 7]
    [0, 8, 3, 7, 5, 6, 2, 1, 4] (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  have hm := mem_list_iff (names := [0, 10, 18, 11, 19, 12, 20, 28, 36]) (φ := fun z => z = 0 ∨ (z % 8 = 2 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 2) ∨ (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 2) ∨ (z % 8 = 4 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 4)) 40
    (by decide +kernel) (by decide +kernel) (by intro z hz; omega)
  refine ⟨G, hG, hR, fun z => by rw [hS, hm z]; rfl, by rw [hE]; rfl, Or.inl ?_⟩
  have := hf 0 (by decide)
  simpa using this


theorem sp0_t22_5 (d : ℕ) : SPG d 0 2 2 5 := by
  obtain ⟨G, hG, hR, hS, hE, hf⟩ := numTreeGU d [0, 10, 18, 11, 19, 12, 20, 28, 36, 44]
    [0, 0, 1, 0, 3, 0, 5, 6, 7, 8]
    [0, 9, 3, 8, 4, 7, 5, 2, 1, 6] (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  have hm := mem_list_iff (names := [0, 10, 18, 11, 19, 12, 20, 28, 36, 44]) (φ := fun z => z = 0 ∨ (z % 8 = 2 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 2) ∨ (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 2) ∨ (z % 8 = 4 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 5)) 48
    (by decide +kernel) (by decide +kernel) (by intro z hz; omega)
  refine ⟨G, hG, hR, fun z => by rw [hS, hm z]; rfl, by rw [hE]; rfl, Or.inl ?_⟩
  have := hf 0 (by decide)
  simpa using this


theorem sp0_t22_6 (d : ℕ) : SPG d 0 2 2 6 := by
  obtain ⟨G, hG, hR, hS, hE, hf⟩ := numTreeGU d [0, 10, 18, 11, 19, 12, 20, 28, 36, 44, 52]
    [0, 0, 1, 0, 3, 0, 5, 6, 7, 8, 9]
    [0, 10, 3, 9, 4, 8, 5, 7, 1, 2, 6] (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  have hm := mem_list_iff (names := [0, 10, 18, 11, 19, 12, 20, 28, 36, 44, 52]) (φ := fun z => z = 0 ∨ (z % 8 = 2 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 2) ∨ (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 2) ∨ (z % 8 = 4 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 6)) 56
    (by decide +kernel) (by decide +kernel) (by intro z hz; omega)
  refine ⟨G, hG, hR, fun z => by rw [hS, hm z]; rfl, by rw [hE]; rfl, Or.inl ?_⟩
  have := hf 0 (by decide)
  simpa using this


theorem sp0_t22_7 (d : ℕ) : SPG d 0 2 2 7 := by
  obtain ⟨G, hG, hR, hS, hE, hf⟩ := numTreeGU d [0, 10, 18, 11, 19, 12, 20, 28, 36, 44, 52, 60]
    [0, 0, 1, 0, 3, 0, 5, 6, 7, 8, 9, 10]
    [0, 11, 3, 10, 4, 9, 2, 7, 6, 8, 5, 1] (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  have hm := mem_list_iff (names := [0, 10, 18, 11, 19, 12, 20, 28, 36, 44, 52, 60]) (φ := fun z => z = 0 ∨ (z % 8 = 2 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 2) ∨ (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 2) ∨ (z % 8 = 4 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 7)) 64
    (by decide +kernel) (by decide +kernel) (by intro z hz; omega)
  refine ⟨G, hG, hR, fun z => by rw [hS, hm z]; rfl, by rw [hE]; rfl, Or.inl ?_⟩
  have := hf 0 (by decide)
  simpa using this


theorem sp0_t22_8 (d : ℕ) : SPG d 0 2 2 8 := by
  obtain ⟨G, hG, hR, hS, hE, hf⟩ := numTreeGU d [0, 10, 18, 11, 19, 12, 20, 28, 36, 44, 52, 60, 68]
    [0, 0, 1, 0, 3, 0, 5, 6, 7, 8, 9, 10, 11]
    [0, 12, 3, 11, 4, 10, 2, 8, 5, 9, 7, 6, 1] (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  have hm := mem_list_iff (names := [0, 10, 18, 11, 19, 12, 20, 28, 36, 44, 52, 60, 68]) (φ := fun z => z = 0 ∨ (z % 8 = 2 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 2) ∨ (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 2) ∨ (z % 8 = 4 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 8)) 72
    (by decide +kernel) (by decide +kernel) (by intro z hz; omega)
  refine ⟨G, hG, hR, fun z => by rw [hS, hm z]; rfl, by rw [hE]; rfl, Or.inl ?_⟩
  have := hf 0 (by decide)
  simpa using this


theorem sp0_tE_2 (d : ℕ) : SPG d 0 4 4 4 := by
  obtain ⟨G, hG, hR, hS, hE, hf⟩ := numTreeGU d [0, 10, 18, 26, 34, 11, 19, 27, 35, 12, 20, 28, 36]
    [0, 0, 1, 2, 3, 0, 5, 6, 7, 0, 9, 10, 11]
    [0, 12, 3, 9, 7, 11, 4, 8, 5, 10, 2, 1, 6] (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  have hm := mem_list_iff (names := [0, 10, 18, 26, 34, 11, 19, 27, 35, 12, 20, 28, 36]) (φ := fun z => z = 0 ∨ (z % 8 = 2 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 4) ∨ (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 4) ∨ (z % 8 = 4 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 4)) 40
    (by decide +kernel) (by decide +kernel) (by intro z hz; omega)
  refine ⟨G, hG, hR, fun z => by rw [hS, hm z]; rfl, by rw [hE]; rfl, Or.inl ?_⟩
  have := hf 0 (by decide)
  simpa using this


theorem sp0_tE_3 (d : ℕ) : SPG d 0 6 6 6 := by
  obtain ⟨G, hG, hR, hS, hE, hf⟩ := numTreeGU d [0, 10, 18, 26, 34, 42, 50, 11, 19, 27, 35, 43, 51, 12, 20, 28, 36, 44, 52]
    [0, 0, 1, 2, 3, 4, 5, 0, 7, 8, 9, 10, 11, 0, 13, 14, 15, 16, 17]
    [0, 18, 3, 15, 6, 9, 1, 17, 4, 14, 7, 8, 12, 16, 2, 13, 11, 5, 10] (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  have hm := mem_list_iff (names := [0, 10, 18, 26, 34, 42, 50, 11, 19, 27, 35, 43, 51, 12, 20, 28, 36, 44, 52]) (φ := fun z => z = 0 ∨ (z % 8 = 2 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 6) ∨ (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 6) ∨ (z % 8 = 4 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 6)) 56
    (by decide +kernel) (by decide +kernel) (by intro z hz; omega)
  refine ⟨G, hG, hR, fun z => by rw [hS, hm z]; rfl, by rw [hE]; rfl, Or.inl ?_⟩
  have := hf 0 (by decide)
  simpa using this


theorem sp0_tE_4 (d : ℕ) : SPG d 0 8 8 8 := by
  obtain ⟨G, hG, hR, hS, hE, hf⟩ := numTreeGU d [0, 10, 18, 26, 34, 42, 50, 58, 66, 11, 19, 27, 35, 43, 51, 59, 67, 12, 20, 28, 36, 44, 52, 60, 68]
    [0, 0, 1, 2, 3, 4, 5, 6, 7, 0, 9, 10, 11, 12, 13, 14, 15, 0, 17, 18, 19, 20, 21, 22, 23]
    [0, 24, 3, 21, 6, 18, 9, 1, 8, 23, 4, 20, 7, 17, 11, 14, 13, 22, 2, 19, 5, 16, 12, 10, 15] (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  have hm := mem_list_iff (names := [0, 10, 18, 26, 34, 42, 50, 58, 66, 11, 19, 27, 35, 43, 51, 59, 67, 12, 20, 28, 36, 44, 52, 60, 68]) (φ := fun z => z = 0 ∨ (z % 8 = 2 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 8) ∨ (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 8) ∨ (z % 8 = 4 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 8)) 72
    (by decide +kernel) (by decide +kernel) (by intro z hz; omega)
  refine ⟨G, hG, hR, fun z => by rw [hS, hm z]; rfl, by rw [hE]; rfl, Or.inl ?_⟩
  have := hf 0 (by decide)
  simpa using this


theorem sp0_tE_5 (d : ℕ) : SPG d 0 10 10 10 := by
  obtain ⟨G, hG, hR, hS, hE, hf⟩ := numTreeGU d [0, 10, 18, 26, 34, 42, 50, 58, 66, 74, 82, 11, 19, 27, 35, 43, 51, 59, 67, 75, 83, 12, 20, 28, 36, 44, 52, 60, 68, 76, 84]
    [0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 0, 11, 12, 13, 14, 15, 16, 17, 18, 19, 0, 21, 22, 23, 24, 25, 26, 27, 28, 29]
    [0, 30, 3, 27, 6, 24, 9, 21, 13, 12, 1, 29, 4, 26, 7, 23, 10, 20, 14, 19, 16, 28, 2, 25, 5, 22, 8, 17, 15, 11, 18] (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  have hm := mem_list_iff (names := [0, 10, 18, 26, 34, 42, 50, 58, 66, 74, 82, 11, 19, 27, 35, 43, 51, 59, 67, 75, 83, 12, 20, 28, 36, 44, 52, 60, 68, 76, 84]) (φ := fun z => z = 0 ∨ (z % 8 = 2 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 10) ∨ (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 10) ∨ (z % 8 = 4 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 10)) 88
    (by decide +kernel) (by decide +kernel) (by intro z hz; omega)
  refine ⟨G, hG, hR, fun z => by rw [hS, hm z]; rfl, by rw [hE]; rfl, Or.inl ?_⟩
  have := hf 0 (by decide)
  simpa using this


theorem sp0_tE_6 (d : ℕ) : SPG d 0 12 12 12 := by
  obtain ⟨G, hG, hR, hS, hE, hf⟩ := numTreeGU d [0, 10, 18, 26, 34, 42, 50, 58, 66, 74, 82, 90, 98, 11, 19, 27, 35, 43, 51, 59, 67, 75, 83, 91, 99, 12, 20, 28, 36, 44, 52, 60, 68, 76, 84, 92, 100]
    [0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 0, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 0, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35]
    [0, 36, 3, 33, 6, 30, 9, 27, 12, 24, 17, 15, 1, 35, 4, 32, 7, 29, 10, 26, 13, 23, 19, 20, 11, 34, 2, 31, 5, 28, 8, 25, 14, 22, 16, 21, 18] (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  have hm := mem_list_iff (names := [0, 10, 18, 26, 34, 42, 50, 58, 66, 74, 82, 90, 98, 11, 19, 27, 35, 43, 51, 59, 67, 75, 83, 91, 99, 12, 20, 28, 36, 44, 52, 60, 68, 76, 84, 92, 100]) (φ := fun z => z = 0 ∨ (z % 8 = 2 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 12) ∨ (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 12) ∨ (z % 8 = 4 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 12)) 104
    (by decide +kernel) (by decide +kernel) (by intro z hz; omega)
  refine ⟨G, hG, hR, fun z => by rw [hS, hm z]; rfl, by rw [hE]; rfl, Or.inl ?_⟩
  have := hf 0 (by decide)
  simpa using this


theorem sp0_tE_7 (d : ℕ) : SPG d 0 14 14 14 := by
  obtain ⟨G, hG, hR, hS, hE, hf⟩ := numTreeGU d [0, 10, 18, 26, 34, 42, 50, 58, 66, 74, 82, 90, 98, 106, 114, 11, 19, 27, 35, 43, 51, 59, 67, 75, 83, 91, 99, 107, 115, 12, 20, 28, 36, 44, 52, 60, 68, 76, 84, 92, 100, 108, 116]
    [0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 0, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 0, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41]
    [0, 42, 3, 39, 6, 36, 9, 33, 12, 30, 15, 1, 14, 22, 19, 41, 4, 38, 7, 35, 10, 32, 13, 29, 17, 26, 20, 24, 23, 40, 2, 37, 5, 34, 8, 31, 11, 28, 18, 25, 27, 16, 21] (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  have hm := mem_list_iff (names := [0, 10, 18, 26, 34, 42, 50, 58, 66, 74, 82, 90, 98, 106, 114, 11, 19, 27, 35, 43, 51, 59, 67, 75, 83, 91, 99, 107, 115, 12, 20, 28, 36, 44, 52, 60, 68, 76, 84, 92, 100, 108, 116]) (φ := fun z => z = 0 ∨ (z % 8 = 2 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 14) ∨ (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 14) ∨ (z % 8 = 4 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 14)) 120
    (by decide +kernel) (by decide +kernel) (by intro z hz; omega)
  refine ⟨G, hG, hR, fun z => by rw [hS, hm z]; rfl, by rw [hE]; rfl, Or.inl ?_⟩
  have := hf 0 (by decide)
  simpa using this

/-! ## SP0 cores with tails, and SP0 for every spider -/

/-- `(2,2,c)`, `c ≥ 9`: the α-core `S(2,2,5)` plus a final graceful tail -/
theorem sp0_225 (d c : ℕ) (hc : 9 ≤ c) : SPG d 0 2 2 c := by
  obtain ⟨A, hS, hE, he, ht⟩ := numTreeAU d 5 0 [0, 10, 18, 11, 19, 12, 20, 28, 36, 44]
    [0, 0, 1, 0, 3, 0, 5, 6, 7, 8] [0, 6, 2, 9, 1, 7, 4, 5, 3, 8] (by decide) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by omega)
  have hm := mem_list_iff (names := [0, 10, 18, 11, 19, 12, 20, 28, 36, 44])
    (φ := fun z => z = 0 ∨ (z % 8 = 2 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 2) ∨ (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 2) ∨
      (z % 8 = 4 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 5)) 48
    (by decide +kernel) (by decide +kernel) (by intro z hz; omega)
  have hS' : ∀ z, z ∈ A.P.S ↔ z = 0 ∨ (z % 8 = 2 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 2) ∨
      (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 2) ∨ (z % 8 = 4 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 5) := by
    intro z; rw [hS, hm z]
  have t44 : A.tau (4 + 8 * 5) = 3 := by have := ht 9 (by decide); simpa using this
  have e0 : A.eps 0 = 0 := by have := he 0 (by decide); simpa using this
  have h0 : (0 : ℕ) ∈ A.P.S := by rw [hS']; left; rfl
  obtain ⟨G, hG, hR, hSG, hEG, hf⟩ := A.attachGArm 4 5 (c - 5) (by omega) (by omega) (by omega)
    (by rw [hS']; omega)
    (by intro i hi hm; rw [hS'] at hm; omega)
    (by intro hm; rw [hS'] at hm; omega)
    (fun e => by omega) (fun e => by omega)
    (by rw [t44]; omega)
  refine ⟨G, hG, hR, fun z => by rw [hSG, hS']; unfold ShU; omega, by rw [hEG, hE]; simp only [List.length_cons, List.length_nil]; omega, ?_⟩
  rcases hf 0 h0 with e | e <;> rw [e0] at e
  · left; exact e
  · right; omega

/-- `(2k)^3`, `k ≥ 8`, `k ≠ 12`: the α-core `S(1,7,1)` plus tails -/
theorem sp0_even_c1 (d k : ℕ) (hk : 8 ≤ k) (hk12 : k ≠ 12) : SPG d 0 (2 * k) (2 * k) (2 * k) := by
  obtain ⟨A, hS, hE, he, ht⟩ := numTreeAU d 4 0 [0, 12, 10, 18, 26, 34, 42, 50, 58, 11]
    [0, 0, 0, 2, 3, 4, 5, 6, 7, 0] [0, 6, 9, 1, 5, 2, 4, 3, 8, 7] (by decide) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by omega)
  have hm := mem_list_iff (names := [0, 12, 10, 18, 26, 34, 42, 50, 58, 11])
    (φ := fun z => z = 0 ∨ (z % 8 = 2 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 7) ∨ (z % 8 = 3 ∧ z / 8 = 1) ∨
      (z % 8 = 4 ∧ z / 8 = 1)) 64
    (by decide +kernel) (by decide +kernel) (by intro z hz; omega)
  have hS0 : ∀ z, z ∈ A.P.S ↔ z = 0 ∨ (z % 8 = 2 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 7) ∨
      (z % 8 = 3 ∧ z / 8 = 1) ∨ (z % 8 = 4 ∧ z / 8 = 1) := by
    intro z; rw [hS, hm z]
  have t58 : A.tau (2 + 8 * 7) = 4 := by have := ht 8 (by decide); simpa using this
  have t11 : A.tau (3 + 8 * 1) = 3 := by have := ht 9 (by decide); simpa using this
  have t12 : A.tau (4 + 8 * 1) = 2 := by have := ht 1 (by decide); simpa using this
  have e0 : A.eps 0 = 0 := by have := he 0 (by decide); simpa using this
  have p58 : par d (2 + 8 * 7) = 1 := by rw [par_arm d 2 7 (by omega) (by omega)]; simp
  have p11 : par d (3 + 8 * 1) = 1 := by rw [par_arm d 3 1 (by omega) (by omega)]; simp
  have p12 : par d (4 + 8 * 1) = 1 := by rw [par_arm d 4 1 (by omega) (by omega)]; simp
  have m0 : (0 : ℕ) ∈ A.P.S := by rw [hS0]; left; rfl
  have m11 : 3 + 8 * 1 ∈ A.P.S := by rw [hS0]; omega
  have m12 : 4 + 8 * 1 ∈ A.P.S := by rw [hS0]; omega
  obtain ⟨B, hSB, hEB, heB, htB, _⟩ := A.attachArm 2 7 (2 * k - 7) (by omega) (by omega) (by omega)
    (by rw [hS0]; omega) (by intro i hi h; rw [hS0] at h; omega) (by intro h; rw [hS0] at h; omega)
    (fun e => by omega) (fun e => by omega)
    (by rw [t58]; exact ⟨by omega, by omega, by omega⟩)
  have hSB' : ∀ z, z ∈ B.P.S ↔ z = 0 ∨ (z % 8 = 2 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 2 * k) ∨
      (z % 8 = 3 ∧ z / 8 = 1) ∨ (z % 8 = 4 ∧ z / 8 = 1) := by
    intro z; rw [hSB, hS0]; omega
  have tB11 : B.tau (3 + 8 * 1) = 3 + (2 * k - 7) / 2 := by
    rw [htB _ m11, t11, p11, p58]; omega
  have tB12 : B.tau (4 + 8 * 1) = 2 + (2 * k - 7) / 2 := by
    rw [htB _ m12, t12, p12, p58]; omega
  have mB0 : (0 : ℕ) ∈ B.P.S := by rw [hSB']; left; rfl
  have mB11 : 3 + 8 * 1 ∈ B.P.S := by rw [hSB']; omega
  have mB12 : 4 + 8 * 1 ∈ B.P.S := by rw [hSB']; omega
  obtain ⟨C, hSC, hEC, heC, htC, _⟩ := B.attachArm 3 1 (2 * k - 1) (by omega) (by omega) (by omega)
    mB11 (by intro i hi h; rw [hSB'] at h; omega) (by intro h; rw [hSB'] at h; omega)
    (fun e => by omega) (fun e => by omega)
    (by rw [tB11]; exact ⟨by omega, by omega, by omega⟩)
  have hSC' : ∀ z, z ∈ C.P.S ↔ z = 0 ∨ (z % 8 = 2 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 2 * k) ∨
      (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 2 * k) ∨ (z % 8 = 4 ∧ z / 8 = 1) := by
    intro z; rw [hSC, hSB']; omega
  have tC12 : C.tau (4 + 8 * 1) = 2 + (2 * k - 7) / 2 + (2 * k - 1) / 2 := by
    rw [htC _ mB12, tB12, p12, p11]; omega
  obtain ⟨G, hG, hR, hSG, hEG, hf⟩ := C.attachGArm 4 1 (2 * k - 1) (by omega) (by omega)
    (by omega) (by rw [hSC']; omega)
    (by intro i hi h; rw [hSC'] at h; omega) (by intro h; rw [hSC'] at h; omega)
    (fun e => by omega) (fun e => by omega)
    (by rw [tC12]; omega)
  refine ⟨G, hG, hR, fun z => by rw [hSG, hSC']; unfold ShU; omega,
    by rw [hEG, hEC, hEB, hE]; simp only [List.length_cons, List.length_nil]; omega, ?_⟩
  have e0' : C.eps 0 = 0 := by rw [heC _ mB0, heB _ m0, e0]
  have mC0 : (0 : ℕ) ∈ C.P.S := by rw [hSC']; left; rfl
  rcases hf 0 mC0 with e | e <;> rw [e0'] at e
  · left; exact e
  · right; omega

/-- `(2k)^3`, `k ≥ 9`, `k ≠ 14`: the α-core `S(1,7,3)` plus tails -/
theorem sp0_even_c3 (d k : ℕ) (hk : 9 ≤ k) (hk14 : k ≠ 14) : SPG d 0 (2 * k) (2 * k) (2 * k) := by
  obtain ⟨A, hS, hE, he, ht⟩ := numTreeAU d 5 0 [0, 12, 10, 18, 26, 34, 42, 50, 58, 11, 19, 27]
    [0, 0, 0, 2, 3, 4, 5, 6, 7, 0, 9, 10] [0, 9, 11, 1, 5, 4, 6, 3, 10, 8, 2, 7] (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by omega)
  have hm := mem_list_iff (names := [0, 12, 10, 18, 26, 34, 42, 50, 58, 11, 19, 27])
    (φ := fun z => z = 0 ∨ (z % 8 = 2 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 7) ∨ (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 3) ∨
      (z % 8 = 4 ∧ z / 8 = 1)) 64
    (by decide +kernel) (by decide +kernel) (by intro z hz; omega)
  have hS0 : ∀ z, z ∈ A.P.S ↔ z = 0 ∨ (z % 8 = 2 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 7) ∨
      (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 3) ∨ (z % 8 = 4 ∧ z / 8 = 1) := by
    intro z; rw [hS, hm z]
  have t58 : A.tau (2 + 8 * 7) = 5 := by have := ht 8 (by decide); simpa using this
  have t27 : A.tau (3 + 8 * 3) = 2 := by have := ht 11 (by decide); simpa using this
  have t12 : A.tau (4 + 8 * 1) = 4 := by have := ht 1 (by decide); simpa using this
  have e0 : A.eps 0 = 0 := by have := he 0 (by decide); simpa using this
  have p58 : par d (2 + 8 * 7) = 1 := by rw [par_arm d 2 7 (by omega) (by omega)]; simp
  have p27 : par d (3 + 8 * 3) = 1 := by rw [par_arm d 3 3 (by omega) (by omega)]; simp
  have p12 : par d (4 + 8 * 1) = 1 := by rw [par_arm d 4 1 (by omega) (by omega)]; simp
  have m0 : (0 : ℕ) ∈ A.P.S := by rw [hS0]; left; rfl
  have m27 : 3 + 8 * 3 ∈ A.P.S := by rw [hS0]; omega
  have m12 : 4 + 8 * 1 ∈ A.P.S := by rw [hS0]; omega
  obtain ⟨B, hSB, hEB, heB, htB, _⟩ := A.attachArm 2 7 (2 * k - 7) (by omega) (by omega) (by omega)
    (by rw [hS0]; omega) (by intro i hi h; rw [hS0] at h; omega) (by intro h; rw [hS0] at h; omega)
    (fun e => by omega) (fun e => by omega)
    (by rw [t58]; exact ⟨by omega, by omega, by omega⟩)
  have hSB' : ∀ z, z ∈ B.P.S ↔ z = 0 ∨ (z % 8 = 2 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 2 * k) ∨
      (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 3) ∨ (z % 8 = 4 ∧ z / 8 = 1) := by
    intro z; rw [hSB, hS0]; omega
  have tB27 : B.tau (3 + 8 * 3) = 2 + (2 * k - 7) / 2 := by
    rw [htB _ m27, t27, p27, p58]; omega
  have tB12 : B.tau (4 + 8 * 1) = 4 + (2 * k - 7) / 2 := by
    rw [htB _ m12, t12, p12, p58]; omega
  have mB0 : (0 : ℕ) ∈ B.P.S := by rw [hSB']; left; rfl
  have mB27 : 3 + 8 * 3 ∈ B.P.S := by rw [hSB']; omega
  have mB12 : 4 + 8 * 1 ∈ B.P.S := by rw [hSB']; omega
  obtain ⟨C, hSC, hEC, heC, htC, _⟩ := B.attachArm 3 3 (2 * k - 3) (by omega) (by omega) (by omega)
    mB27 (by intro i hi h; rw [hSB'] at h; omega) (by intro h; rw [hSB'] at h; omega)
    (fun e => by omega) (fun e => by omega)
    (by rw [tB27]; exact ⟨by omega, by omega, by omega⟩)
  have hSC' : ∀ z, z ∈ C.P.S ↔ z = 0 ∨ (z % 8 = 2 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 2 * k) ∨
      (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 2 * k) ∨ (z % 8 = 4 ∧ z / 8 = 1) := by
    intro z; rw [hSC, hSB']; omega
  have tC12 : C.tau (4 + 8 * 1) = 4 + (2 * k - 7) / 2 + (2 * k - 3) / 2 := by
    rw [htC _ mB12, tB12, p12, p27]; omega
  obtain ⟨G, hG, hR, hSG, hEG, hf⟩ := C.attachGArm 4 1 (2 * k - 1) (by omega) (by omega)
    (by omega) (by rw [hSC']; omega)
    (by intro i hi h; rw [hSC'] at h; omega) (by intro h; rw [hSC'] at h; omega)
    (fun e => by omega) (fun e => by omega)
    (by rw [tC12]; omega)
  refine ⟨G, hG, hR, fun z => by rw [hSG, hSC']; unfold ShU; omega,
    by rw [hEG, hEC, hEB, hE]; simp only [List.length_cons, List.length_nil]; omega, ?_⟩
  have e0' : C.eps 0 = 0 := by rw [heC _ mB0, heB _ m0, e0]
  have mC0 : (0 : ℕ) ∈ C.P.S := by rw [hSC']; left; rfl
  rcases hf 0 mC0 with e | e <;> rw [e0'] at e
  · left; exact e
  · right; omega

/-- **SP0 for every spider** `a ≤ b ≤ c` -/
theorem sp0_all (d a b c : ℕ) (hd : 1 ≤ d) (ha : 1 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) :
    SPG d 0 a b c := by
  by_cases h22 : a = 2 ∧ b = 2
  · obtain ⟨rfl, rfl⟩ := h22
    by_cases hc : 9 ≤ c
    · exact sp0_225 d c hc
    · interval_cases c
      · exact sp0_t22_2 d
      · exact sp0_t22_3 d
      · exact sp0_t22_4 d
      · exact sp0_t22_5 d
      · exact sp0_t22_6 d
      · exact sp0_t22_7 d
      · exact sp0_t22_8 d
  by_cases he : a = b ∧ b = c ∧ a % 2 = 0
  · obtain ⟨rfl, rfl, h2⟩ := he
    obtain ⟨k, rfl⟩ : ∃ k, a = 2 * k := ⟨a / 2, by omega⟩
    by_cases hk : 8 ≤ k
    · by_cases hk12 : k = 12
      · exact sp0_even_c3 d k (by omega) (by omega)
      · exact sp0_even_c1 d k hk hk12
    · have : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega
      rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact absurd ⟨rfl, rfl⟩ h22
      · exact sp0_tE_2 d
      · exact sp0_tE_3 d
      · exact sp0_tE_4 d
      · exact sp0_tE_5 d
      · exact sp0_tE_6 d
      · exact sp0_tE_7 d
  -- generic: IVL0 on the arms `2, 3` and a final segment on `4`
  have h3 : Arms3 2 3 4 := ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
  obtain ⟨G, hG, hR, hS, hE, hf⟩ := sp0_gen (d := d) (x := a) (y := b) (z := c) h3
    (ivl0_all (x := a) (y := b) hd h3.arms2 ha (by omega) (by omega)) (by omega) (by omega)
  exact ⟨G, hG, hR, fun z => by rw [hS]; rfl, hE, by rcases hf with h | h <;> simp [h]⟩

/-! ## Assembly: Tset membership, cutting the `d`-path, joining two sides -/

theorem mem_Tset_iff {a b c d e f s : ℕ} (hd : 1 ≤ d) :
    s ∈ Tset a b c d e f ↔ s = 0 ∨ s = 1 ∨ (s % 8 = 2 ∧ 1 ≤ s / 8 ∧ s / 8 ≤ a) ∨
      (s % 8 = 3 ∧ 1 ≤ s / 8 ∧ s / 8 ≤ b) ∨ (s % 8 = 4 ∧ 1 ≤ s / 8 ∧ s / 8 ≤ c) ∨
      (s % 8 = 5 ∧ 1 ≤ s / 8 ∧ s / 8 ≤ d - 1) ∨ (s % 8 = 6 ∧ 1 ≤ s / 8 ∧ s / 8 ≤ e) ∨
      (s % 8 = 7 ∧ 1 ≤ s / 8 ∧ s / 8 ≤ f) := by
  rw [mem_Tset]
  constructor
  · rintro (h | h | ⟨X, k, h2, h7, hk1, hk, rfl⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · unfold armLen at hk
      have hX : X = 2 ∨ X = 3 ∨ X = 4 ∨ X = 5 ∨ X = 6 ∨ X = 7 := by omega
      rcases hX with rfl | rfl | rfl | rfl | rfl | rfl <;> simp at hk <;> omega
  · rintro (h | h | h | h | h | h | h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    all_goals
      right; right
      refine ⟨s % 8, s / 8, by omega, by omega, by omega, ?_, by omega⟩
      unfold armLen
      have : s % 8 = 2 ∨ s % 8 = 3 ∨ s % 8 = 4 ∨ s % 8 = 5 ∨ s % 8 = 6 ∨ s % 8 = 7 := by omega
      rcases this with e | e | e | e | e | e <;> simp [e] <;> omega

/-- the part of the tree on `u`'s side of the `d`-path edge between positions `j` and `j+1` -/
def uPart (j z : ℕ) : Prop :=
  z = 0 ∨ ((z % 8 = 2 ∨ z % 8 = 3 ∨ z % 8 = 4) ∧ 1 ≤ z / 8) ∨ (z % 8 = 5 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ j)

/-- the part on `v`'s side -/
def vPart (d j z : ℕ) : Prop :=
  z = 1 ∨ ((z % 8 = 6 ∨ z % 8 = 7) ∧ 1 ≤ z / 8) ∨ (z % 8 = 5 ∧ j + 1 ≤ z / 8 ∧ z / 8 ≤ d - 1)

/-- position `i` of the `d`-path (`0 = u`, `d = v`) -/
def dnode (d i : ℕ) : ℕ := if i = 0 then 0 else if i = d then 1 else 5 + 8 * i

/-- the only edge between the two parts is `dnode j — dnode (j+1)` -/
theorem cross_cut (d j : ℕ) (hj : j + 1 ≤ d) (p q : ℕ) (hp : vPart d j p) (hq : uPart j q)
    (h : Tadj d p q) : p = dnode d (j + 1) ∧ q = dnode d j := by
  unfold vPart at hp
  unfold uPart at hq
  unfold dnode
  rcases hq with rfl | hq | hq
  · -- q = u: then `p`'s parent is `u`
    unfold Tadj at h
    rcases h with ⟨hp0, hpar⟩ | ⟨h0, _⟩
    · rcases hp with rfl | ⟨hX, hk⟩ | ⟨h5, hk1, hk2⟩
      · unfold Tpar dEnd at hpar
        rw [if_neg (by omega), if_pos rfl] at hpar
        split_ifs at hpar with h2
        · omega
        · have : d = 1 := by omega
          subst this
          have : j = 0 := by omega
          subst this
          simp
      · have hX' : 2 ≤ p % 8 ∧ p % 8 ≤ 7 := by omega
        have := Tpar_arm d (p % 8) (p / 8) hX' hk
        rw [show p % 8 + 8 * (p / 8) = p by omega] at this
        rw [this] at hpar
        unfold armRoot at hpar
        split_ifs at hpar <;> omega
      · have := Tpar_arm d 5 (p / 8) (by omega) (by omega)
        rw [show 5 + 8 * (p / 8) = p by omega] at this
        rw [this] at hpar
        unfold armRoot at hpar
        split_ifs at hpar with h2
        · omega
        · have hj0 : j = 0 := by omega
          subst hj0
          refine ⟨?_, by simp⟩
          rw [if_neg (by omega), if_neg (by omega)]; omega
    · exact absurd rfl h0
  · -- q on a u-arm: its neighbours stay on that arm or are `u`
    have hX : 2 ≤ q % 8 ∧ q % 8 ≤ 7 := by omega
    have hq' : q = q % 8 + 8 * (q / 8) := by omega
    rw [hq'] at h
    rcases (Tadj_arm_iff d (q % 8) (q / 8) p hX (by omega)).mp h with h1 | h1 | ⟨h5, _, _⟩
    · split_ifs at h1
      · unfold armRoot at h1; split_ifs at h1 <;> omega
      · omega
    · omega
    · omega
  · -- q on the `d`-path at position `≤ j`
    have hX : 2 ≤ 5 ∧ 5 ≤ 7 := by omega
    have hq' : q = 5 + 8 * (q / 8) := by omega
    rw [hq'] at h
    rcases (Tadj_arm_iff d 5 (q / 8) p hX (by omega)).mp h with h1 | h1 | ⟨_, h2, h3⟩
    · split_ifs at h1
      · unfold armRoot at h1; rw [if_pos (by omega)] at h1; omega
      · omega
    · refine ⟨?_, ?_⟩
      · rw [if_neg (by omega)]; split_ifs <;> omega
      · rw [if_neg (by omega), if_neg (by omega)]; omega
    · refine ⟨?_, ?_⟩
      · rw [if_neg (by omega), if_pos (by omega)]; exact h3
      · rw [if_neg (by omega), if_neg (by omega)]; omega

theorem uPart_vPart_disj (d j z : ℕ) (hu : uPart j z) (hv : vPart d j z) : False := by
  unfold uPart at hu; unfold vPart at hv; omega

theorem dnode_adj (d j : ℕ) (hj : j + 1 ≤ d) : Tadj d (dnode d (j + 1)) (dnode d j) := by
  unfold dnode
  by_cases h0 : j = 0
  · subst h0
    by_cases hd : d = 1
    · subst hd; rw [tadjB_iff]; decide
    · rw [if_neg (by omega), if_neg (by omega), if_pos rfl, tadjB_iff,
        tadjB_indep d _ _ (by omega) (by omega)]
      decide
  · by_cases hv : j + 1 = d
    · rw [if_neg (by omega), if_pos hv, if_neg h0, if_neg (by omega)]
      left
      refine ⟨by omega, ?_⟩
      unfold Tpar dEnd
      rw [if_neg (by omega), if_pos rfl, if_pos (by omega)]
      omega
    · rw [if_neg (by omega), if_neg hv, if_neg h0, if_neg (by omega)]
      exact (Tadj_arm_iff d 5 j _ (by omega) (by omega)).mpr (Or.inr (Or.inl rfl))

/-- join an α-piece on the `v`-side with a graceful piece on the `u`-side -/
theorem join_vu {a b c d e f j q : ℕ} (hd : 1 ≤ d) (hj : j + 1 ≤ d) (A : APc d q) (G : Pc)
    (hG : G.Grace) (hGR : G.R = Tadj d)
    (hA : ∀ z, z ∈ A.P.S → vPart d j z) (hGu : ∀ z, z ∈ G.S → uPart j z)
    (hx : dnode d (j + 1) ∈ A.P.S) (hw : dnode d j ∈ G.S)
    (hlab : G.f (dnode d j) = A.tau (dnode d (j + 1)) ∨
      G.f (dnode d j) = G.E.card - A.tau (dnode d (j + 1)))
    (htb : A.tau (dnode d (j + 1)) ≤ G.E.card)
    (hT : ∀ s, (s ∈ A.P.S ∨ s ∈ G.S) ↔ s ∈ Tset a b c d e f) : CanonGraceful a b c d e f := by
  obtain ⟨P, hP, hPR, hPS, _, _⟩ := A.joinG G hG hGR hx hw (dnode_adj d j hj)
    (by rw [Finset.disjoint_left]; intro z h1 h2; exact uPart_vPart_disj d j z (hGu z h2) (hA z h1))
    (fun p hp q' hq' h => cross_cut d j hj p q' (hA p hp) (hGu q' hq') h) hlab htb
  exact canon_of_piece P hP hPR (fun s => by rw [hPS]; exact hT s)

/-- join an α-piece on the `u`-side with a graceful piece on the `v`-side -/
theorem join_uv {a b c d e f j q : ℕ} (hd : 1 ≤ d) (hj : j + 1 ≤ d) (A : APc d q) (G : Pc)
    (hG : G.Grace) (hGR : G.R = Tadj d)
    (hA : ∀ z, z ∈ A.P.S → uPart j z) (hGv : ∀ z, z ∈ G.S → vPart d j z)
    (hx : dnode d j ∈ A.P.S) (hw : dnode d (j + 1) ∈ G.S)
    (hlab : G.f (dnode d (j + 1)) = A.tau (dnode d j) ∨
      G.f (dnode d (j + 1)) = G.E.card - A.tau (dnode d j))
    (htb : A.tau (dnode d j) ≤ G.E.card)
    (hT : ∀ s, (s ∈ A.P.S ∨ s ∈ G.S) ↔ s ∈ Tset a b c d e f) : CanonGraceful a b c d e f := by
  obtain ⟨P, hP, hPR, hPS, _, _⟩ := A.joinG G hG hGR hx hw (Tadj_symm d _ _ (dnode_adj d j hj))
    (by rw [Finset.disjoint_left]; intro z h1 h2; exact uPart_vPart_disj d j z (hA z h1) (hGv z h2))
    (fun p hp q' hq' h => by
      have := cross_cut d j hj q' p (hGv q' hq') (hA p hp) (Tadj_symm d _ _ h)
      exact ⟨this.2, this.1⟩) hlab htb
  exact canon_of_piece P hP hPR (fun s => by rw [hPS]; exact hT s)

/-! ## Family A: `(e,f) ≠ (2,2)` -/

theorem famA (a b c d e f : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) (hd : 1 ≤ d)
    (he : 1 ≤ e) (hef : e ≤ f) (h22 : ¬ (e = 2 ∧ f = 2)) : CanonGraceful a b c d e f := by
  obtain ⟨A0, hS0, _, he0, _⟩ := ivl0_all (d := d) (r := 1) (X := 6) (Y := 7) (x := e) (y := f)
    hd arms_v he (by omega) h22
  have h1S : (1 : ℕ) ∈ A0.P.S := by rw [hS0]; left; rfl
  have t1 : A0.refl.tau 1 = 0 := by rw [A0.refl_tau h1S]; exact he0
  have hS1 : ∀ z, z ∈ A0.refl.P.S ↔ Sh2 1 6 e 7 f z := by intro z; rw [A0.refl_S]; exact hS0 z
  obtain ⟨G, hG, hGR, hGS, hGE, hGf⟩ := sp0_all d a b c hd ha hab hbc
  have hGu : ∀ z, z ∈ G.S → uPart 0 z := by
    intro z hz; rw [hGS] at hz; unfold ShU at hz; unfold uPart; omega
  have hw : dnode d 0 ∈ G.S := by unfold dnode; rw [if_pos rfl, hGS]; left; rfl
  have hGf' : G.f (dnode d 0) = 0 ∨ G.f (dnode d 0) = G.E.card - 0 := by
    unfold dnode; rw [if_pos rfl]; rcases hGf with h | h <;> [left; right] <;> omega
  by_cases hd1 : d = 1
  · subst hd1
    refine join_vu (j := 0) (by omega) (by omega) A0.refl G hG hGR
      (by intro z hz; rw [hS1] at hz; unfold Sh2 at hz; unfold vPart; omega) hGu
      (by unfold dnode; simp; exact (hS1 1).mpr (Or.inl rfl)) hw
      (by
        have : dnode 1 (0 + 1) = 1 := by unfold dnode; simp
        rw [this, t1]; exact hGf')
      (by have : dnode 1 (0 + 1) = 1 := by unfold dnode; simp
          rw [this, t1]; omega)
      (by
        intro s; rw [hS1, hGS, mem_Tset_iff (by omega)]; unfold Sh2 ShU
        constructor
        · rintro ((h | h | h) | (h | h | h | h)) <;> omega
        · rintro (h | h | h | h | h | h | h | h) <;> omega)
  · obtain ⟨B, hSB, _, _, _, htB⟩ := A0.refl.attachDV (d - 1) (by omega) (by omega)
      ((hS1 1).mpr (Or.inl rfl))
      (by intro i hi h; rw [hS1] at h; unfold Sh2 at h; omega)
      (by intro _ h; rw [hS1] at h; unfold Sh2 at h; omega)
      (by intro h; omega)
      (by intro h; rw [hS1] at h; unfold Sh2 at h; omega)
      (by rw [t1]; exact ⟨by omega, by omega, by omega⟩)
    rw [t1, show d - (d - 1) = 1 by omega] at htB
    have hx : dnode d (0 + 1) = 5 + 8 * 1 := by
      unfold dnode; rw [if_neg (by omega), if_neg (by omega)]
    refine join_vu (j := 0) hd (by omega) B G hG hGR
      (by intro z hz; rw [hSB, hS1] at hz; unfold Sh2 at hz; unfold vPart; omega) hGu
      (by rw [hx, hSB]; right; omega) hw
      (by rw [hx, htB]; exact hGf')
      (by rw [hx, htB]; omega)
      (by
        intro s; rw [hSB, hS1, hGS, mem_Tset_iff hd]; unfold Sh2 ShU
        constructor
        · rintro (((h | h | h) | h) | (h | h | h | h)) <;> omega
        · rintro (h | h | h | h | h | h | h | h) <;> omega)

/-! ## Graceful spiders at `u` with the centre at `σ` (σ = 1, 2) -/

/-- shape of a spider at `u` with arms `X, Y, Z` -/
def ShXYZ (X x Y y Z z w : ℕ) : Prop :=
  w = 0 ∨ (w % 8 = X ∧ 1 ≤ w / 8 ∧ w / 8 ≤ x) ∨ (w % 8 = Y ∧ 1 ≤ w / 8 ∧ w / 8 ≤ y) ∨
    (w % 8 = Z ∧ 1 ≤ w / 8 ∧ w / 8 ≤ z)

/-- a graceful spider at `u` with arms `X, Y, Z` and the centre at `σ` or `m - σ` -/
def SPX (d σ X x Y y Z z : ℕ) : Prop :=
  ∃ G : Pc, G.Grace ∧ G.R = Tadj d ∧ (∀ w, w ∈ G.S ↔ ShXYZ X x Y y Z z w) ∧
    G.E.card = x + y + z ∧ (G.f 0 = σ ∨ G.f 0 = G.E.card - σ)

/-- program spA: α-EPL from `u` along `X` (u at `σ`), `Y` at `u`, final segment `Z` -/
theorem spA_prog {d σ X Y Z x y z : ℕ} (hd : 1 ≤ d) (h : Arms3 X Y Z) (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hz : 1 ≤ z) (hok1 : AeplOK (x + 1) σ) (hok2 : AeplOK y (x / 2 - σ))
    (hok3 : x / 2 - σ + y / 2 ≤ z - 1) : SPX d σ X x Y y Z z := by
  obtain ⟨hX, hY, hZ, hXY, hXZ, hYZ⟩ := h
  have hrX := armRoot_u hX
  have hrY := armRoot_u hY
  have hrZ := armRoot_u hZ
  obtain ⟨Lab, hLab, hLab0⟩ := aepl (x + 1) σ hok1
  have hs : σ ≤ x / 2 := by have := hok1.2.1; omega
  rw [show (x + 1 - 1) / 2 = x / 2 by omega] at hLab
  obtain ⟨A0, hS0', hE0, he0, ht0⟩ := startArm d X x hd (by omega) Lab hLab (by omega) (by omega)
  have hS0 : ∀ w, w ∈ A0.P.S ↔ w = 0 ∨ (w % 8 = X ∧ 1 ≤ w / 8 ∧ w / 8 ≤ x) :=
    fun w => by rw [hS0' w, hrX]
  have e0 : A0.eps 0 = σ := by
    have := he0 0 (by omega); simp only [anode, if_true, hrX] at this
    rw [this]; unfold peps; rw [hLab0, if_pos (by omega)]
  have t0 : A0.tau 0 = x / 2 - σ := by
    have := ht0 0 (by omega); simp only [anode, if_true, hrX] at this
    rw [this]; unfold ptau; rw [hLab0, if_pos (by omega)]; omega
  have m0 : (0 : ℕ) ∈ A0.P.S := by rw [hS0]; left; rfl
  obtain ⟨A1, hS1, hE1, he1, ht1, _⟩ := A0.attachRoot Y y (by omega) hy (by rw [hrY]; exact m0)
    (by intro i hi hm; rw [hS0] at hm; omega) (by intro hm; rw [hS0] at hm; omega)
    (fun e => by omega) (fun e => by omega) (by rw [hrY, t0]; exact hok2)
  have t1 : A1.tau 0 = x / 2 - σ + y / 2 := by
    rw [ht1 _ m0, t0, hrY]; rw [show (par d 0 + par d 0) % 2 = 0 by rw [par_zero]]; omega
  have hS1' : ∀ w, w ∈ A1.P.S ↔ w = 0 ∨ (w % 8 = X ∧ 1 ≤ w / 8 ∧ w / 8 ≤ x) ∨
      (w % 8 = Y ∧ 1 ≤ w / 8 ∧ w / 8 ≤ y) := by
    intro w; rw [hS1, hS0]; omega
  have m1 : (0 : ℕ) ∈ A1.P.S := by rw [hS1']; left; rfl
  obtain ⟨G, hG, hR, hSG, hEG, hf⟩ := A1.attachGRoot Z z (by omega) hz (by rw [hrZ]; exact m1)
    (by intro i hi hm; rw [hS1'] at hm; omega) (by intro hm; rw [hS1'] at hm; omega)
    (fun e => by omega) (fun e => by omega) (by rw [hrZ, t1]; exact hok3)
  refine ⟨G, hG, hR, fun w => by rw [hSG, hS1']; unfold ShXYZ; omega,
    by rw [hEG, hE1, hE0], ?_⟩
  rcases hf 0 m1 with e | e <;> rw [he1 _ m0, e0] at e
  · left; exact e
  · right; exact e

/-- program sw1: IVL0 on `X, Y`, reflect, two vertices of `Z`, reflect, final segment of `Z` -/
theorem sw1_prog {d X Y Z x y z : ℕ} (hd : 1 ≤ d) (h : Arms3 X Y Z) (H : IVL0P d 0 X Y x y)
    (hz : x / 2 + y / 2 + 4 ≤ z) : SPX d 1 X x Y y Z z := by
  obtain ⟨hX, hY, hZ, hXY, hXZ, hYZ⟩ := h
  have hrZ := armRoot_u hZ
  have pZ2 : par d (Z + 8 * 2) = 0 := by
    rw [par_arm_root d Z 2 (by omega) (by omega), hrZ, par_zero]
  obtain ⟨A0, hS0, hE0, e0, t0⟩ := H
  have m0 : (0 : ℕ) ∈ A0.P.S := by rw [hS0]; left; rfl
  -- reflect: τ(u) = 0, ε(u) = x/2 + y/2
  have hS1 : ∀ w, w ∈ A0.refl.P.S ↔ Sh2 0 X x Y y w := by intro w; rw [A0.refl_S]; exact hS0 w
  have t1 : A0.refl.tau 0 = 0 := by rw [A0.refl_tau m0, e0]
  have e1 : A0.refl.eps 0 = x / 2 + y / 2 := by rw [A0.refl_eps m0, t0]
  have m1 : (0 : ℕ) ∈ A0.refl.P.S := by rw [hS1]; left; rfl
  obtain ⟨A2, hS2, hE2, he2, ht2, hend⟩ := A0.refl.attachRoot Z 2 (by omega) (by omega)
    (by rw [hrZ]; exact m1)
    (by intro i hi hm; rw [hS1] at hm; unfold Sh2 at hm; omega)
    (by intro hm; rw [hS1] at hm; unfold Sh2 at hm; omega)
    (fun e => by omega) (fun e => by omega) (by rw [hrZ, t1]; exact ⟨by omega, by omega, by omega⟩)
  rw [hrZ, t1] at hend
  have hS2' : ∀ w, w ∈ A2.P.S ↔ w = 0 ∨ (w % 8 = X ∧ 1 ≤ w / 8 ∧ w / 8 ≤ x) ∨
      (w % 8 = Y ∧ 1 ≤ w / 8 ∧ w / 8 ≤ y) ∨ (w % 8 = Z ∧ 1 ≤ w / 8 ∧ w / 8 ≤ 2) := by
    intro w; rw [hS2, hS1]; unfold Sh2; omega
  have m2 : (0 : ℕ) ∈ A2.P.S := by rw [hS2']; left; rfl
  have mZ2 : Z + 8 * 2 ∈ A2.P.S := by rw [hS2']; omega
  have t2 : A2.tau 0 = 1 := by
    rw [ht2 _ m1, t1, hrZ, show (par d 0 + par d 0) % 2 = 0 by rw [par_zero]]
  have e2 : A2.eps 0 = x / 2 + y / 2 := by rw [he2 _ m1, e1]
  have eZ2 : A2.eps (Z + 8 * 2) = x / 2 + y / 2 + 1 := by
    have := A2.eps_tau_same mZ2 m2 (by rw [pZ2, par_zero])
    rw [hend, e2, t2] at this; omega
  -- reflect again: ε(u) = 1
  have hS3 : ∀ w, w ∈ A2.refl.P.S ↔ w = 0 ∨ (w % 8 = X ∧ 1 ≤ w / 8 ∧ w / 8 ≤ x) ∨
      (w % 8 = Y ∧ 1 ≤ w / 8 ∧ w / 8 ≤ y) ∨ (w % 8 = Z ∧ 1 ≤ w / 8 ∧ w / 8 ≤ 2) := by
    intro w; rw [A2.refl_S]; exact hS2' w
  have e3 : A2.refl.eps 0 = 1 := by rw [A2.refl_eps m2, t2]
  have tZ2 : A2.refl.tau (Z + 8 * 2) = x / 2 + y / 2 + 1 := by rw [A2.refl_tau mZ2, eZ2]
  have mZ2' : Z + 8 * 2 ∈ A2.refl.P.S := by rw [hS3]; omega
  obtain ⟨G, hG, hR, hSG, hEG, hf⟩ := A2.refl.attachGArm Z 2 (z - 2) (by omega) (by omega)
    (by omega) mZ2'
    (by intro i hi hm; rw [hS3] at hm; omega) (by intro hm; rw [hS3] at hm; omega)
    (fun e => by omega) (fun e => by omega) (by rw [tZ2]; omega)
  have m3 : (0 : ℕ) ∈ A2.refl.P.S := by rw [hS3]; left; rfl
  refine ⟨G, hG, hR, fun w => by rw [hSG, hS3]; unfold ShXYZ; omega,
    by rw [hEG, A2.refl_card, hE2, A0.refl_card, hE0]; omega, ?_⟩
  rcases hf 0 m3 with e | e <;> rw [e3] at e
  · left; exact e
  · right; exact e

/-- program sw2: zigzag `X`, reflect, two vertices of `Y`, reflect, `Y` tail, final segment `Z` -/
theorem sw2_prog {d X Y Z x y z : ℕ} (hd : 1 ≤ d) (h : Arms3 X Y Z) (hx : 1 ≤ x) (hy : 3 ≤ y)
    (hz : 1 ≤ z) (hok : AeplOK (y - 2) (x / 2 + 1)) (hK : x / 2 + y / 2 ≤ z) :
    SPX d 1 X x Y y Z z := by
  obtain ⟨hX, hY, hZ, hXY, hXZ, hYZ⟩ := h
  have hrX := armRoot_u hX
  have hrY := armRoot_u hY
  have hrZ := armRoot_u hZ
  have pY2 : par d (Y + 8 * 2) = 0 := by
    rw [par_arm_root d Y 2 (by omega) (by omega), hrY, par_zero]
  obtain ⟨A0, hS0', hE0, e0', t0', _, _⟩ := startZZ d X x hd (by omega) (by omega) hx
  have hS0 : ∀ w, w ∈ A0.P.S ↔ w = 0 ∨ (w % 8 = X ∧ 1 ≤ w / 8 ∧ w / 8 ≤ x) :=
    fun w => by rw [hS0' w, hrX]
  have e0 : A0.eps 0 = 0 := (congrArg (fun w => A0.eps w) hrX).symm.trans e0'
  have t0 : A0.tau 0 = x / 2 := (congrArg (fun w => A0.tau w) hrX).symm.trans t0'
  have m0 : (0 : ℕ) ∈ A0.P.S := by rw [hS0]; left; rfl
  have hS1 : ∀ w, w ∈ A0.refl.P.S ↔ w = 0 ∨ (w % 8 = X ∧ 1 ≤ w / 8 ∧ w / 8 ≤ x) := by
    intro w; rw [A0.refl_S]; exact hS0 w
  have t1 : A0.refl.tau 0 = 0 := by rw [A0.refl_tau m0, e0]
  have e1 : A0.refl.eps 0 = x / 2 := by rw [A0.refl_eps m0, t0]
  have m1 : (0 : ℕ) ∈ A0.refl.P.S := by rw [hS1]; left; rfl
  obtain ⟨A2, hS2, hE2, he2, ht2, hend⟩ := A0.refl.attachRoot Y 2 (by omega) (by omega)
    (by rw [hrY]; exact m1)
    (by intro i hi hm; rw [hS1] at hm; omega) (by intro hm; rw [hS1] at hm; omega)
    (fun e => by omega) (fun e => by omega) (by rw [hrY, t1]; exact ⟨by omega, by omega, by omega⟩)
  rw [hrY, t1] at hend
  have hS2' : ∀ w, w ∈ A2.P.S ↔ w = 0 ∨ (w % 8 = X ∧ 1 ≤ w / 8 ∧ w / 8 ≤ x) ∨
      (w % 8 = Y ∧ 1 ≤ w / 8 ∧ w / 8 ≤ 2) := by
    intro w; rw [hS2, hS1]; omega
  have m2 : (0 : ℕ) ∈ A2.P.S := by rw [hS2']; left; rfl
  have mY2 : Y + 8 * 2 ∈ A2.P.S := by rw [hS2']; omega
  have t2 : A2.tau 0 = 1 := by
    rw [ht2 _ m1, t1, hrY, show (par d 0 + par d 0) % 2 = 0 by rw [par_zero]]
  have e2 : A2.eps 0 = x / 2 := by rw [he2 _ m1, e1]
  have eY2 : A2.eps (Y + 8 * 2) = x / 2 + 1 := by
    have := A2.eps_tau_same mY2 m2 (by rw [pY2, par_zero])
    rw [hend, e2, t2] at this; omega
  have hS3 : ∀ w, w ∈ A2.refl.P.S ↔ w = 0 ∨ (w % 8 = X ∧ 1 ≤ w / 8 ∧ w / 8 ≤ x) ∨
      (w % 8 = Y ∧ 1 ≤ w / 8 ∧ w / 8 ≤ 2) := by
    intro w; rw [A2.refl_S]; exact hS2' w
  have e3 : A2.refl.eps 0 = 1 := by rw [A2.refl_eps m2, t2]
  have t3 : A2.refl.tau 0 = x / 2 := by rw [A2.refl_tau m2, e2]
  have tY2 : A2.refl.tau (Y + 8 * 2) = x / 2 + 1 := by rw [A2.refl_tau mY2, eY2]
  have m3 : (0 : ℕ) ∈ A2.refl.P.S := by rw [hS3]; left; rfl
  have mY2' : Y + 8 * 2 ∈ A2.refl.P.S := by rw [hS3]; omega
  obtain ⟨A4, hS4, hE4, he4, ht4, _⟩ := A2.refl.attachArm Y 2 (y - 2) (by omega) (by omega)
    (by omega) mY2'
    (by intro i hi hm; rw [hS3] at hm; omega) (by intro hm; rw [hS3] at hm; omega)
    (fun e => by omega) (fun e => by omega) (by rw [tY2]; exact hok)
  have hS4' : ∀ w, w ∈ A4.P.S ↔ w = 0 ∨ (w % 8 = X ∧ 1 ≤ w / 8 ∧ w / 8 ≤ x) ∨
      (w % 8 = Y ∧ 1 ≤ w / 8 ∧ w / 8 ≤ y) := by
    intro w; rw [hS4, hS3]; omega
  have t4 : A4.tau 0 = x / 2 + (y - 2) / 2 := by
    rw [ht4 _ m3, t3, pY2, par_zero]; omega
  have e4 : A4.eps 0 = 1 := by rw [he4 _ m3, e3]
  have m4 : (0 : ℕ) ∈ A4.P.S := by rw [hS4']; left; rfl
  obtain ⟨G, hG, hR, hSG, hEG, hf⟩ := A4.attachGRoot Z z (by omega) hz (by rw [hrZ]; exact m4)
    (by intro i hi hm; rw [hS4'] at hm; omega) (by intro hm; rw [hS4'] at hm; omega)
    (fun e => by omega) (fun e => by omega) (by rw [hrZ, t4]; omega)
  refine ⟨G, hG, hR, fun w => by rw [hSG, hS4']; unfold ShXYZ; omega,
    by rw [hEG, hE4, A2.refl_card, hE2, A0.refl_card, hE0]; omega, ?_⟩
  rcases hf 0 m4 with e | e <;> rw [e4] at e
  · left; exact e
  · right; exact e

/-- turning a permuted spider into `SPG` -/
theorem spg_of_spx {d σ X Y Z x y z a b c : ℕ} (h : Arms3 X Y Z) (H : SPX d σ X x Y y Z z)
    (ha : a = if X = 2 then x else if Y = 2 then y else z)
    (hb : b = if X = 3 then x else if Y = 3 then y else z)
    (hc : c = if X = 4 then x else if Y = 4 then y else z) : SPG d σ a b c := by
  obtain ⟨G, hG, hR, hS, hE, hf⟩ := H
  refine ⟨G, hG, hR, fun w => by rw [hS]; unfold ShXYZ; exact shU_perm h ha hb hc, ?_, hf⟩
  rw [hE]
  obtain ⟨hX, hY, hZ, hXY, hXZ, hYZ⟩ := h
  rcases hX with rfl | rfl | rfl <;> rcases hY with rfl | rfl | rfl <;>
    rcases hZ with rfl | rfl | rfl <;> simp_all <;> omega

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

/-! ## Family C: template U (α u-side, graceful `P(2,2)` at `v`) -/

/-- graceful `P(2,2)` at `v` with `v` at label `1` or `3` -/
theorem p22G_13 (d : ℕ) (hd : 1 ≤ d) :
    ∃ G : Pc, G.Grace ∧ G.R = Tadj d ∧
      (∀ z, z ∈ G.S ↔ z = 1 ∨ z = 14 ∨ z = 22 ∨ z = 15 ∨ z = 23) ∧ G.E.card = 4 ∧
      (G.f 1 = 1 ∨ G.f 1 = 3) := by
  obtain ⟨A, hS, hE, he, _⟩ := startThrough d 1 6 7 2 2 hd arms_v (by omega) (by omega) labP22
    (by simpa using labP22_alpha) (by decide)
  have h1 : tnm 1 6 7 2 2 = 1 := by simp [tnm]
  have e1 := he 2 (by omega)
  rw [h1, show peps (2 + 2 + 1) labP22 2 = 1 by decide] at e1
  have hf := A.f_eps (z := 1) (by rw [hS]; left; rfl)
  rw [e1, hE] at hf
  exact ⟨A.P, A.hA.1, A.hR, fun z => by rw [hS]; unfold Sh2; omega, hE, by omega⟩

/-- graceful `P(2,2)` at `v` with `v` at label `0` or `4` -/
theorem p22G_04 (d : ℕ) (hd : 1 ≤ d) :
    ∃ G : Pc, G.Grace ∧ G.R = Tadj d ∧
      (∀ z, z ∈ G.S ↔ z = 1 ∨ z = 14 ∨ z = 22 ∨ z = 15 ∨ z = 23) ∧ G.E.card = 4 ∧
      (G.f 1 = 0 ∨ G.f 1 = 4) := by
  have hL : PathAlpha (2 + 1) (fun i => [0, 2, 1].getD i 0) (2 / 2) := by
    apply pathAlpha_of <;> decide
  obtain ⟨A, hS0, hE, he, ht⟩ := startArm d 7 2 hd (by omega) _ hL (by decide) (by omega)
  have hr : armRoot 7 = 1 := rfl
  have e1 : A.eps 1 = 0 := by
    have := he 0 (by omega); simp only [anode, if_true, hr] at this; rw [this]; decide
  have t1 : A.tau 1 = 1 := by
    have := ht 0 (by omega); simp only [anode, if_true, hr] at this; rw [this]; decide
  have hS : ∀ z, z ∈ A.P.S ↔ z = 1 ∨ (z % 8 = 7 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 2) :=
    fun z => by rw [hS0 z, hr]
  have m1 : (1 : ℕ) ∈ A.P.S := by rw [hS]; left; rfl
  obtain ⟨G, hG, hR, hSG, hEG, hf⟩ := A.attachGRoot 6 2 (by omega) (by omega)
    (by rw [show armRoot 6 = 1 from rfl]; exact m1)
    (by intro i hi h; rw [hS] at h; omega) (by intro h; rw [hS] at h; omega)
    (fun e => by omega) (fun e => by omega)
    (by rw [show armRoot 6 = 1 from rfl, t1])
  refine ⟨G, hG, hR, fun z => by rw [hSG, hS]; omega, by rw [hEG, hE], ?_⟩
  rcases hf 1 m1 with e | e <;> rw [e1] at e
  · left; exact e
  · right; rw [e, hEG, hE]

/-- graceful `P(2,2)` at `v` with `v` at `ρ` or `4 - ρ`, for `ρ ∈ {0,1,3,4}` -/
theorem p22G (d ρ : ℕ) (hd : 1 ≤ d) (hρ : ρ = 0 ∨ ρ = 1 ∨ ρ = 3 ∨ ρ = 4) :
    ∃ G : Pc, G.Grace ∧ G.R = Tadj d ∧
      (∀ z, z ∈ G.S ↔ z = 1 ∨ z = 14 ∨ z = 22 ∨ z = 15 ∨ z = 23) ∧ G.E.card = 4 ∧
      (G.f 1 = ρ ∨ G.f 1 = G.E.card - ρ) := by
  rcases hρ with rfl | rfl | rfl | rfl
  · obtain ⟨G, h1, h2, h3, h4, h5⟩ := p22G_04 d hd
    exact ⟨G, h1, h2, h3, h4, by rw [h4]; omega⟩
  · obtain ⟨G, h1, h2, h3, h4, h5⟩ := p22G_13 d hd
    exact ⟨G, h1, h2, h3, h4, by rw [h4]; omega⟩
  · obtain ⟨G, h1, h2, h3, h4, h5⟩ := p22G_13 d hd
    exact ⟨G, h1, h2, h3, h4, by rw [h4]; omega⟩
  · obtain ⟨G, h1, h2, h3, h4, h5⟩ := p22G_04 d hd
    exact ⟨G, h1, h2, h3, h4, by rw [h4]; omega⟩

/-- U-side, first half: zigzag along `X` from `u`, then the `d`-path from `u` -/
theorem famC_U1 {d X x : ℕ} (hd : 1 ≤ d) (hX : X = 2 ∨ X = 3 ∨ X = 4) (hx : 1 ≤ x)
    (hD : d = 1 ∨ AeplOK (d - 1) (x / 2)) :
    ∃ q, ∃ A : APc d q, (∀ w, w ∈ A.P.S ↔ w = 0 ∨ (w % 8 = X ∧ 1 ≤ w / 8 ∧ w / 8 ≤ x) ∨
        (w % 8 = 5 ∧ 1 ≤ w / 8 ∧ w / 8 ≤ d - 1)) ∧
      A.eps 0 = 0 ∧ A.tau (dnode d (d - 1)) = x / 2 := by
  have hrX := armRoot_u hX
  obtain ⟨A0, hS0', _, e0', t0', _, _⟩ := startZZ d X x hd (by omega) (by omega) hx
  have hS0 : ∀ w, w ∈ A0.P.S ↔ w = 0 ∨ (w % 8 = X ∧ 1 ≤ w / 8 ∧ w / 8 ≤ x) :=
    fun w => by rw [hS0' w, hrX]
  have e0 : A0.eps 0 = 0 := (congrArg (fun w => A0.eps w) hrX).symm.trans e0'
  have t0 : A0.tau 0 = x / 2 := (congrArg (fun w => A0.tau w) hrX).symm.trans t0'
  have m0 : (0 : ℕ) ∈ A0.P.S := by rw [hS0]; left; rfl
  by_cases hd1 : d = 1
  · subst hd1
    refine ⟨_, A0, fun w => by rw [hS0]; omega, e0, ?_⟩
    have : dnode 1 (1 - 1) = 0 := by unfold dnode; simp
    rw [this, t0]
  · have hok' : AeplOK (d - 1) (x / 2) := by rcases hD with h' | h' <;> [omega; exact h']
    obtain ⟨B, hSB, _, heB, _, htB⟩ := A0.attachRoot 5 (d - 1) (by omega) (by omega)
      (by rw [show armRoot 5 = 0 from rfl]; exact m0)
      (by intro i hi hm; rw [hS0] at hm; omega) (by intro hm; rw [hS0] at hm; omega)
      (fun _ => by omega) (fun _ _ hm => by rw [hS0] at hm; omega)
      (by rw [show armRoot 5 = 0 from rfl, t0]; exact hok')
    refine ⟨_, B, fun w => by rw [hSB, hS0]; omega, by rw [heB _ m0, e0], ?_⟩
    have : dnode d (d - 1) = 5 + 8 * (d - 1) := by
      unfold dnode; rw [if_neg (by omega), if_neg (by omega)]
    rw [this, htB, show armRoot 5 = 0 from rfl, t0]

/-- U-side, second half: reflect, `Y` and `Z` at `u`, reflect back -/
theorem famC_U2 {d X Y Z x y z q1 : ℕ} (h : Arms3 X Y Z) (hy : 1 ≤ y) (hz : 1 ≤ z)
    (hok : AeplOK z (y / 2)) (A1 : APc d q1)
    (hS1 : ∀ w, w ∈ A1.P.S ↔ w = 0 ∨ (w % 8 = X ∧ 1 ≤ w / 8 ∧ w / 8 ≤ x) ∨
        (w % 8 = 5 ∧ 1 ≤ w / 8 ∧ w / 8 ≤ d - 1))
    (e1 : A1.eps 0 = 0) (j : ℕ) (mj : j ∈ A1.P.S) (tj : A1.tau j = x / 2) :
    ∃ A : APc d q1, (∀ w, w ∈ A.P.S ↔ w = 0 ∨ (w % 8 = X ∧ 1 ≤ w / 8 ∧ w / 8 ≤ x) ∨
        (w % 8 = 5 ∧ 1 ≤ w / 8 ∧ w / 8 ≤ d - 1) ∨ (w % 8 = Y ∧ 1 ≤ w / 8 ∧ w / 8 ≤ y) ∨
        (w % 8 = Z ∧ 1 ≤ w / 8 ∧ w / 8 ≤ z)) ∧ A.tau j = x / 2 := by
  obtain ⟨hX, hY, hZ, hXY, hXZ, hYZ⟩ := h
  have hrY := armRoot_u hY
  have hrZ := armRoot_u hZ
  have m1 : (0 : ℕ) ∈ A1.P.S := by rw [hS1]; left; rfl
  have t2 : A1.refl.tau 0 = 0 := by rw [A1.refl_tau m1, e1]
  have ej : A1.refl.eps j = x / 2 := by rw [A1.refl_eps mj, tj]
  have m2 : (0 : ℕ) ∈ A1.refl.P.S := by rw [A1.refl_S]; exact m1
  have mj2 : j ∈ A1.refl.P.S := by rw [A1.refl_S]; exact mj
  obtain ⟨A3, hS3, _, he3, ht3, _⟩ := A1.refl.attachRoot Y y (by omega) hy
    (by rw [hrY]; exact m2)
    (by intro i hi hm; rw [A1.refl_S, hS1] at hm; omega)
    (by intro hm; rw [A1.refl_S, hS1] at hm; omega)
    (fun _ => by omega) (fun _ => by omega)
    (by rw [hrY, t2]; exact ⟨by omega, by omega, by omega⟩)
  have hS3' : ∀ w, w ∈ A3.P.S ↔ w = 0 ∨ (w % 8 = X ∧ 1 ≤ w / 8 ∧ w / 8 ≤ x) ∨
      (w % 8 = 5 ∧ 1 ≤ w / 8 ∧ w / 8 ≤ d - 1) ∨ (w % 8 = Y ∧ 1 ≤ w / 8 ∧ w / 8 ≤ y) := by
    intro w; rw [hS3, A1.refl_S, hS1]; omega
  have t3 : A3.tau 0 = y / 2 := by
    rw [ht3 _ m2, t2, hrY, show (par d 0 + par d 0) % 2 = 0 by rw [par_zero]]; omega
  have m3 : (0 : ℕ) ∈ A3.P.S := by rw [hS3']; left; rfl
  have mj3 : j ∈ A3.P.S := by rw [hS3]; left; exact mj2
  obtain ⟨A4, hS4, _, he4, _, _⟩ := A3.attachRoot Z z (by omega) hz
    (by rw [hrZ]; exact m3)
    (by intro i hi hm; rw [hS3'] at hm; omega) (by intro hm; rw [hS3'] at hm; omega)
    (fun _ => by omega) (fun _ => by omega)
    (by rw [hrZ, t3]; exact hok)
  have mj4 : j ∈ A4.P.S := by rw [hS4]; left; exact mj3
  refine ⟨A4.refl, fun w => by rw [A4.refl_S, hS4, hS3']; omega, ?_⟩
  rw [A4.refl_tau mj4, he4 _ mj3, he3 _ mj2, ej]

/-- template U -/
theorem famC_U {a b c d X Y Z x y z : ℕ} (hd : 1 ≤ d) (h : Arms3 X Y Z)
    (ha : a = if X = 2 then x else if Y = 2 then y else z)
    (hb : b = if X = 3 then x else if Y = 3 then y else z)
    (hc : c = if X = 4 then x else if Y = 4 then y else z)
    (hx : 1 ≤ x) (hy : 1 ≤ y) (hz : 1 ≤ z)
    (hρ : x / 2 = 0 ∨ x / 2 = 1 ∨ x / 2 = 3 ∨ x / 2 = 4)
    (hD : d = 1 ∨ AeplOK (d - 1) (x / 2)) (hok : AeplOK z (y / 2)) :
    CanonGraceful a b c d 2 2 := by
  have hperm := fun w => shU_perm (w := w) h ha hb hc
  obtain ⟨q1, A1, hS1, e1, tj⟩ := famC_U1 hd h.hX hx hD
  have mj : dnode d (d - 1) ∈ A1.P.S := by
    have := h.hX
    rw [hS1]; unfold dnode; split_ifs <;> omega
  obtain ⟨A, hS, ht⟩ := famC_U2 h hy hz hok A1 hS1 e1 _ mj tj
  obtain ⟨G, hG, hGR, hGS, hGE, hGf⟩ := p22G d (x / 2) hd hρ
  have hv : dnode d (d - 1 + 1) = 1 := by unfold dnode; rw [if_neg (by omega), if_pos (by omega)]
  have hX := h.hX
  have hY := h.hY
  have hZ := h.hZ
  refine join_uv (j := d - 1) hd (by omega) A G hG hGR
    (by
      intro w hw; rw [hS] at hw; unfold uPart
      rcases hw with h' | h' | h' | h' | h' <;> omega)
    (by intro w hw; rw [hGS] at hw; unfold vPart; omega)
    (by rw [hS]; have := (hS1 _).mp mj; omega)
    (by rw [hv, hGS]; left; rfl)
    (by rw [hv, ht]; exact hGf)
    (by rw [ht, hGE]; omega)
    (by
      intro s; rw [hS, hGS, tset22_iff hd, ← hperm s]
      constructor
      · rintro ((h' | h' | h' | h' | h') | h') <;> omega
      · rintro ((h' | h' | h' | h') | h' | h' | h' | h' | h' | h') <;> omega)

/-! ## Family C at `d = 3`: templates PiE, Pi', PiE2_3 (explicit start through `v` and `u`) -/

/-- a leaf chain along arm `X` hanging at its root -/
theorem leafRoot {d : ℕ} (hd : 1 ≤ d) (X L : ℕ) (hX : 2 ≤ X ∧ X ≤ 7) (hX5 : X ≠ 5) (G : Pc)
    (hG : G.Grace) (hR : G.R = Tadj d) (hx : armRoot X ∈ G.S)
    (hf : G.f (armRoot X) = 0 ∨ G.f (armRoot X) = G.E.card)
    (hfresh : ∀ w, w % 8 = X → 1 ≤ w / 8 → w / 8 ≤ L + 1 → w ∉ G.S) :
    ∃ G' : Pc, G'.Grace ∧ G'.R = Tadj d ∧
      (∀ s, s ∈ G'.S ↔ s ∈ G.S ∨ (s % 8 = X ∧ 1 ≤ s / 8 ∧ s / 8 ≤ L)) ∧
      G'.E.card = G.E.card + L := by
  obtain ⟨G', h1, h2, h3, h4⟩ := leafChain hd X hX L 0 G hG hR (by rw [if_pos rfl]; exact hx)
    (by rw [if_pos rfl]; exact hf)
    (fun i hi => hfresh _ (by omega) (by omega) (by omega))
    (hfresh _ (by omega) (by omega) (by omega)) (fun h => absurd h hX5) (fun h => absurd h hX5)
  exact ⟨G', h1, h2, fun s => by rw [h3, exists_out_iff X 0 L s (by omega), zero_add, zero_add], h4⟩

/-- vertex set of a `d = 3` start: `f2, f1, v, d2, d1, u` and arm `2` up to `a` -/
def D3S (a w : ℕ) : Prop :=
  w = 23 ∨ w = 15 ∨ w = 1 ∨ w = 21 ∨ w = 13 ∨ w = 0 ∨ (w % 8 = 2 ∧ 1 ≤ w / 8 ∧ w / 8 ≤ a)

/-- the common finish at `d = 3`: `b` (α) and `c` (final) at `u`, then the `e`-arm at `v` -/
theorem d3_finish {a b c q t : ℕ} (A : APc 3 q) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hS : ∀ w, w ∈ A.P.S ↔ D3S a w) (hev : A.eps 1 = 0) (htu : A.tau 0 = t)
    (hok : AeplOK b t) (hok2 : t + b / 2 ≤ c - 1) : CanonGraceful a b c 3 2 2 := by
  have m0 : (0 : ℕ) ∈ A.P.S := by rw [hS]; unfold D3S; omega
  have m1 : (1 : ℕ) ∈ A.P.S := by rw [hS]; unfold D3S; omega
  obtain ⟨A2, hS2, _, he2, ht2, _⟩ := A.attachRoot 3 b (by omega) hb
    (by rw [show armRoot 3 = 0 from rfl]; exact m0)
    (by intro i hi hm; rw [hS] at hm; unfold D3S at hm; omega)
    (by intro hm; rw [hS] at hm; unfold D3S at hm; omega)
    (fun e => by omega) (fun e => by omega)
    (by rw [show armRoot 3 = 0 from rfl, htu]; exact hok)
  have hS2' : ∀ w, w ∈ A2.P.S ↔ D3S a w ∨ (w % 8 = 3 ∧ 1 ≤ w / 8 ∧ w / 8 ≤ b) := by
    intro w; rw [hS2, hS]
  have t2 : A2.tau 0 = t + b / 2 := by
    rw [ht2 _ m0, htu, show armRoot 3 = 0 from rfl, par_zero]; omega
  have m0' : (0 : ℕ) ∈ A2.P.S := by rw [hS2]; left; exact m0
  have m1' : (1 : ℕ) ∈ A2.P.S := by rw [hS2]; left; exact m1
  obtain ⟨G, hG, hR, hSG, hEG, hf⟩ := A2.attachGRoot 4 c (by omega) hc
    (by rw [show armRoot 4 = 0 from rfl]; exact m0')
    (by intro i hi hm; rw [hS2'] at hm; unfold D3S at hm; omega)
    (by intro hm; rw [hS2'] at hm; unfold D3S at hm; omega)
    (fun e => by omega) (fun e => by omega)
    (by rw [show armRoot 4 = 0 from rfl, t2]; exact hok2)
  have hv : G.f 1 = 0 ∨ G.f 1 = G.E.card := by
    rcases hf 1 m1' with e | e <;> rw [he2 _ m1, hev] at e
    · left; exact e
    · right; rw [e]; rfl
  obtain ⟨G', hG', hR', hS', _⟩ := leafRoot (d := 3) (by omega) 6 2 (by omega) (by omega) G hG hR
    (by rw [show armRoot 6 = 1 from rfl, hSG]; left; exact m1')
    (by rw [show armRoot 6 = 1 from rfl]; exact hv)
    (by intro w h1 h2 h3 hm; rw [hSG, hS2'] at hm; unfold D3S at hm; omega)
  refine canon_of_piece G' hG' hR' (fun s => ?_)
  rw [hS', hSG, hS2', tset22_iff (by omega)]
  unfold D3S ShU
  constructor
  · rintro ((((h | h | h | h | h | h | h) | h) | h) | h) <;> omega
  · rintro ((h | h | h | h) | h | h | h | h | h | h) <;> omega

/-- start PiE, `x = 1`: path `f2 f1 v d2 d1 u a1` -/
theorem d3_sE1 : ∃ q, ∃ A : APc 3 q, (∀ w, w ∈ A.P.S ↔ D3S 1 w) ∧ A.eps 1 = 0 ∧ A.tau 0 = 0 := by
  obtain ⟨A, hS, _, he, ht⟩ := numTreeA 3 4 1 [23, 15, 1, 21, 13, 0, 10] [0, 0, 1, 2, 3, 4, 5]
    [1, 5, 0, 6, 3, 4, 2] (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by omega)
  have hm := mem_list_iff (names := [23, 15, 1, 21, 13, 0, 10])
    (φ := fun w => w = 23 ∨ w = 15 ∨ w = 1 ∨ w = 21 ∨ w = 13 ∨ w = 0 ∨
      (w % 8 = 2 ∧ 1 ≤ w / 8 ∧ w / 8 ≤ 1)) 32
    (by decide +kernel) (by decide +kernel) (by intro z hz; omega)
  refine ⟨1, A, fun w => by rw [hS, hm w]; rfl, ?_, ?_⟩
  · have := he 2 (by decide); simpa using this
  · have := ht 5 (by decide); simpa using this

/-- start PiE, `x = 2`: path `f2 f1 v d2 d1 u a1 a2` (`τ(a2) = 1`) -/
theorem d3_sE2 : ∃ q, ∃ A : APc 3 q, (∀ w, w ∈ A.P.S ↔ D3S 2 w) ∧ A.eps 1 = 0 ∧ A.tau 0 = 0 ∧
    A.tau 18 = 1 := by
  obtain ⟨A, hS, _, he, ht⟩ := numTreeA 3 4 1 [23, 15, 1, 21, 13, 0, 10, 18] [0, 0, 1, 2, 3, 4, 5, 6]
    [1, 6, 0, 7, 3, 4, 2, 5] (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by omega)
  have hm := mem_list_iff (names := [23, 15, 1, 21, 13, 0, 10, 18])
    (φ := fun w => w = 23 ∨ w = 15 ∨ w = 1 ∨ w = 21 ∨ w = 13 ∨ w = 0 ∨
      (w % 8 = 2 ∧ 1 ≤ w / 8 ∧ w / 8 ≤ 2)) 32
    (by decide +kernel) (by decide +kernel) (by intro z hz; omega)
  refine ⟨1, A, fun w => by rw [hS, hm w]; rfl, ?_, ?_, ?_⟩
  · have := he 2 (by decide); simpa using this
  · have := ht 5 (by decide); simpa using this
  · have := ht 7 (by decide); simpa using this

/-- start PiE, `x = 4`: path `f2 f1 v d2 d1 u a1 a2 a3 a4` -/
theorem d3_sE4 : ∃ q, ∃ A : APc 3 q, (∀ w, w ∈ A.P.S ↔ D3S 4 w) ∧ A.eps 1 = 0 ∧ A.tau 0 = 0 := by
  obtain ⟨A, hS, _, he, ht⟩ := numTreeA 3 5 1 [23, 15, 1, 21, 13, 0, 10, 18, 26, 34]
    [0, 0, 1, 2, 3, 4, 5, 6, 7, 8] [1, 8, 0, 9, 3, 5, 4, 7, 2, 6] (by decide) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by omega)
  have hm := mem_list_iff (names := [23, 15, 1, 21, 13, 0, 10, 18, 26, 34])
    (φ := fun w => w = 23 ∨ w = 15 ∨ w = 1 ∨ w = 21 ∨ w = 13 ∨ w = 0 ∨
      (w % 8 = 2 ∧ 1 ≤ w / 8 ∧ w / 8 ≤ 4)) 40
    (by decide +kernel) (by decide +kernel) (by intro z hz; omega)
  refine ⟨1, A, fun w => by rw [hS, hm w]; rfl, ?_, ?_⟩
  · have := he 2 (by decide); simpa using this
  · have := ht 5 (by decide); simpa using this

/-- start PiE2_3: path `f2 f1 v d2 d1 u a1 a2 a3` -/
theorem d3_sE3 : ∃ q, ∃ A : APc 3 q, (∀ w, w ∈ A.P.S ↔ D3S 3 w) ∧ A.eps 1 = 0 ∧ A.tau 0 = 0 := by
  obtain ⟨A, hS, _, he, ht⟩ := numTreeA 3 5 1 [23, 15, 1, 21, 13, 0, 10, 18, 26]
    [0, 0, 1, 2, 3, 4, 5, 6, 7] [1, 8, 0, 6, 4, 5, 2, 7, 3] (by decide) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by omega)
  have hm := mem_list_iff (names := [23, 15, 1, 21, 13, 0, 10, 18, 26])
    (φ := fun w => w = 23 ∨ w = 15 ∨ w = 1 ∨ w = 21 ∨ w = 13 ∨ w = 0 ∨
      (w % 8 = 2 ∧ 1 ≤ w / 8 ∧ w / 8 ≤ 3)) 32
    (by decide +kernel) (by decide +kernel) (by intro z hz; omega)
  refine ⟨1, A, fun w => by rw [hS, hm w]; rfl, ?_, ?_⟩
  · have := he 2 (by decide); simpa using this
  · have := ht 5 (by decide); simpa using this

/-- start Pi': path `f2 f1 v d2 d1 u` with `τ(u) = 1` -/
theorem d3_sP : ∃ q, ∃ A : APc 3 q, (∀ w, w ∈ A.P.S ↔ D3S 0 w) ∧ A.eps 1 = 0 ∧ A.tau 0 = 1 := by
  obtain ⟨A, hS, _, he, ht⟩ := numTreeA 3 3 1 [23, 15, 1, 21, 13, 0] [0, 0, 1, 2, 3, 4]
    [1, 5, 0, 3, 2, 4] (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by omega)
  have hm := mem_list_iff (names := [23, 15, 1, 21, 13, 0])
    (φ := fun w => w = 23 ∨ w = 15 ∨ w = 1 ∨ w = 21 ∨ w = 13 ∨ w = 0 ∨
      (w % 8 = 2 ∧ 1 ≤ w / 8 ∧ w / 8 ≤ 0)) 24
    (by decide +kernel) (by decide +kernel) (by intro z hz; omega)
  refine ⟨1, A, fun w => by rw [hS, hm w]; rfl, ?_, ?_⟩
  · have := he 2 (by decide); simpa using this
  · have := ht 5 (by decide); simpa using this

/-- template PiE for `x ≥ 5` (`x ≠ 7`): start `x = 2`, then the arm-2 tail at `a2` -/
theorem d3_sEg {a : ℕ} (ha : 5 ≤ a) (ha7 : a ≠ 7) :
    ∃ q, ∃ A : APc 3 q, (∀ w, w ∈ A.P.S ↔ D3S a w) ∧ A.eps 1 = 0 ∧ A.tau 0 = (a - 2) / 2 := by
  obtain ⟨q, A, hS, he1, ht0, ht18⟩ := d3_sE2
  have m18 : 2 + 8 * 2 ∈ A.P.S := by rw [hS]; unfold D3S; omega
  obtain ⟨B, hSB, _, heB, htB, _⟩ := A.attachArm 2 2 (a - 2) (by omega) (by omega) (by omega) m18
    (by intro i hi hm; rw [hS] at hm; unfold D3S at hm; omega)
    (by intro hm; rw [hS] at hm; unfold D3S at hm; omega)
    (fun e => by omega) (fun e => by omega)
    (by rw [show 2 + 8 * 2 = 18 from rfl, ht18]; exact ⟨by omega, by omega, by omega⟩)
  have m0 : (0 : ℕ) ∈ A.P.S := by rw [hS]; unfold D3S; omega
  have m1 : (1 : ℕ) ∈ A.P.S := by rw [hS]; unfold D3S; omega
  refine ⟨q, B, fun w => by rw [hSB, hS]; unfold D3S; omega, by rw [heB _ m1, he1], ?_⟩
  rw [htB _ m0, ht0, par_zero, show par 3 (2 + 8 * 2) = 0 by decide]
  omega

/-- template Pi': start Pi', then arm `2` (α) at `u` -/
theorem d3_sPa {a : ℕ} (ha : 1 ≤ a) (hok : AeplOK a 1) :
    ∃ q, ∃ A : APc 3 q, (∀ w, w ∈ A.P.S ↔ D3S a w) ∧ A.eps 1 = 0 ∧ A.tau 0 = 1 + a / 2 := by
  obtain ⟨q, A, hS, he1, ht0⟩ := d3_sP
  have m0 : (0 : ℕ) ∈ A.P.S := by rw [hS]; unfold D3S; omega
  have m1 : (1 : ℕ) ∈ A.P.S := by rw [hS]; unfold D3S; omega
  obtain ⟨B, hSB, _, heB, htB, _⟩ := A.attachRoot 2 a (by omega) ha
    (by rw [show armRoot 2 = 0 from rfl]; exact m0)
    (by intro i hi hm; rw [hS] at hm; unfold D3S at hm; omega)
    (by intro hm; rw [hS] at hm; unfold D3S at hm; omega)
    (fun e => by omega) (fun e => by omega)
    (by rw [show armRoot 2 = 0 from rfl, ht0]; exact hok)
  refine ⟨q, B, fun w => by rw [hSB, hS]; unfold D3S; omega, by rw [heB _ m1, he1], ?_⟩
  rw [htB _ m0, ht0, show armRoot 2 = 0 from rfl, par_zero]
  omega

/-- **every `(a,b,c)` at `d = 3`** -/
theorem famC_d3 (a b c : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) :
    CanonGraceful a b c 3 2 2 := by
  have hb : 1 ≤ b := by omega
  have hc : 1 ≤ c := by omega
  -- the finish with `t = 0` works for every `b ≤ c`
  have fin0 : ∀ q (A : APc 3 q), (∀ w, w ∈ A.P.S ↔ D3S a w) → A.eps 1 = 0 → A.tau 0 = 0 →
      CanonGraceful a b c 3 2 2 := fun q A hS he ht =>
    d3_finish A hb hc hS he ht ⟨by omega, by omega, by omega⟩ (by omega)
  -- template cut (`x = a`)
  have cut : 4 ≤ a → AeplOK (a - 1) 1 → AeplOK b (a / 2) → a / 2 + b / 2 ≤ c - 1 →
      CanonGraceful a b c 3 2 2 := fun h4 h1 h2 h3 =>
    famC_cut (X := 2) (Y := 3) (Z := 4) (x := a) (y := b) (z := c) (d := 3) (by omega)
      ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩ (by simp) (by simp) (by simp)
      (by omega) hb hc h1 h2 h3 (vsp1 3 1 (by omega) (Or.inr (Or.inr (Or.inl rfl))))
  -- template Pi'
  have pi' : AeplOK a 1 → AeplOK b (1 + a / 2) → 1 + a / 2 + b / 2 ≤ c - 1 →
      CanonGraceful a b c 3 2 2 := fun h1 h2 h3 => by
    obtain ⟨q, A, hS, he, ht⟩ := d3_sPa ha h1
    exact d3_finish A hb hc hS he ht h2 h3
  by_cases h1 : a = 1
  · subst h1; obtain ⟨q, A, hS, he, ht⟩ := d3_sE1; exact fin0 q A hS he ht
  by_cases h2 : a = 2
  · subst h2; obtain ⟨q, A, hS, he, ht, _⟩ := d3_sE2; exact fin0 q A hS he ht
  by_cases h3 : a = 3
  · subst h3; obtain ⟨q, A, hS, he, ht⟩ := d3_sE3; exact fin0 q A hS he ht
  by_cases h4 : a = 4
  · subst h4; obtain ⟨q, A, hS, he, ht⟩ := d3_sE4; exact fin0 q A hS he ht
  by_cases h7 : a = 7
  · subst h7
    by_cases h13 : b = 13
    · subst h13
      exact pi' ⟨by omega, by omega, by omega⟩ ⟨by omega, by omega, by omega⟩ (by omega)
    · exact cut (by omega) ⟨by omega, by omega, by omega⟩ ⟨by omega, by omega, by omega⟩ (by omega)
  by_cases hx : b % 4 = 1 ∧ 4 * ((a - 2) / 2) = b - 1
  · by_cases h6 : a = 6
    · subst h6
      exact pi' ⟨by omega, by omega, by omega⟩ ⟨by omega, by omega, by omega⟩ (by omega)
    · exact cut (by omega) ⟨by omega, by omega, by omega⟩ ⟨by omega, by omega, by omega⟩ (by omega)
  · obtain ⟨q, A, hS, he, ht⟩ := d3_sEg (a := a) (by omega) h7
    exact d3_finish A hb hc hS he ht ⟨by omega, by omega, by omega⟩ (by omega)

/-! ## Graceful spiders with the centre at `1` (all but 13 spiders) and at `2` -/

theorem arms_234 : Arms3 2 3 4 := ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
theorem arms_324 : Arms3 3 2 4 := ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
theorem arms_423 : Arms3 4 2 3 := ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
theorem arms_243 : Arms3 2 4 3 := ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩

theorem spg_spA_abc {d σ a b c : ℕ} (hd : 1 ≤ d) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (h1 : AeplOK (a + 1) σ) (h2 : AeplOK b (a / 2 - σ)) (h3 : a / 2 - σ + b / 2 ≤ c - 1) :
    SPG d σ a b c :=
  spg_of_spx arms_234 (spA_prog hd arms_234 ha hb hc h1 h2 h3) (by simp) (by simp) (by simp)

theorem spg_spA_bac {d σ a b c : ℕ} (hd : 1 ≤ d) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (h1 : AeplOK (b + 1) σ) (h2 : AeplOK a (b / 2 - σ)) (h3 : b / 2 - σ + a / 2 ≤ c - 1) :
    SPG d σ a b c :=
  spg_of_spx arms_324 (spA_prog hd arms_324 hb ha hc h1 h2 h3) (by simp) (by simp) (by simp)

theorem spg_spA_cab {d σ a b c : ℕ} (hd : 1 ≤ d) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (h1 : AeplOK (c + 1) σ) (h2 : AeplOK a (c / 2 - σ)) (h3 : c / 2 - σ + a / 2 ≤ b - 1) :
    SPG d σ a b c :=
  spg_of_spx arms_423 (spA_prog hd arms_423 hc ha hb h1 h2 h3) (by simp) (by simp) (by simp)

theorem spg_spA_acb {d σ a b c : ℕ} (hd : 1 ≤ d) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (h1 : AeplOK (a + 1) σ) (h2 : AeplOK c (a / 2 - σ)) (h3 : a / 2 - σ + c / 2 ≤ b - 1) :
    SPG d σ a b c :=
  spg_of_spx arms_243 (spA_prog hd arms_243 ha hc hb h1 h2 h3) (by simp) (by simp) (by simp)

theorem spg_sw1_abc {d a b c : ℕ} (hd : 1 ≤ d) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (h22 : ¬ (a = 2 ∧ b = 2)) (h3 : a / 2 + b / 2 + 4 ≤ c) : SPG d 1 a b c :=
  spg_of_spx arms_234 (sw1_prog hd arms_234 (ivl0_all hd arms_234.arms2 ha hb h22) h3)
    (by simp) (by simp) (by simp)

theorem spg_sw2_abc {d a b c : ℕ} (hd : 1 ≤ d) (ha : 1 ≤ a) (hb : 3 ≤ b) (hc : 1 ≤ c)
    (hok : AeplOK (b - 2) (a / 2 + 1)) (hK : a / 2 + b / 2 ≤ c) : SPG d 1 a b c :=
  spg_of_spx arms_234 (sw2_prog hd arms_234 ha hb hc hok hK) (by simp) (by simp) (by simp)

theorem spg_sw2_acb {d a b c : ℕ} (hd : 1 ≤ d) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 3 ≤ c)
    (hok : AeplOK (c - 2) (a / 2 + 1)) (hK : a / 2 + c / 2 ≤ b) : SPG d 1 a b c :=
  spg_of_spx arms_243 (sw2_prog hd arms_243 ha hc hb hok hK) (by simp) (by simp) (by simp)

/-- the 13 spiders without an SP1 program -/
def F1 (a b c : ℕ) : Prop :=
  (a = 1 ∧ b = 1 ∧ c = 1) ∨ (a = 1 ∧ b = 4 ∧ c = 4) ∨ (a = 4 ∧ b = 4 ∧ c = 4) ∨
  (a = 4 ∧ b = 4 ∧ c = 6) ∨ (a = 4 ∧ b = 4 ∧ c = 7) ∨ (a = 4 ∧ b = 6 ∧ c = 6) ∨
  (a = 4 ∧ b = 6 ∧ c = 7) ∨ (a = 4 ∧ b = 6 ∧ c = 8) ∨ (a = 4 ∧ b = 7 ∧ c = 7) ∨
  (a = 4 ∧ b = 7 ∧ c = 8) ∨ (a = 4 ∧ b = 8 ∧ c = 8) ∨ (a = 5 ∧ b = 5 ∧ c = 5) ∨
  (a = 6 ∧ b = 9 ∧ c = 9)

/-- **SP1**: a graceful spider at `u` with `u` at `1` (or `m - 1`) for every sorted spider not in `F1` -/
theorem sp1_all (d a b c : ℕ) (hd : 1 ≤ d) (ha : 1 ≤ a) (hab : a ≤ b) (hbc : b ≤ c)
    (hF : ¬ F1 a b c) : SPG d 1 a b c := by
  by_cases hA : 2 ≤ a ∧ a ≠ 4 ∧ ¬ (b % 4 = 1 ∧ 1 < b ∧ 4 * (a / 2 - 1) = b - 1)
  · exact spg_spA_abc hd ha (by omega) (by omega) ⟨by omega, by omega, by omega⟩
      ⟨by omega, by omega, by omega⟩ (by omega)
  by_cases h1 : a = 1
  · subst h1
    by_cases hb1 : b = 1
    · subst hb1
      by_cases hc4 : 4 ≤ c
      · exact spg_sw1_abc hd (by omega) (by omega) (by omega) (by omega)
      · have : c = 1 ∨ c = 2 ∨ c = 3 := by omega
        rcases this with rfl | rfl | rfl
        · exact (hF (by unfold F1; decide)).elim
        · exact spg_spA_cab hd (by omega) (by omega) (by omega) ⟨by omega, by omega, by omega⟩
            ⟨by omega, by omega, by omega⟩ (by omega)
        · exact spg_spA_cab hd (by omega) (by omega) (by omega) ⟨by omega, by omega, by omega⟩
            ⟨by omega, by omega, by omega⟩ (by omega)
    by_cases hb23 : b = 2 ∨ b = 3
    · exact spg_spA_bac hd (by omega) (by omega) (by omega) ⟨by omega, by omega, by omega⟩
        ⟨by omega, by omega, by omega⟩ (by omega)
    by_cases hb7 : b = 7
    · exact spg_sw1_abc hd (by omega) (by omega) (by omega) (by omega)
    by_cases hb4 : b = 4
    · subst hb4
      by_cases hc6 : 6 ≤ c
      · exact spg_sw1_abc hd (by omega) (by omega) (by omega) (by omega)
      · have : c = 4 ∨ c = 5 := by omega
        rcases this with rfl | rfl
        · exact (hF (by unfold F1; decide)).elim
        · exact spg_sw2_acb hd (by omega) (by omega) (by omega) ⟨by omega, by omega, by omega⟩
            (by omega)
    · exact spg_sw2_abc hd (by omega) (by omega) (by omega) ⟨by omega, by omega, by omega⟩
        (by omega)
  by_cases h4 : a = 4
  · subst h4
    by_cases hb9 : 9 ≤ b ∧ b ≠ 15
    · exact spg_sw2_abc hd (by omega) (by omega) (by omega) ⟨by omega, by omega, by omega⟩
        (by omega)
    by_cases hs : 4 / 2 + b / 2 + 4 ≤ c
    · exact spg_sw1_abc hd (by omega) (by omega) (by omega) hs
    have hb8 : b ≤ 8 := by omega
    have hc9 : c ≤ 9 := by omega
    interval_cases b <;> interval_cases c <;>
      first
      | omega
      | exact (hF (by unfold F1; decide)).elim
      | exact spg_spA_cab hd (by omega) (by omega) (by omega) ⟨by omega, by omega, by omega⟩
          ⟨by omega, by omega, by omega⟩ (by omega)
      | exact spg_spA_bac hd (by omega) (by omega) (by omega) ⟨by omega, by omega, by omega⟩
          ⟨by omega, by omega, by omega⟩ (by omega)
      | exact spg_sw2_acb hd (by omega) (by omega) (by omega) ⟨by omega, by omega, by omega⟩
          (by omega)
  -- the exceptional `b = 4⌊a/2⌋ - 3`
  have hx : b % 4 = 1 ∧ 1 < b ∧ 4 * (a / 2 - 1) = b - 1 := by
    by_contra hn; exact hA ⟨by omega, h4, hn⟩
  by_cases hs : a / 2 + b / 2 + 4 ≤ c
  · exact spg_sw1_abc hd (by omega) (by omega) (by omega) hs
  have hab' : (a = 5 ∧ b = 5) ∨ (a = 6 ∧ b = 9) ∨ (a = 7 ∧ b = 9) ∨ (a = 8 ∧ b = 13) ∨
      (a = 9 ∧ b = 13) := by omega
  rcases hab' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have : c = 5 ∨ c = 6 ∨ c = 7 := by omega
    rcases this with rfl | rfl | rfl
    · exact (hF (by unfold F1; decide)).elim
    · exact spg_spA_acb hd (by omega) (by omega) (by omega) ⟨by omega, by omega, by omega⟩
        ⟨by omega, by omega, by omega⟩ (by omega)
    · exact spg_spA_acb hd (by omega) (by omega) (by omega) ⟨by omega, by omega, by omega⟩
        ⟨by omega, by omega, by omega⟩ (by omega)
  · have : c = 9 ∨ c = 10 := by omega
    rcases this with rfl | rfl
    · exact (hF (by unfold F1; decide)).elim
    · exact spg_spA_acb hd (by omega) (by omega) (by omega) ⟨by omega, by omega, by omega⟩
        ⟨by omega, by omega, by omega⟩ (by omega)
  · exact spg_spA_bac hd (by omega) (by omega) (by omega) ⟨by omega, by omega, by omega⟩
      ⟨by omega, by omega, by omega⟩ (by omega)
  · exact spg_sw2_abc hd (by omega) (by omega) (by omega) ⟨by omega, by omega, by omega⟩ (by omega)
  · exact spg_sw2_abc hd (by omega) (by omega) (by omega) ⟨by omega, by omega, by omega⟩ (by omega)

/-- the v-side with `τ = 2` at the junction `u`-neighbour, for `d ∈ {4,5}` or `d ≥ 9` -/
theorem vsp2_ok (d : ℕ) (h : d = 4 ∨ d = 5 ∨ 9 ≤ d) : VSP d (d - 1) 2 := by
  apply vsp2 d (d - 1) (by omega)
  by_cases h13 : d = 13
  · subst h13; right; right; right; exact ⟨by omega, by omega, by omega, by omega⟩
  · rcases h with rfl | rfl | h
    · left; rfl
    · right; left; rfl
    · right; right; left; exact ⟨by omega, by omega, by omega, by omega⟩

/-- the v-side with `τ = 1`, for every `d ≠ 3` -/
theorem vsp1_ok (d : ℕ) (hd : 1 ≤ d) (h3 : d ≠ 3) : VSP d (d - 1) 1 := by
  apply vsp1 d (d - 1) (by omega)
  by_cases h1 : d = 1
  · left; omega
  by_cases h2 : d = 2
  · right; right; left; omega
  by_cases h6 : d = 6
  · right; right; right; omega
  · right; left; exact ⟨by omega, by omega, by omega⟩

/-! ## Explicit graceful cores (`u` at `0`) with leaf chains, and a table -/

/-- a graceful core with `u` at label `0`, plus a leaf chain on a free arm at `u` -/
theorem core_leaf {a b c d : ℕ} (hd : 1 ≤ d) (X L : ℕ) (hX : X = 2 ∨ X = 3 ∨ X = 4) (G : Pc)
    (hG : G.Grace) (hR : G.R = Tadj d) (h0 : (0 : ℕ) ∈ G.S) (hu : G.f 0 = 0)
    (hfresh : ∀ w, w % 8 = X → 1 ≤ w / 8 → w / 8 ≤ L + 1 → w ∉ G.S)
    (hT : ∀ s, (s ∈ G.S ∨ (s % 8 = X ∧ 1 ≤ s / 8 ∧ s / 8 ≤ L)) ↔ s ∈ Tset a b c d 2 2) :
    CanonGraceful a b c d 2 2 := by
  have hr : armRoot X = 0 := armRoot_u hX
  obtain ⟨G', hG', hR', hS', _⟩ := leafRoot hd X L (by omega) (by omega) G hG hR
    (by rw [hr]; exact h0) (by rw [hr]; left; exact hu) hfresh
  exact canon_of_piece G' hG' hR' (fun s => by rw [hS']; exact hT s)

theorem hcore23_d1 (c : ℕ) : CanonGraceful 4 4 c 1 2 2 := by
  obtain ⟨G, hG, hR, hS, _, hf⟩ := numTreeG 1 [0, 10, 18, 26, 34, 11, 19, 27, 35, 1, 14, 22, 15, 23]
    [0, 0, 1, 2, 3, 0, 5, 6, 7, 0, 9, 10, 9, 12]
    [0, 13, 3, 10, 6, 12, 4, 9, 7, 11, 2, 1, 5, 8] (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
  have hm := mem_list_iff (names := [0, 10, 18, 26, 34, 11, 19, 27, 35, 1, 14, 22, 15, 23])
    (φ := fun z => z = 0 ∨ (z % 8 = 2 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 4) ∨ (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 4) ∨ z = 1 ∨ z = 14 ∨ z = 22 ∨ z = 15 ∨ z = 23) 40
    (by decide +kernel) (by decide +kernel) (by intro z hz; omega)
  have hS' : ∀ z, z ∈ G.S ↔ z = 0 ∨ (z % 8 = 2 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 4) ∨ (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 4) ∨ z = 1 ∨ z = 14 ∨ z = 22 ∨ z = 15 ∨ z = 23 := by
    intro z; rw [hS, hm z]
  refine core_leaf (d := 1) (by omega) 4 c (by omega) G hG hR (by rw [hS']; omega)
    (by have := hf 0 (by decide); simpa using this)
    (by intro w h1 h2 h3 hw; rw [hS'] at hw; omega) (fun s => ?_)
  rw [hS', tset22_iff (by omega)]; unfold ShU
  constructor
  · rintro ((h | h | h | h | h | h | h | h) | h) <;> omega
  · rintro ((h | h | h | h) | h | h | h | h | h | h) <;> omega

theorem hcore34_d1 (a : ℕ) : CanonGraceful a 4 4 1 2 2 := by
  obtain ⟨G, hG, hR, hS, _, hf⟩ := numTreeG 1 [0, 11, 19, 27, 35, 12, 20, 28, 36, 1, 14, 22, 15, 23]
    [0, 0, 1, 2, 3, 0, 5, 6, 7, 0, 9, 10, 9, 12]
    [0, 13, 3, 10, 6, 12, 4, 9, 7, 11, 2, 1, 5, 8] (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
  have hm := mem_list_iff (names := [0, 11, 19, 27, 35, 12, 20, 28, 36, 1, 14, 22, 15, 23])
    (φ := fun z => z = 0 ∨ (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 4) ∨ (z % 8 = 4 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 4) ∨ z = 1 ∨ z = 14 ∨ z = 22 ∨ z = 15 ∨ z = 23) 40
    (by decide +kernel) (by decide +kernel) (by intro z hz; omega)
  have hS' : ∀ z, z ∈ G.S ↔ z = 0 ∨ (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 4) ∨ (z % 8 = 4 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 4) ∨ z = 1 ∨ z = 14 ∨ z = 22 ∨ z = 15 ∨ z = 23 := by
    intro z; rw [hS, hm z]
  refine core_leaf (d := 1) (by omega) 2 a (by omega) G hG hR (by rw [hS']; omega)
    (by have := hf 0 (by decide); simpa using this)
    (by intro w h1 h2 h3 hw; rw [hS'] at hw; omega) (fun s => ?_)
  rw [hS', tset22_iff (by omega)]; unfold ShU
  constructor
  · rintro ((h | h | h | h | h | h | h | h) | h) <;> omega
  · rintro ((h | h | h | h) | h | h | h | h | h | h) <;> omega

theorem hcore23_d2 (c : ℕ) : CanonGraceful 4 4 c 2 2 2 := by
  obtain ⟨G, hG, hR, hS, _, hf⟩ := numTreeG 2 [0, 10, 18, 26, 34, 11, 19, 27, 35, 13, 1, 14, 22, 15, 23]
    [0, 0, 1, 2, 3, 0, 5, 6, 7, 0, 9, 10, 11, 10, 13]
    [0, 14, 3, 11, 7, 13, 4, 6, 1, 12, 2, 9, 10, 8, 5] (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
  have hm := mem_list_iff (names := [0, 10, 18, 26, 34, 11, 19, 27, 35, 13, 1, 14, 22, 15, 23])
    (φ := fun z => z = 0 ∨ (z % 8 = 2 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 4) ∨ (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 4) ∨ (z % 8 = 5 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 1) ∨ z = 1 ∨ z = 14 ∨ z = 22 ∨ z = 15 ∨ z = 23) 40
    (by decide +kernel) (by decide +kernel) (by intro z hz; omega)
  have hS' : ∀ z, z ∈ G.S ↔ z = 0 ∨ (z % 8 = 2 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 4) ∨ (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 4) ∨ (z % 8 = 5 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 1) ∨ z = 1 ∨ z = 14 ∨ z = 22 ∨ z = 15 ∨ z = 23 := by
    intro z; rw [hS, hm z]
  refine core_leaf (d := 2) (by omega) 4 c (by omega) G hG hR (by rw [hS']; omega)
    (by have := hf 0 (by decide); simpa using this)
    (by intro w h1 h2 h3 hw; rw [hS'] at hw; omega) (fun s => ?_)
  rw [hS', tset22_iff (by omega)]; unfold ShU
  constructor
  · rintro ((h | h | h | h | h | h | h | h | h) | h) <;> omega
  · rintro ((h | h | h | h) | h | h | h | h | h | h) <;> omega

theorem hcore34_d2 (a : ℕ) : CanonGraceful a 4 4 2 2 2 := by
  obtain ⟨G, hG, hR, hS, _, hf⟩ := numTreeG 2 [0, 11, 19, 27, 35, 12, 20, 28, 36, 13, 1, 14, 22, 15, 23]
    [0, 0, 1, 2, 3, 0, 5, 6, 7, 0, 9, 10, 11, 10, 13]
    [0, 14, 3, 11, 7, 13, 4, 6, 1, 12, 2, 9, 10, 8, 5] (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
  have hm := mem_list_iff (names := [0, 11, 19, 27, 35, 12, 20, 28, 36, 13, 1, 14, 22, 15, 23])
    (φ := fun z => z = 0 ∨ (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 4) ∨ (z % 8 = 4 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 4) ∨ (z % 8 = 5 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 1) ∨ z = 1 ∨ z = 14 ∨ z = 22 ∨ z = 15 ∨ z = 23) 40
    (by decide +kernel) (by decide +kernel) (by intro z hz; omega)
  have hS' : ∀ z, z ∈ G.S ↔ z = 0 ∨ (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 4) ∨ (z % 8 = 4 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 4) ∨ (z % 8 = 5 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 1) ∨ z = 1 ∨ z = 14 ∨ z = 22 ∨ z = 15 ∨ z = 23 := by
    intro z; rw [hS, hm z]
  refine core_leaf (d := 2) (by omega) 2 a (by omega) G hG hR (by rw [hS']; omega)
    (by have := hf 0 (by decide); simpa using this)
    (by intro w h1 h2 h3 hw; rw [hS'] at hw; omega) (fun s => ?_)
  rw [hS', tset22_iff (by omega)]; unfold ShU
  constructor
  · rintro ((h | h | h | h | h | h | h | h | h) | h) <;> omega
  · rintro ((h | h | h | h) | h | h | h | h | h | h) <;> omega

theorem hcore23_d6 (c : ℕ) : CanonGraceful 4 4 c 6 2 2 := by
  obtain ⟨G, hG, hR, hS, _, hf⟩ := numTreeG 6 [0, 10, 18, 26, 34, 11, 19, 27, 35, 13, 21, 29, 37, 45, 1, 14, 22, 15, 23]
    [0, 0, 1, 2, 3, 0, 5, 6, 7, 0, 9, 10, 11, 12, 13, 14, 15, 14, 17]
    [0, 18, 3, 15, 6, 17, 4, 14, 7, 16, 2, 13, 10, 5, 11, 9, 1, 12, 8] (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
  have hm := mem_list_iff (names := [0, 10, 18, 26, 34, 11, 19, 27, 35, 13, 21, 29, 37, 45, 1, 14, 22, 15, 23])
    (φ := fun z => z = 0 ∨ (z % 8 = 2 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 4) ∨ (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 4) ∨ (z % 8 = 5 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 5) ∨ z = 1 ∨ z = 14 ∨ z = 22 ∨ z = 15 ∨ z = 23) 48
    (by decide +kernel) (by decide +kernel) (by intro z hz; omega)
  have hS' : ∀ z, z ∈ G.S ↔ z = 0 ∨ (z % 8 = 2 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 4) ∨ (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 4) ∨ (z % 8 = 5 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 5) ∨ z = 1 ∨ z = 14 ∨ z = 22 ∨ z = 15 ∨ z = 23 := by
    intro z; rw [hS, hm z]
  refine core_leaf (d := 6) (by omega) 4 c (by omega) G hG hR (by rw [hS']; omega)
    (by have := hf 0 (by decide); simpa using this)
    (by intro w h1 h2 h3 hw; rw [hS'] at hw; omega) (fun s => ?_)
  rw [hS', tset22_iff (by omega)]; unfold ShU
  constructor
  · rintro ((h | h | h | h | h | h | h | h | h) | h) <;> omega
  · rintro ((h | h | h | h) | h | h | h | h | h | h) <;> omega

theorem hcore34_d6 (a : ℕ) : CanonGraceful a 4 4 6 2 2 := by
  obtain ⟨G, hG, hR, hS, _, hf⟩ := numTreeG 6 [0, 11, 19, 27, 35, 12, 20, 28, 36, 13, 21, 29, 37, 45, 1, 14, 22, 15, 23]
    [0, 0, 1, 2, 3, 0, 5, 6, 7, 0, 9, 10, 11, 12, 13, 14, 15, 14, 17]
    [0, 18, 3, 15, 6, 17, 4, 14, 7, 16, 2, 13, 10, 5, 11, 9, 1, 12, 8] (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
  have hm := mem_list_iff (names := [0, 11, 19, 27, 35, 12, 20, 28, 36, 13, 21, 29, 37, 45, 1, 14, 22, 15, 23])
    (φ := fun z => z = 0 ∨ (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 4) ∨ (z % 8 = 4 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 4) ∨ (z % 8 = 5 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 5) ∨ z = 1 ∨ z = 14 ∨ z = 22 ∨ z = 15 ∨ z = 23) 48
    (by decide +kernel) (by decide +kernel) (by intro z hz; omega)
  have hS' : ∀ z, z ∈ G.S ↔ z = 0 ∨ (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 4) ∨ (z % 8 = 4 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 4) ∨ (z % 8 = 5 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 5) ∨ z = 1 ∨ z = 14 ∨ z = 22 ∨ z = 15 ∨ z = 23 := by
    intro z; rw [hS, hm z]
  refine core_leaf (d := 6) (by omega) 2 a (by omega) G hG hR (by rw [hS']; omega)
    (by have := hf 0 (by decide); simpa using this)
    (by intro w h1 h2 h3 hw; rw [hS'] at hw; omega) (fun s => ?_)
  rw [hS', tset22_iff (by omega)]; unfold ShU
  constructor
  · rintro ((h | h | h | h | h | h | h | h | h) | h) <;> omega
  · rintro ((h | h | h | h) | h | h | h | h | h | h) <;> omega

theorem hcore23_d7 (c : ℕ) : CanonGraceful 4 4 c 7 2 2 := by
  obtain ⟨G, hG, hR, hS, _, hf⟩ := numTreeG 7 [0, 10, 18, 26, 34, 11, 19, 27, 35, 13, 21, 29, 37, 45, 53, 1, 14, 22, 15, 23]
    [0, 0, 1, 2, 3, 0, 5, 6, 7, 0, 9, 10, 11, 12, 13, 14, 15, 16, 15, 18]
    [0, 19, 3, 16, 6, 18, 4, 15, 7, 17, 2, 14, 8, 11, 9, 5, 12, 13, 10, 1] (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
  have hm := mem_list_iff (names := [0, 10, 18, 26, 34, 11, 19, 27, 35, 13, 21, 29, 37, 45, 53, 1, 14, 22, 15, 23])
    (φ := fun z => z = 0 ∨ (z % 8 = 2 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 4) ∨ (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 4) ∨ (z % 8 = 5 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 6) ∨ z = 1 ∨ z = 14 ∨ z = 22 ∨ z = 15 ∨ z = 23) 56
    (by decide +kernel) (by decide +kernel) (by intro z hz; omega)
  have hS' : ∀ z, z ∈ G.S ↔ z = 0 ∨ (z % 8 = 2 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 4) ∨ (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 4) ∨ (z % 8 = 5 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 6) ∨ z = 1 ∨ z = 14 ∨ z = 22 ∨ z = 15 ∨ z = 23 := by
    intro z; rw [hS, hm z]
  refine core_leaf (d := 7) (by omega) 4 c (by omega) G hG hR (by rw [hS']; omega)
    (by have := hf 0 (by decide); simpa using this)
    (by intro w h1 h2 h3 hw; rw [hS'] at hw; omega) (fun s => ?_)
  rw [hS', tset22_iff (by omega)]; unfold ShU
  constructor
  · rintro ((h | h | h | h | h | h | h | h | h) | h) <;> omega
  · rintro ((h | h | h | h) | h | h | h | h | h | h) <;> omega

theorem hcore34_d7 (a : ℕ) : CanonGraceful a 4 4 7 2 2 := by
  obtain ⟨G, hG, hR, hS, _, hf⟩ := numTreeG 7 [0, 11, 19, 27, 35, 12, 20, 28, 36, 13, 21, 29, 37, 45, 53, 1, 14, 22, 15, 23]
    [0, 0, 1, 2, 3, 0, 5, 6, 7, 0, 9, 10, 11, 12, 13, 14, 15, 16, 15, 18]
    [0, 19, 3, 16, 6, 18, 4, 15, 7, 17, 2, 14, 8, 11, 9, 5, 12, 13, 10, 1] (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
  have hm := mem_list_iff (names := [0, 11, 19, 27, 35, 12, 20, 28, 36, 13, 21, 29, 37, 45, 53, 1, 14, 22, 15, 23])
    (φ := fun z => z = 0 ∨ (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 4) ∨ (z % 8 = 4 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 4) ∨ (z % 8 = 5 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 6) ∨ z = 1 ∨ z = 14 ∨ z = 22 ∨ z = 15 ∨ z = 23) 56
    (by decide +kernel) (by decide +kernel) (by intro z hz; omega)
  have hS' : ∀ z, z ∈ G.S ↔ z = 0 ∨ (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 4) ∨ (z % 8 = 4 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 4) ∨ (z % 8 = 5 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 6) ∨ z = 1 ∨ z = 14 ∨ z = 22 ∨ z = 15 ∨ z = 23 := by
    intro z; rw [hS, hm z]
  refine core_leaf (d := 7) (by omega) 2 a (by omega) G hG hR (by rw [hS']; omega)
    (by have := hf 0 (by decide); simpa using this)
    (by intro w h1 h2 h3 hw; rw [hS'] at hw; omega) (fun s => ?_)
  rw [hS', tset22_iff (by omega)]; unfold ShU
  constructor
  · rintro ((h | h | h | h | h | h | h | h | h) | h) <;> omega
  · rintro ((h | h | h | h) | h | h | h | h | h | h) <;> omega

theorem hcore23_d8 (c : ℕ) : CanonGraceful 4 4 c 8 2 2 := by
  obtain ⟨G, hG, hR, hS, _, hf⟩ := numTreeG 8 [0, 10, 18, 26, 34, 11, 19, 27, 35, 13, 21, 29, 37, 45, 53, 61, 1, 14, 22, 15, 23]
    [0, 0, 1, 2, 3, 0, 5, 6, 7, 0, 9, 10, 11, 12, 13, 14, 15, 16, 17, 16, 19]
    [0, 20, 3, 17, 6, 19, 4, 16, 7, 18, 2, 15, 5, 13, 11, 10, 14, 8, 1, 9, 12] (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
  have hm := mem_list_iff (names := [0, 10, 18, 26, 34, 11, 19, 27, 35, 13, 21, 29, 37, 45, 53, 61, 1, 14, 22, 15, 23])
    (φ := fun z => z = 0 ∨ (z % 8 = 2 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 4) ∨ (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 4) ∨ (z % 8 = 5 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 7) ∨ z = 1 ∨ z = 14 ∨ z = 22 ∨ z = 15 ∨ z = 23) 64
    (by decide +kernel) (by decide +kernel) (by intro z hz; omega)
  have hS' : ∀ z, z ∈ G.S ↔ z = 0 ∨ (z % 8 = 2 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 4) ∨ (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 4) ∨ (z % 8 = 5 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 7) ∨ z = 1 ∨ z = 14 ∨ z = 22 ∨ z = 15 ∨ z = 23 := by
    intro z; rw [hS, hm z]
  refine core_leaf (d := 8) (by omega) 4 c (by omega) G hG hR (by rw [hS']; omega)
    (by have := hf 0 (by decide); simpa using this)
    (by intro w h1 h2 h3 hw; rw [hS'] at hw; omega) (fun s => ?_)
  rw [hS', tset22_iff (by omega)]; unfold ShU
  constructor
  · rintro ((h | h | h | h | h | h | h | h | h) | h) <;> omega
  · rintro ((h | h | h | h) | h | h | h | h | h | h) <;> omega

theorem hcore34_d8 (a : ℕ) : CanonGraceful a 4 4 8 2 2 := by
  obtain ⟨G, hG, hR, hS, _, hf⟩ := numTreeG 8 [0, 11, 19, 27, 35, 12, 20, 28, 36, 13, 21, 29, 37, 45, 53, 61, 1, 14, 22, 15, 23]
    [0, 0, 1, 2, 3, 0, 5, 6, 7, 0, 9, 10, 11, 12, 13, 14, 15, 16, 17, 16, 19]
    [0, 20, 3, 17, 6, 19, 4, 16, 7, 18, 2, 15, 5, 13, 11, 10, 14, 8, 1, 9, 12] (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
  have hm := mem_list_iff (names := [0, 11, 19, 27, 35, 12, 20, 28, 36, 13, 21, 29, 37, 45, 53, 61, 1, 14, 22, 15, 23])
    (φ := fun z => z = 0 ∨ (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 4) ∨ (z % 8 = 4 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 4) ∨ (z % 8 = 5 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 7) ∨ z = 1 ∨ z = 14 ∨ z = 22 ∨ z = 15 ∨ z = 23) 64
    (by decide +kernel) (by decide +kernel) (by intro z hz; omega)
  have hS' : ∀ z, z ∈ G.S ↔ z = 0 ∨ (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 4) ∨ (z % 8 = 4 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 4) ∨ (z % 8 = 5 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 7) ∨ z = 1 ∨ z = 14 ∨ z = 22 ∨ z = 15 ∨ z = 23 := by
    intro z; rw [hS, hm z]
  refine core_leaf (d := 8) (by omega) 2 a (by omega) G hG hR (by rw [hS']; omega)
    (by have := hf 0 (by decide); simpa using this)
    (by intro w h1 h2 h3 hw; rw [hS'] at hw; omega) (fun s => ?_)
  rw [hS', tset22_iff (by omega)]; unfold ShU
  constructor
  · rintro ((h | h | h | h | h | h | h | h | h) | h) <;> omega
  · rintro ((h | h | h | h) | h | h | h | h | h | h) <;> omega

theorem kcore_d2 (c : ℕ) : CanonGraceful 6 9 c 2 2 2 := by
  obtain ⟨G, hG, hR, hS, _, hf⟩ := numTreeG 2 [0, 10, 18, 26, 34, 42, 50, 11, 19, 27, 35, 43, 51, 59, 67, 75, 13, 1, 14, 22, 15, 23]
    [0, 0, 1, 2, 3, 4, 5, 0, 7, 8, 9, 10, 11, 12, 13, 14, 0, 16, 17, 18, 17, 20]
    [0, 21, 3, 18, 7, 15, 9, 20, 4, 17, 8, 1, 5, 10, 12, 13, 19, 2, 16, 6, 14, 11] (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
  have hm := mem_list_iff (names := [0, 10, 18, 26, 34, 42, 50, 11, 19, 27, 35, 43, 51, 59, 67, 75, 13, 1, 14, 22, 15, 23])
    (φ := fun z => z = 0 ∨ (z % 8 = 2 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 6) ∨ (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 9) ∨ (z % 8 = 5 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 1) ∨ z = 1 ∨ z = 14 ∨ z = 22 ∨ z = 15 ∨ z = 23) 80
    (by decide +kernel) (by decide +kernel) (by intro z hz; omega)
  have hS' : ∀ z, z ∈ G.S ↔ z = 0 ∨ (z % 8 = 2 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 6) ∨ (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 9) ∨ (z % 8 = 5 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 1) ∨ z = 1 ∨ z = 14 ∨ z = 22 ∨ z = 15 ∨ z = 23 := by
    intro z; rw [hS, hm z]
  refine core_leaf (d := 2) (by omega) 4 c (by omega) G hG hR (by rw [hS']; omega)
    (by have := hf 0 (by decide); simpa using this)
    (by intro w h1 h2 h3 hw; rw [hS'] at hw; omega) (fun s => ?_)
  rw [hS', tset22_iff (by omega)]; unfold ShU
  constructor
  · rintro ((h | h | h | h | h | h | h | h | h) | h) <;> omega
  · rintro ((h | h | h | h) | h | h | h | h | h | h) <;> omega

theorem kcore_d6 (c : ℕ) : CanonGraceful 6 9 c 6 2 2 := by
  obtain ⟨G, hG, hR, hS, _, hf⟩ := numTreeG 6 [0, 10, 18, 26, 34, 42, 50, 11, 19, 27, 35, 43, 51, 59, 67, 75, 13, 21, 29, 37, 45, 1, 14, 22, 15, 23]
    [0, 0, 1, 2, 3, 4, 5, 0, 7, 8, 9, 10, 11, 12, 13, 14, 0, 16, 17, 18, 19, 20, 21, 22, 21, 24]
    [0, 25, 3, 22, 6, 19, 9, 24, 4, 21, 7, 18, 10, 1, 8, 13, 23, 2, 20, 5, 17, 11, 15, 16, 14, 12] (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
  have hm := mem_list_iff (names := [0, 10, 18, 26, 34, 42, 50, 11, 19, 27, 35, 43, 51, 59, 67, 75, 13, 21, 29, 37, 45, 1, 14, 22, 15, 23])
    (φ := fun z => z = 0 ∨ (z % 8 = 2 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 6) ∨ (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 9) ∨ (z % 8 = 5 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 5) ∨ z = 1 ∨ z = 14 ∨ z = 22 ∨ z = 15 ∨ z = 23) 80
    (by decide +kernel) (by decide +kernel) (by intro z hz; omega)
  have hS' : ∀ z, z ∈ G.S ↔ z = 0 ∨ (z % 8 = 2 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 6) ∨ (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 9) ∨ (z % 8 = 5 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 5) ∨ z = 1 ∨ z = 14 ∨ z = 22 ∨ z = 15 ∨ z = 23 := by
    intro z; rw [hS, hm z]
  refine core_leaf (d := 6) (by omega) 4 c (by omega) G hG hR (by rw [hS']; omega)
    (by have := hf 0 (by decide); simpa using this)
    (by intro w h1 h2 h3 hw; rw [hS'] at hw; omega) (fun s => ?_)
  rw [hS', tset22_iff (by omega)]; unfold ShU
  constructor
  · rintro ((h | h | h | h | h | h | h | h | h) | h) <;> omega
  · rintro ((h | h | h | h) | h | h | h | h | h | h) <;> omega

theorem kcore_d7 (c : ℕ) : CanonGraceful 6 9 c 7 2 2 := by
  obtain ⟨G, hG, hR, hS, _, hf⟩ := numTreeG 7 [0, 10, 18, 26, 34, 42, 50, 11, 19, 27, 35, 43, 51, 59, 67, 75, 13, 21, 29, 37, 45, 53, 1, 14, 22, 15, 23]
    [0, 0, 1, 2, 3, 4, 5, 0, 7, 8, 9, 10, 11, 12, 13, 14, 0, 16, 17, 18, 19, 20, 21, 22, 23, 22, 25]
    [0, 26, 3, 23, 6, 20, 9, 25, 4, 22, 7, 19, 10, 15, 8, 16, 24, 2, 21, 5, 18, 12, 14, 11, 1, 13, 17] (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
  have hm := mem_list_iff (names := [0, 10, 18, 26, 34, 42, 50, 11, 19, 27, 35, 43, 51, 59, 67, 75, 13, 21, 29, 37, 45, 53, 1, 14, 22, 15, 23])
    (φ := fun z => z = 0 ∨ (z % 8 = 2 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 6) ∨ (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 9) ∨ (z % 8 = 5 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 6) ∨ z = 1 ∨ z = 14 ∨ z = 22 ∨ z = 15 ∨ z = 23) 80
    (by decide +kernel) (by decide +kernel) (by intro z hz; omega)
  have hS' : ∀ z, z ∈ G.S ↔ z = 0 ∨ (z % 8 = 2 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 6) ∨ (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 9) ∨ (z % 8 = 5 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 6) ∨ z = 1 ∨ z = 14 ∨ z = 22 ∨ z = 15 ∨ z = 23 := by
    intro z; rw [hS, hm z]
  refine core_leaf (d := 7) (by omega) 4 c (by omega) G hG hR (by rw [hS']; omega)
    (by have := hf 0 (by decide); simpa using this)
    (by intro w h1 h2 h3 hw; rw [hS'] at hw; omega) (fun s => ?_)
  rw [hS', tset22_iff (by omega)]; unfold ShU
  constructor
  · rintro ((h | h | h | h | h | h | h | h | h) | h) <;> omega
  · rintro ((h | h | h | h) | h | h | h | h | h | h) <;> omega

theorem t555_d1 : CanonGraceful 5 5 5 1 2 2 := by
  obtain ⟨G, hG, hR, hS, _, _⟩ := numTreeG 1 [0, 10, 18, 26, 34, 42, 11, 19, 27, 35, 43, 12, 20, 28, 36, 44, 1, 14, 22, 15, 23]
    [0, 0, 1, 2, 3, 4, 0, 6, 7, 8, 9, 0, 11, 12, 13, 14, 0, 16, 17, 16, 19]
    [0, 20, 4, 16, 10, 15, 19, 5, 14, 1, 2, 18, 3, 11, 8, 12, 17, 6, 13, 7, 9] (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
  have hm := mem_list_iff (names := [0, 10, 18, 26, 34, 42, 11, 19, 27, 35, 43, 12, 20, 28, 36, 44, 1, 14, 22, 15, 23])
    (φ := fun z => z = 0 ∨ (z % 8 = 2 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 5) ∨ (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 5) ∨ (z % 8 = 4 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 5) ∨ z = 1 ∨ z = 14 ∨ z = 22 ∨ z = 15 ∨ z = 23) 48
    (by decide +kernel) (by decide +kernel) (by intro z hz; omega)
  have hS' : ∀ z, z ∈ G.S ↔ z = 0 ∨ (z % 8 = 2 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 5) ∨ (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 5) ∨ (z % 8 = 4 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 5) ∨ z = 1 ∨ z = 14 ∨ z = 22 ∨ z = 15 ∨ z = 23 := by
    intro z; rw [hS, hm z]
  refine canon_of_piece G hG hR (fun s => ?_)
  rw [hS', tset22_iff (by omega)]; unfold ShU
  constructor
  · rintro (h | h | h | h | h | h | h | h | h) <;> omega
  · rintro ((h | h | h | h) | h | h | h | h | h | h) <;> omega


/-! ## Family C (`e = f = 2`): coverage, and the main theorem -/

theorem famC_V2 {a b c d : ℕ} (hd : 1 ≤ d) (h : d = 4 ∨ d = 5 ∨ 9 ≤ d) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hc : 1 ≤ c) (hS : SPG d 2 a b c) : CanonGraceful a b c d 2 2 :=
  famC_V hd ha hb hc (by omega) (vsp2_ok d h) hS

theorem vsp1_cut (d : ℕ) (hd : 2 ≤ d) (h3 : d ≠ 3) (h4 : d ≠ 4) : VSP d (d - 2) 1 := by
  apply vsp1 d (d - 2) (by omega)
  by_cases h2 : d = 2
  · left; omega
  by_cases h7 : d = 7
  · right; right; right; omega
  · right; left; exact ⟨by omega, by omega, by omega⟩

theorem famC_cut_abc {a b c d : ℕ} (hd : 2 ≤ d) (h3 : d ≠ 3) (h4 : d ≠ 4) (ha : 2 ≤ a)
    (hb : 1 ≤ b) (hc : 1 ≤ c) (hok1 : AeplOK (a - 1) 1) (hok2 : AeplOK b (a / 2))
    (hok3 : a / 2 + b / 2 ≤ c - 1) : CanonGraceful a b c d 2 2 :=
  famC_cut (X := 2) (Y := 3) (Z := 4) hd arms_234 (by simp) (by simp) (by simp) ha hb hc
    hok1 hok2 hok3 (vsp1_cut d hd h3 h4)

/-- the six spiders `(4, b, c)` with `6 ≤ b ≤ c ≤ 8` -/
theorem famC_4bc {b c d : ℕ} (hd : 1 ≤ d) (hd3 : d ≠ 3) (hb : 6 ≤ b) (hbc : b ≤ c) (hc : c ≤ 8) :
    CanonGraceful 4 b c d 2 2 := by
  by_cases h1 : d = 1
  · subst h1
    exact famC_U (X := 3) (Y := 2) (Z := 4) (x := b) (y := 4) (z := c) (by omega) arms_324
      (by simp) (by simp) (by simp) (by omega) (by omega) (by omega) (by omega) (Or.inl rfl)
      ⟨by omega, by omega, by omega⟩
  by_cases h4 : d = 4
  · subst h4
    exact famC_V2 (by omega) (Or.inl rfl) (by omega) (by omega) (by omega)
      (spg_spA_abc (by omega) (by omega) (by omega) (by omega) ⟨by omega, by omega, by omega⟩
        ⟨by omega, by omega, by omega⟩ (by omega))
  · exact famC_cut_abc (by omega) hd3 h4 (by omega) (by omega) (by omega)
      ⟨by omega, by omega, by omega⟩ ⟨by omega, by omega, by omega⟩ (by omega)

/-- the spiders `(4, 4, c)` -/
theorem famC_44c {c d : ℕ} (hd : 1 ≤ d) (hd3 : d ≠ 3) (hc : 4 ≤ c) :
    CanonGraceful 4 4 c d 2 2 := by
  rcases (show d = 1 ∨ d = 2 ∨ d = 6 ∨ d = 7 ∨ d = 8 ∨ (d = 4 ∨ d = 5 ∨ 9 ≤ d) by omega) with
    rfl | rfl | rfl | rfl | rfl | h
  · exact hcore23_d1 c
  · exact hcore23_d2 c
  · exact hcore23_d6 c
  · exact hcore23_d7 c
  · exact hcore23_d8 c
  · exact famC_V2 hd h (by omega) (by omega) (by omega)
      (spg_spA_abc hd (by omega) (by omega) (by omega) ⟨by omega, by omega, by omega⟩
        ⟨by omega, by omega, by omega⟩ (by omega))

/-- the 13 spiders without SP1, for `d ≠ 3` -/
theorem famC_F1 (a b c d : ℕ) (hd : 1 ≤ d) (hd3 : d ≠ 3) (hF : F1 a b c) :
    CanonGraceful a b c d 2 2 := by
  unfold F1 at hF
  rcases hF with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · -- (1,1,1): template U
    have hD : d = 1 ∨ AeplOK (d - 1) (1 / 2) := by
      by_cases h1 : d = 1
      · exact Or.inl h1
      · exact Or.inr ⟨by omega, by omega, by omega⟩
    exact famC_U (X := 2) (Y := 3) (Z := 4) (x := 1) (y := 1) (z := 1) hd arms_234
      (by simp) (by simp) (by simp) (by omega) (by omega) (by omega) (by omega) hD
      ⟨by omega, by omega, by omega⟩
  · -- (1,4,4)
    rcases (show d = 1 ∨ d = 2 ∨ d = 6 ∨ d = 7 ∨ d = 8 ∨ (d = 4 ∨ d = 5 ∨ 9 ≤ d) by omega) with
      rfl | rfl | rfl | rfl | rfl | h
    · exact hcore34_d1 1
    · exact hcore34_d2 1
    · exact hcore34_d6 1
    · exact hcore34_d7 1
    · exact hcore34_d8 1
    · exact famC_V2 hd h (by omega) (by omega) (by omega)
        (spg_spA_bac hd (by omega) (by omega) (by omega) ⟨by omega, by omega, by omega⟩
          ⟨by omega, by omega, by omega⟩ (by omega))
  · exact famC_44c hd hd3 (by omega)
  · exact famC_44c hd hd3 (by omega)
  · exact famC_44c hd hd3 (by omega)
  · exact famC_4bc hd hd3 (by omega) (by omega) (by omega)
  · exact famC_4bc hd hd3 (by omega) (by omega) (by omega)
  · exact famC_4bc hd hd3 (by omega) (by omega) (by omega)
  · exact famC_4bc hd hd3 (by omega) (by omega) (by omega)
  · exact famC_4bc hd hd3 (by omega) (by omega) (by omega)
  · exact famC_4bc hd hd3 (by omega) (by omega) (by omega)
  · -- (5,5,5)
    rcases (show d = 1 ∨ d = 4 ∨ (2 ≤ d ∧ d ≠ 4) by omega) with rfl | rfl | h
    · exact t555_d1
    · exact famC_V2 (by omega) (Or.inl rfl) (by omega) (by omega) (by omega)
        (spg_spA_abc (by omega) (by omega) (by omega) (by omega) ⟨by omega, by omega, by omega⟩
          ⟨by omega, by omega, by omega⟩ (by omega))
    · exact famC_cut_abc h.1 hd3 h.2 (by omega) (by omega) (by omega)
        ⟨by omega, by omega, by omega⟩ ⟨by omega, by omega, by omega⟩ (by omega)
  · -- (6,9,9)
    rcases (show d = 1 ∨ d = 8 ∨ d = 2 ∨ d = 6 ∨ d = 7 ∨ (d = 4 ∨ d = 5 ∨ 9 ≤ d) by omega) with
      rfl | rfl | rfl | rfl | rfl | h
    · exact famC_U (X := 2) (Y := 3) (Z := 4) (x := 6) (y := 9) (z := 9) (by omega) arms_234
        (by simp) (by simp) (by simp) (by omega) (by omega) (by omega) (by omega) (Or.inl rfl)
        ⟨by omega, by omega, by omega⟩
    · exact famC_U (X := 2) (Y := 3) (Z := 4) (x := 6) (y := 9) (z := 9) (by omega) arms_234
        (by simp) (by simp) (by simp) (by omega) (by omega) (by omega) (by omega)
        (Or.inr ⟨by omega, by omega, by omega⟩) ⟨by omega, by omega, by omega⟩
    · exact kcore_d2 9
    · exact kcore_d6 9
    · exact kcore_d7 9
    · exact famC_V2 hd h (by omega) (by omega) (by omega)
        (spg_spA_abc hd (by omega) (by omega) (by omega) ⟨by omega, by omega, by omega⟩
          ⟨by omega, by omega, by omega⟩ (by omega))

/-- **family C**: every sorted `(a,b,c)` and every `d ≥ 1`, with `e = f = 2` -/
theorem famC (a b c d : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) (hd : 1 ≤ d) :
    CanonGraceful a b c d 2 2 := by
  by_cases h3 : d = 3
  · subst h3; exact famC_d3 a b c ha hab hbc
  by_cases hF : F1 a b c
  · exact famC_F1 a b c d hd h3 hF
  · exact famC_V hd ha (by omega) (by omega) (by omega) (vsp1_ok d hd h3)
      (sp1_all d a b c hd ha hab hbc hF)

/-- **Every finite tree with exactly two branch vertices, of degrees 4 and 3, is graceful.** -/
theorem target : Math15.Graceful.Target10 :=
  target_of_canon (fun a b c d e f ha hab hbc hd he hef => by
    by_cases h22 : e = 2 ∧ f = 2
    · obtain ⟨rfl, rfl⟩ := h22
      exact famC a b c d ha hab hbc hd
    · exact famA a b c d e f ha hab hbc hd he hef h22)

