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
