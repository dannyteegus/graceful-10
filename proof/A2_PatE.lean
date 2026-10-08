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
