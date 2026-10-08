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
