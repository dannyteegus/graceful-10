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
