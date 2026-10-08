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
