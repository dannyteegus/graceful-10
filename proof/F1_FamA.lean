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
