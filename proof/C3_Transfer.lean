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
