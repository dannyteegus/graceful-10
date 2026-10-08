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
