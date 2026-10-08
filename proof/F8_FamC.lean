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
