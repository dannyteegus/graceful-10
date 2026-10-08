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
