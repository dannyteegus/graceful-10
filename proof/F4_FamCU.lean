/-! ## Family C: template U (α u-side, graceful `P(2,2)` at `v`) -/

/-- graceful `P(2,2)` at `v` with `v` at label `1` or `3` -/
theorem p22G_13 (d : ℕ) (hd : 1 ≤ d) :
    ∃ G : Pc, G.Grace ∧ G.R = Tadj d ∧
      (∀ z, z ∈ G.S ↔ z = 1 ∨ z = 14 ∨ z = 22 ∨ z = 15 ∨ z = 23) ∧ G.E.card = 4 ∧
      (G.f 1 = 1 ∨ G.f 1 = 3) := by
  obtain ⟨A, hS, hE, he, _⟩ := startThrough d 1 6 7 2 2 hd arms_v (by omega) (by omega) labP22
    (by simpa using labP22_alpha) (by decide)
  have h1 : tnm 1 6 7 2 2 = 1 := by simp [tnm]
  have e1 := he 2 (by omega)
  rw [h1, show peps (2 + 2 + 1) labP22 2 = 1 by decide] at e1
  have hf := A.f_eps (z := 1) (by rw [hS]; left; rfl)
  rw [e1, hE] at hf
  exact ⟨A.P, A.hA.1, A.hR, fun z => by rw [hS]; unfold Sh2; omega, hE, by omega⟩

/-- graceful `P(2,2)` at `v` with `v` at label `0` or `4` -/
theorem p22G_04 (d : ℕ) (hd : 1 ≤ d) :
    ∃ G : Pc, G.Grace ∧ G.R = Tadj d ∧
      (∀ z, z ∈ G.S ↔ z = 1 ∨ z = 14 ∨ z = 22 ∨ z = 15 ∨ z = 23) ∧ G.E.card = 4 ∧
      (G.f 1 = 0 ∨ G.f 1 = 4) := by
  have hL : PathAlpha (2 + 1) (fun i => [0, 2, 1].getD i 0) (2 / 2) := by
    apply pathAlpha_of <;> decide
  obtain ⟨A, hS0, hE, he, ht⟩ := startArm d 7 2 hd (by omega) _ hL (by decide) (by omega)
  have hr : armRoot 7 = 1 := rfl
  have e1 : A.eps 1 = 0 := by
    have := he 0 (by omega); simp only [anode, if_true, hr] at this; rw [this]; decide
  have t1 : A.tau 1 = 1 := by
    have := ht 0 (by omega); simp only [anode, if_true, hr] at this; rw [this]; decide
  have hS : ∀ z, z ∈ A.P.S ↔ z = 1 ∨ (z % 8 = 7 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 2) :=
    fun z => by rw [hS0 z, hr]
  have m1 : (1 : ℕ) ∈ A.P.S := by rw [hS]; left; rfl
  obtain ⟨G, hG, hR, hSG, hEG, hf⟩ := A.attachGRoot 6 2 (by omega) (by omega)
    (by rw [show armRoot 6 = 1 from rfl]; exact m1)
    (by intro i hi h; rw [hS] at h; omega) (by intro h; rw [hS] at h; omega)
    (fun e => by omega) (fun e => by omega)
    (by rw [show armRoot 6 = 1 from rfl, t1])
  refine ⟨G, hG, hR, fun z => by rw [hSG, hS]; omega, by rw [hEG, hE], ?_⟩
  rcases hf 1 m1 with e | e <;> rw [e1] at e
  · left; exact e
  · right; rw [e, hEG, hE]

/-- graceful `P(2,2)` at `v` with `v` at `ρ` or `4 - ρ`, for `ρ ∈ {0,1,3,4}` -/
theorem p22G (d ρ : ℕ) (hd : 1 ≤ d) (hρ : ρ = 0 ∨ ρ = 1 ∨ ρ = 3 ∨ ρ = 4) :
    ∃ G : Pc, G.Grace ∧ G.R = Tadj d ∧
      (∀ z, z ∈ G.S ↔ z = 1 ∨ z = 14 ∨ z = 22 ∨ z = 15 ∨ z = 23) ∧ G.E.card = 4 ∧
      (G.f 1 = ρ ∨ G.f 1 = G.E.card - ρ) := by
  rcases hρ with rfl | rfl | rfl | rfl
  · obtain ⟨G, h1, h2, h3, h4, h5⟩ := p22G_04 d hd
    exact ⟨G, h1, h2, h3, h4, by rw [h4]; omega⟩
  · obtain ⟨G, h1, h2, h3, h4, h5⟩ := p22G_13 d hd
    exact ⟨G, h1, h2, h3, h4, by rw [h4]; omega⟩
  · obtain ⟨G, h1, h2, h3, h4, h5⟩ := p22G_13 d hd
    exact ⟨G, h1, h2, h3, h4, by rw [h4]; omega⟩
  · obtain ⟨G, h1, h2, h3, h4, h5⟩ := p22G_04 d hd
    exact ⟨G, h1, h2, h3, h4, by rw [h4]; omega⟩

/-- U-side, first half: zigzag along `X` from `u`, then the `d`-path from `u` -/
theorem famC_U1 {d X x : ℕ} (hd : 1 ≤ d) (hX : X = 2 ∨ X = 3 ∨ X = 4) (hx : 1 ≤ x)
    (hD : d = 1 ∨ AeplOK (d - 1) (x / 2)) :
    ∃ q, ∃ A : APc d q, (∀ w, w ∈ A.P.S ↔ w = 0 ∨ (w % 8 = X ∧ 1 ≤ w / 8 ∧ w / 8 ≤ x) ∨
        (w % 8 = 5 ∧ 1 ≤ w / 8 ∧ w / 8 ≤ d - 1)) ∧
      A.eps 0 = 0 ∧ A.tau (dnode d (d - 1)) = x / 2 := by
  have hrX := armRoot_u hX
  obtain ⟨A0, hS0', _, e0', t0', _, _⟩ := startZZ d X x hd (by omega) (by omega) hx
  have hS0 : ∀ w, w ∈ A0.P.S ↔ w = 0 ∨ (w % 8 = X ∧ 1 ≤ w / 8 ∧ w / 8 ≤ x) :=
    fun w => by rw [hS0' w, hrX]
  have e0 : A0.eps 0 = 0 := (congrArg (fun w => A0.eps w) hrX).symm.trans e0'
  have t0 : A0.tau 0 = x / 2 := (congrArg (fun w => A0.tau w) hrX).symm.trans t0'
  have m0 : (0 : ℕ) ∈ A0.P.S := by rw [hS0]; left; rfl
  by_cases hd1 : d = 1
  · subst hd1
    refine ⟨_, A0, fun w => by rw [hS0]; omega, e0, ?_⟩
    have : dnode 1 (1 - 1) = 0 := by unfold dnode; simp
    rw [this, t0]
  · have hok' : AeplOK (d - 1) (x / 2) := by rcases hD with h' | h' <;> [omega; exact h']
    obtain ⟨B, hSB, _, heB, _, htB⟩ := A0.attachRoot 5 (d - 1) (by omega) (by omega)
      (by rw [show armRoot 5 = 0 from rfl]; exact m0)
      (by intro i hi hm; rw [hS0] at hm; omega) (by intro hm; rw [hS0] at hm; omega)
      (fun _ => by omega) (fun _ _ hm => by rw [hS0] at hm; omega)
      (by rw [show armRoot 5 = 0 from rfl, t0]; exact hok')
    refine ⟨_, B, fun w => by rw [hSB, hS0]; omega, by rw [heB _ m0, e0], ?_⟩
    have : dnode d (d - 1) = 5 + 8 * (d - 1) := by
      unfold dnode; rw [if_neg (by omega), if_neg (by omega)]
    rw [this, htB, show armRoot 5 = 0 from rfl, t0]

/-- U-side, second half: reflect, `Y` and `Z` at `u`, reflect back -/
theorem famC_U2 {d X Y Z x y z q1 : ℕ} (h : Arms3 X Y Z) (hy : 1 ≤ y) (hz : 1 ≤ z)
    (hok : AeplOK z (y / 2)) (A1 : APc d q1)
    (hS1 : ∀ w, w ∈ A1.P.S ↔ w = 0 ∨ (w % 8 = X ∧ 1 ≤ w / 8 ∧ w / 8 ≤ x) ∨
        (w % 8 = 5 ∧ 1 ≤ w / 8 ∧ w / 8 ≤ d - 1))
    (e1 : A1.eps 0 = 0) (j : ℕ) (mj : j ∈ A1.P.S) (tj : A1.tau j = x / 2) :
    ∃ A : APc d q1, (∀ w, w ∈ A.P.S ↔ w = 0 ∨ (w % 8 = X ∧ 1 ≤ w / 8 ∧ w / 8 ≤ x) ∨
        (w % 8 = 5 ∧ 1 ≤ w / 8 ∧ w / 8 ≤ d - 1) ∨ (w % 8 = Y ∧ 1 ≤ w / 8 ∧ w / 8 ≤ y) ∨
        (w % 8 = Z ∧ 1 ≤ w / 8 ∧ w / 8 ≤ z)) ∧ A.tau j = x / 2 := by
  obtain ⟨hX, hY, hZ, hXY, hXZ, hYZ⟩ := h
  have hrY := armRoot_u hY
  have hrZ := armRoot_u hZ
  have m1 : (0 : ℕ) ∈ A1.P.S := by rw [hS1]; left; rfl
  have t2 : A1.refl.tau 0 = 0 := by rw [A1.refl_tau m1, e1]
  have ej : A1.refl.eps j = x / 2 := by rw [A1.refl_eps mj, tj]
  have m2 : (0 : ℕ) ∈ A1.refl.P.S := by rw [A1.refl_S]; exact m1
  have mj2 : j ∈ A1.refl.P.S := by rw [A1.refl_S]; exact mj
  obtain ⟨A3, hS3, _, he3, ht3, _⟩ := A1.refl.attachRoot Y y (by omega) hy
    (by rw [hrY]; exact m2)
    (by intro i hi hm; rw [A1.refl_S, hS1] at hm; omega)
    (by intro hm; rw [A1.refl_S, hS1] at hm; omega)
    (fun _ => by omega) (fun _ => by omega)
    (by rw [hrY, t2]; exact ⟨by omega, by omega, by omega⟩)
  have hS3' : ∀ w, w ∈ A3.P.S ↔ w = 0 ∨ (w % 8 = X ∧ 1 ≤ w / 8 ∧ w / 8 ≤ x) ∨
      (w % 8 = 5 ∧ 1 ≤ w / 8 ∧ w / 8 ≤ d - 1) ∨ (w % 8 = Y ∧ 1 ≤ w / 8 ∧ w / 8 ≤ y) := by
    intro w; rw [hS3, A1.refl_S, hS1]; omega
  have t3 : A3.tau 0 = y / 2 := by
    rw [ht3 _ m2, t2, hrY, show (par d 0 + par d 0) % 2 = 0 by rw [par_zero]]; omega
  have m3 : (0 : ℕ) ∈ A3.P.S := by rw [hS3']; left; rfl
  have mj3 : j ∈ A3.P.S := by rw [hS3]; left; exact mj2
  obtain ⟨A4, hS4, _, he4, _, _⟩ := A3.attachRoot Z z (by omega) hz
    (by rw [hrZ]; exact m3)
    (by intro i hi hm; rw [hS3'] at hm; omega) (by intro hm; rw [hS3'] at hm; omega)
    (fun _ => by omega) (fun _ => by omega)
    (by rw [hrZ, t3]; exact hok)
  have mj4 : j ∈ A4.P.S := by rw [hS4]; left; exact mj3
  refine ⟨A4.refl, fun w => by rw [A4.refl_S, hS4, hS3']; omega, ?_⟩
  rw [A4.refl_tau mj4, he4 _ mj3, he3 _ mj2, ej]

/-- template U -/
theorem famC_U {a b c d X Y Z x y z : ℕ} (hd : 1 ≤ d) (h : Arms3 X Y Z)
    (ha : a = if X = 2 then x else if Y = 2 then y else z)
    (hb : b = if X = 3 then x else if Y = 3 then y else z)
    (hc : c = if X = 4 then x else if Y = 4 then y else z)
    (hx : 1 ≤ x) (hy : 1 ≤ y) (hz : 1 ≤ z)
    (hρ : x / 2 = 0 ∨ x / 2 = 1 ∨ x / 2 = 3 ∨ x / 2 = 4)
    (hD : d = 1 ∨ AeplOK (d - 1) (x / 2)) (hok : AeplOK z (y / 2)) :
    CanonGraceful a b c d 2 2 := by
  have hperm := fun w => shU_perm (w := w) h ha hb hc
  obtain ⟨q1, A1, hS1, e1, tj⟩ := famC_U1 hd h.hX hx hD
  have mj : dnode d (d - 1) ∈ A1.P.S := by
    have := h.hX
    rw [hS1]; unfold dnode; split_ifs <;> omega
  obtain ⟨A, hS, ht⟩ := famC_U2 h hy hz hok A1 hS1 e1 _ mj tj
  obtain ⟨G, hG, hGR, hGS, hGE, hGf⟩ := p22G d (x / 2) hd hρ
  have hv : dnode d (d - 1 + 1) = 1 := by unfold dnode; rw [if_neg (by omega), if_pos (by omega)]
  have hX := h.hX
  have hY := h.hY
  have hZ := h.hZ
  refine join_uv (j := d - 1) hd (by omega) A G hG hGR
    (by
      intro w hw; rw [hS] at hw; unfold uPart
      rcases hw with h' | h' | h' | h' | h' <;> omega)
    (by intro w hw; rw [hGS] at hw; unfold vPart; omega)
    (by rw [hS]; have := (hS1 _).mp mj; omega)
    (by rw [hv, hGS]; left; rfl)
    (by rw [hv, ht]; exact hGf)
    (by rw [ht, hGE]; omega)
    (by
      intro s; rw [hS, hGS, tset22_iff hd, ← hperm s]
      constructor
      · rintro ((h' | h' | h' | h' | h') | h') <;> omega
      · rintro ((h' | h' | h' | h') | h' | h' | h' | h' | h' | h') <;> omega)
