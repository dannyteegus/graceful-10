/-! ## Graceful spiders at `u` with the centre at `σ` (σ = 1, 2) -/

/-- shape of a spider at `u` with arms `X, Y, Z` -/
def ShXYZ (X x Y y Z z w : ℕ) : Prop :=
  w = 0 ∨ (w % 8 = X ∧ 1 ≤ w / 8 ∧ w / 8 ≤ x) ∨ (w % 8 = Y ∧ 1 ≤ w / 8 ∧ w / 8 ≤ y) ∨
    (w % 8 = Z ∧ 1 ≤ w / 8 ∧ w / 8 ≤ z)

/-- a graceful spider at `u` with arms `X, Y, Z` and the centre at `σ` or `m - σ` -/
def SPX (d σ X x Y y Z z : ℕ) : Prop :=
  ∃ G : Pc, G.Grace ∧ G.R = Tadj d ∧ (∀ w, w ∈ G.S ↔ ShXYZ X x Y y Z z w) ∧
    G.E.card = x + y + z ∧ (G.f 0 = σ ∨ G.f 0 = G.E.card - σ)

/-- program spA: α-EPL from `u` along `X` (u at `σ`), `Y` at `u`, final segment `Z` -/
theorem spA_prog {d σ X Y Z x y z : ℕ} (hd : 1 ≤ d) (h : Arms3 X Y Z) (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hz : 1 ≤ z) (hok1 : AeplOK (x + 1) σ) (hok2 : AeplOK y (x / 2 - σ))
    (hok3 : x / 2 - σ + y / 2 ≤ z - 1) : SPX d σ X x Y y Z z := by
  obtain ⟨hX, hY, hZ, hXY, hXZ, hYZ⟩ := h
  have hrX := armRoot_u hX
  have hrY := armRoot_u hY
  have hrZ := armRoot_u hZ
  obtain ⟨Lab, hLab, hLab0⟩ := aepl (x + 1) σ hok1
  have hs : σ ≤ x / 2 := by have := hok1.2.1; omega
  rw [show (x + 1 - 1) / 2 = x / 2 by omega] at hLab
  obtain ⟨A0, hS0', hE0, he0, ht0⟩ := startArm d X x hd (by omega) Lab hLab (by omega) (by omega)
  have hS0 : ∀ w, w ∈ A0.P.S ↔ w = 0 ∨ (w % 8 = X ∧ 1 ≤ w / 8 ∧ w / 8 ≤ x) :=
    fun w => by rw [hS0' w, hrX]
  have e0 : A0.eps 0 = σ := by
    have := he0 0 (by omega); simp only [anode, if_true, hrX] at this
    rw [this]; unfold peps; rw [hLab0, if_pos (by omega)]
  have t0 : A0.tau 0 = x / 2 - σ := by
    have := ht0 0 (by omega); simp only [anode, if_true, hrX] at this
    rw [this]; unfold ptau; rw [hLab0, if_pos (by omega)]; omega
  have m0 : (0 : ℕ) ∈ A0.P.S := by rw [hS0]; left; rfl
  obtain ⟨A1, hS1, hE1, he1, ht1, _⟩ := A0.attachRoot Y y (by omega) hy (by rw [hrY]; exact m0)
    (by intro i hi hm; rw [hS0] at hm; omega) (by intro hm; rw [hS0] at hm; omega)
    (fun e => by omega) (fun e => by omega) (by rw [hrY, t0]; exact hok2)
  have t1 : A1.tau 0 = x / 2 - σ + y / 2 := by
    rw [ht1 _ m0, t0, hrY]; rw [show (par d 0 + par d 0) % 2 = 0 by rw [par_zero]]; omega
  have hS1' : ∀ w, w ∈ A1.P.S ↔ w = 0 ∨ (w % 8 = X ∧ 1 ≤ w / 8 ∧ w / 8 ≤ x) ∨
      (w % 8 = Y ∧ 1 ≤ w / 8 ∧ w / 8 ≤ y) := by
    intro w; rw [hS1, hS0]; omega
  have m1 : (0 : ℕ) ∈ A1.P.S := by rw [hS1']; left; rfl
  obtain ⟨G, hG, hR, hSG, hEG, hf⟩ := A1.attachGRoot Z z (by omega) hz (by rw [hrZ]; exact m1)
    (by intro i hi hm; rw [hS1'] at hm; omega) (by intro hm; rw [hS1'] at hm; omega)
    (fun e => by omega) (fun e => by omega) (by rw [hrZ, t1]; exact hok3)
  refine ⟨G, hG, hR, fun w => by rw [hSG, hS1']; unfold ShXYZ; omega,
    by rw [hEG, hE1, hE0], ?_⟩
  rcases hf 0 m1 with e | e <;> rw [he1 _ m0, e0] at e
  · left; exact e
  · right; exact e

/-- program sw1: IVL0 on `X, Y`, reflect, two vertices of `Z`, reflect, final segment of `Z` -/
theorem sw1_prog {d X Y Z x y z : ℕ} (hd : 1 ≤ d) (h : Arms3 X Y Z) (H : IVL0P d 0 X Y x y)
    (hz : x / 2 + y / 2 + 4 ≤ z) : SPX d 1 X x Y y Z z := by
  obtain ⟨hX, hY, hZ, hXY, hXZ, hYZ⟩ := h
  have hrZ := armRoot_u hZ
  have pZ2 : par d (Z + 8 * 2) = 0 := by
    rw [par_arm_root d Z 2 (by omega) (by omega), hrZ, par_zero]
  obtain ⟨A0, hS0, hE0, e0, t0⟩ := H
  have m0 : (0 : ℕ) ∈ A0.P.S := by rw [hS0]; left; rfl
  -- reflect: τ(u) = 0, ε(u) = x/2 + y/2
  have hS1 : ∀ w, w ∈ A0.refl.P.S ↔ Sh2 0 X x Y y w := by intro w; rw [A0.refl_S]; exact hS0 w
  have t1 : A0.refl.tau 0 = 0 := by rw [A0.refl_tau m0, e0]
  have e1 : A0.refl.eps 0 = x / 2 + y / 2 := by rw [A0.refl_eps m0, t0]
  have m1 : (0 : ℕ) ∈ A0.refl.P.S := by rw [hS1]; left; rfl
  obtain ⟨A2, hS2, hE2, he2, ht2, hend⟩ := A0.refl.attachRoot Z 2 (by omega) (by omega)
    (by rw [hrZ]; exact m1)
    (by intro i hi hm; rw [hS1] at hm; unfold Sh2 at hm; omega)
    (by intro hm; rw [hS1] at hm; unfold Sh2 at hm; omega)
    (fun e => by omega) (fun e => by omega) (by rw [hrZ, t1]; exact ⟨by omega, by omega, by omega⟩)
  rw [hrZ, t1] at hend
  have hS2' : ∀ w, w ∈ A2.P.S ↔ w = 0 ∨ (w % 8 = X ∧ 1 ≤ w / 8 ∧ w / 8 ≤ x) ∨
      (w % 8 = Y ∧ 1 ≤ w / 8 ∧ w / 8 ≤ y) ∨ (w % 8 = Z ∧ 1 ≤ w / 8 ∧ w / 8 ≤ 2) := by
    intro w; rw [hS2, hS1]; unfold Sh2; omega
  have m2 : (0 : ℕ) ∈ A2.P.S := by rw [hS2']; left; rfl
  have mZ2 : Z + 8 * 2 ∈ A2.P.S := by rw [hS2']; omega
  have t2 : A2.tau 0 = 1 := by
    rw [ht2 _ m1, t1, hrZ, show (par d 0 + par d 0) % 2 = 0 by rw [par_zero]]
  have e2 : A2.eps 0 = x / 2 + y / 2 := by rw [he2 _ m1, e1]
  have eZ2 : A2.eps (Z + 8 * 2) = x / 2 + y / 2 + 1 := by
    have := A2.eps_tau_same mZ2 m2 (by rw [pZ2, par_zero])
    rw [hend, e2, t2] at this; omega
  -- reflect again: ε(u) = 1
  have hS3 : ∀ w, w ∈ A2.refl.P.S ↔ w = 0 ∨ (w % 8 = X ∧ 1 ≤ w / 8 ∧ w / 8 ≤ x) ∨
      (w % 8 = Y ∧ 1 ≤ w / 8 ∧ w / 8 ≤ y) ∨ (w % 8 = Z ∧ 1 ≤ w / 8 ∧ w / 8 ≤ 2) := by
    intro w; rw [A2.refl_S]; exact hS2' w
  have e3 : A2.refl.eps 0 = 1 := by rw [A2.refl_eps m2, t2]
  have tZ2 : A2.refl.tau (Z + 8 * 2) = x / 2 + y / 2 + 1 := by rw [A2.refl_tau mZ2, eZ2]
  have mZ2' : Z + 8 * 2 ∈ A2.refl.P.S := by rw [hS3]; omega
  obtain ⟨G, hG, hR, hSG, hEG, hf⟩ := A2.refl.attachGArm Z 2 (z - 2) (by omega) (by omega)
    (by omega) mZ2'
    (by intro i hi hm; rw [hS3] at hm; omega) (by intro hm; rw [hS3] at hm; omega)
    (fun e => by omega) (fun e => by omega) (by rw [tZ2]; omega)
  have m3 : (0 : ℕ) ∈ A2.refl.P.S := by rw [hS3]; left; rfl
  refine ⟨G, hG, hR, fun w => by rw [hSG, hS3]; unfold ShXYZ; omega,
    by rw [hEG, A2.refl_card, hE2, A0.refl_card, hE0]; omega, ?_⟩
  rcases hf 0 m3 with e | e <;> rw [e3] at e
  · left; exact e
  · right; exact e

/-- program sw2: zigzag `X`, reflect, two vertices of `Y`, reflect, `Y` tail, final segment `Z` -/
theorem sw2_prog {d X Y Z x y z : ℕ} (hd : 1 ≤ d) (h : Arms3 X Y Z) (hx : 1 ≤ x) (hy : 3 ≤ y)
    (hz : 1 ≤ z) (hok : AeplOK (y - 2) (x / 2 + 1)) (hK : x / 2 + y / 2 ≤ z) :
    SPX d 1 X x Y y Z z := by
  obtain ⟨hX, hY, hZ, hXY, hXZ, hYZ⟩ := h
  have hrX := armRoot_u hX
  have hrY := armRoot_u hY
  have hrZ := armRoot_u hZ
  have pY2 : par d (Y + 8 * 2) = 0 := by
    rw [par_arm_root d Y 2 (by omega) (by omega), hrY, par_zero]
  obtain ⟨A0, hS0', hE0, e0', t0', _, _⟩ := startZZ d X x hd (by omega) (by omega) hx
  have hS0 : ∀ w, w ∈ A0.P.S ↔ w = 0 ∨ (w % 8 = X ∧ 1 ≤ w / 8 ∧ w / 8 ≤ x) :=
    fun w => by rw [hS0' w, hrX]
  have e0 : A0.eps 0 = 0 := (congrArg (fun w => A0.eps w) hrX).symm.trans e0'
  have t0 : A0.tau 0 = x / 2 := (congrArg (fun w => A0.tau w) hrX).symm.trans t0'
  have m0 : (0 : ℕ) ∈ A0.P.S := by rw [hS0]; left; rfl
  have hS1 : ∀ w, w ∈ A0.refl.P.S ↔ w = 0 ∨ (w % 8 = X ∧ 1 ≤ w / 8 ∧ w / 8 ≤ x) := by
    intro w; rw [A0.refl_S]; exact hS0 w
  have t1 : A0.refl.tau 0 = 0 := by rw [A0.refl_tau m0, e0]
  have e1 : A0.refl.eps 0 = x / 2 := by rw [A0.refl_eps m0, t0]
  have m1 : (0 : ℕ) ∈ A0.refl.P.S := by rw [hS1]; left; rfl
  obtain ⟨A2, hS2, hE2, he2, ht2, hend⟩ := A0.refl.attachRoot Y 2 (by omega) (by omega)
    (by rw [hrY]; exact m1)
    (by intro i hi hm; rw [hS1] at hm; omega) (by intro hm; rw [hS1] at hm; omega)
    (fun e => by omega) (fun e => by omega) (by rw [hrY, t1]; exact ⟨by omega, by omega, by omega⟩)
  rw [hrY, t1] at hend
  have hS2' : ∀ w, w ∈ A2.P.S ↔ w = 0 ∨ (w % 8 = X ∧ 1 ≤ w / 8 ∧ w / 8 ≤ x) ∨
      (w % 8 = Y ∧ 1 ≤ w / 8 ∧ w / 8 ≤ 2) := by
    intro w; rw [hS2, hS1]; omega
  have m2 : (0 : ℕ) ∈ A2.P.S := by rw [hS2']; left; rfl
  have mY2 : Y + 8 * 2 ∈ A2.P.S := by rw [hS2']; omega
  have t2 : A2.tau 0 = 1 := by
    rw [ht2 _ m1, t1, hrY, show (par d 0 + par d 0) % 2 = 0 by rw [par_zero]]
  have e2 : A2.eps 0 = x / 2 := by rw [he2 _ m1, e1]
  have eY2 : A2.eps (Y + 8 * 2) = x / 2 + 1 := by
    have := A2.eps_tau_same mY2 m2 (by rw [pY2, par_zero])
    rw [hend, e2, t2] at this; omega
  have hS3 : ∀ w, w ∈ A2.refl.P.S ↔ w = 0 ∨ (w % 8 = X ∧ 1 ≤ w / 8 ∧ w / 8 ≤ x) ∨
      (w % 8 = Y ∧ 1 ≤ w / 8 ∧ w / 8 ≤ 2) := by
    intro w; rw [A2.refl_S]; exact hS2' w
  have e3 : A2.refl.eps 0 = 1 := by rw [A2.refl_eps m2, t2]
  have t3 : A2.refl.tau 0 = x / 2 := by rw [A2.refl_tau m2, e2]
  have tY2 : A2.refl.tau (Y + 8 * 2) = x / 2 + 1 := by rw [A2.refl_tau mY2, eY2]
  have m3 : (0 : ℕ) ∈ A2.refl.P.S := by rw [hS3]; left; rfl
  have mY2' : Y + 8 * 2 ∈ A2.refl.P.S := by rw [hS3]; omega
  obtain ⟨A4, hS4, hE4, he4, ht4, _⟩ := A2.refl.attachArm Y 2 (y - 2) (by omega) (by omega)
    (by omega) mY2'
    (by intro i hi hm; rw [hS3] at hm; omega) (by intro hm; rw [hS3] at hm; omega)
    (fun e => by omega) (fun e => by omega) (by rw [tY2]; exact hok)
  have hS4' : ∀ w, w ∈ A4.P.S ↔ w = 0 ∨ (w % 8 = X ∧ 1 ≤ w / 8 ∧ w / 8 ≤ x) ∨
      (w % 8 = Y ∧ 1 ≤ w / 8 ∧ w / 8 ≤ y) := by
    intro w; rw [hS4, hS3]; omega
  have t4 : A4.tau 0 = x / 2 + (y - 2) / 2 := by
    rw [ht4 _ m3, t3, pY2, par_zero]; omega
  have e4 : A4.eps 0 = 1 := by rw [he4 _ m3, e3]
  have m4 : (0 : ℕ) ∈ A4.P.S := by rw [hS4']; left; rfl
  obtain ⟨G, hG, hR, hSG, hEG, hf⟩ := A4.attachGRoot Z z (by omega) hz (by rw [hrZ]; exact m4)
    (by intro i hi hm; rw [hS4'] at hm; omega) (by intro hm; rw [hS4'] at hm; omega)
    (fun e => by omega) (fun e => by omega) (by rw [hrZ, t4]; omega)
  refine ⟨G, hG, hR, fun w => by rw [hSG, hS4']; unfold ShXYZ; omega,
    by rw [hEG, hE4, A2.refl_card, hE2, A0.refl_card, hE0]; omega, ?_⟩
  rcases hf 0 m4 with e | e <;> rw [e4] at e
  · left; exact e
  · right; exact e

/-- turning a permuted spider into `SPG` -/
theorem spg_of_spx {d σ X Y Z x y z a b c : ℕ} (h : Arms3 X Y Z) (H : SPX d σ X x Y y Z z)
    (ha : a = if X = 2 then x else if Y = 2 then y else z)
    (hb : b = if X = 3 then x else if Y = 3 then y else z)
    (hc : c = if X = 4 then x else if Y = 4 then y else z) : SPG d σ a b c := by
  obtain ⟨G, hG, hR, hS, hE, hf⟩ := H
  refine ⟨G, hG, hR, fun w => by rw [hS]; unfold ShXYZ; exact shU_perm h ha hb hc, ?_, hf⟩
  rw [hE]
  obtain ⟨hX, hY, hZ, hXY, hXZ, hYZ⟩ := h
  rcases hX with rfl | rfl | rfl <;> rcases hY with rfl | rfl | rfl <;>
    rcases hZ with rfl | rfl | rfl <;> simp_all <;> omega
