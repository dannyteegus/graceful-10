/-! ## IVL0: α-labelings of two arms at a root with the root at `ε = 0` -/

theorem par_arm_root (d X k : ℕ) (hX : 2 ≤ X ∧ X ≤ 7) (hk : 1 ≤ k) :
    par d (X + 8 * k) = (par d (armRoot X) + k) % 2 := by
  rw [par_arm d X k hX hk]
  unfold armRoot
  split_ifs with h1 h2 h2
  · omega
  · rw [par_one]; omega
  · rw [par_zero]; omega
  · omega

theorem armRoot_lt (X : ℕ) : armRoot X < 2 := by unfold armRoot; split_ifs <;> omega

/-- shape of a root with two arms -/
def Sh2 (r X x Y y z : ℕ) : Prop :=
  z = r ∨ (z % 8 = X ∧ 1 ≤ z / 8 ∧ z / 8 ≤ x) ∨ (z % 8 = Y ∧ 1 ≤ z / 8 ∧ z / 8 ≤ y)

/-- standing hypotheses: two distinct non-path arms at the root `r` -/
structure Arms2 (r X Y : ℕ) : Prop where
  hX : 2 ≤ X ∧ X ≤ 7
  hY : 2 ≤ Y ∧ Y ≤ 7
  hXY : X ≠ Y
  hX5 : X ≠ 5
  hY5 : Y ≠ 5
  hrX : armRoot X = r
  hrY : armRoot Y = r

theorem Arms2.symm {r X Y : ℕ} (h : Arms2 r X Y) : Arms2 r Y X :=
  ⟨h.hY, h.hX, h.hXY.symm, h.hY5, h.hX5, h.hrY, h.hrX⟩

/-- IVL0: an α-piece on a root and two arms with the root at `ε = 0` -/
def IVL0P (d r X Y x y : ℕ) : Prop :=
  ∃ A : APc d (par d r), (∀ z, z ∈ A.P.S ↔ Sh2 r X x Y y z) ∧
    A.P.E.card = x + y ∧ A.eps r = 0 ∧ A.tau r = x / 2 + y / 2

theorem ivl0_symm {d r X Y x y : ℕ} (H : IVL0P d r X Y x y) : IVL0P d r Y X y x := by
  obtain ⟨A, hS, hE, he, ht⟩ := H
  refine ⟨A, fun z => by rw [hS]; unfold Sh2; tauto, by rw [hE]; ring, he, by rw [ht]; ring⟩

/-- start: zigzag along arm `X` from its root -/
theorem startZZ (d X x : ℕ) (hd : 1 ≤ d) (hX : 2 ≤ X ∧ X ≤ 7) (hX5 : X ≠ 5) (hx : 1 ≤ x) :
    ∃ A : APc d (par d (armRoot X)),
      (∀ z, z ∈ A.P.S ↔ z = armRoot X ∨ (z % 8 = X ∧ 1 ≤ z / 8 ∧ z / 8 ≤ x)) ∧ A.P.E.card = x ∧
      A.eps (armRoot X) = 0 ∧ A.tau (armRoot X) = x / 2 ∧
      (∀ i, 1 ≤ i → i ≤ x → A.eps (X + 8 * i) = i / 2) ∧
      (∀ i, 1 ≤ i → i ≤ x → A.tau (X + 8 * i) =
        if i % 2 = 0 then x / 2 - i / 2 else x - i / 2 - x / 2 - 1) := by
  obtain ⟨A0, hS0, hE0, he0, ht0⟩ := startArm d X x hd hX (zz (x + 1))
    (by have := zz_alpha (x + 1) (by omega); rwa [show (x + 1 - 1) / 2 = x / 2 by omega] at this)
    (by simp [zz]) (fun e => absurd e hX5)
  refine ⟨A0, hS0, hE0, ?_, ?_, ?_, ?_⟩
  · have := he0 0 (by omega); simp only [anode, if_true] at this; rw [this, zz_peps _ _ (by omega)]
  · have := ht0 0 (by omega); simp only [anode, if_true] at this; rw [this, zz_ptau _ _ (by omega)]
    simp
  · intro i hi1 hix
    have := he0 i hix
    simp only [anode, if_neg (show i ≠ 0 by omega)] at this
    rw [this, zz_peps _ _ (by omega)]
  · intro i hi1 hix
    have := ht0 i hix
    simp only [anode, if_neg (show i ≠ 0 by omega)] at this
    rw [this, zz_ptau _ _ (by omega)]
    simp only [show x + 1 - 1 = x by omega]

/-- program a: zigzag along `X`, then `Y` at the root -/
theorem ivl0_a {d r X Y x y : ℕ} (hd : 1 ≤ d) (h : Arms2 r X Y) (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hok : AeplOK y (x / 2)) : IVL0P d r X Y x y := by
  obtain ⟨hX, hY, hXY, hX5, hY5, hrX, hrY⟩ := h
  subst hrX
  have hr2 := armRoot_lt X
  obtain ⟨A0, hS0, hE0, e0, t0, _, _⟩ := startZZ d X x hd hX hX5 hx
  have hrS : armRoot X ∈ A0.P.S := by rw [hS0]; left; rfl
  obtain ⟨B, hS, hE, he, ht, _⟩ := A0.attachRoot Y y hY hy (by rw [hrY]; exact hrS)
    (by intro i hi hm; rw [hS0] at hm; omega)
    (by intro hm; rw [hS0] at hm; omega)
    (fun e => absurd e hY5) (fun e => absurd e hY5)
    (by rw [hrY, t0]; exact hok)
  refine ⟨B, ?_, by rw [hE, hE0], by rw [he _ hrS, e0], ?_⟩
  · intro z; rw [hS, hS0]; unfold Sh2; omega
  · rw [ht _ hrS, t0, hrY]
    have : (par d (armRoot X) + par d (armRoot X)) % 2 = 0 := by omega
    rw [this]; omega

/-- program b: `X1`, then `Y1` at the root, then the two tails -/
theorem ivl0_b {d r X Y x y : ℕ} (hd : 1 ≤ d) (h : Arms2 r X Y) (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hok1 : AeplOK (x - 1) 1) (hok2 : AeplOK (y - 1) ((x - 1) / 2)) : IVL0P d r X Y x y := by
  obtain ⟨hX, hY, hXY, hX5, hY5, hrX, hrY⟩ := h
  subst hrX
  have hr2 := armRoot_lt X
  have pX1 := par_arm_root d X 1 hX (by omega)
  have pY1 := par_arm_root d Y 1 hY (by omega)
  rw [hrY] at pY1
  have pr := par_le_one d (armRoot X)
  obtain ⟨A0, hS0, hE0, e0, t0, _, tX⟩ := startZZ d X 1 hd hX hX5 (by omega)
  have tX1 : A0.tau (X + 8 * 1) = 0 := by rw [tX 1 (by omega) (by omega)]; simp
  have hrS0 : armRoot X ∈ A0.P.S := by rw [hS0]; left; rfl
  have hX1S0 : X + 8 * 1 ∈ A0.P.S := by rw [hS0]; right; omega
  obtain ⟨A1, hS1, hE1, he1, ht1, hY1⟩ := A0.attachRoot Y 1 hY (by omega)
    (by rw [hrY]; exact hrS0)
    (by intro i hi hm; rw [hS0] at hm; omega)
    (by intro hm; rw [hS0] at hm; omega)
    (fun e => absurd e hY5) (fun e => absurd e hY5)
    (by rw [hrY, t0]; exact ⟨by omega, by omega, by omega⟩)
  rw [hrY] at ht1 hY1
  have hS1' : ∀ z, z ∈ A1.P.S ↔ z = armRoot X ∨ (z % 8 = X ∧ z / 8 = 1) ∨ (z % 8 = Y ∧ z / 8 = 1) := by
    intro z; rw [hS1, hS0]; omega
  have hrS1 : armRoot X ∈ A1.P.S := by rw [hS1']; left; rfl
  have hX1S1 : X + 8 * 1 ∈ A1.P.S := by rw [hS1']; right; left; omega
  have hY1S1 : Y + 8 * 1 ∈ A1.P.S := by rw [hS1']; right; right; omega
  have t1r : A1.tau (armRoot X) = 0 := by
    rw [ht1 _ hrS0, t0]; have : (par d (armRoot X) + par d (armRoot X)) % 2 = 0 := by omega
    rw [this]
  have t1X : A1.tau (X + 8 * 1) = 1 := by rw [ht1 _ hX1S0, tX1, pX1]; omega
  have t1Y : A1.tau (Y + 8 * 1) = 0 := by rw [hY1, t0]
  have e1r : A1.eps (armRoot X) = 0 := by rw [he1 _ hrS0, e0]
  obtain ⟨A2, hS2, hE2, he2, ht2, _⟩ := A1.attachArm X 1 (x - 1) hX (by omega) (by omega) hX1S1
    (by intro i hi hm; rw [hS1'] at hm; omega)
    (by intro hm; rw [hS1'] at hm; omega)
    (fun e => absurd e hX5) (fun e => absurd e hX5)
    (by rw [t1X]; exact hok1)
  have hS2' : ∀ z, z ∈ A2.P.S ↔ z = armRoot X ∨ (z % 8 = X ∧ 1 ≤ z / 8 ∧ z / 8 ≤ x) ∨
      (z % 8 = Y ∧ z / 8 = 1) := by
    intro z; rw [hS2, hS1']; omega
  have t2r : A2.tau (armRoot X) = x / 2 := by
    rw [ht2 _ hrS1, t1r, pX1]
    have : (par d (armRoot X) + (par d (armRoot X) + 1) % 2) % 2 = 1 := by omega
    rw [this]; omega
  have t2Y : A2.tau (Y + 8 * 1) = (x - 1) / 2 := by
    rw [ht2 _ hY1S1, t1Y, pX1, pY1]
    have : ((par d (armRoot X) + 1) % 2 + (par d (armRoot X) + 1) % 2) % 2 = 0 := by omega
    rw [this]; omega
  have e2r : A2.eps (armRoot X) = 0 := by rw [he2 _ hrS1, e1r]
  have hrS2 : armRoot X ∈ A2.P.S := by rw [hS2']; left; rfl
  have hY1S2 : Y + 8 * 1 ∈ A2.P.S := by rw [hS2']; right; right; omega
  obtain ⟨A3, hS3, hE3, he3, ht3, _⟩ := A2.attachArm Y 1 (y - 1) hY (by omega) (by omega) hY1S2
    (by intro i hi hm; rw [hS2'] at hm; omega)
    (by intro hm; rw [hS2'] at hm; omega)
    (fun e => absurd e hY5) (fun e => absurd e hY5)
    (by rw [t2Y]; exact hok2)
  refine ⟨A3, ?_, by rw [hE3, hE2, hE1, hE0]; omega, by rw [he3 _ hrS2, e2r], ?_⟩
  · intro z; rw [hS3, hS2']; unfold Sh2; omega
  · rw [ht3 _ hrS2, t2r, pY1]
    have : (par d (armRoot X) + (par d (armRoot X) + 1) % 2) % 2 = 1 := by omega
    rw [this]; omega

/-- program s0: `X1`, then `Y` at the root, then the `X` tail -/
theorem ivl0_s0 {d r X Y x y : ℕ} (hd : 1 ≤ d) (h : Arms2 r X Y) (hx : 2 ≤ x) (hy : 1 ≤ y)
    (hok : AeplOK (x - 1) ((y + 1) / 2)) : IVL0P d r X Y x y := by
  obtain ⟨hX, hY, hXY, hX5, hY5, hrX, hrY⟩ := h
  subst hrX
  have hr2 := armRoot_lt X
  have pX1 := par_arm_root d X 1 hX (by omega)
  have pr := par_le_one d (armRoot X)
  obtain ⟨A0, hS0, hE0, e0, t0, _, tX⟩ := startZZ d X 1 hd hX hX5 (by omega)
  have tX1 : A0.tau (X + 8 * 1) = 0 := by rw [tX 1 (by omega) (by omega)]; simp
  have hrS0 : armRoot X ∈ A0.P.S := by rw [hS0]; left; rfl
  have hX1S0 : X + 8 * 1 ∈ A0.P.S := by rw [hS0]; right; omega
  obtain ⟨A1, hS1, hE1, he1, ht1, _⟩ := A0.attachRoot Y y hY hy
    (by rw [hrY]; exact hrS0)
    (by intro i hi hm; rw [hS0] at hm; omega)
    (by intro hm; rw [hS0] at hm; omega)
    (fun e => absurd e hY5) (fun e => absurd e hY5)
    (by rw [hrY, t0]; exact ⟨by omega, by omega, by omega⟩)
  rw [hrY] at ht1
  have hS1' : ∀ z, z ∈ A1.P.S ↔ z = armRoot X ∨ (z % 8 = X ∧ z / 8 = 1) ∨
      (z % 8 = Y ∧ 1 ≤ z / 8 ∧ z / 8 ≤ y) := by
    intro z; rw [hS1, hS0]; omega
  have t1r : A1.tau (armRoot X) = y / 2 := by
    rw [ht1 _ hrS0, t0]; have : (par d (armRoot X) + par d (armRoot X)) % 2 = 0 := by omega
    rw [this]; omega
  have t1X : A1.tau (X + 8 * 1) = (y + 1) / 2 := by
    rw [ht1 _ hX1S0, tX1, pX1]
    have : ((par d (armRoot X) + 1) % 2 + par d (armRoot X)) % 2 = 1 := by omega
    rw [this]; omega
  have hrS1 : armRoot X ∈ A1.P.S := by rw [hS1']; left; rfl
  have hX1S1 : X + 8 * 1 ∈ A1.P.S := by rw [hS1']; right; left; omega
  obtain ⟨A2, hS2, hE2, he2, ht2, _⟩ := A1.attachArm X 1 (x - 1) hX (by omega) (by omega) hX1S1
    (by intro i hi hm; rw [hS1'] at hm; omega)
    (by intro hm; rw [hS1'] at hm; omega)
    (fun e => absurd e hX5) (fun e => absurd e hX5)
    (by rw [t1X]; exact hok)
  refine ⟨A2, ?_, by rw [hE2, hE1, hE0]; omega, by rw [he2 _ hrS1, he1 _ hrS0, e0], ?_⟩
  · intro z; rw [hS2, hS1']; unfold Sh2; omega
  · rw [ht2 _ hrS1, t1r, pX1]
    have : (par d (armRoot X) + (par d (armRoot X) + 1) % 2) % 2 = 1 := by omega
    rw [this]; omega

/-- program s1: `X1`, `X2`, then `Y` at the root, then the `X` tail -/
theorem ivl0_s1 {d r X Y x y : ℕ} (hd : 1 ≤ d) (h : Arms2 r X Y) (hx : 3 ≤ x) (hy : 1 ≤ y)
    (hok1 : AeplOK y 1) (hok2 : AeplOK (x - 2) (y / 2)) : IVL0P d r X Y x y := by
  obtain ⟨hX, hY, hXY, hX5, hY5, hrX, hrY⟩ := h
  subst hrX
  have hr2 := armRoot_lt X
  have pX1 := par_arm_root d X 1 hX (by omega)
  have pX2 := par_arm_root d X 2 hX (by omega)
  have pr := par_le_one d (armRoot X)
  obtain ⟨A0, hS0, hE0, e0, t0, _, tX⟩ := startZZ d X 1 hd hX hX5 (by omega)
  have tX1 : A0.tau (X + 8 * 1) = 0 := by rw [tX 1 (by omega) (by omega)]; simp
  have hrS0 : armRoot X ∈ A0.P.S := by rw [hS0]; left; rfl
  have hX1S0 : X + 8 * 1 ∈ A0.P.S := by rw [hS0]; right; omega
  obtain ⟨A1, hS1, hE1, he1, ht1, hX2⟩ := A0.attachArm X 1 1 hX (by omega) (by omega) hX1S0
    (by intro i hi hm; rw [hS0] at hm; omega)
    (by intro hm; rw [hS0] at hm; omega)
    (fun e => absurd e hX5) (fun e => absurd e hX5)
    (by rw [tX1]; exact ⟨by omega, by omega, by omega⟩)
  have hS1' : ∀ z, z ∈ A1.P.S ↔ z = armRoot X ∨ (z % 8 = X ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 2) := by
    intro z; rw [hS1, hS0]; omega
  have t1r : A1.tau (armRoot X) = 1 := by
    rw [ht1 _ hrS0, t0, pX1]
    have : (par d (armRoot X) + (par d (armRoot X) + 1) % 2) % 2 = 1 := by omega
    rw [this]
  have t1X2 : A1.tau (X + 8 * 2) = 0 := by
    rw [show X + 8 * 2 = X + 8 * (1 + 1) by ring, hX2, tX1]
  have hrS1 : armRoot X ∈ A1.P.S := by rw [hS1']; left; rfl
  have hX2S1 : X + 8 * 2 ∈ A1.P.S := by rw [hS1']; right; omega
  obtain ⟨A2, hS2, hE2, he2, ht2, _⟩ := A1.attachRoot Y y hY hy
    (by rw [hrY]; exact hrS1)
    (by intro i hi hm; rw [hS1'] at hm; omega)
    (by intro hm; rw [hS1'] at hm; omega)
    (fun e => absurd e hY5) (fun e => absurd e hY5)
    (by rw [hrY, t1r]; exact hok1)
  rw [hrY] at ht2
  have hS2' : ∀ z, z ∈ A2.P.S ↔ z = armRoot X ∨ (z % 8 = X ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 2) ∨
      (z % 8 = Y ∧ 1 ≤ z / 8 ∧ z / 8 ≤ y) := by
    intro z; rw [hS2, hS1']; omega
  have t2r : A2.tau (armRoot X) = 1 + y / 2 := by
    rw [ht2 _ hrS1, t1r]; have : (par d (armRoot X) + par d (armRoot X)) % 2 = 0 := by omega
    rw [this]; omega
  have t2X2 : A2.tau (X + 8 * 2) = y / 2 := by
    rw [ht2 _ hX2S1, t1X2, pX2]
    have : ((par d (armRoot X) + 2) % 2 + par d (armRoot X)) % 2 = 0 := by omega
    rw [this]; omega
  have hrS2 : armRoot X ∈ A2.P.S := by rw [hS2']; left; rfl
  have hX2S2 : X + 8 * 2 ∈ A2.P.S := by rw [hS2']; right; left; omega
  obtain ⟨A3, hS3, hE3, he3, ht3, _⟩ := A2.attachArm X 2 (x - 2) hX (by omega) (by omega) hX2S2
    (by intro i hi hm; rw [hS2'] at hm; omega)
    (by intro hm; rw [hS2'] at hm; omega)
    (fun e => absurd e hX5) (fun e => absurd e hX5)
    (by rw [t2X2]; exact hok2)
  refine ⟨A3, ?_, by rw [hE3, hE2, hE1, hE0]; omega,
    by rw [he3 _ hrS2, he2 _ hrS1, he1 _ hrS0, e0], ?_⟩
  · intro z; rw [hS3, hS2']; unfold Sh2; omega
  · rw [ht3 _ hrS2, t2r, pX2]
    have : (par d (armRoot X) + (par d (armRoot X) + 2) % 2) % 2 = 0 := by omega
    rw [this]; omega
