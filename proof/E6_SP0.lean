/-! ## Spiders at `u` with the centre at label `0` (SP0) -/

theorem Tpar_indep (d x : ℕ) (hx : x ≠ 1) : Tpar d x = Tpar 1 x := by
  unfold Tpar; simp [hx]

theorem tadjB_indep (d x y : ℕ) (hx : x ≠ 1) (hy : y ≠ 1) : tadjB d x y = tadjB 1 x y := by
  unfold tadjB; rw [Tpar_indep d x hx, Tpar_indep d y hy]

theorem par_indep (d z : ℕ) (h1 : z ≠ 1) (h6 : z % 8 < 6) : par d z = par 0 z := by
  unfold par; simp only [h1, if_false]; split_ifs <;> omega

/-- an explicit α-tree on numeral names avoiding `v` and the arms at `v`, for any `d` -/
theorem numTreeAU (d th q : ℕ) (names pa lab : List ℕ) (hn : 1 ≤ names.length)
    (hv : ∀ i, i < names.length → names.getD i 0 ≠ 1 ∧ names.getD i 0 % 8 < 6)
    (hinj : ∀ i, i < names.length → ∀ j, j < names.length →
      names.getD i 0 = names.getD j 0 → i = j)
    (hpos : ∀ i, i < names.length → names.idxOf (names.getD i 0) = i)
    (hadj : ∀ i, i < names.length → ∀ j, j < names.length →
      (tadjB 1 (names.getD i 0) (names.getD j 0) = true ↔
        (i ≠ 0 ∧ pa.getD i 0 = j) ∨ (j ≠ 0 ∧ pa.getD j 0 = i)))
    (hc : treeCheck names.length th true (fun i => pa.getD i 0) (fun i => lab.getD i 0) = true)
    (hlow : ∀ i, i < names.length → (lab.getD i 0 < th ↔ par 0 (names.getD i 0) = q))
    (hq : q ≤ 1) :
    ∃ A : APc d q, (∀ z, z ∈ A.P.S ↔ ∃ i, i < names.length ∧ names.getD i 0 = z) ∧
      A.P.E.card = names.length - 1 ∧
      (∀ i, i < names.length → A.eps (names.getD i 0) =
        if lab.getD i 0 < th then lab.getD i 0 else names.length - 1 - lab.getD i 0) ∧
      (∀ i, i < names.length → A.tau (names.getD i 0) =
        if lab.getD i 0 < th then th - 1 - lab.getD i 0 else lab.getD i 0 - th) :=
  numTreeA d th q names pa lab hn hinj hpos
    (fun i hi j hj => by rw [tadjB_indep d _ _ (hv i hi).1 (hv j hj).1]; exact hadj i hi j hj) hc
    (fun i hi => by rw [par_indep d _ (hv i hi).1 (hv i hi).2]; exact hlow i hi) hq

/-- an explicit graceful tree on numeral names avoiding `v` and the arms at `v`, for any `d` -/
theorem numTreeGU (d : ℕ) (names pa lab : List ℕ) (hn : 1 ≤ names.length)
    (hv : ∀ i, i < names.length → names.getD i 0 ≠ 1)
    (hinj : ∀ i, i < names.length → ∀ j, j < names.length →
      names.getD i 0 = names.getD j 0 → i = j)
    (hpos : ∀ i, i < names.length → names.idxOf (names.getD i 0) = i)
    (hadj : ∀ i, i < names.length → ∀ j, j < names.length →
      (tadjB 1 (names.getD i 0) (names.getD j 0) = true ↔
        (i ≠ 0 ∧ pa.getD i 0 = j) ∨ (j ≠ 0 ∧ pa.getD j 0 = i)))
    (hc : treeCheck names.length 0 false (fun i => pa.getD i 0) (fun i => lab.getD i 0) = true) :
    ∃ G : Pc, G.Grace ∧ G.R = Tadj d ∧ (∀ z, z ∈ G.S ↔ ∃ i, i < names.length ∧ names.getD i 0 = z) ∧
      G.E.card = names.length - 1 ∧ (∀ i, i < names.length → G.f (names.getD i 0) = lab.getD i 0) :=
  numTreeG d names pa lab hn hinj hpos
    (fun i hi j hj => by rw [tadjB_indep d _ _ (hv i hi) (hv j hj)]; exact hadj i hi j hj) hc

/-- shape of the spider at `u` with arms `2, 3, 4` of lengths `a, b, c` -/
def ShU (a b c z : ℕ) : Prop :=
  z = 0 ∨ (z % 8 = 2 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ a) ∨ (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ b) ∨
    (z % 8 = 4 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ c)

/-- a graceful spider at `u` (arms `2,3,4` of lengths `a,b,c`) with `u` at label `σ` or `m - σ` -/
def SPG (d σ a b c : ℕ) : Prop :=
  ∃ G : Pc, G.Grace ∧ G.R = Tadj d ∧ (∀ z, z ∈ G.S ↔ ShU a b c z) ∧ G.E.card = a + b + c ∧
    (G.f 0 = σ ∨ G.f 0 = G.E.card - σ)

/-- standing hypotheses: three distinct arms `X, Y, Z` at `u` -/
structure Arms3 (X Y Z : ℕ) : Prop where
  hX : X = 2 ∨ X = 3 ∨ X = 4
  hY : Y = 2 ∨ Y = 3 ∨ Y = 4
  hZ : Z = 2 ∨ Z = 3 ∨ Z = 4
  hXY : X ≠ Y
  hXZ : X ≠ Z
  hYZ : Y ≠ Z

theorem Arms3.arms2 {X Y Z : ℕ} (h : Arms3 X Y Z) : Arms2 0 X Y := by
  obtain ⟨hX, hY, _, hXY, _, _⟩ := h
  refine ⟨by omega, by omega, hXY, by omega, by omega, ?_, ?_⟩ <;>
    (unfold armRoot; split_ifs <;> omega)

theorem armRoot_u {X : ℕ} (h : X = 2 ∨ X = 3 ∨ X = 4) : armRoot X = 0 := by
  unfold armRoot; split_ifs <;> omega

/-- `ShU` as seen through a permutation of the arms -/
theorem shU_perm {X Y Z x y z a b c w : ℕ} (h : Arms3 X Y Z)
    (ha : a = if X = 2 then x else if Y = 2 then y else z)
    (hb : b = if X = 3 then x else if Y = 3 then y else z)
    (hc : c = if X = 4 then x else if Y = 4 then y else z) :
    (w = 0 ∨ (w % 8 = X ∧ 1 ≤ w / 8 ∧ w / 8 ≤ x) ∨ (w % 8 = Y ∧ 1 ≤ w / 8 ∧ w / 8 ≤ y) ∨
      (w % 8 = Z ∧ 1 ≤ w / 8 ∧ w / 8 ≤ z)) ↔ ShU a b c w := by
  obtain ⟨hX, hY, hZ, hXY, hXZ, hYZ⟩ := h
  unfold ShU
  rcases hX with rfl | rfl | rfl <;> rcases hY with rfl | rfl | rfl <;>
    rcases hZ with rfl | rfl | rfl <;> simp_all <;> omega

/-- SP0, generic program: IVL0 on `X, Y`, then a final graceful segment on `Z` -/
theorem sp0_gen {d X Y Z x y z : ℕ} (h : Arms3 X Y Z) (H : IVL0P d 0 X Y x y)
    (hz : 1 ≤ z) (hK : x / 2 + y / 2 ≤ z - 1) :
    ∃ G : Pc, G.Grace ∧ G.R = Tadj d ∧
      (∀ w, w ∈ G.S ↔ w = 0 ∨ (w % 8 = X ∧ 1 ≤ w / 8 ∧ w / 8 ≤ x) ∨
        (w % 8 = Y ∧ 1 ≤ w / 8 ∧ w / 8 ≤ y) ∨ (w % 8 = Z ∧ 1 ≤ w / 8 ∧ w / 8 ≤ z)) ∧
      G.E.card = x + y + z ∧ (G.f 0 = 0 ∨ G.f 0 = G.E.card) := by
  obtain ⟨hX, hY, hZ, hXY, hXZ, hYZ⟩ := h
  obtain ⟨A, hS, hE, he, ht⟩ := H
  have hZr := armRoot_u hZ
  have h0 : (0 : ℕ) ∈ A.P.S := by rw [hS]; left; rfl
  obtain ⟨G, hG, hR, hSG, hEG, hf⟩ := A.attachGRoot Z z (by omega) hz (by rw [hZr]; exact h0)
    (by intro i hi hm; rw [hS] at hm; unfold Sh2 at hm; omega)
    (by intro hm; rw [hS] at hm; unfold Sh2 at hm; omega)
    (fun e => by omega) (fun e => by omega)
    (by rw [hZr, ht]; exact hK)
  refine ⟨G, hG, hR, fun w => by rw [hSG, hS]; unfold Sh2; omega, by rw [hEG, hE], ?_⟩
  rcases hf 0 h0 with e | e <;> rw [he] at e
  · left; exact e
  · right; rw [e]; rfl
