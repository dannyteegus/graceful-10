/-! ## Labeled pieces over ℕ-named vertices -/

/-- A labeled piece: finite vertex set `S`, symmetric adjacency `R` (only meaningful on `S`),
labeling `f`. -/
structure Pc where
  S : Finset ℕ
  R : ℕ → ℕ → Prop
  f : ℕ → ℕ

/-- oriented edge set (pairs `x < y`) of a piece -/
noncomputable def Pc.E (P : Pc) : Finset (ℕ × ℕ) := by
  classical
  exact (P.S ×ˢ P.S).filter (fun e => e.1 < e.2 ∧ P.R e.1 e.2)

theorem Pc.mem_E {P : Pc} {e : ℕ × ℕ} :
    e ∈ P.E ↔ e.1 ∈ P.S ∧ e.2 ∈ P.S ∧ e.1 < e.2 ∧ P.R e.1 e.2 := by
  classical
  unfold Pc.E
  simp [Finset.mem_filter, Finset.mem_product, and_assoc]

/-- graceful piece: tree-sized, labels injective in `[0,m]`, edge labels injective. -/
def Pc.Grace (P : Pc) : Prop :=
  (∀ x y, P.R x y → P.R y x) ∧
  P.S.card = P.E.card + 1 ∧
  (∀ x ∈ P.S, ∀ y ∈ P.S, P.f x = P.f y → x = y) ∧
  (∀ x ∈ P.S, P.f x ≤ P.E.card) ∧
  (∀ e ∈ P.E, ∀ e' ∈ P.E,
      Nat.dist (P.f e.1) (P.f e.2) = Nat.dist (P.f e'.1) (P.f e'.2) → e = e')

/-- α-piece with `th` low labels (`x` is low iff `f x < th`). -/
def Pc.Alpha (P : Pc) (th : ℕ) : Prop :=
  P.Grace ∧ th ≤ P.E.card + 1 ∧
  ∀ x ∈ P.S, ∀ y ∈ P.S, P.R x y → (P.f x < th ↔ th ≤ P.f y)
