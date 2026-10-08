/-! ## Explicit trees on numeral names (checked by `decide`) -/

/-- Boolean adjacency of the canonical tree -/
def tadjB (d x y : ℕ) : Bool := (x != 0 && Tpar d x == y) || (y != 0 && Tpar d y == x)

theorem tadjB_iff (d x y : ℕ) : Tadj d x y ↔ tadjB d x y = true := by
  unfold Tadj tadjB
  simp [Bool.or_eq_true, Bool.and_eq_true, bne_iff_ne, beq_iff_eq]

/-- an explicit α-tree on numeral names: lists of names, parents (indices) and labels -/
theorem numTreeA (d th q : ℕ) (names pa lab : List ℕ) (hn : 1 ≤ names.length)
    (hinj : ∀ i, i < names.length → ∀ j, j < names.length →
      names.getD i 0 = names.getD j 0 → i = j)
    (hpos : ∀ i, i < names.length → names.idxOf (names.getD i 0) = i)
    (hadj : ∀ i, i < names.length → ∀ j, j < names.length →
      (tadjB d (names.getD i 0) (names.getD j 0) = true ↔
        (i ≠ 0 ∧ pa.getD i 0 = j) ∨ (j ≠ 0 ∧ pa.getD j 0 = i)))
    (hc : treeCheck names.length th true (fun i => pa.getD i 0) (fun i => lab.getD i 0) = true)
    (hlow : ∀ i, i < names.length → (lab.getD i 0 < th ↔ par d (names.getD i 0) = q))
    (hq : q ≤ 1) :
    ∃ A : APc d q, (∀ z, z ∈ A.P.S ↔ ∃ i, i < names.length ∧ names.getD i 0 = z) ∧
      A.P.E.card = names.length - 1 ∧
      (∀ i, i < names.length → A.eps (names.getD i 0) =
        if lab.getD i 0 < th then lab.getD i 0 else names.length - 1 - lab.getD i 0) ∧
      (∀ i, i < names.length → A.tau (names.getD i 0) =
        if lab.getD i 0 < th then th - 1 - lab.getD i 0 else lab.getD i 0 - th) :=
  startTree d names.length th q (fun i => names.getD i 0) (fun z => names.idxOf z)
    (fun i => pa.getD i 0) (fun i => lab.getD i 0) hn (fun i j hi hj e => hinj i hi j hj e) hpos
    (fun i j hi hj => by rw [tadjB_iff]; exact hadj i hi j hj) hc hlow hq

/-- an explicit graceful tree on numeral names -/
theorem numTreeG (d : ℕ) (names pa lab : List ℕ) (hn : 1 ≤ names.length)
    (hinj : ∀ i, i < names.length → ∀ j, j < names.length →
      names.getD i 0 = names.getD j 0 → i = j)
    (hpos : ∀ i, i < names.length → names.idxOf (names.getD i 0) = i)
    (hadj : ∀ i, i < names.length → ∀ j, j < names.length →
      (tadjB d (names.getD i 0) (names.getD j 0) = true ↔
        (i ≠ 0 ∧ pa.getD i 0 = j) ∨ (j ≠ 0 ∧ pa.getD j 0 = i)))
    (hc : treeCheck names.length 0 false (fun i => pa.getD i 0) (fun i => lab.getD i 0) = true) :
    ∃ G : Pc, G.Grace ∧ G.R = Tadj d ∧ (∀ z, z ∈ G.S ↔ ∃ i, i < names.length ∧ names.getD i 0 = z) ∧
      G.E.card = names.length - 1 ∧ (∀ i, i < names.length → G.f (names.getD i 0) = lab.getD i 0) := by
  obtain ⟨hG, hE, _⟩ := treePc_props d names.length 0 false (fun i => names.getD i 0)
    (fun z => names.idxOf z) (fun i => pa.getD i 0) (fun i => lab.getD i 0) hn
    (fun i j hi hj e => hinj i hi j hj e) hpos
    (fun i j hi hj => by rw [tadjB_iff]; exact hadj i hi j hj) hc
  refine ⟨_, hG, rfl, fun z => treePc_mem, hE, ?_⟩
  intro i hi
  show lab.getD (names.idxOf (names.getD i 0)) 0 = _
  rw [hpos i hi]

/-- membership in a list of numerals as an arithmetic formula, via a bound -/
theorem mem_list_iff {names : List ℕ} {φ : ℕ → Prop} (B : ℕ)
    (h1 : ∀ z, z < B → ((∃ i, i < names.length ∧ names.getD i 0 = z) ↔ φ z))
    (h2 : ∀ i, i < names.length → names.getD i 0 < B) (h3 : ∀ z, B ≤ z → ¬ φ z) :
    ∀ z, (∃ i, i < names.length ∧ names.getD i 0 = z) ↔ φ z := by
  intro z
  by_cases hz : z < B
  · exact h1 z hz
  · constructor
    · rintro ⟨i, hi, rfl⟩; exact absurd (h2 i hi) hz
    · intro h; exact absurd h (h3 z (by omega))
