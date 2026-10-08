/-! ## Canonical tree T(a,b,c|d|e,f) on ℕ-names

`u = 0`, `v = 1`, arm `X ∈ {2,…,7}` position `k ≥ 1` is `X + 8k`.
Arms: 2,3,4 at `u` (lengths a,b,c), 5 = interior of the u–v path (length d−1), 6,7 at `v`. -/

/-- arm lengths -/
def armLen (a b c d e f X : ℕ) : ℕ :=
  if X = 2 then a else if X = 3 then b else if X = 4 then c else
  if X = 5 then d - 1 else if X = 6 then e else if X = 7 then f else 0

/-- root of arm `X` -/
def armRoot (X : ℕ) : ℕ := if X ≤ 5 then 0 else 1

/-- last vertex of the u–v path before `v` -/
def dEnd (d : ℕ) : ℕ := if 2 ≤ d then 5 + 8 * (d - 1) else 0

/-- canonical parent function (tree rooted at `u = 0`) -/
def Tpar (d : ℕ) (x : ℕ) : ℕ :=
  if x = 0 then 0 else if x = 1 then dEnd d else
  if 2 ≤ x / 8 then x - 8 else armRoot (x % 8)

/-- canonical adjacency (symmetric parent relation) -/
def Tadj (d : ℕ) (x y : ℕ) : Prop := (x ≠ 0 ∧ Tpar d x = y) ∨ (y ≠ 0 ∧ Tpar d y = x)

/-- canonical vertex set -/
def Tset (a b c d e f : ℕ) : Finset ℕ :=
  {0, 1} ∪ (Finset.Icc 2 7).biUnion (fun X => (Finset.Icc 1 (armLen a b c d e f X)).image
    (fun k => X + 8 * k))

theorem mem_Tset {a b c d e f x : ℕ} :
    x ∈ Tset a b c d e f ↔ x = 0 ∨ x = 1 ∨
      ∃ X k, 2 ≤ X ∧ X ≤ 7 ∧ 1 ≤ k ∧ k ≤ armLen a b c d e f X ∧ x = X + 8 * k := by
  unfold Tset
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_biUnion,
    Finset.mem_Icc, Finset.mem_image]
  constructor
  · rintro ((h | h) | ⟨X, ⟨h1, h2⟩, k, ⟨k1, k2⟩, rfl⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨X, k, h1, h2, k1, k2, rfl⟩)
  · rintro (h | h | ⟨X, k, h1, h2, k1, k2, rfl⟩)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr ⟨X, ⟨h1, h2⟩, k, ⟨k1, k2⟩, rfl⟩

theorem Tadj_symm (d : ℕ) : ∀ x y, Tadj d x y → Tadj d y x := by
  intro x y h; rcases h with h | h
  · exact Or.inr h
  · exact Or.inl h

theorem Tpar_arm (d X k : ℕ) (hX : 2 ≤ X ∧ X ≤ 7) (hk : 1 ≤ k) :
    Tpar d (X + 8 * k) = if 2 ≤ k then X + 8 * (k - 1) else armRoot X := by
  unfold Tpar
  have h1 : X + 8 * k ≠ 0 := by omega
  have h2 : X + 8 * k ≠ 1 := by omega
  have h3 : (X + 8 * k) / 8 = k := by omega
  have h4 : (X + 8 * k) % 8 = X := by omega
  rw [if_neg h1, if_neg h2, h3, h4]
  split_ifs <;> omega

theorem armLen_2 (a b c d e f : ℕ) : armLen a b c d e f 2 = a := rfl
theorem armLen_3 (a b c d e f : ℕ) : armLen a b c d e f 3 = b := rfl
theorem armLen_4 (a b c d e f : ℕ) : armLen a b c d e f 4 = c := rfl
theorem armLen_5 (a b c d e f : ℕ) : armLen a b c d e f 5 = d - 1 := rfl
theorem armLen_6 (a b c d e f : ℕ) : armLen a b c d e f 6 = e := rfl
theorem armLen_7 (a b c d e f : ℕ) : armLen a b c d e f 7 = f := rfl
