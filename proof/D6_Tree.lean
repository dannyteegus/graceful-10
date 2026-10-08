/-! ## Explicit labeled trees, checked by computation -/

/-- `pa` is a parent function (`pa i < i` for `1 ≤ i < n`), `lab` is injective into `[0,n-1]`
with distinct edge labels `|lab i - lab (pa i)|`; with `alpha`, every edge crosses threshold `th`. -/
def treeCheck (n th : ℕ) (alpha : Bool) (pa lab : ℕ → ℕ) : Bool :=
  ((List.range n).all fun i => decide (lab i < n)) &&
  ((List.range n).all fun i => (List.range n).all fun j => decide (i = j) || decide (lab i ≠ lab j)) &&
  ((List.range n).all fun i => decide (i = 0) || decide (pa i < i)) &&
  ((List.range n).all fun i => (List.range n).all fun j =>
      decide (i = 0) || decide (j = 0) || decide (i = j) ||
      decide (Nat.dist (lab i) (lab (pa i)) ≠ Nat.dist (lab j) (lab (pa j)))) &&
  (!alpha || (decide (th ≤ n) && (List.range n).all fun i =>
      decide (i = 0) || (decide (lab i < th) != decide (lab (pa i) < th))))

theorem treeCheck_spec {n th : ℕ} {alpha : Bool} {pa lab : ℕ → ℕ}
    (h : treeCheck n th alpha pa lab = true) :
    (∀ i, i < n → lab i < n) ∧
    (∀ i j, i < n → j < n → lab i = lab j → i = j) ∧
    (∀ i, i < n → i ≠ 0 → pa i < i) ∧
    (∀ i j, i < n → j < n → i ≠ 0 → j ≠ 0 →
      Nat.dist (lab i) (lab (pa i)) = Nat.dist (lab j) (lab (pa j)) → i = j) ∧
    (alpha = true → th ≤ n ∧ ∀ i, i < n → i ≠ 0 → (lab i < th ↔ ¬ lab (pa i) < th)) := by
  unfold treeCheck at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    decide_eq_true_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨h1, ?_, ?_, ?_, ?_⟩
  · intro i j hi hj e
    rcases h2 i hi j hj with h | h
    · exact h
    · exact absurd e h
  · intro i hi h0
    rcases h3 i hi with h | h
    · exact absurd h h0
    · exact h
  · intro i j hi hj hi0 hj0 e
    rcases h4 i hi j hj with ((h | h) | h) | h
    · exact absurd h hi0
    · exact absurd h hj0
    · exact h
    · exact absurd e h
  · intro ha
    rcases h5 with h | ⟨hth, h⟩
    · rw [ha] at h; exact absurd h (by decide)
    · refine ⟨hth, fun i hi hi0 => ?_⟩
      rcases h i hi with h' | h'
      · exact absurd h' hi0
      · have h'' : ¬ (lab i < th ↔ lab (pa i) < th) := by
          intro e
          by_cases a : lab i < th
          · have b := e.mp a
            simp [a, b] at h'
          · have b : ¬ lab (pa i) < th := fun b => a (e.mpr b)
            simp [a, b] at h'
        tauto

/-- the piece of an explicit tree on names `nm i` with labels `lab i` -/
noncomputable def treePc (d n : ℕ) (nm pos lab : ℕ → ℕ) : Pc where
  S := (Finset.range n).image nm
  R := Tadj d
  f := fun z => lab (pos z)

theorem treePc_mem {d n : ℕ} {nm pos lab : ℕ → ℕ} {z : ℕ} :
    z ∈ (treePc d n nm pos lab).S ↔ ∃ i, i < n ∧ nm i = z := by
  simp [treePc, Finset.mem_image]

theorem treePc_props (d n th : ℕ) (alpha : Bool) (nm pos pa lab : ℕ → ℕ) (hn : 1 ≤ n)
    (hinj : ∀ i j, i < n → j < n → nm i = nm j → i = j) (hpos : ∀ i, i < n → pos (nm i) = i)
    (hadj : ∀ i j, i < n → j < n →
      (Tadj d (nm i) (nm j) ↔ (i ≠ 0 ∧ pa i = j) ∨ (j ≠ 0 ∧ pa j = i)))
    (hc : treeCheck n th alpha pa lab = true) :
    (treePc d n nm pos lab).Grace ∧ (treePc d n nm pos lab).E.card = n - 1 ∧
      (alpha = true → (treePc d n nm pos lab).Alpha th) := by
  classical
  obtain ⟨c1, c2, c3, c4, c5⟩ := treeCheck_spec hc
  set P := treePc d n nm pos lab with hP
  have hf : ∀ i, i < n → P.f (nm i) = lab i := by
    intro i hi; show lab (pos (nm i)) = lab i; rw [hpos i hi]
  -- edges are exactly the parent pairs
  have hEmem : ∀ e, e ∈ P.E ↔ ∃ i, i < n ∧ i ≠ 0 ∧ e = opair (nm i) (nm (pa i)) := by
    intro e
    rw [Pc.mem_E]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      obtain ⟨i, hi, hie⟩ := treePc_mem.mp h1
      obtain ⟨j, hj, hje⟩ := treePc_mem.mp h2
      have h4' : Tadj d (nm i) (nm j) := by rw [hie, hje]; exact h4
      rcases (hadj i j hi hj).mp h4' with ⟨hi0, hp⟩ | ⟨hj0, hp⟩
      · refine ⟨i, hi, hi0, ?_⟩
        rw [hp, hie, hje]
        unfold opair
        rw [min_eq_left (le_of_lt h3), max_eq_right (le_of_lt h3)]
      · refine ⟨j, hj, hj0, ?_⟩
        rw [hp, hie, hje]
        unfold opair
        rw [min_eq_right (le_of_lt h3), max_eq_left (le_of_lt h3)]
    · rintro ⟨i, hi, hi0, rfl⟩
      have hpi := c3 i hi hi0
      have hne : nm i ≠ nm (pa i) := fun e => by have := hinj _ _ hi (by omega) e; omega
      have hadj' := (hadj i (pa i) hi (by omega)).mpr (Or.inl ⟨hi0, rfl⟩)
      have m1 : nm i ∈ P.S := treePc_mem.mpr ⟨i, hi, rfl⟩
      have m2 : nm (pa i) ∈ P.S := treePc_mem.mpr ⟨pa i, by omega, rfl⟩
      unfold opair
      rcases lt_or_gt_of_ne hne with hl | hl
      · rw [min_eq_left (le_of_lt hl), max_eq_right (le_of_lt hl)]
        exact ⟨m1, m2, hl, hadj'⟩
      · rw [min_eq_right (le_of_lt hl), max_eq_left (le_of_lt hl)]
        exact ⟨m2, m1, hl, Tadj_symm d _ _ hadj'⟩
  have hEimg : P.E = ((Finset.range n).filter (fun i => i ≠ 0)).image
      (fun i => opair (nm i) (nm (pa i))) := by
    ext e
    rw [hEmem, Finset.mem_image]
    constructor
    · rintro ⟨i, hi, hi0, rfl⟩; exact ⟨i, by simp [hi, hi0], rfl⟩
    · rintro ⟨i, hi, rfl⟩; simp at hi; exact ⟨i, hi.1, hi.2, rfl⟩
  have hcard : P.E.card = n - 1 := by
    rw [hEimg, Finset.card_image_of_injOn]
    · have : (Finset.range n).filter (fun i => i ≠ 0) = (Finset.range n).erase 0 := by
        ext i; simp [and_comm]
      rw [this, Finset.card_erase_of_mem (by simp; omega), Finset.card_range]
    · intro i hi j hj e
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hi hj
      simp only [opair, Prod.mk.injEq] at e
      have hpi := c3 i hi.1 hi.2
      have hpj := c3 j hj.1 hj.2
      obtain ⟨e1, e2⟩ := e
      have key : (nm i = nm j ∧ nm (pa i) = nm (pa j)) ∨ (nm i = nm (pa j) ∧ nm (pa i) = nm j) := by
        rcases le_total (nm i) (nm (pa i)) with a | a <;>
          rcases le_total (nm j) (nm (pa j)) with b | b
        · rw [min_eq_left a, min_eq_left b] at e1; rw [max_eq_right a, max_eq_right b] at e2
          exact Or.inl ⟨e1, e2⟩
        · rw [min_eq_left a, min_eq_right b] at e1; rw [max_eq_right a, max_eq_left b] at e2
          exact Or.inr ⟨e1, e2⟩
        · rw [min_eq_right a, min_eq_left b] at e1; rw [max_eq_left a, max_eq_right b] at e2
          exact Or.inr ⟨e2, e1⟩
        · rw [min_eq_right a, min_eq_right b] at e1; rw [max_eq_left a, max_eq_left b] at e2
          exact Or.inl ⟨e2, e1⟩
      rcases key with ⟨k1, _⟩ | ⟨k1, k2⟩
      · exact hinj _ _ hi.1 hj.1 k1
      · have := hinj _ _ hi.1 (by omega) k1
        have := hinj _ _ (by omega) hj.1 k2
        omega
  have hScard : P.S.card = n := by
    show ((Finset.range n).image nm).card = n
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro i hi j hj e
    exact hinj i j (by simpa using hi) (by simpa using hj) e
  have hG : P.Grace := by
    refine ⟨Tadj_symm d, by rw [hScard, hcard]; omega, ?_, ?_, ?_⟩
    · intro x hx y hy e
      obtain ⟨i, hi, rfl⟩ := treePc_mem.mp hx
      obtain ⟨j, hj, rfl⟩ := treePc_mem.mp hy
      rw [hf i hi, hf j hj] at e
      rw [c2 i j hi hj e]
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := treePc_mem.mp hx
      rw [hf i hi, hcard]
      have := c1 i hi; omega
    · intro e he e' he' h
      obtain ⟨i, hi, hi0, rfl⟩ := (hEmem e).mp he
      obtain ⟨j, hj, hj0, rfl⟩ := (hEmem e').mp he'
      have hpi := c3 i hi hi0
      have hpj := c3 j hj hj0
      have dist_op : ∀ k, k < n → k ≠ 0 →
          Nat.dist (P.f (opair (nm k) (nm (pa k))).1) (P.f (opair (nm k) (nm (pa k))).2) =
            Nat.dist (lab k) (lab (pa k)) := by
        intro k hk hk0
        have := c3 k hk hk0
        unfold opair
        rcases le_total (nm k) (nm (pa k)) with a | a
        · rw [min_eq_left a, max_eq_right a, hf k hk, hf (pa k) (by omega)]
        · rw [min_eq_right a, max_eq_left a, hf k hk, hf (pa k) (by omega), Nat.dist_comm]
      rw [dist_op i hi hi0, dist_op j hj hj0] at h
      rw [c4 i j hi hj hi0 hj0 h]
  refine ⟨hG, hcard, fun ha => ⟨hG, ?_, ?_⟩⟩
  · rw [hcard]; have := (c5 ha).1; omega
  · intro x hx y hy hr
    obtain ⟨i, hi, rfl⟩ := treePc_mem.mp hx
    obtain ⟨j, hj, rfl⟩ := treePc_mem.mp hy
    rw [hf i hi, hf j hj]
    have hr' : Tadj d (nm i) (nm j) := hr
    have alt := (c5 ha).2
    rcases (hadj i j hi hj).mp hr' with ⟨hi0, hp⟩ | ⟨hj0, hp⟩
    · have := alt i hi hi0; rw [hp] at this; omega
    · have := alt j hj hj0; rw [hp] at this; omega

/-- an explicit α-tree as a start piece -/
theorem startTree (d n th q : ℕ) (nm pos pa lab : ℕ → ℕ) (hn : 1 ≤ n)
    (hinj : ∀ i j, i < n → j < n → nm i = nm j → i = j) (hpos : ∀ i, i < n → pos (nm i) = i)
    (hadj : ∀ i j, i < n → j < n →
      (Tadj d (nm i) (nm j) ↔ (i ≠ 0 ∧ pa i = j) ∨ (j ≠ 0 ∧ pa j = i)))
    (hc : treeCheck n th true pa lab = true)
    (hlow : ∀ i, i < n → (lab i < th ↔ par d (nm i) = q)) (hq : q ≤ 1) :
    ∃ A : APc d q, (∀ z, z ∈ A.P.S ↔ ∃ i, i < n ∧ nm i = z) ∧ A.P.E.card = n - 1 ∧
      (∀ i, i < n → A.eps (nm i) = if lab i < th then lab i else n - 1 - lab i) ∧
      (∀ i, i < n → A.tau (nm i) = if lab i < th then th - 1 - lab i else lab i - th) := by
  obtain ⟨_, hcard, hal⟩ := treePc_props d n th true nm pos pa lab hn hinj hpos hadj hc
  have hA := hal rfl
  have hf : ∀ i, i < n → (treePc d n nm pos lab).f (nm i) = lab i := by
    intro i hi; show lab (pos (nm i)) = lab i; rw [hpos i hi]
  refine ⟨⟨treePc d n nm pos lab, th, rfl, hA, ?_, hq⟩, fun z => treePc_mem, hcard, ?_, ?_⟩
  · intro z hz
    obtain ⟨i, hi, rfl⟩ := treePc_mem.mp hz
    rw [hf i hi]; exact hlow i hi
  · intro i hi
    show (treePc d n nm pos lab).eps th (nm i) = _
    unfold Pc.eps; rw [hf i hi, hcard]
  · intro i hi
    show (treePc d n nm pos lab).tau th (nm i) = _
    unfold Pc.tau; rw [hf i hi]
