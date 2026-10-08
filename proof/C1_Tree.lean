/-! ## Rooted-tree facts via distances -/

section TreeFacts
variable {V : Type} {G : SimpleGraph V}

theorem tree_par_exists (hT : G.IsTree) (u x : V) (hx : x ≠ u) :
    ∃ y, G.Adj y x ∧ G.dist u y + 1 = G.dist u x := by
  obtain ⟨p, hp⟩ := hT.isConnected.preconnected u x |>.exists_walk_length_eq_dist
  cases hq : p.reverse with
  | nil => exact absurd rfl hx
  | cons h q =>
    rename_i y
    refine ⟨y, h.symm, ?_⟩
    have hlen : q.length + 1 = G.dist u x := by
      have := p.length_reverse
      rw [hq, SimpleGraph.Walk.length_cons] at this
      omega
    have h1 : G.dist u y ≤ q.length := by
      have := SimpleGraph.dist_le q.reverse
      rw [SimpleGraph.Walk.length_reverse] at this
      exact this
    have h2 := hT.dist_eq_dist_add_one_of_adj u h
    omega


theorem tree_not_mem_support_of_far (hT : G.IsTree) {u y x : V} (p : G.Walk u y)
    (hp : p.length = G.dist u y) (hfar : G.dist u y < G.dist u x) : x ∉ p.support := by
  classical
  intro hx
  have h1 := SimpleGraph.dist_le (p.takeUntil x hx)
  have h2 := p.length_takeUntil_le hx
  omega

theorem tree_par_unique (hT : G.IsTree) {u x y₁ y₂ : V} (h₁ : G.Adj y₁ x) (h₂ : G.Adj y₂ x)
    (d₁ : G.dist u y₁ + 1 = G.dist u x) (d₂ : G.dist u y₂ + 1 = G.dist u x) : y₁ = y₂ := by
  classical
  obtain ⟨p₁, hp₁, hl₁⟩ := hT.isConnected.exists_path_of_dist u y₁
  obtain ⟨p₂, hp₂, hl₂⟩ := hT.isConnected.exists_path_of_dist u y₂
  have n₁ := tree_not_mem_support_of_far hT p₁ hl₁ (by omega : G.dist u y₁ < G.dist u x)
  have n₂ := tree_not_mem_support_of_far hT p₂ hl₂ (by omega : G.dist u y₂ < G.dist u x)
  have q₁ := hp₁.concat n₁ h₁
  have q₂ := hp₂.concat n₂ h₂
  have heq : p₁.concat h₁ = p₂.concat h₂ :=
    congrArg Subtype.val (hT.IsAcyclic.path_unique ⟨_, q₁⟩ ⟨_, q₂⟩)
  have := congrArg SimpleGraph.Walk.penultimate heq
  simpa [SimpleGraph.Walk.penultimate_concat] using this


/-- parent of `x` in the tree rooted at `u` (`u` itself for `x = u`). -/
noncomputable def tpar (hT : G.IsTree) (u x : V) : V := by
  classical
  exact if h : x = u then u else Classical.choose (tree_par_exists hT u x h)

theorem tpar_spec (hT : G.IsTree) (u x : V) (hx : x ≠ u) :
    G.Adj (tpar hT u x) x ∧ G.dist u (tpar hT u x) + 1 = G.dist u x := by
  classical
  unfold tpar
  simp only [dif_neg hx]
  exact Classical.choose_spec (tree_par_exists hT u x hx)

theorem tpar_eq (hT : G.IsTree) {u x y : V} (hx : x ≠ u) (hadj : G.Adj y x)
    (hd : G.dist u y + 1 = G.dist u x) : tpar hT u x = y :=
  tree_par_unique hT (tpar_spec hT u x hx).1 hadj (tpar_spec hT u x hx).2 hd

theorem dist_pos_of_ne (hT : G.IsTree) {u x : V} (hx : x ≠ u) : 1 ≤ G.dist u x := by
  have := hT.isConnected.pos_dist_of_ne (Ne.symm hx)
  omega

theorem eq_of_dist_zero (hT : G.IsTree) {u x : V} (h : G.dist u x = 0) : x = u :=
  ((hT.isConnected.dist_eq_zero_iff).mp h).symm

/-- adjacency is exactly the parent relation -/
theorem adj_iff_par (hT : G.IsTree) (u : V) {x y : V} (hadj : G.Adj x y) :
    (y ≠ u ∧ tpar hT u y = x ∧ G.dist u y = G.dist u x + 1) ∨
    (x ≠ u ∧ tpar hT u x = y ∧ G.dist u x = G.dist u y + 1) := by
  rcases hT.dist_eq_dist_add_one_of_adj u hadj with h | h
  · right
    have hx : x ≠ u := by
      intro e; subst e; simp at h
    exact ⟨hx, tpar_eq hT hx hadj.symm (by omega), h⟩
  · left
    have hy : y ≠ u := by
      intro e; subst e; simp at h
    exact ⟨hy, tpar_eq hT hy hadj (by omega), h⟩

theorem iter_tpar_dist (hT : G.IsTree) (u x : V) :
    ∀ i, i ≤ G.dist u x → G.dist u ((tpar hT u)^[i] x) = G.dist u x - i := by
  intro i
  induction i with
  | zero => intro _; simp
  | succ i ih =>
    intro hi
    rw [Function.iterate_succ_apply']
    have h1 := ih (by omega)
    have hne : (tpar hT u)^[i] x ≠ u := by
      intro e; rw [e] at h1; simp at h1; omega
    have := (tpar_spec hT u _ hne).2
    omega

/-- ancestor of `x` at depth `j` -/
noncomputable def anc (hT : G.IsTree) (u x : V) (j : ℕ) : V := (tpar hT u)^[G.dist u x - j] x

theorem anc_dist (hT : G.IsTree) (u x : V) {j : ℕ} (hj : j ≤ G.dist u x) :
    G.dist u (anc hT u x j) = j := by
  unfold anc
  rw [iter_tpar_dist hT u x _ (by omega)]
  omega

theorem anc_self (hT : G.IsTree) (u x : V) : anc hT u x (G.dist u x) = x := by
  simp [anc]

theorem anc_tpar (hT : G.IsTree) (u x : V) (hx : x ≠ u) {j : ℕ} (hj : j < G.dist u x) :
    anc hT u (tpar hT u x) j = anc hT u x j := by
  unfold anc
  have hd := (tpar_spec hT u x hx).2
  have e : G.dist u x - j = (G.dist u (tpar hT u x) - j) + 1 := by omega
  rw [e, Function.iterate_succ_apply]

theorem anc_anc (hT : G.IsTree) (u x : V) {i j : ℕ} (hji : j ≤ i) (hi : i ≤ G.dist u x) :
    anc hT u (anc hT u x i) j = anc hT u x j := by
  have hd := anc_dist hT u x hi
  unfold anc at hd ⊢
  rw [hd, ← Function.iterate_add_apply]
  congr 1
  omega

end TreeFacts
