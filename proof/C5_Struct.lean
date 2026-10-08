/-! ## Structure of Branch43 trees -/

section Struct
variable {n : ℕ} {G : SimpleGraph (Fin n)}

theorem nbr_root_depth (hT : G.IsTree) {u y : Fin n} (h : G.Adj u y) :
    G.dist u y = 1 ∧ tpar hT u y = u := by
  rcases adj_iff_par hT u h with ⟨_, h2, h3⟩ | ⟨h1, _, _⟩
  · rw [SimpleGraph.dist_self] at h3; exact ⟨by omega, h2⟩
  · exact absurd rfl h1

theorem anc_one_adj (hT : G.IsTree) {u x : Fin n} (hx : x ≠ u) :
    G.Adj u (anc hT u x 1) := by
  have hd : 1 ≤ G.dist u x := dist_pos_of_ne hT hx
  have h1 := anc_dist hT u x hd
  have hne : anc hT u x 1 ≠ u := by
    intro e; rw [e, SimpleGraph.dist_self] at h1; omega
  obtain ⟨hadj, hdd⟩ := tpar_spec hT u (anc hT u x 1) hne
  rw [h1] at hdd
  have : tpar hT u (anc hT u x 1) = u := eq_of_dist_zero hT (by omega)
  rw [this] at hadj
  exact hadj

theorem anc_one_ne_root (hT : G.IsTree) {u x : Fin n} (hx : x ≠ u) : anc hT u x 1 ≠ u := by
  have h1 := anc_dist hT u x (dist_pos_of_ne hT hx)
  intro e; rw [e, SimpleGraph.dist_self] at h1; omega

/-- the branch of a vertex is inherited from its parent -/
theorem anc_one_tpar (hT : G.IsTree) {u x : Fin n} (hx : x ≠ u) (h2 : 2 ≤ G.dist u x) :
    anc hT u (tpar hT u x) 1 = anc hT u x 1 :=
  anc_tpar hT u x hx (by omega)

/-- neighbours of a non-root vertex: its parent and its children -/
theorem nbr_cases (hT : G.IsTree) {u q y : Fin n} (h : G.Adj q y) :
    (tpar hT u y = q ∧ y ≠ u ∧ G.dist u y = G.dist u q + 1) ∨
    (q ≠ u ∧ tpar hT u q = y ∧ G.dist u q = G.dist u y + 1) := by
  rcases adj_iff_par hT u h with ⟨a, b, c⟩ | ⟨a, b, c⟩
  · exact Or.inl ⟨b, a, c⟩
  · exact Or.inr ⟨a, b, c⟩

end Struct
