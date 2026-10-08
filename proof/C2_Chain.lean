/-! ## Chains: one vertex per depth in a low-degree branch -/

section Chain
variable {n : ℕ} {G : SimpleGraph (Fin n)}

theorem deg_ge_three {q a b c : Fin n} (ha : G.Adj q a) (hb : G.Adj q b) (hc : G.Adj q c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : 3 ≤ Math15.Graceful.degree G q := by
  classical
  unfold Math15.Graceful.degree
  have hsub : ({a, b, c} : Finset (Fin n)) ⊆ (Finset.univ : Finset (Fin n)).filter (G.Adj q) := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hz with rfl | rfl | rfl <;> assumption
  have hcard : ({a, b, c} : Finset (Fin n)).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair hbc]
    simp [hab, hac]
  calc 3 = ({a, b, c} : Finset (Fin n)).card := hcard.symm
    _ ≤ _ := Finset.card_le_card hsub

theorem chain_uniq (hT : G.IsTree) (u w : Fin n) (K : ℕ) (hw : 1 ≤ G.dist u w)
    (hdeg : ∀ q, G.dist u w ≤ G.dist u q → G.dist u q < K →
      anc hT u q (G.dist u w) = w → Math15.Graceful.degree G q ≤ 2) :
    ∀ x y, G.dist u w ≤ G.dist u x → G.dist u x ≤ K →
      anc hT u x (G.dist u w) = w → anc hT u y (G.dist u w) = w →
      G.dist u x = G.dist u y → x = y := by
  intro x y
  induction' h : G.dist u x - G.dist u w with j ih generalizing x y
  · intro hx _ ax ay hxy
    have e1 : G.dist u x = G.dist u w := by omega
    have e2 : G.dist u y = G.dist u w := by omega
    have hx' : w = x := by
      have h1 := anc_self hT u x
      rw [e1, ax] at h1
      exact h1
    have hy' : w = y := by
      have h1 := anc_self hT u y
      rw [e2, ay] at h1
      exact h1
    exact hx'.symm.trans hy'
  · intro hx hK ax ay hxy
    have hxu : x ≠ u := by
      intro e; rw [e, SimpleGraph.dist_self] at hx; omega
    have hyu : y ≠ u := by
      intro e; rw [e, SimpleGraph.dist_self] at hxy; omega
    obtain ⟨hpx, dpx⟩ := tpar_spec hT u x hxu
    obtain ⟨hpy, dpy⟩ := tpar_spec hT u y hyu
    have apx : anc hT u (tpar hT u x) (G.dist u w) = w := by
      rw [anc_tpar hT u x hxu (by omega)]; exact ax
    have apy : anc hT u (tpar hT u y) (G.dist u w) = w := by
      rw [anc_tpar hT u y hyu (by omega)]; exact ay
    have heq : tpar hT u x = tpar hT u y :=
      ih (tpar hT u x) (tpar hT u y) (by omega) (by omega) (by omega) apx apy (by omega)
    by_contra hne
    set q := tpar hT u x with hq
    have hqu : q ≠ u := fun e => by rw [e] at dpx; simp at dpx; omega
    obtain ⟨hpq, dpq⟩ := tpar_spec hT u q hqu
    have h3 : 3 ≤ Math15.Graceful.degree G q := by
      refine deg_ge_three (a := tpar hT u q) (b := x) (c := y) hpq.symm hpx (heq ▸ hpy) ?_ ?_ hne
      · intro e; rw [e] at dpq; omega
      · intro e; rw [e] at dpq; omega
    have := hdeg q (by omega) (by omega) apx
    omega

end Chain
