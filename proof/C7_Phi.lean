/-! ## The canonical map φ -/

namespace B43Setup
variable {n : ℕ} {G : SimpleGraph (Fin n)} (S : B43Setup G)

/-- the canonical name of a vertex -/
noncomputable def phi (x : Fin n) : ℕ := by
  classical
  exact if x = S.u then 0 else if x = S.v then 1
  else if anc S.hT S.u x 1 = S.wa then 2 + 8 * G.dist S.u x
  else if anc S.hT S.u x 1 = S.wb then 3 + 8 * G.dist S.u x
  else if anc S.hT S.u x 1 = S.wc then 4 + 8 * G.dist S.u x
  else if G.dist S.u x < G.dist S.u S.v then 5 + 8 * G.dist S.u x
  else if anc S.hT S.u x (G.dist S.u S.v + 1) = S.ce then 6 + 8 * (G.dist S.u x - G.dist S.u S.v)
  else 7 + 8 * (G.dist S.u x - G.dist S.u S.v)

theorem anc_v_one : anc S.hT S.u S.v 1 ≠ S.wa ∧ anc S.hT S.u S.v 1 ≠ S.wb ∧
    anc S.hT S.u S.v 1 ≠ S.wc := ⟨S.had.symm, S.hbd.symm, S.hcd.symm⟩

/-- the categories of vertices, with the value of `phi` -/
theorem phi_cases (x : Fin n) :
    (x = S.u ∧ S.phi x = 0) ∨
    (x = S.v ∧ S.phi x = 1) ∨
    (x ≠ S.u ∧ x ≠ S.v ∧ anc S.hT S.u x 1 = S.wa ∧ S.phi x = 2 + 8 * G.dist S.u x) ∨
    (x ≠ S.u ∧ x ≠ S.v ∧ anc S.hT S.u x 1 = S.wb ∧ S.phi x = 3 + 8 * G.dist S.u x) ∨
    (x ≠ S.u ∧ x ≠ S.v ∧ anc S.hT S.u x 1 = S.wc ∧ S.phi x = 4 + 8 * G.dist S.u x) ∨
    (x ≠ S.u ∧ x ≠ S.v ∧ anc S.hT S.u x 1 = anc S.hT S.u S.v 1 ∧
      G.dist S.u x < G.dist S.u S.v ∧ S.phi x = 5 + 8 * G.dist S.u x) ∨
    (x ≠ S.u ∧ anc S.hT S.u x 1 = anc S.hT S.u S.v 1 ∧ G.dist S.u S.v < G.dist S.u x ∧
      anc S.hT S.u x (G.dist S.u S.v + 1) = S.ce ∧
      S.phi x = 6 + 8 * (G.dist S.u x - G.dist S.u S.v)) ∨
    (x ≠ S.u ∧ anc S.hT S.u x 1 = anc S.hT S.u S.v 1 ∧ G.dist S.u S.v < G.dist S.u x ∧
      anc S.hT S.u x (G.dist S.u S.v + 1) = S.cf ∧
      S.phi x = 7 + 8 * (G.dist S.u x - G.dist S.u S.v)) := by
  classical
  have hv := S.anc_v_one
  by_cases hu : x = S.u
  · left; exact ⟨hu, by simp [phi, hu]⟩
  by_cases hvx : x = S.v
  · right; left; exact ⟨hvx, by simp [phi, hvx, S.huv]⟩
  rcases S.hbr x hu with ha | hb | hc | hd
  · right; right; left; exact ⟨hu, hvx, ha, by simp [phi, hu, hvx, ha]⟩
  · have : anc S.hT S.u x 1 ≠ S.wa := by rw [hb]; exact S.hab.symm
    right; right; right; left; exact ⟨hu, hvx, hb, by simp [phi, hu, hvx, hb, Ne.symm S.hab]⟩
  · have h1 : anc S.hT S.u x 1 ≠ S.wa := by rw [hc]; exact S.hac.symm
    have h2 : anc S.hT S.u x 1 ≠ S.wb := by rw [hc]; exact S.hbc.symm
    right; right; right; right; left
    exact ⟨hu, hvx, hc, by simp [phi, hu, hvx, hc, Ne.symm S.hac, Ne.symm S.hbc]⟩
  · have h1 : anc S.hT S.u x 1 ≠ S.wa := by rw [hd]; exact hv.1
    have h2 : anc S.hT S.u x 1 ≠ S.wb := by rw [hd]; exact hv.2.1
    have h3 : anc S.hT S.u x 1 ≠ S.wc := by rw [hd]; exact hv.2.2
    rcases lt_trichotomy (G.dist S.u x) (G.dist S.u S.v) with hl | he | hg
    · right; right; right; right; right; left
      exact ⟨hu, hvx, hd, hl, by simp [phi, hu, hvx, h1, h2, h3, hl]⟩
    · exact absurd (S.dpath_uniq hu S.huv hd rfl (le_of_eq he) he) hvx
    · have hnl : ¬ G.dist S.u x < G.dist S.u S.v := by omega
      rcases S.hsub x hu hd hg with he' | hf'
      · right; right; right; right; right; right; left
        exact ⟨hu, hd, hg, he', by simp [phi, hu, hvx, h1, h2, h3, hnl, he']⟩
      · have hne : anc S.hT S.u x (G.dist S.u S.v + 1) ≠ S.ce := by rw [hf']; exact S.hef.symm
        right; right; right; right; right; right; right
        exact ⟨hu, hd, hg, hf', by simp [phi, hu, hvx, h1, h2, h3, hnl, hne]⟩

theorem phi_armA {x : Fin n} (hx : x ≠ S.u) (ax : anc S.hT S.u x 1 = S.wa) :
    S.phi x = 2 + 8 * G.dist S.u x := by
  rcases S.phi_cases x with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, _, _, p⟩ | ⟨_, _, a, _⟩ | ⟨_, _, a, _⟩ |
      ⟨_, _, a, _, _⟩ | ⟨_, a, _, _, _⟩ | ⟨_, a, _, _, _⟩
  · exact absurd h hx
  · rw [h] at ax; exact absurd ax S.anc_v_one.1
  · exact p
  · rw [ax] at a; exact absurd a S.hab
  · rw [ax] at a; exact absurd a S.hac
  all_goals (rw [ax] at a; exact absurd a S.had)

theorem phi_armB {x : Fin n} (hx : x ≠ S.u) (ax : anc S.hT S.u x 1 = S.wb) :
    S.phi x = 3 + 8 * G.dist S.u x := by
  rcases S.phi_cases x with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, _, a, _⟩ | ⟨_, _, _, p⟩ | ⟨_, _, a, _⟩ |
      ⟨_, _, a, _, _⟩ | ⟨_, a, _, _, _⟩ | ⟨_, a, _, _, _⟩
  · exact absurd h hx
  · rw [h] at ax; exact absurd ax S.anc_v_one.2.1
  · rw [ax] at a; exact absurd a.symm S.hab
  · exact p
  · rw [ax] at a; exact absurd a S.hbc
  all_goals (rw [ax] at a; exact absurd a S.hbd)

theorem phi_armC {x : Fin n} (hx : x ≠ S.u) (ax : anc S.hT S.u x 1 = S.wc) :
    S.phi x = 4 + 8 * G.dist S.u x := by
  rcases S.phi_cases x with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, _, a, _⟩ | ⟨_, _, a, _⟩ | ⟨_, _, _, p⟩ |
      ⟨_, _, a, _, _⟩ | ⟨_, a, _, _, _⟩ | ⟨_, a, _, _, _⟩
  · exact absurd h hx
  · rw [h] at ax; exact absurd ax S.anc_v_one.2.2
  · rw [ax] at a; exact absurd a.symm S.hac
  · rw [ax] at a; exact absurd a.symm S.hbc
  · exact p
  all_goals (rw [ax] at a; exact absurd a S.hcd)

theorem phi_dpath {x : Fin n} (hx : x ≠ S.u) (ax : anc S.hT S.u x 1 = anc S.hT S.u S.v 1)
    (dx : G.dist S.u x < G.dist S.u S.v) : S.phi x = 5 + 8 * G.dist S.u x := by
  rcases S.phi_cases x with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, _, a, _⟩ | ⟨_, _, a, _⟩ | ⟨_, _, a, _⟩ |
      ⟨_, _, _, _, p⟩ | ⟨_, _, d, _, _⟩ | ⟨_, _, d, _, _⟩
  · exact absurd h hx
  · rw [h] at dx; omega
  · rw [ax] at a; exact absurd a S.anc_v_one.1
  · rw [ax] at a; exact absurd a S.anc_v_one.2.1
  · rw [ax] at a; exact absurd a S.anc_v_one.2.2
  · exact p
  all_goals omega

theorem phi_subE {x : Fin n} (hx : x ≠ S.u) (ax : anc S.hT S.u x 1 = anc S.hT S.u S.v 1)
    (dx : G.dist S.u S.v < G.dist S.u x) (sx : anc S.hT S.u x (G.dist S.u S.v + 1) = S.ce) :
    S.phi x = 6 + 8 * (G.dist S.u x - G.dist S.u S.v) := by
  rcases S.phi_cases x with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, _, a, _⟩ | ⟨_, _, a, _⟩ | ⟨_, _, a, _⟩ |
      ⟨_, _, _, d, _⟩ | ⟨_, _, _, _, p⟩ | ⟨_, _, _, s, _⟩
  · exact absurd h hx
  · rw [h] at dx; omega
  · rw [ax] at a; exact absurd a S.anc_v_one.1
  · rw [ax] at a; exact absurd a S.anc_v_one.2.1
  · rw [ax] at a; exact absurd a S.anc_v_one.2.2
  · omega
  · exact p
  · rw [sx] at s; exact absurd s S.hef

theorem phi_subF {x : Fin n} (hx : x ≠ S.u) (ax : anc S.hT S.u x 1 = anc S.hT S.u S.v 1)
    (dx : G.dist S.u S.v < G.dist S.u x) (sx : anc S.hT S.u x (G.dist S.u S.v + 1) = S.cf) :
    S.phi x = 7 + 8 * (G.dist S.u x - G.dist S.u S.v) := by
  rcases S.phi_cases x with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, _, a, _⟩ | ⟨_, _, a, _⟩ | ⟨_, _, a, _⟩ |
      ⟨_, _, _, d, _⟩ | ⟨_, _, _, s, _⟩ | ⟨_, _, _, _, p⟩
  · exact absurd h hx
  · rw [h] at dx; omega
  · rw [ax] at a; exact absurd a S.anc_v_one.1
  · rw [ax] at a; exact absurd a S.anc_v_one.2.1
  · rw [ax] at a; exact absurd a S.anc_v_one.2.2
  · omega
  · rw [sx] at s; exact absurd s.symm S.hef
  · exact p

theorem phi_inj : Function.Injective S.phi := by
  intro x y h
  rcases S.phi_cases x with ⟨hx, px⟩ | ⟨hx, px⟩ | ⟨xu, xv, ax, px⟩ | ⟨xu, xv, ax, px⟩ |
      ⟨xu, xv, ax, px⟩ | ⟨xu, xv, ax, dx, px⟩ | ⟨xu, ax, dx, sx, px⟩ | ⟨xu, ax, dx, sx, px⟩ <;>
  rcases S.phi_cases y with ⟨hy, py⟩ | ⟨hy, py⟩ | ⟨yu, yv, ay, py⟩ | ⟨yu, yv, ay, py⟩ |
      ⟨yu, yv, ay, py⟩ | ⟨yu, yv, ay, dy, py⟩ | ⟨yu, ay, dy, sy, py⟩ | ⟨yu, ay, dy, sy, py⟩ <;>
  rw [px, py] at h
  all_goals first
    | omega
    | (rw [hx, hy])
    | exact S.arm_uniq (Or.inl rfl) xu yu ax ay (by omega)
    | exact S.arm_uniq (Or.inr (Or.inl rfl)) xu yu ax ay (by omega)
    | exact S.arm_uniq (Or.inr (Or.inr rfl)) xu yu ax ay (by omega)
    | exact S.dpath_uniq xu yu ax ay (le_of_lt dx) (by omega)
    | exact S.sub_uniq (Or.inl rfl) sx sy (by omega) (by omega)
    | exact S.sub_uniq (Or.inr rfl) sx sy (by omega) (by omega)

theorem phi_u : S.phi S.u = 0 := by
  rcases S.phi_cases S.u with ⟨_, p⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩
  · exact p
  · exact absurd h.symm S.huv
  all_goals exact absurd rfl h

theorem phi_v : S.phi S.v = 1 := by
  rcases S.phi_cases S.v with ⟨h, _⟩ | ⟨_, p⟩ | ⟨_, h, _⟩ | ⟨_, h, _⟩ | ⟨_, h, _⟩ | ⟨_, h, _⟩ |
      ⟨_, _, d, _⟩ | ⟨_, _, d, _⟩
  · exact absurd h S.huv
  · exact p
  all_goals first | exact absurd rfl h | omega

theorem tpar_of_depth_one {x : Fin n} (hx : x ≠ S.u) (h1 : G.dist S.u x = 1) :
    tpar S.hT S.u x = S.u := by
  have := (tpar_spec S.hT S.u x hx).2
  exact eq_of_dist_zero S.hT (by omega)

theorem phi_par {x : Fin n} (hx : x ≠ S.u) :
    S.phi (tpar S.hT S.u x) = Tpar (G.dist S.u S.v) (S.phi x) := by
  have dpar := (tpar_spec S.hT S.u x hx).2
  have dv := S.dv_pos
  have dx1 := dist_pos_of_ne S.hT hx
  rcases S.phi_cases x with ⟨h, _⟩ | ⟨hv, px⟩ | ⟨_, _, ax, px⟩ | ⟨_, _, ax, px⟩ |
      ⟨_, _, ax, px⟩ | ⟨_, _, ax, dx, px⟩ | ⟨_, ax, dx, sx, px⟩ | ⟨_, ax, dx, sx, px⟩
  · exact absurd h hx
  · subst hv
    rw [px]
    unfold Tpar dEnd
    rw [if_neg one_ne_zero, if_pos rfl]
    by_cases h2 : 2 ≤ G.dist S.u S.v
    · rw [if_pos h2]
      have hp : tpar S.hT S.u S.v ≠ S.u := S.ne_root_of_pos (by omega)
      rw [S.phi_dpath hp (anc_one_tpar S.hT hx h2) (by omega)]; omega
    · rw [if_neg h2, S.tpar_of_depth_one hx (by omega), S.phi_u]
  · rw [px, Tpar_arm _ 2 _ (by omega) dx1]
    by_cases h2 : 2 ≤ G.dist S.u x
    · rw [if_pos h2]
      have hp : tpar S.hT S.u x ≠ S.u := S.ne_root_of_pos (by omega)
      have ap := anc_one_tpar S.hT hx h2
      rw [ax] at ap
      rw [S.phi_armA hp ap]; omega
    · rw [if_neg h2, S.tpar_of_depth_one hx (by omega), S.phi_u]
      try simp [armRoot]
  · rw [px, Tpar_arm _ 3 _ (by omega) dx1]
    by_cases h2 : 2 ≤ G.dist S.u x
    · rw [if_pos h2]
      have hp : tpar S.hT S.u x ≠ S.u := S.ne_root_of_pos (by omega)
      have ap := anc_one_tpar S.hT hx h2
      rw [ax] at ap
      rw [S.phi_armB hp ap]; omega
    · rw [if_neg h2, S.tpar_of_depth_one hx (by omega), S.phi_u]
      try simp [armRoot]
  · rw [px, Tpar_arm _ 4 _ (by omega) dx1]
    by_cases h2 : 2 ≤ G.dist S.u x
    · rw [if_pos h2]
      have hp : tpar S.hT S.u x ≠ S.u := S.ne_root_of_pos (by omega)
      have ap := anc_one_tpar S.hT hx h2
      rw [ax] at ap
      rw [S.phi_armC hp ap]; omega
    · rw [if_neg h2, S.tpar_of_depth_one hx (by omega), S.phi_u]
      try simp [armRoot]
  · rw [px, Tpar_arm _ 5 _ (by omega) dx1]
    by_cases h2 : 2 ≤ G.dist S.u x
    · rw [if_pos h2]
      have hp : tpar S.hT S.u x ≠ S.u := S.ne_root_of_pos (by omega)
      have ap := anc_one_tpar S.hT hx h2
      rw [ax] at ap
      rw [S.phi_dpath hp ap (by omega)]; omega
    · rw [if_neg h2, S.tpar_of_depth_one hx (by omega), S.phi_u]
      try simp [armRoot]
  · rw [px, Tpar_arm _ 6 _ (by omega) (by omega)]
    have hp : tpar S.hT S.u x ≠ S.u := S.ne_root_of_pos (by omega)
    have ap := anc_one_tpar S.hT hx (by omega)
    rw [ax] at ap
    by_cases h2 : 2 ≤ G.dist S.u x - G.dist S.u S.v
    · rw [if_pos h2]
      have sp := anc_tpar S.hT S.u x hx (j := G.dist S.u S.v + 1) (by omega)
      rw [sx] at sp
      rw [S.phi_subE hp ap (by omega) sp]; omega
    · rw [if_neg h2]
      have : tpar S.hT S.u x = S.v := S.dpath_uniq hp S.huv ap rfl (by omega) (by omega)
      rw [this, S.phi_v]
      try simp [armRoot]
  · rw [px, Tpar_arm _ 7 _ (by omega) (by omega)]
    have hp : tpar S.hT S.u x ≠ S.u := S.ne_root_of_pos (by omega)
    have ap := anc_one_tpar S.hT hx (by omega)
    rw [ax] at ap
    by_cases h2 : 2 ≤ G.dist S.u x - G.dist S.u S.v
    · rw [if_pos h2]
      have sp := anc_tpar S.hT S.u x hx (j := G.dist S.u S.v + 1) (by omega)
      rw [sx] at sp
      rw [S.phi_subF hp ap (by omega) sp]; omega
    · rw [if_neg h2]
      have : tpar S.hT S.u x = S.v := S.dpath_uniq hp S.huv ap rfl (by omega) (by omega)
      rw [this, S.phi_v]
      try simp [armRoot]

end B43Setup
