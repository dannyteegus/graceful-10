/-! ## The image of φ is the canonical tree -/

namespace B43Setup
variable {n : ℕ} {G : SimpleGraph (Fin n)} (S : B43Setup G)

/-- length of the u-arm through `w` -/
noncomputable def lenU (w : Fin n) : ℕ :=
  ((Finset.univ : Finset (Fin n)).filter (fun x => x ≠ S.u ∧ anc S.hT S.u x 1 = w)).sup
    (fun x => G.dist S.u x)

/-- length of the v-arm through `c` -/
noncomputable def lenV (c : Fin n) : ℕ :=
  ((Finset.univ : Finset (Fin n)).filter (fun x => x ≠ S.u ∧
    anc S.hT S.u x 1 = anc S.hT S.u S.v 1 ∧ G.dist S.u S.v < G.dist S.u x ∧
    anc S.hT S.u x (G.dist S.u S.v + 1) = c)).sup (fun x => G.dist S.u x - G.dist S.u S.v)

theorem le_lenU {w x : Fin n} (hx : x ≠ S.u) (ax : anc S.hT S.u x 1 = w) :
    G.dist S.u x ≤ S.lenU w := by
  unfold lenU
  exact Finset.le_sup (f := fun x => G.dist S.u x) (by simp [hx, ax])

theorem le_lenV {c x : Fin n} (hx : x ≠ S.u) (ax : anc S.hT S.u x 1 = anc S.hT S.u S.v 1)
    (dx : G.dist S.u S.v < G.dist S.u x) (sx : anc S.hT S.u x (G.dist S.u S.v + 1) = c) :
    G.dist S.u x - G.dist S.u S.v ≤ S.lenV c := by
  unfold lenV
  exact Finset.le_sup (f := fun x => G.dist S.u x - G.dist S.u S.v) (by simp [hx, ax, dx, sx])

theorem self_anc_one {w : Fin n} (hw : G.dist S.u w = 1) : anc S.hT S.u w 1 = w := by
  have := anc_self S.hT S.u w
  rw [hw] at this; exact this

theorem lenU_spec {w : Fin n} (hw : G.dist S.u w = 1) :
    1 ≤ S.lenU w ∧ ∃ x, x ≠ S.u ∧ anc S.hT S.u x 1 = w ∧ G.dist S.u x = S.lenU w := by
  have hwu : w ≠ S.u := S.ne_root_of_pos (by omega)
  have hmem : w ∈ (Finset.univ : Finset (Fin n)).filter
      (fun x => x ≠ S.u ∧ anc S.hT S.u x 1 = w) := by
    simp [hwu, S.self_anc_one hw]
  refine ⟨?_, ?_⟩
  · have := S.le_lenU hwu (S.self_anc_one hw); omega
  · obtain ⟨x, hx, hxe⟩ := Finset.exists_mem_eq_sup _ ⟨w, hmem⟩ (fun x => G.dist S.u x)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    exact ⟨x, hx.1, hx.2, by unfold lenU; rw [hxe]⟩

theorem c_props {c : Fin n} (hc : tpar S.hT S.u c = S.v ∧ c ≠ S.u ∧
    G.dist S.u c = G.dist S.u S.v + 1) :
    anc S.hT S.u c 1 = anc S.hT S.u S.v 1 ∧ anc S.hT S.u c (G.dist S.u S.v + 1) = c := by
  obtain ⟨h1, h2, h3⟩ := hc
  refine ⟨?_, ?_⟩
  · have := anc_tpar S.hT S.u c h2 (j := 1) (by have := S.dv_pos; omega)
    rw [h1] at this; exact this.symm
  · have := anc_self S.hT S.u c
    rw [h3] at this; exact this

theorem lenV_spec {c : Fin n} (hc : tpar S.hT S.u c = S.v ∧ c ≠ S.u ∧
    G.dist S.u c = G.dist S.u S.v + 1) :
    1 ≤ S.lenV c ∧ ∃ x, x ≠ S.u ∧ anc S.hT S.u x 1 = anc S.hT S.u S.v 1 ∧
      G.dist S.u S.v < G.dist S.u x ∧ anc S.hT S.u x (G.dist S.u S.v + 1) = c ∧
      G.dist S.u x - G.dist S.u S.v = S.lenV c := by
  obtain ⟨p1, p2⟩ := S.c_props hc
  have hmem : c ∈ (Finset.univ : Finset (Fin n)).filter (fun x => x ≠ S.u ∧
      anc S.hT S.u x 1 = anc S.hT S.u S.v 1 ∧ G.dist S.u S.v < G.dist S.u x ∧
      anc S.hT S.u x (G.dist S.u S.v + 1) = c) := by
    simp [hc.2.1, p1, p2, hc.2.2]
  refine ⟨?_, ?_⟩
  · have := S.le_lenV hc.2.1 p1 (by omega) p2; omega
  · obtain ⟨x, hx, hxe⟩ := Finset.exists_mem_eq_sup _ ⟨c, hmem⟩
      (fun x => G.dist S.u x - G.dist S.u S.v)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    exact ⟨x, hx.1, hx.2.1, hx.2.2.1, hx.2.2.2, by unfold lenV; rw [hxe]⟩

/-- the arm lengths -/
noncomputable def La : ℕ := S.lenU S.wa
noncomputable def Lb : ℕ := S.lenU S.wb
noncomputable def Lc : ℕ := S.lenU S.wc
noncomputable def Le : ℕ := S.lenV S.ce
noncomputable def Lf : ℕ := S.lenV S.cf

theorem phi_mem (x : Fin n) :
    S.phi x ∈ Tset S.La S.Lb S.Lc (G.dist S.u S.v) S.Le S.Lf := by
  rw [mem_Tset]
  rcases S.phi_cases x with ⟨_, px⟩ | ⟨_, px⟩ | ⟨xu, _, ax, px⟩ | ⟨xu, _, ax, px⟩ |
      ⟨xu, _, ax, px⟩ | ⟨xu, _, ax, dx, px⟩ | ⟨xu, ax, dx, sx, px⟩ | ⟨xu, ax, dx, sx, px⟩
  · exact Or.inl px
  · exact Or.inr (Or.inl px)
  · have := S.le_lenU xu ax
    exact Or.inr (Or.inr ⟨2, G.dist S.u x, by omega, by omega, dist_pos_of_ne S.hT xu,
      by rw [armLen_2]; exact this, px⟩)
  · have := S.le_lenU xu ax
    exact Or.inr (Or.inr ⟨3, G.dist S.u x, by omega, by omega, dist_pos_of_ne S.hT xu,
      by rw [armLen_3]; exact this, px⟩)
  · have := S.le_lenU xu ax
    exact Or.inr (Or.inr ⟨4, G.dist S.u x, by omega, by omega, dist_pos_of_ne S.hT xu,
      by rw [armLen_4]; exact this, px⟩)
  · exact Or.inr (Or.inr ⟨5, G.dist S.u x, by omega, by omega, dist_pos_of_ne S.hT xu,
      by rw [armLen_5]; omega, px⟩)
  · have := S.le_lenV xu ax dx sx
    exact Or.inr (Or.inr ⟨6, G.dist S.u x - G.dist S.u S.v, by omega, by omega, by omega,
      by rw [armLen_6]; exact this, px⟩)
  · have := S.le_lenV xu ax dx sx
    exact Or.inr (Or.inr ⟨7, G.dist S.u x - G.dist S.u S.v, by omega, by omega, by omega,
      by rw [armLen_7]; exact this, px⟩)

/-- a u-arm vertex at each depth up to the arm length -/
theorem uarm_at {w : Fin n} (hw : G.dist S.u w = 1) {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ S.lenU w) :
    ∃ y, y ≠ S.u ∧ anc S.hT S.u y 1 = w ∧ G.dist S.u y = k := by
  obtain ⟨_, x, xu, ax, dx⟩ := S.lenU_spec hw
  refine ⟨anc S.hT S.u x k, S.ne_root_of_pos ?_, ?_, ?_⟩
  · rw [anc_dist S.hT S.u x (by omega)]; exact hk1
  · rw [anc_anc S.hT S.u x hk1 (by omega)]; exact ax
  · exact anc_dist S.hT S.u x (by omega)

theorem varm_at {c : Fin n} (hc : tpar S.hT S.u c = S.v ∧ c ≠ S.u ∧
    G.dist S.u c = G.dist S.u S.v + 1) {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ S.lenV c) :
    ∃ y, y ≠ S.u ∧ anc S.hT S.u y 1 = anc S.hT S.u S.v 1 ∧
      G.dist S.u S.v < G.dist S.u y ∧ anc S.hT S.u y (G.dist S.u S.v + 1) = c ∧
      G.dist S.u y = G.dist S.u S.v + k := by
  obtain ⟨_, x, xu, ax, dx, sx, ex⟩ := S.lenV_spec hc
  have dv := S.dv_pos
  have hd : G.dist S.u (anc S.hT S.u x (G.dist S.u S.v + k)) = G.dist S.u S.v + k :=
    anc_dist S.hT S.u x (by omega)
  refine ⟨anc S.hT S.u x (G.dist S.u S.v + k), S.ne_root_of_pos (by omega), ?_, by omega, ?_, hd⟩
  · rw [anc_anc S.hT S.u x (by omega) (by omega)]; exact ax
  · rw [anc_anc S.hT S.u x (by omega) (by omega)]; exact sx

theorem phi_surj (s : ℕ) (hs : s ∈ Tset S.La S.Lb S.Lc (G.dist S.u S.v) S.Le S.Lf) :
    ∃ x, S.phi x = s := by
  rw [mem_Tset] at hs
  rcases hs with rfl | rfl | ⟨X, k, h2, h7, hk1, hk, rfl⟩
  · exact ⟨S.u, S.phi_u⟩
  · exact ⟨S.v, S.phi_v⟩
  have hX : X = 2 ∨ X = 3 ∨ X = 4 ∨ X = 5 ∨ X = 6 ∨ X = 7 := by omega
  rcases hX with rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨y, yu, ay, dy⟩ := S.uarm_at S.dist_wa hk1 (by rw [armLen_2] at hk; exact hk)
    exact ⟨y, by rw [S.phi_armA yu ay, dy]⟩
  · obtain ⟨y, yu, ay, dy⟩ := S.uarm_at S.dist_wb hk1 (by rw [armLen_3] at hk; exact hk)
    exact ⟨y, by rw [S.phi_armB yu ay, dy]⟩
  · obtain ⟨y, yu, ay, dy⟩ := S.uarm_at S.dist_wc hk1 (by rw [armLen_4] at hk; exact hk)
    exact ⟨y, by rw [S.phi_armC yu ay, dy]⟩
  · rw [armLen_5] at hk
    have hkd : k ≤ G.dist S.u S.v := by omega
    have yd := anc_dist S.hT S.u S.v hkd
    refine ⟨anc S.hT S.u S.v k, ?_⟩
    rw [S.phi_dpath (S.ne_root_of_pos (by omega)) (anc_anc S.hT S.u S.v hk1 hkd) (by omega), yd]
  · obtain ⟨y, yu, ay, dy, sy, ey⟩ := S.varm_at S.hce hk1 (by rw [armLen_6] at hk; exact hk)
    exact ⟨y, by rw [S.phi_subE yu ay dy sy, ey]; omega⟩
  · obtain ⟨y, yu, ay, dy, sy, ey⟩ := S.varm_at S.hcf hk1 (by rw [armLen_7] at hk; exact hk)
    exact ⟨y, by rw [S.phi_subF yu ay dy sy, ey]; omega⟩

theorem phi_ne_zero {x : Fin n} (hx : x ≠ S.u) : S.phi x ≠ 0 := by
  intro e; apply hx; apply S.phi_inj; rw [e, S.phi_u]

theorem phi_adj (x y : Fin n) : G.Adj x y ↔ Tadj (G.dist S.u S.v) (S.phi x) (S.phi y) := by
  constructor
  · intro h
    rcases nbr_cases S.hT (u := S.u) h with ⟨hp, hy, _⟩ | ⟨hx, hp, _⟩
    · exact Or.inr ⟨S.phi_ne_zero hy, by rw [← S.phi_par hy, hp]⟩
    · exact Or.inl ⟨S.phi_ne_zero hx, by rw [← S.phi_par hx, hp]⟩
  · rintro (⟨h0, hp⟩ | ⟨h0, hp⟩)
    · have hx : x ≠ S.u := by intro e; rw [e, S.phi_u] at h0; exact h0 rfl
      rw [← S.phi_par hx] at hp
      rw [← S.phi_inj hp]; exact (tpar_spec S.hT S.u x hx).1.symm
    · have hy : y ≠ S.u := by intro e; rw [e, S.phi_u] at h0; exact h0 rfl
      rw [← S.phi_par hy] at hp
      rw [← S.phi_inj hp]; exact (tpar_spec S.hT S.u y hy).1

end B43Setup
