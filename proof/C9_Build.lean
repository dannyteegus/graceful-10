/-! ## Building the setup from `Branch43`, and the reduction to canonical trees -/

section Build
variable {n : ℕ} {G : SimpleGraph (Fin n)}

theorem tpar_anc (hT : G.IsTree) (u x : Fin n) {j : ℕ} (hj : 1 ≤ j) (hjx : j ≤ G.dist u x) :
    tpar hT u (anc hT u x j) = anc hT u x (j - 1) := by
  unfold anc
  have e : G.dist u x - (j - 1) = (G.dist u x - j) + 1 := by omega
  rw [e, Function.iterate_succ_apply']

theorem nbr_finset (q : Fin n) :
    ∃ N : Finset (Fin n), N.card = Math15.Graceful.degree G q ∧ ∀ z, z ∈ N ↔ G.Adj q z := by
  classical
  refine ⟨(Finset.univ : Finset (Fin n)).filter (G.Adj q), ?_, fun z => by simp⟩
  unfold Math15.Graceful.degree
  rfl

theorem build_setup (hT : G.IsTree) {u v : Fin n} (hb : Math15.Graceful.Branch43 G u v) :
    Nonempty (B43Setup G) := by
  classical
  obtain ⟨huv, hdu, hdv, hdeg⟩ := hb
  have hvu : v ≠ u := Ne.symm huv
  have dv : 1 ≤ G.dist u v := dist_pos_of_ne hT hvu
  have dwd : G.dist u (anc hT u v 1) = 1 := anc_dist hT u v dv
  -- the three other neighbours of u
  obtain ⟨N, hN, hNm⟩ := nbr_finset (G := G) u
  rw [hdu] at hN
  have wdN : anc hT u v 1 ∈ N := (hNm _).2 (anc_one_adj hT hvu)
  have h3 : (N.erase (anc hT u v 1)).card = 3 := by rw [Finset.card_erase_of_mem wdN, hN]
  obtain ⟨wa, wb, wc, hab, hac, hbc, hE⟩ := Finset.card_eq_three.mp h3
  have memE : ∀ z, z ∈ N.erase (anc hT u v 1) ↔ z = wa ∨ z = wb ∨ z = wc := by
    intro z; rw [hE]; simp
  have ha := (memE wa).2 (Or.inl rfl)
  have hb' := (memE wb).2 (Or.inr (Or.inl rfl))
  have hc := (memE wc).2 (Or.inr (Or.inr rfl))
  rw [Finset.mem_erase] at ha hb' hc
  -- the two children of v
  obtain ⟨M, hM, hMm⟩ := nbr_finset (G := G) v
  rw [hdv] at hM
  have pM : tpar hT u v ∈ M := (hMm _).2 (tpar_spec hT u v hvu).1.symm
  have h2 : (M.erase (tpar hT u v)).card = 2 := by rw [Finset.card_erase_of_mem pM, hM]
  obtain ⟨ce, cf, hef, hE2⟩ := Finset.card_eq_two.mp h2
  have memE2 : ∀ z, z ∈ M.erase (tpar hT u v) ↔ z = ce ∨ z = cf := by
    intro z; rw [hE2]; simp
  have child : ∀ c, c ∈ M.erase (tpar hT u v) →
      tpar hT u c = v ∧ c ≠ u ∧ G.dist u c = G.dist u v + 1 := by
    intro c hc
    rw [Finset.mem_erase] at hc
    rcases adj_iff_par hT u ((hMm c).1 hc.2) with ⟨a1, a2, a3⟩ | ⟨_, a2, _⟩
    · exact ⟨a2, a1, a3⟩
    · exact absurd a2.symm hc.1
  have hdegd : ∀ q, G.dist u (anc hT u v 1) ≤ G.dist u q → G.dist u q < G.dist u v →
      anc hT u q (G.dist u (anc hT u v 1)) = anc hT u v 1 →
      Math15.Graceful.degree G q ≤ 2 := by
    intro q h1 h2 _
    apply hdeg q
    · intro e; rw [e, SimpleGraph.dist_self] at h1; omega
    · intro e; rw [e] at h2; omega
  refine ⟨{
    hT := hT, u := u, v := v, wa := wa, wb := wb, wc := wc, ce := ce, cf := cf,
    huv := hvu, hdeg := fun q h1 h2 => hdeg q h1 h2, hbr := ?_,
    hwa := (hNm wa).1 ha.2, hwb := (hNm wb).1 hb'.2, hwc := (hNm wc).1 hc.2,
    hab := hab, hac := hac, hbc := hbc, had := ha.1, hbd := hb'.1, hcd := hc.1,
    hce := child ce ((memE2 ce).2 (Or.inl rfl)), hcf := child cf ((memE2 cf).2 (Or.inr rfl)),
    hef := hef, hsub := ?_ }⟩
  · intro x hx
    have hN1 := (hNm _).2 (anc_one_adj hT hx)
    by_cases e : anc hT u x 1 = anc hT u v 1
    · exact Or.inr (Or.inr (Or.inr e))
    · have := (memE _).1 (Finset.mem_erase.2 ⟨e, hN1⟩)
      rcases this with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
  · intro x hx ax dx
    have dz : G.dist u (anc hT u x (G.dist u v)) = G.dist u v := anc_dist hT u x (le_of_lt dx)
    have zv : anc hT u x (G.dist u v) = v := by
      refine chain_uniq hT u (anc hT u v 1) (G.dist u v) (by omega) hdegd _ v
        (by rw [dwd, dz]; exact dv) (le_of_eq dz) ?_ (by rw [dwd]) dz
      rw [dwd, anc_anc hT u x dv (le_of_lt dx)]; exact ax
    have dy : G.dist u (anc hT u x (G.dist u v + 1)) = G.dist u v + 1 :=
      anc_dist hT u x (by omega)
    have tpy : tpar hT u (anc hT u x (G.dist u v + 1)) = v := by
      rw [tpar_anc hT u x (by omega) (by omega), Nat.add_sub_cancel]; exact zv
    have yu : anc hT u x (G.dist u v + 1) ≠ u := by
      intro e; rw [e, SimpleGraph.dist_self] at dy; omega
    have hadj := (tpar_spec hT u _ yu).1
    rw [tpy] at hadj
    have yM := (hMm _).2 hadj
    have yp : anc hT u x (G.dist u v + 1) ≠ tpar hT u v := by
      intro e
      have := (tpar_spec hT u v hvu).2
      rw [← e, dy] at this; omega
    exact (memE2 _).1 (Finset.mem_erase.2 ⟨yp, yM⟩)

end Build

namespace B43Setup
variable {n : ℕ} {G : SimpleGraph (Fin n)} (S : B43Setup G)

/-- swap the u-arms a and b -/
def swapAB : B43Setup G :=
  { S with
    wa := S.wb, wb := S.wa,
    hbr := fun x hx => by have := S.hbr x hx; tauto,
    hwa := S.hwb, hwb := S.hwa, hab := S.hab.symm, hac := S.hbc, hbc := S.hac,
    had := S.hbd, hbd := S.had }

/-- swap the u-arms b and c -/
def swapBC : B43Setup G :=
  { S with
    wb := S.wc, wc := S.wb,
    hbr := fun x hx => by have := S.hbr x hx; tauto,
    hwb := S.hwc, hwc := S.hwb, hab := S.hac, hac := S.hab, hbc := S.hbc.symm,
    hbd := S.hcd, hcd := S.hbd }

/-- swap the v-arms -/
def swapEF : B43Setup G :=
  { S with
    ce := S.cf, cf := S.ce, hce := S.hcf, hcf := S.hce, hef := S.hef.symm,
    hsub := fun x hx ax dx => by have := S.hsub x hx ax dx; tauto }

theorem swapAB_L : S.swapAB.La = S.Lb ∧ S.swapAB.Lb = S.La ∧ S.swapAB.Lc = S.Lc ∧
    S.swapAB.Le = S.Le ∧ S.swapAB.Lf = S.Lf := ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem swapBC_L : S.swapBC.La = S.La ∧ S.swapBC.Lb = S.Lc ∧ S.swapBC.Lc = S.Lb ∧
    S.swapBC.Le = S.Le ∧ S.swapBC.Lf = S.Lf := ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem swapEF_L : S.swapEF.La = S.La ∧ S.swapEF.Lb = S.Lb ∧ S.swapEF.Lc = S.Lc ∧
    S.swapEF.Le = S.Lf ∧ S.swapEF.Lf = S.Le := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem sortABC (hef : S.Le ≤ S.Lf) :
    ∃ S' : B43Setup G, S'.La ≤ S'.Lb ∧ S'.Lb ≤ S'.Lc ∧ S'.Le ≤ S'.Lf := by
  have p1 := S.swapAB_L
  have p2 := S.swapBC_L
  have p3 := S.swapAB.swapBC_L
  have p4 := S.swapBC.swapAB_L
  have p5 := S.swapAB.swapBC.swapAB_L
  by_cases h1 : S.La ≤ S.Lb <;> by_cases h2 : S.Lb ≤ S.Lc <;> by_cases h3 : S.La ≤ S.Lc
  · exact ⟨S, h1, h2, hef⟩
  · omega
  · exact ⟨S.swapBC, by omega⟩
  · exact ⟨S.swapBC.swapAB, by omega⟩
  · exact ⟨S.swapAB, by omega⟩
  · exact ⟨S.swapAB.swapBC, by omega⟩
  · omega
  · exact ⟨S.swapAB.swapBC.swapAB, by omega⟩

theorem sorted (S : B43Setup G) : ∃ S' : B43Setup G, S'.La ≤ S'.Lb ∧ S'.Lb ≤ S'.Lc ∧ S'.Le ≤ S'.Lf := by
  by_cases h : S.Le ≤ S.Lf
  · exact S.sortABC h
  · exact S.swapEF.sortABC (by rw [S.swapEF_L.2.2.2.1, S.swapEF_L.2.2.2.2]; omega)

theorem L_pos : 1 ≤ S.La ∧ 1 ≤ S.Lb ∧ 1 ≤ S.Lc ∧ 1 ≤ G.dist S.u S.v ∧ 1 ≤ S.Le ∧ 1 ≤ S.Lf :=
  ⟨(S.lenU_spec S.dist_wa).1, (S.lenU_spec S.dist_wb).1, (S.lenU_spec S.dist_wc).1, S.dv_pos,
    (S.lenV_spec S.hce).1, (S.lenV_spec S.hcf).1⟩

end B43Setup

/-- a canonical tree with a graceful labelling of its names -/
def CanonGraceful (a b c d e f : ℕ) : Prop :=
  ∃ P : Pc, P.Grace ∧ (∀ s, s ∈ P.S ↔ s ∈ Tset a b c d e f) ∧
    (∀ x ∈ P.S, ∀ y ∈ P.S, P.R x y ↔ Tadj d x y)

theorem B43Setup.graceful {n : ℕ} {G : SimpleGraph (Fin n)} (S : B43Setup G)
    (h : CanonGraceful S.La S.Lb S.Lc (G.dist S.u S.v) S.Le S.Lf) :
    Math15.Graceful.IsGraceful G := by
  obtain ⟨P, hP, hS, hR⟩ := h
  refine graceful_of_piece P hP S.phi S.phi_inj (fun x => (hS _).2 (S.phi_mem x))
    (fun s hs => S.phi_surj s ((hS s).1 hs)) (fun x y => ?_)
  rw [S.phi_adj, hR _ ((hS _).2 (S.phi_mem x)) _ ((hS _).2 (S.phi_mem y))]

/-- the reduction: it suffices to label every sorted canonical tree -/
theorem target_of_canon (H : ∀ a b c d e f, 1 ≤ a → a ≤ b → b ≤ c → 1 ≤ d → 1 ≤ e → e ≤ f →
    CanonGraceful a b c d e f) : Math15.Graceful.Target10 := by
  intro n G hT ⟨u, v, hb⟩
  obtain ⟨S⟩ := build_setup hT hb
  obtain ⟨S', h1, h2, h3⟩ := S.sorted
  have hp := S'.L_pos
  exact S'.graceful (H _ _ _ _ _ _ hp.1 h1 h2 hp.2.2.2.1 hp.2.2.2.2.1 h3)
