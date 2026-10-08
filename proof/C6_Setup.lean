/-! ## Setup data for a Branch43 tree -/

/-- the branch data of a Branch43 tree rooted at `u` -/
structure B43Setup {n : ℕ} (G : SimpleGraph (Fin n)) where
  hT : G.IsTree
  u : Fin n
  v : Fin n
  wa : Fin n
  wb : Fin n
  wc : Fin n
  ce : Fin n
  cf : Fin n
  huv : v ≠ u
  hdeg : ∀ q, q ≠ u → q ≠ v → Math15.Graceful.degree G q ≤ 2
  /-- every non-root vertex lies in exactly one of the four branches -/
  hbr : ∀ x, x ≠ u → anc hT u x 1 = wa ∨ anc hT u x 1 = wb ∨ anc hT u x 1 = wc ∨
    anc hT u x 1 = anc hT u v 1
  hwa : G.Adj u wa
  hwb : G.Adj u wb
  hwc : G.Adj u wc
  hab : wa ≠ wb
  hac : wa ≠ wc
  hbc : wb ≠ wc
  had : wa ≠ anc hT u v 1
  hbd : wb ≠ anc hT u v 1
  hcd : wc ≠ anc hT u v 1
  hce : tpar hT u ce = v ∧ ce ≠ u ∧ G.dist u ce = G.dist u v + 1
  hcf : tpar hT u cf = v ∧ cf ≠ u ∧ G.dist u cf = G.dist u v + 1
  hef : ce ≠ cf
  /-- every vertex below `v` lies in the subtree of `ce` or `cf` -/
  hsub : ∀ x, x ≠ u → anc hT u x 1 = anc hT u v 1 → G.dist u v < G.dist u x →
    anc hT u x (G.dist u v + 1) = ce ∨ anc hT u x (G.dist u v + 1) = cf

namespace B43Setup
variable {n : ℕ} {G : SimpleGraph (Fin n)} (S : B43Setup G)

theorem dist_wa : G.dist S.u S.wa = 1 := (nbr_root_depth S.hT S.hwa).1
theorem dist_wb : G.dist S.u S.wb = 1 := (nbr_root_depth S.hT S.hwb).1
theorem dist_wc : G.dist S.u S.wc = 1 := (nbr_root_depth S.hT S.hwc).1

theorem dv_pos : 1 ≤ G.dist S.u S.v := dist_pos_of_ne S.hT S.huv

theorem ne_root_of_pos {x : Fin n} (h : 1 ≤ G.dist S.u x) : x ≠ S.u := by
  intro e; rw [e, SimpleGraph.dist_self] at h; omega

/-- uniqueness in the three u-arms -/
theorem arm_uniq {w : Fin n} (hw : w = S.wa ∨ w = S.wb ∨ w = S.wc) {x y : Fin n}
    (hx : x ≠ S.u) (hy : y ≠ S.u) (ax : anc S.hT S.u x 1 = w) (ay : anc S.hT S.u y 1 = w)
    (hxy : G.dist S.u x = G.dist S.u y) : x = y := by
  have dw : G.dist S.u w = 1 := by
    rcases hw with rfl | rfl | rfl
    · exact S.dist_wa
    · exact S.dist_wb
    · exact S.dist_wc
  have hwd : w ≠ anc S.hT S.u S.v 1 := by
    rcases hw with rfl | rfl | rfl
    · exact S.had
    · exact S.hbd
    · exact S.hcd
  refine chain_uniq S.hT S.u w (G.dist S.u x + 1) (by omega) ?_ x y (by rw [dw]; exact dist_pos_of_ne S.hT hx)
    (by omega) (by rw [dw]; exact ax) (by rw [dw]; exact ay) hxy
  intro q h1 _ h3
  rw [dw] at h1 h3
  apply S.hdeg q (S.ne_root_of_pos h1)
  intro e; rw [e] at h3; exact hwd h3.symm

/-- uniqueness on the u–v path (depths ≤ dist u v) -/
theorem dpath_uniq {x y : Fin n} (hx : x ≠ S.u) (hy : y ≠ S.u)
    (ax : anc S.hT S.u x 1 = anc S.hT S.u S.v 1) (ay : anc S.hT S.u y 1 = anc S.hT S.u S.v 1)
    (hxv : G.dist S.u x ≤ G.dist S.u S.v) (hxy : G.dist S.u x = G.dist S.u y) : x = y := by
  set wd := anc S.hT S.u S.v 1 with hwd
  have dw : G.dist S.u wd = 1 := anc_dist S.hT S.u S.v S.dv_pos
  refine chain_uniq S.hT S.u wd (G.dist S.u S.v) (by omega) ?_ x y
    (by rw [dw]; exact dist_pos_of_ne S.hT hx) hxv (by rw [dw]; exact ax) (by rw [dw]; exact ay) hxy
  intro q h1 h2 _
  rw [dw] at h1
  apply S.hdeg q (S.ne_root_of_pos h1)
  intro e; rw [e] at h2; omega

/-- below `v`, the ancestor at depth `dist u v` is `v` -/
theorem anc_v {x : Fin n} (hx : x ≠ S.u) (ax : anc S.hT S.u x 1 = anc S.hT S.u S.v 1)
    (hxv : G.dist S.u S.v ≤ G.dist S.u x) : anc S.hT S.u x (G.dist S.u S.v) = S.v := by
  have h1 := anc_dist S.hT S.u x hxv
  refine S.dpath_uniq (S.ne_root_of_pos (by rw [h1]; exact S.dv_pos)) S.huv ?_ rfl (le_of_eq h1) h1
  rw [anc_anc S.hT S.u x (by have := S.dv_pos; omega) hxv]; exact ax

/-- uniqueness in the two v-subtrees -/
theorem sub_uniq {w : Fin n} (hw : w = S.ce ∨ w = S.cf) {x y : Fin n}
    (ax : anc S.hT S.u x (G.dist S.u S.v + 1) = w) (ay : anc S.hT S.u y (G.dist S.u S.v + 1) = w)
    (hx : G.dist S.u S.v + 1 ≤ G.dist S.u x) (hxy : G.dist S.u x = G.dist S.u y) : x = y := by
  have dw : G.dist S.u w = G.dist S.u S.v + 1 := by
    rcases hw with rfl | rfl
    · exact S.hce.2.2
    · exact S.hcf.2.2
  refine chain_uniq S.hT S.u w (G.dist S.u x + 1) (by have := S.dv_pos; omega) ?_ x y
    (by rw [dw]; exact hx) (by omega) (by rw [dw]; exact ax) (by rw [dw]; exact ay) hxy
  intro q h1 _ _
  rw [dw] at h1
  apply S.hdeg q (S.ne_root_of_pos (by have := S.dv_pos; omega))
  intro e; rw [e] at h1; omega

end B43Setup
