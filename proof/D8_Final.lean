/-! ## Final steps: graceful segments, joins, leaf chains, assembly -/

theorem Tadj_irrefl (d y : ℕ) (hd : 1 ≤ d) : ¬ Tadj d y y := by
  unfold Tadj Tpar dEnd armRoot
  intro h
  rcases h with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> split_ifs at h1 <;> omega

/-- the cross condition for an outward segment on arm `X` -/
theorem cross_out {d X k0 L : ℕ} {S : Finset ℕ} (hX : 2 ≤ X ∧ X ≤ 7)
    (hfresh : ∀ i, i < L → X + 8 * (k0 + 1 + i) ∉ S)
    (hnext : X + 8 * (k0 + L + 1) ∉ S)
    (hd5 : X = 5 → k0 + L + 1 ≤ d) (hv : X = 5 → k0 + L + 1 = d → 1 ∉ S) :
    ∀ p ∈ S, ∀ i, i < L → Tadj d p (X + 8 * (k0 + 1 + i)) →
      p = (if k0 = 0 then armRoot X else X + 8 * k0) ∧ i = 0 := by
  intro p hp i hi h
  rcases (Tadj_arm_iff d X (k0 + 1 + i) p hX (by omega)).mp h with h1 | h1 | ⟨h5, hd, rfl⟩
  · by_cases hi0 : i = 0
    · subst hi0
      refine ⟨?_, rfl⟩
      rw [h1]
      by_cases hk : k0 = 0
      · rw [if_pos (by omega), if_pos hk]
      · rw [if_neg (by omega), if_neg hk]; congr 1
    · exfalso
      rw [if_neg (by omega)] at h1
      exact hfresh (i - 1) (by omega)
        (by rw [show X + 8 * (k0 + 1 + (i - 1)) = p by omega]; exact hp)
  · exfalso
    by_cases hiL : i + 1 < L
    · exact hfresh (i + 1) hiL (by rw [show X + 8 * (k0 + 1 + (i + 1)) = p by omega]; exact hp)
    · exact hnext (by rw [show X + 8 * (k0 + L + 1) = p by omega]; exact hp)
  · exfalso
    have := hd5 h5
    exact hv h5 (by omega) hp

namespace APc
variable {d q : ℕ}

/-- final step: attach a graceful segment on arm `X` (needs only `τ(x) ≤ L - 1`) -/
theorem attachGOut (A : APc d q) (X k0 L : ℕ) (hX : 2 ≤ X ∧ X ≤ 7) (hL : 1 ≤ L)
    (hx : (if k0 = 0 then armRoot X else X + 8 * k0) ∈ A.P.S)
    (hfresh : ∀ i, i < L → X + 8 * (k0 + 1 + i) ∉ A.P.S)
    (hnext : X + 8 * (k0 + L + 1) ∉ A.P.S)
    (hd5 : X = 5 → k0 + L + 1 ≤ d) (hv : X = 5 → k0 + L + 1 = d → 1 ∉ A.P.S)
    (hep : A.tau (if k0 = 0 then armRoot X else X + 8 * k0) ≤ L - 1) :
    ∃ G : Pc, G.Grace ∧ G.R = Tadj d ∧
      (∀ z, z ∈ G.S ↔ z ∈ A.P.S ∨ ∃ i, i < L ∧ X + 8 * (k0 + 1 + i) = z) ∧
      G.E.card = A.P.E.card + L ∧
      (∀ z ∈ A.P.S, G.f z = A.eps z ∨ G.f z = G.E.card - A.eps z) := by
  classical
  set x := (if k0 = 0 then armRoot X else X + 8 * k0) with hxdef
  have hs := segOut d X k0 L hX hL
  have hcross := cross_out (d := d) hX hfresh hnext hd5 hv
  have hfx := A.f_le hx
  have hth := A.hA.2.1
  set tg := if A.P.f x < A.th then L - 1 - A.tau x else A.tau x with htg
  obtain ⟨g, hg, hg0⟩ := epl L tg hL (by rw [htg]; split_ifs <;> omega)
  set nm : ℕ → ℕ := fun i => X + 8 * (k0 + 1 + i) with hnm
  set B := ipathPc (Tadj d) L nm (fun z => z / 8 - (k0 + 1)) g with hB
  have hBg : B.Grace := ipathPc_grace (R := Tadj d) (nm := nm) (pos := fun z => z / 8 - (k0 + 1)) hL
    (Tadj_symm d) hs.inj hs.hpos hs.cons hs.chord hg
  have hBS : ∀ z, z ∈ B.S ↔ ∃ i, i < L ∧ nm i = z := fun z => ipathPc_mem
  have hBE : B.E.card = L - 1 := by
    have h1 := hBg.2.1
    have h2 : B.S.card = L := ipathPc_card_S hs.inj
    omega
  have hBf0 : B.f (nm 0) = g 0 := by
    show g ((X + 8 * (k0 + 1 + 0)) / 8 - (k0 + 1)) = g 0
    congr 1; omega
  have hR : A.P.R = B.R := A.hR
  have hd : Disjoint A.P.S B.S := by
    rw [Finset.disjoint_left]
    intro z hzA hzB
    obtain ⟨i, hi, rfl⟩ := (hBS z).mp hzB
    exact hfresh i hi hzA
  have hw : nm 0 ∈ B.S := (hBS _).mpr ⟨0, by omega, rfl⟩
  have hxw : A.P.R x (nm 0) := by rw [A.hR]; exact hs.xw
  have hcr : ∀ p ∈ A.P.S, ∀ q' ∈ B.S, A.P.R p q' → p = x ∧ q' = nm 0 := by
    intro p hp q' hq' hr
    obtain ⟨i, hi, rfl⟩ := (hBS q').mp hq'
    rw [A.hR] at hr
    obtain ⟨h1, h2⟩ := hcross p hp i hi hr
    exact ⟨h1, by rw [h2]⟩
  have htau : A.tau x = if A.P.f x < A.th then A.th - 1 - A.P.f x else A.P.f x - A.th := rfl
  have hc : (A.P.f x < A.th ∧ B.f (nm 0) + (A.th - 1 - A.P.f x) = B.E.card) ∨
      (A.th ≤ A.P.f x ∧ B.f (nm 0) + A.th = A.P.f x) := by
    rw [hBf0, hg0, hBE, htg]
    by_cases hl : A.P.f x < A.th
    · left; rw [if_pos hl]; rw [htau, if_pos hl] at hep ⊢; omega
    · right; rw [if_neg hl]; rw [htau, if_neg hl]; omega
  have hG := Pc.ifgl A.hA hBg hR hd hx hw hxw hcr hc
  have hGE := Pc.ijoin_card_E (th := A.th) hR A.hA.1.1 hd hx hw hxw hcr
  rw [hBE] at hGE
  refine ⟨Pc.ijoin A.P B A.th x (nm 0), hG, A.hR, ?_, by rw [hGE]; omega, ?_⟩
  · intro z
    show z ∈ A.P.S ∪ B.S ↔ _
    rw [Finset.mem_union, hBS]
  · intro z hz
    have hle := A.f_le hz
    show (Pc.join A.P B A.th x (nm 0)).f z = _ ∨ (Pc.join A.P B A.th x (nm 0)).f z = _
    rw [hGE]
    unfold eps Pc.eps
    by_cases hl : A.P.f z < A.th
    · rw [Pc.join_f_lowA hz hl, if_pos hl]; left; rfl
    · rw [Pc.join_f_highA hz (by omega), if_neg hl, hBE]; right; omega

/-- join an α-piece and a graceful piece along the edge `x - w` -/
theorem joinG (A : APc d q) (B : Pc) (hB : B.Grace) (hBR : B.R = Tadj d) {x w : ℕ}
    (hx : x ∈ A.P.S) (hw : w ∈ B.S) (hxw : Tadj d x w) (hd : Disjoint A.P.S B.S)
    (hcross : ∀ p ∈ A.P.S, ∀ q' ∈ B.S, Tadj d p q' → p = x ∧ q' = w)
    (hlab : B.f w = A.tau x ∨ B.f w = B.E.card - A.tau x) (htb : A.tau x ≤ B.E.card) :
    ∃ G : Pc, G.Grace ∧ G.R = Tadj d ∧ (∀ z, z ∈ G.S ↔ z ∈ A.P.S ∨ z ∈ B.S) ∧
      G.E.card = A.P.E.card + B.E.card + 1 ∧
      (∀ z ∈ A.P.S, G.f z = A.eps z ∨ G.f z = G.E.card - A.eps z) := by
  classical
  have hfx := A.f_le hx
  have hth := A.hA.2.1
  have htau : A.tau x = if A.P.f x < A.th then A.th - 1 - A.P.f x else A.P.f x - A.th := rfl
  have hBw := hB.2.2.2.1 w hw
  -- choose B or its complement
  obtain ⟨B', hB', hB'R, hB'S, hB'E, hc⟩ : ∃ B' : Pc, B'.Grace ∧ B'.R = Tadj d ∧ B'.S = B.S ∧
      B'.E.card = B.E.card ∧
      ((A.P.f x < A.th ∧ B'.f w + (A.th - 1 - A.P.f x) = B'.E.card) ∨
        (A.th ≤ A.P.f x ∧ B'.f w + A.th = A.P.f x)) := by
    by_cases hl : A.P.f x < A.th
    · rw [htau, if_pos hl] at hlab htb
      by_cases h1 : B.f w = B.E.card - (A.th - 1 - A.P.f x)
      · exact ⟨B, hB, hBR, rfl, rfl, Or.inl ⟨hl, by omega⟩⟩
      · have h2 : B.f w = A.th - 1 - A.P.f x := by tauto
        refine ⟨B.cmp, Pc.cmp_grace hB, hBR, rfl, rfl, Or.inl ⟨hl, ?_⟩⟩
        show B.E.card - B.f w + _ = B.cmp.E.card
        rw [Pc.cmp_E]; omega
    · rw [htau, if_neg hl] at hlab htb
      by_cases h1 : B.f w = A.P.f x - A.th
      · exact ⟨B, hB, hBR, rfl, rfl, Or.inr ⟨by omega, by omega⟩⟩
      · have h2 : B.f w = B.E.card - (A.P.f x - A.th) := by tauto
        refine ⟨B.cmp, Pc.cmp_grace hB, hBR, rfl, rfl, Or.inr ⟨by omega, ?_⟩⟩
        show B.E.card - B.f w + _ = _
        omega
  have hR : A.P.R = B'.R := by rw [A.hR, hB'R]
  have hd' : Disjoint A.P.S B'.S := by rw [hB'S]; exact hd
  have hw' : w ∈ B'.S := by rw [hB'S]; exact hw
  have hxw' : A.P.R x w := by rw [A.hR]; exact hxw
  have hcr : ∀ p ∈ A.P.S, ∀ q' ∈ B'.S, A.P.R p q' → p = x ∧ q' = w := by
    intro p hp q' hq' hr
    rw [hB'S] at hq'; rw [A.hR] at hr
    exact hcross p hp q' hq' hr
  have hG := Pc.ifgl A.hA hB' hR hd' hx hw' hxw' hcr hc
  have hGE := Pc.ijoin_card_E (th := A.th) hR A.hA.1.1 hd' hx hw' hxw' hcr
  rw [hB'E] at hGE
  refine ⟨Pc.ijoin A.P B' A.th x w, hG, A.hR, ?_, hGE, ?_⟩
  · intro z
    show z ∈ A.P.S ∪ B'.S ↔ _
    rw [Finset.mem_union, hB'S]
  · intro z hz
    have hle := A.f_le hz
    show (Pc.join A.P B' A.th x w).f z = _ ∨ (Pc.join A.P B' A.th x w).f z = _
    rw [hGE]
    unfold eps Pc.eps
    by_cases hl : A.P.f z < A.th
    · rw [Pc.join_f_lowA hz hl, if_pos hl]; left; rfl
    · rw [Pc.join_f_highA hz (by omega), if_neg hl, hB'E]; right; omega

end APc

/-- the one-vertex α-piece -/
noncomputable def singlePc (d y : ℕ) : Pc where
  S := {y}
  R := Tadj d
  f := fun _ => 0

theorem singlePc_E (d y : ℕ) (hd : 1 ≤ d) : (singlePc d y).E = ∅ := by
  classical
  ext e
  rw [Pc.mem_E]
  simp only [singlePc, Finset.mem_singleton, Finset.notMem_empty, iff_false, not_and]
  intro h1 h2 h3
  omega

theorem singlePc_alpha (d y : ℕ) (hd : 1 ≤ d) : (singlePc d y).Alpha 1 := by
  have hE := singlePc_E d y hd
  refine ⟨⟨Tadj_symm d, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [hE]; simp [singlePc]
  · intro a ha b hb _
    simp only [singlePc, Finset.mem_singleton] at ha hb
    rw [ha, hb]
  · intro a _; rw [hE]; simp [singlePc]
  · intro e he; rw [hE] at he; simp at he
  · rw [hE]; simp
  · intro a ha b hb hr
    simp only [singlePc, Finset.mem_singleton] at ha hb
    rw [ha, hb] at hr
    exact absurd hr (Tadj_irrefl d y hd)

/-- one leaf added at a vertex labeled `0` or `m`; the new leaf gets label `0` -/
theorem leafStep {d : ℕ} (hd : 1 ≤ d) (G : Pc) (hG : G.Grace) (hR : G.R = Tadj d) {z y : ℕ}
    (hz : z ∈ G.S) (hy : y ∉ G.S) (hzy : Tadj d z y) (hcr : ∀ p ∈ G.S, Tadj d p y → p = z)
    (hgood : G.f z = 0 ∨ G.f z = G.E.card) :
    ∃ G' : Pc, G'.Grace ∧ G'.R = Tadj d ∧ (∀ s, s ∈ G'.S ↔ s ∈ G.S ∨ s = y) ∧
      G'.E.card = G.E.card + 1 ∧ G'.f y = 0 := by
  classical
  have hzle := hG.2.2.2.1 z hz
  obtain ⟨B, hB, hBR, hBS, hBE, hBz⟩ : ∃ B : Pc, B.Grace ∧ B.R = Tadj d ∧ B.S = G.S ∧
      B.E.card = G.E.card ∧ B.f z = B.E.card := by
    by_cases h : G.f z = G.E.card
    · exact ⟨G, hG, hR, rfl, rfl, h⟩
    · refine ⟨G.cmp, Pc.cmp_grace hG, hR, rfl, rfl, ?_⟩
      have : G.f z = 0 := by tauto
      show G.E.card - G.f z = G.cmp.E.card
      rw [Pc.cmp_E]; omega
  have hA := singlePc_alpha d y hd
  have hAE : (singlePc d y).E.card = 0 := by rw [singlePc_E d y hd]; rfl
  have hRR : (singlePc d y).R = B.R := by rw [hBR]; rfl
  have hdj : Disjoint (singlePc d y).S B.S := by
    rw [hBS]; simp [singlePc, hy]
  have hyA : y ∈ (singlePc d y).S := by simp [singlePc]
  have hzB : z ∈ B.S := by rw [hBS]; exact hz
  have hyz : (singlePc d y).R y z := Tadj_symm d _ _ hzy
  have hcross : ∀ p ∈ (singlePc d y).S, ∀ q' ∈ B.S, (singlePc d y).R p q' → p = y ∧ q' = z := by
    intro p hp q' hq' hr
    simp only [singlePc, Finset.mem_singleton] at hp
    subst hp
    rw [hBS] at hq'
    exact ⟨rfl, hcr q' hq' (Tadj_symm d _ _ hr)⟩
  have hc : ((singlePc d y).f y < 1 ∧ B.f z + (1 - 1 - (singlePc d y).f y) = B.E.card) ∨
      (1 ≤ (singlePc d y).f y ∧ B.f z + 1 = (singlePc d y).f y) := by
    left; refine ⟨by simp [singlePc], ?_⟩; simp [singlePc]; exact hBz
  have hJ := Pc.ifgl hA hB hRR hdj hyA hzB hyz hcross hc
  have hJE := Pc.ijoin_card_E (th := 1) hRR (Tadj_symm d) hdj hyA hzB hyz hcross
  rw [hAE, hBE] at hJE
  refine ⟨Pc.ijoin (singlePc d y) B 1 y z, hJ, rfl, ?_, by rw [hJE]; omega, ?_⟩
  · intro s
    show s ∈ (singlePc d y).S ∪ B.S ↔ _
    rw [Finset.mem_union, hBS]
    simp [singlePc]; tauto
  · show (Pc.join (singlePc d y) B 1 y z).f y = 0
    rw [Pc.join_f_lowA hyA (by simp [singlePc])]
    rfl

/-- a chain of leaves along arm `X` (positions `k0+1 … k0+L`) from a vertex labeled `0` or `m` -/
theorem leafChain {d : ℕ} (hd : 1 ≤ d) (X : ℕ) (hX : 2 ≤ X ∧ X ≤ 7) :
    ∀ L k0 (G : Pc), G.Grace → G.R = Tadj d →
      (if k0 = 0 then armRoot X else X + 8 * k0) ∈ G.S →
      (G.f (if k0 = 0 then armRoot X else X + 8 * k0) = 0 ∨
        G.f (if k0 = 0 then armRoot X else X + 8 * k0) = G.E.card) →
      (∀ i, i < L → X + 8 * (k0 + 1 + i) ∉ G.S) → X + 8 * (k0 + L + 1) ∉ G.S →
      (X = 5 → k0 + L + 1 ≤ d) → (X = 5 → k0 + L + 1 = d → 1 ∉ G.S) →
      ∃ G' : Pc, G'.Grace ∧ G'.R = Tadj d ∧
        (∀ s, s ∈ G'.S ↔ s ∈ G.S ∨ ∃ i, i < L ∧ X + 8 * (k0 + 1 + i) = s) ∧
        G'.E.card = G.E.card + L := by
  intro L
  induction L with
  | zero =>
    intro k0 G hG hR _ _ _ _ _ _
    exact ⟨G, hG, hR, fun s => by simp, rfl⟩
  | succ L ih =>
    intro k0 G hG hR hz hgood hfresh hnext hd5 hv
    set z := (if k0 = 0 then armRoot X else X + 8 * k0) with hzdef
    set y := X + 8 * (k0 + 1) with hy
    have hyS : y ∉ G.S := by have := hfresh 0 (by omega); simpa using this
    have hzy : Tadj d z y := by
      apply (Tadj_arm_iff d X (k0 + 1) z hX (by omega)).mpr
      left
      by_cases hk : k0 = 0
      · rw [hzdef, if_pos hk, if_pos (by omega)]
      · rw [hzdef, if_neg hk, if_neg (by omega)]; congr 1
    have hcr : ∀ p ∈ G.S, Tadj d p y → p = z := by
      intro p hp h
      have := cross_out (d := d) (L := 1) (k0 := k0) (S := G.S) hX
        (fun i hi => by have := hfresh 0 (by omega); rw [show i = 0 by omega]; simpa using this)
        (by intro h'; by_cases hL : L = 0
            · subst hL; exact hnext (by simpa using h')
            · exact hfresh 1 (by omega) (by rw [show X + 8 * (k0 + 1 + 1) = X + 8 * (k0 + 1 + 1) from rfl]; simpa [show k0 + 1 + 1 = k0 + 2 by omega] using h'))
        (fun h5 => by have := hd5 h5; omega)
        (fun h5 h' => hv h5 (by
            have := hd5 h5
            omega) ) p hp 0 (by omega) (by simpa using h)
      exact this.1
    obtain ⟨G1, hG1, hR1, hS1, hE1, hf1⟩ := leafStep hd G hG hR hz hyS hzy hcr hgood
    obtain ⟨G2, hG2, hR2, hS2, hE2⟩ := ih (k0 + 1) G1 hG1 hR1
      (by rw [if_neg (by omega)]; exact (hS1 _).mpr (Or.inr rfl))
      (by rw [if_neg (by omega)]; exact Or.inl hf1)
      (by
        intro i hi h
        rcases (hS1 _).mp h with h' | h'
        · exact hfresh (i + 1) (by omega) (by rw [show X + 8 * (k0 + 1 + (i + 1)) = X + 8 * (k0 + 1 + 1 + i) by ring]; exact h')
        · omega)
      (by
        intro h
        rcases (hS1 _).mp h with h' | h'
        · exact hnext (by rw [show X + 8 * (k0 + (L + 1) + 1) = X + 8 * (k0 + 1 + L + 1) by ring]; exact h')
        · omega)
      (fun h5 => by have := hd5 h5; omega)
      (fun h5 h' h1 => by
        rcases (hS1 _).mp h1 with h'' | h''
        · exact hv h5 (by omega) h''
        · omega)
    refine ⟨G2, hG2, hR2, ?_, by rw [hE2, hE1]; ring⟩
    intro s
    rw [hS2, hS1]
    constructor
    · rintro ((h | rfl) | ⟨i, hi, rfl⟩)
      · exact Or.inl h
      · exact Or.inr ⟨0, by omega, by rw [hy]⟩
      · exact Or.inr ⟨i + 1, by omega, by ring_nf⟩
    · rintro (h | ⟨i, hi, rfl⟩)
      · exact Or.inl (Or.inl h)
      · by_cases hi0 : i = 0
        · subst hi0; exact Or.inl (Or.inr (by rw [hy]))
        · exact Or.inr ⟨i - 1, by omega, by congr 1; omega⟩

/-- the final assembly -/
theorem canon_of_piece {a b c d e f : ℕ} (G : Pc) (hG : G.Grace) (hR : G.R = Tadj d)
    (hS : ∀ s, s ∈ G.S ↔ s ∈ Tset a b c d e f) : CanonGraceful a b c d e f :=
  ⟨G, hG, hS, fun x _ y _ => by rw [hR]⟩
