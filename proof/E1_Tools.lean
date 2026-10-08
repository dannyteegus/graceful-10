/-! ## Tools for the constructions -/

theorem exists_out_iff (X k0 L z : ℕ) (hX : X < 8) :
    (∃ i, i < L ∧ X + 8 * (k0 + 1 + i) = z) ↔ (z % 8 = X ∧ k0 + 1 ≤ z / 8 ∧ z / 8 ≤ k0 + L) := by
  constructor
  · rintro ⟨i, hi, rfl⟩; omega
  · intro h; exact ⟨z / 8 - (k0 + 1), by omega, by omega⟩

theorem exists_in_iff (k0 L z : ℕ) (hk : L ≤ k0) :
    (∃ i, i < L ∧ 5 + 8 * (k0 - i) = z) ↔ (z % 8 = 5 ∧ k0 + 1 - L ≤ z / 8 ∧ z / 8 ≤ k0) := by
  constructor
  · rintro ⟨i, hi, rfl⟩; omega
  · intro h; exact ⟨k0 - z / 8, by omega, by omega⟩

theorem zz_peps (n i : ℕ) (hi : i < n) : peps n (zz n) i = i / 2 := by
  unfold peps zz; split_ifs <;> omega

theorem zz_ptau (n i : ℕ) (hi : i < n) :
    ptau n (zz n) i = if i % 2 = 0 then (n - 1) / 2 - i / 2 else n - 1 - i / 2 - (n - 1) / 2 - 1 := by
  unfold ptau zz; split_ifs <;> omega

/-- the vertex at position `i` of arm `X` (position `0` = the root) -/
def anode (X i : ℕ) : ℕ := if i = 0 then armRoot X else X + 8 * i

theorem armRoot_le (X : ℕ) : armRoot X ≤ 1 := by unfold armRoot; split_ifs <;> omega

/-- a start piece: root plus arm `X` up to position `x`, labeled by an α-path labeling -/
theorem startArm (d X x : ℕ) (hd : 1 ≤ d) (hX : 2 ≤ X ∧ X ≤ 7) (Lab : ℕ → ℕ)
    (hLab : PathAlpha (x + 1) Lab (x / 2)) (h0 : Lab 0 ≤ x / 2)
    (hd5 : X = 5 → x + 1 ≤ d) :
    ∃ A : APc d (par d (armRoot X)),
      (∀ z, z ∈ A.P.S ↔ z = armRoot X ∨ (z % 8 = X ∧ 1 ≤ z / 8 ∧ z / 8 ≤ x)) ∧ A.P.E.card = x ∧
      (∀ i, i ≤ x → A.eps (anode X i) = peps (x + 1) Lab i) ∧
      (∀ i, i ≤ x → A.tau (anode X i) = ptau (x + 1) Lab i) := by
  have hr := armRoot_le X
  have hnm0 : anode X 0 = armRoot X := by simp [anode]
  have hpar0 : ∀ i, 1 ≤ i → par d (X + 8 * i) = (par d (armRoot X) + i) % 2 := by
    intro i hi
    rw [par_arm d X i hX hi]
    unfold armRoot
    split_ifs with h1 h2 h2
    · omega
    · rw [par_one]; omega
    · rw [par_zero]; omega
    · omega
  have hlab : (x + 1 - 1) / 2 = x / 2 := by omega
  rw [← hlab] at hLab h0
  obtain ⟨A, hS, hE, heps, htau⟩ := startPath d (x + 1) (anode X)
    (fun z => if z = armRoot X then 0 else z / 8) Lab (by omega)
    (by intro i j _ _ e; unfold anode at e; split_ifs at e <;> omega)
    (by
      intro i _
      unfold anode
      split_ifs <;> omega)
    (by
      intro i hi
      unfold anode
      rw [if_neg (show i + 1 ≠ 0 by omega)]
      apply (Tadj_arm_iff d X (i + 1) _ hX (by omega)).mpr
      left
      by_cases h : i = 0
      · rw [if_pos h, if_pos (by omega)]
      · rw [if_neg h, if_neg (by omega)]; congr 1)
    (by
      intro i j hi hj h
      unfold anode at h
      by_cases hj0 : j = 0
      · rw [if_pos hj0] at h
        by_cases hi0 : i = 0
        · rw [if_pos hi0] at h; exact absurd h (Tadj_irrefl d _ hd)
        · rw [if_neg hi0] at h
          rcases (Tadj_arm_iff d X i _ hX (by omega)).mp (Tadj_symm d _ _ h) with h1 | h1 | ⟨h5, _, h1⟩
          · split_ifs at h1 <;> omega
          · unfold armRoot at h1; split_ifs at h1 <;> omega
          · unfold armRoot at h1; rw [if_pos (by omega)] at h1; omega
      · rw [if_neg hj0] at h
        rcases (Tadj_arm_iff d X j _ hX (by omega)).mp h with h1 | h1 | ⟨h5, _, h1⟩
        · split_ifs at h1 with h2 h3 h3
          · omega
          · unfold armRoot at h1; split_ifs at h1 <;> omega
          · unfold armRoot at h1; split_ifs at h1 <;> omega
          · omega
        · split_ifs at h1 <;> [skip; omega]
          unfold armRoot at h1; split_ifs at h1 <;> omega
        · split_ifs at h1
          · unfold armRoot at h1; rw [if_pos (by omega)] at h1; omega
          · omega)
    (by
      intro i hi
      rw [hnm0]
      unfold anode
      by_cases h : i = 0
      · rw [if_pos h, h]; have := par_le_one d (armRoot X); omega
      · rw [if_neg h]; exact hpar0 i (by omega))
    hLab h0
  refine ⟨A, ?_, by rw [hE]; omega, fun i hi => heps i (by omega), fun i hi => htau i (by omega)⟩
  intro z
  rw [hS]
  constructor
  · rintro ⟨i, hi, rfl⟩
    unfold anode
    split_ifs with h
    · left; rfl
    · right; omega
  · rintro (rfl | h)
    · exact ⟨0, by omega, by simp [anode]⟩
    · refine ⟨z / 8, by omega, ?_⟩
      unfold anode
      rw [if_neg (by omega)]
      omega

/-- change the parity index of an α-piece along an equation -/
def APc.recast {d q q' : ℕ} (A : APc d q) (h : q = q') : APc d q' :=
  ⟨A.P, A.th, A.hR, A.hA, fun z hz => by rw [← h]; exact A.hlow z hz, h ▸ A.hq⟩

theorem APc.recast_P {d q q' : ℕ} (A : APc d q) (h : q = q') : (A.recast h).P = A.P := rfl
theorem APc.recast_eps {d q q' : ℕ} (A : APc d q) (h : q = q') (z : ℕ) :
    (A.recast h).eps z = A.eps z := rfl
theorem APc.recast_tau {d q q' : ℕ} (A : APc d q) (h : q = q') (z : ℕ) :
    (A.recast h).tau z = A.tau z := rfl

namespace APc
variable {d q : ℕ}

/-- attach an α-EPL segment along arm `X` at its root -/
theorem attachRoot (A : APc d q) (X L : ℕ) (hX : 2 ≤ X ∧ X ≤ 7) (hL : 1 ≤ L)
    (hx : armRoot X ∈ A.P.S) (hfresh : ∀ i, i < L → X + 8 * (1 + i) ∉ A.P.S)
    (hnext : X + 8 * (L + 1) ∉ A.P.S)
    (hd5 : X = 5 → L + 1 ≤ d) (hv : X = 5 → L + 1 = d → 1 ∉ A.P.S)
    (hok : AeplOK L (A.tau (armRoot X))) :
    ∃ B : APc d q, (∀ z, z ∈ B.P.S ↔ z ∈ A.P.S ∨ (z % 8 = X ∧ 1 ≤ z / 8 ∧ z / 8 ≤ L)) ∧
      B.P.E.card = A.P.E.card + L ∧
      (∀ z ∈ A.P.S, B.eps z = A.eps z) ∧
      (∀ z ∈ A.P.S, B.tau z = A.tau z + (L + (par d z + par d (armRoot X)) % 2) / 2) ∧
      B.tau (X + 8 * L) = A.tau (armRoot X) := by
  obtain ⟨B, h1, h2, h3, h4, h5⟩ := A.attachOut X 0 L hX hL (by rw [if_pos rfl]; exact hx)
    (by intro i hi; rw [show 0 + 1 + i = 1 + i by ring]; exact hfresh i hi)
    (by rw [show 0 + L + 1 = L + 1 by ring]; exact hnext)
    (fun h => by have := hd5 h; omega) (fun h e => hv h (by omega))
    (by rw [if_pos rfl]; exact hok)
  refine ⟨B, fun z => by rw [h1, exists_out_iff X 0 L z (by omega), zero_add, zero_add], h2, h3, ?_, ?_⟩
  · intro z hz; rw [h4 z hz, if_pos rfl]
  · rw [show X + 8 * L = X + 8 * (0 + L) by ring, h5, if_pos rfl]

/-- attach an α-EPL segment along arm `X` at position `k ≥ 1` -/
theorem attachArm (A : APc d q) (X k L : ℕ) (hX : 2 ≤ X ∧ X ≤ 7) (hk : 1 ≤ k) (hL : 1 ≤ L)
    (hx : X + 8 * k ∈ A.P.S) (hfresh : ∀ i, i < L → X + 8 * (k + 1 + i) ∉ A.P.S)
    (hnext : X + 8 * (k + L + 1) ∉ A.P.S)
    (hd5 : X = 5 → k + L + 1 ≤ d) (hv : X = 5 → k + L + 1 = d → 1 ∉ A.P.S)
    (hok : AeplOK L (A.tau (X + 8 * k))) :
    ∃ B : APc d q, (∀ z, z ∈ B.P.S ↔ z ∈ A.P.S ∨ (z % 8 = X ∧ k + 1 ≤ z / 8 ∧ z / 8 ≤ k + L)) ∧
      B.P.E.card = A.P.E.card + L ∧
      (∀ z ∈ A.P.S, B.eps z = A.eps z) ∧
      (∀ z ∈ A.P.S, B.tau z = A.tau z + (L + (par d z + par d (X + 8 * k)) % 2) / 2) ∧
      B.tau (X + 8 * (k + L)) = A.tau (X + 8 * k) := by
  have hk0 : k ≠ 0 := by omega
  obtain ⟨B, h1, h2, h3, h4, h5⟩ := A.attachOut X k L hX hL (by rw [if_neg hk0]; exact hx)
    hfresh hnext hd5 hv (by rw [if_neg hk0]; exact hok)
  refine ⟨B, fun z => by rw [h1, exists_out_iff X k L z (by omega)], h2, h3, ?_, ?_⟩
  · intro z hz; rw [h4 z hz, if_neg hk0]
  · rw [h5, if_neg hk0]

/-- final graceful segment along arm `X` at its root -/
theorem attachGRoot (A : APc d q) (X L : ℕ) (hX : 2 ≤ X ∧ X ≤ 7) (hL : 1 ≤ L)
    (hx : armRoot X ∈ A.P.S) (hfresh : ∀ i, i < L → X + 8 * (1 + i) ∉ A.P.S)
    (hnext : X + 8 * (L + 1) ∉ A.P.S)
    (hd5 : X = 5 → L + 1 ≤ d) (hv : X = 5 → L + 1 = d → 1 ∉ A.P.S)
    (hep : A.tau (armRoot X) ≤ L - 1) :
    ∃ G : Pc, G.Grace ∧ G.R = Tadj d ∧
      (∀ z, z ∈ G.S ↔ z ∈ A.P.S ∨ (z % 8 = X ∧ 1 ≤ z / 8 ∧ z / 8 ≤ L)) ∧
      G.E.card = A.P.E.card + L ∧
      (∀ z ∈ A.P.S, G.f z = A.eps z ∨ G.f z = G.E.card - A.eps z) := by
  obtain ⟨G, h1, h2, h3, h4, h5⟩ := A.attachGOut X 0 L hX hL (by rw [if_pos rfl]; exact hx)
    (by intro i hi; rw [show 0 + 1 + i = 1 + i by ring]; exact hfresh i hi)
    (by rw [show 0 + L + 1 = L + 1 by ring]; exact hnext)
    (fun h => by have := hd5 h; omega) (fun h e => hv h (by omega))
    (by rw [if_pos rfl]; exact hep)
  exact ⟨G, h1, h2, fun z => by rw [h3, exists_out_iff X 0 L z (by omega), zero_add, zero_add], h4, h5⟩

/-- final graceful segment along arm `X` at position `k ≥ 1` -/
theorem attachGArm (A : APc d q) (X k L : ℕ) (hX : 2 ≤ X ∧ X ≤ 7) (hk : 1 ≤ k) (hL : 1 ≤ L)
    (hx : X + 8 * k ∈ A.P.S) (hfresh : ∀ i, i < L → X + 8 * (k + 1 + i) ∉ A.P.S)
    (hnext : X + 8 * (k + L + 1) ∉ A.P.S)
    (hd5 : X = 5 → k + L + 1 ≤ d) (hv : X = 5 → k + L + 1 = d → 1 ∉ A.P.S)
    (hep : A.tau (X + 8 * k) ≤ L - 1) :
    ∃ G : Pc, G.Grace ∧ G.R = Tadj d ∧
      (∀ z, z ∈ G.S ↔ z ∈ A.P.S ∨ (z % 8 = X ∧ k + 1 ≤ z / 8 ∧ z / 8 ≤ k + L)) ∧
      G.E.card = A.P.E.card + L ∧
      (∀ z ∈ A.P.S, G.f z = A.eps z ∨ G.f z = G.E.card - A.eps z) := by
  have hk0 : k ≠ 0 := by omega
  obtain ⟨G, h1, h2, h3, h4, h5⟩ := A.attachGOut X k L hX hL (by rw [if_neg hk0]; exact hx)
    hfresh hnext hd5 hv (by rw [if_neg hk0]; exact hep)
  exact ⟨G, h1, h2, fun z => by rw [h3, exists_out_iff X k L z (by omega)], h4, h5⟩

/-- attach an α-EPL segment on the `d`-path at `v`: positions `d-1, …, d-L` -/
theorem attachDV (A : APc d q) (L : ℕ) (hL : 1 ≤ L) (hLd : L + 1 ≤ d)
    (hx : 1 ∈ A.P.S) (hfresh : ∀ i, i < L → 5 + 8 * (d - 1 - i) ∉ A.P.S)
    (hnext0 : d - 1 = L → 0 ∉ A.P.S) (hnext : L < d - 1 → 5 + 8 * (d - 1 - L) ∉ A.P.S)
    (hbeyond : 5 + 8 * d ∉ A.P.S)
    (hok : AeplOK L (A.tau 1)) :
    ∃ B : APc d q, (∀ z, z ∈ B.P.S ↔ z ∈ A.P.S ∨ (z % 8 = 5 ∧ d - L ≤ z / 8 ∧ z / 8 ≤ d - 1)) ∧
      B.P.E.card = A.P.E.card + L ∧
      (∀ z ∈ A.P.S, B.eps z = A.eps z) ∧
      (∀ z ∈ A.P.S, B.tau z = A.tau z + (L + (par d z + par d 1) % 2) / 2) ∧
      B.tau (5 + 8 * (d - L)) = A.tau 1 := by
  have hv : d - 1 + 1 = d := by omega
  obtain ⟨B, h1, h2, h3, h4, h5⟩ := A.attachIn (d - 1) L hL (by omega) (by omega)
    (by rw [if_pos hv]; exact hx) hfresh hnext0 hnext (fun _ => hbeyond)
    (by rw [if_pos hv]; exact hok)
  refine ⟨B, fun z => by rw [h1, exists_in_iff (d - 1) L z (by omega), show d - 1 + 1 - L = d - L by omega], h2, h3, ?_, ?_⟩
  · intro z hz; rw [h4 z hz, if_pos hv]
  · rw [show d - L = d - 1 + 1 - L by omega, h5, if_pos hv]

/-- attach an α-EPL segment on the `d`-path at position `k+1` going toward `u`:
positions `k, …, k-L+1` -/
theorem attachDD (A : APc d q) (k L : ℕ) (hL : 1 ≤ L) (hk : L ≤ k) (hkd : k + 2 ≤ d)
    (hx : 5 + 8 * (k + 1) ∈ A.P.S) (hfresh : ∀ i, i < L → 5 + 8 * (k - i) ∉ A.P.S)
    (hnext0 : k = L → 0 ∉ A.P.S) (hnext : L < k → 5 + 8 * (k - L) ∉ A.P.S)
    (hok : AeplOK L (A.tau (5 + 8 * (k + 1)))) :
    ∃ B : APc d q, (∀ z, z ∈ B.P.S ↔ z ∈ A.P.S ∨ (z % 8 = 5 ∧ k + 1 - L ≤ z / 8 ∧ z / 8 ≤ k)) ∧
      B.P.E.card = A.P.E.card + L ∧
      (∀ z ∈ A.P.S, B.eps z = A.eps z) ∧
      (∀ z ∈ A.P.S, B.tau z = A.tau z + (L + (par d z + par d (5 + 8 * (k + 1))) % 2) / 2) ∧
      B.tau (5 + 8 * (k + 1 - L)) = A.tau (5 + 8 * (k + 1)) := by
  have hv : k + 1 ≠ d := by omega
  obtain ⟨B, h1, h2, h3, h4, h5⟩ := A.attachIn k L hL hk (by omega)
    (by rw [if_neg hv]; exact hx) hfresh hnext0 hnext (fun h => absurd h hv)
    (by rw [if_neg hv]; exact hok)
  refine ⟨B, fun z => by rw [h1, exists_in_iff k L z hk], h2, h3, ?_, ?_⟩
  · intro z hz; rw [h4 z hz, if_neg hv]
  · rw [h5, if_neg hv]

end APc
