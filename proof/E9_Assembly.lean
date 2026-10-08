/-! ## Assembly: Tset membership, cutting the `d`-path, joining two sides -/

theorem mem_Tset_iff {a b c d e f s : ℕ} (hd : 1 ≤ d) :
    s ∈ Tset a b c d e f ↔ s = 0 ∨ s = 1 ∨ (s % 8 = 2 ∧ 1 ≤ s / 8 ∧ s / 8 ≤ a) ∨
      (s % 8 = 3 ∧ 1 ≤ s / 8 ∧ s / 8 ≤ b) ∨ (s % 8 = 4 ∧ 1 ≤ s / 8 ∧ s / 8 ≤ c) ∨
      (s % 8 = 5 ∧ 1 ≤ s / 8 ∧ s / 8 ≤ d - 1) ∨ (s % 8 = 6 ∧ 1 ≤ s / 8 ∧ s / 8 ≤ e) ∨
      (s % 8 = 7 ∧ 1 ≤ s / 8 ∧ s / 8 ≤ f) := by
  rw [mem_Tset]
  constructor
  · rintro (h | h | ⟨X, k, h2, h7, hk1, hk, rfl⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · unfold armLen at hk
      have hX : X = 2 ∨ X = 3 ∨ X = 4 ∨ X = 5 ∨ X = 6 ∨ X = 7 := by omega
      rcases hX with rfl | rfl | rfl | rfl | rfl | rfl <;> simp at hk <;> omega
  · rintro (h | h | h | h | h | h | h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    all_goals
      right; right
      refine ⟨s % 8, s / 8, by omega, by omega, by omega, ?_, by omega⟩
      unfold armLen
      have : s % 8 = 2 ∨ s % 8 = 3 ∨ s % 8 = 4 ∨ s % 8 = 5 ∨ s % 8 = 6 ∨ s % 8 = 7 := by omega
      rcases this with e | e | e | e | e | e <;> simp [e] <;> omega

/-- the part of the tree on `u`'s side of the `d`-path edge between positions `j` and `j+1` -/
def uPart (j z : ℕ) : Prop :=
  z = 0 ∨ ((z % 8 = 2 ∨ z % 8 = 3 ∨ z % 8 = 4) ∧ 1 ≤ z / 8) ∨ (z % 8 = 5 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ j)

/-- the part on `v`'s side -/
def vPart (d j z : ℕ) : Prop :=
  z = 1 ∨ ((z % 8 = 6 ∨ z % 8 = 7) ∧ 1 ≤ z / 8) ∨ (z % 8 = 5 ∧ j + 1 ≤ z / 8 ∧ z / 8 ≤ d - 1)

/-- position `i` of the `d`-path (`0 = u`, `d = v`) -/
def dnode (d i : ℕ) : ℕ := if i = 0 then 0 else if i = d then 1 else 5 + 8 * i

/-- the only edge between the two parts is `dnode j — dnode (j+1)` -/
theorem cross_cut (d j : ℕ) (hj : j + 1 ≤ d) (p q : ℕ) (hp : vPart d j p) (hq : uPart j q)
    (h : Tadj d p q) : p = dnode d (j + 1) ∧ q = dnode d j := by
  unfold vPart at hp
  unfold uPart at hq
  unfold dnode
  rcases hq with rfl | hq | hq
  · -- q = u: then `p`'s parent is `u`
    unfold Tadj at h
    rcases h with ⟨hp0, hpar⟩ | ⟨h0, _⟩
    · rcases hp with rfl | ⟨hX, hk⟩ | ⟨h5, hk1, hk2⟩
      · unfold Tpar dEnd at hpar
        rw [if_neg (by omega), if_pos rfl] at hpar
        split_ifs at hpar with h2
        · omega
        · have : d = 1 := by omega
          subst this
          have : j = 0 := by omega
          subst this
          simp
      · have hX' : 2 ≤ p % 8 ∧ p % 8 ≤ 7 := by omega
        have := Tpar_arm d (p % 8) (p / 8) hX' hk
        rw [show p % 8 + 8 * (p / 8) = p by omega] at this
        rw [this] at hpar
        unfold armRoot at hpar
        split_ifs at hpar <;> omega
      · have := Tpar_arm d 5 (p / 8) (by omega) (by omega)
        rw [show 5 + 8 * (p / 8) = p by omega] at this
        rw [this] at hpar
        unfold armRoot at hpar
        split_ifs at hpar with h2
        · omega
        · have hj0 : j = 0 := by omega
          subst hj0
          refine ⟨?_, by simp⟩
          rw [if_neg (by omega), if_neg (by omega)]; omega
    · exact absurd rfl h0
  · -- q on a u-arm: its neighbours stay on that arm or are `u`
    have hX : 2 ≤ q % 8 ∧ q % 8 ≤ 7 := by omega
    have hq' : q = q % 8 + 8 * (q / 8) := by omega
    rw [hq'] at h
    rcases (Tadj_arm_iff d (q % 8) (q / 8) p hX (by omega)).mp h with h1 | h1 | ⟨h5, _, _⟩
    · split_ifs at h1
      · unfold armRoot at h1; split_ifs at h1 <;> omega
      · omega
    · omega
    · omega
  · -- q on the `d`-path at position `≤ j`
    have hX : 2 ≤ 5 ∧ 5 ≤ 7 := by omega
    have hq' : q = 5 + 8 * (q / 8) := by omega
    rw [hq'] at h
    rcases (Tadj_arm_iff d 5 (q / 8) p hX (by omega)).mp h with h1 | h1 | ⟨_, h2, h3⟩
    · split_ifs at h1
      · unfold armRoot at h1; rw [if_pos (by omega)] at h1; omega
      · omega
    · refine ⟨?_, ?_⟩
      · rw [if_neg (by omega)]; split_ifs <;> omega
      · rw [if_neg (by omega), if_neg (by omega)]; omega
    · refine ⟨?_, ?_⟩
      · rw [if_neg (by omega), if_pos (by omega)]; exact h3
      · rw [if_neg (by omega), if_neg (by omega)]; omega

theorem uPart_vPart_disj (d j z : ℕ) (hu : uPart j z) (hv : vPart d j z) : False := by
  unfold uPart at hu; unfold vPart at hv; omega

theorem dnode_adj (d j : ℕ) (hj : j + 1 ≤ d) : Tadj d (dnode d (j + 1)) (dnode d j) := by
  unfold dnode
  by_cases h0 : j = 0
  · subst h0
    by_cases hd : d = 1
    · subst hd; rw [tadjB_iff]; decide
    · rw [if_neg (by omega), if_neg (by omega), if_pos rfl, tadjB_iff,
        tadjB_indep d _ _ (by omega) (by omega)]
      decide
  · by_cases hv : j + 1 = d
    · rw [if_neg (by omega), if_pos hv, if_neg h0, if_neg (by omega)]
      left
      refine ⟨by omega, ?_⟩
      unfold Tpar dEnd
      rw [if_neg (by omega), if_pos rfl, if_pos (by omega)]
      omega
    · rw [if_neg (by omega), if_neg hv, if_neg h0, if_neg (by omega)]
      exact (Tadj_arm_iff d 5 j _ (by omega) (by omega)).mpr (Or.inr (Or.inl rfl))

/-- join an α-piece on the `v`-side with a graceful piece on the `u`-side -/
theorem join_vu {a b c d e f j q : ℕ} (hd : 1 ≤ d) (hj : j + 1 ≤ d) (A : APc d q) (G : Pc)
    (hG : G.Grace) (hGR : G.R = Tadj d)
    (hA : ∀ z, z ∈ A.P.S → vPart d j z) (hGu : ∀ z, z ∈ G.S → uPart j z)
    (hx : dnode d (j + 1) ∈ A.P.S) (hw : dnode d j ∈ G.S)
    (hlab : G.f (dnode d j) = A.tau (dnode d (j + 1)) ∨
      G.f (dnode d j) = G.E.card - A.tau (dnode d (j + 1)))
    (htb : A.tau (dnode d (j + 1)) ≤ G.E.card)
    (hT : ∀ s, (s ∈ A.P.S ∨ s ∈ G.S) ↔ s ∈ Tset a b c d e f) : CanonGraceful a b c d e f := by
  obtain ⟨P, hP, hPR, hPS, _, _⟩ := A.joinG G hG hGR hx hw (dnode_adj d j hj)
    (by rw [Finset.disjoint_left]; intro z h1 h2; exact uPart_vPart_disj d j z (hGu z h2) (hA z h1))
    (fun p hp q' hq' h => cross_cut d j hj p q' (hA p hp) (hGu q' hq') h) hlab htb
  exact canon_of_piece P hP hPR (fun s => by rw [hPS]; exact hT s)

/-- join an α-piece on the `u`-side with a graceful piece on the `v`-side -/
theorem join_uv {a b c d e f j q : ℕ} (hd : 1 ≤ d) (hj : j + 1 ≤ d) (A : APc d q) (G : Pc)
    (hG : G.Grace) (hGR : G.R = Tadj d)
    (hA : ∀ z, z ∈ A.P.S → uPart j z) (hGv : ∀ z, z ∈ G.S → vPart d j z)
    (hx : dnode d j ∈ A.P.S) (hw : dnode d (j + 1) ∈ G.S)
    (hlab : G.f (dnode d (j + 1)) = A.tau (dnode d j) ∨
      G.f (dnode d (j + 1)) = G.E.card - A.tau (dnode d j))
    (htb : A.tau (dnode d j) ≤ G.E.card)
    (hT : ∀ s, (s ∈ A.P.S ∨ s ∈ G.S) ↔ s ∈ Tset a b c d e f) : CanonGraceful a b c d e f := by
  obtain ⟨P, hP, hPR, hPS, _, _⟩ := A.joinG G hG hGR hx hw (Tadj_symm d _ _ (dnode_adj d j hj))
    (by rw [Finset.disjoint_left]; intro z h1 h2; exact uPart_vPart_disj d j z (hA z h1) (hGv z h2))
    (fun p hp q' hq' h => by
      have := cross_cut d j hj q' p (hGv q' hq') (hA p hp) (Tadj_symm d _ _ h)
      exact ⟨this.2, this.1⟩) hlab htb
  exact canon_of_piece P hP hPR (fun s => by rw [hPS]; exact hT s)
