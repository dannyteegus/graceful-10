/-! ## Explicit graceful cores (`u` at `0`) with leaf chains, and a table -/

/-- a graceful core with `u` at label `0`, plus a leaf chain on a free arm at `u` -/
theorem core_leaf {a b c d : ℕ} (hd : 1 ≤ d) (X L : ℕ) (hX : X = 2 ∨ X = 3 ∨ X = 4) (G : Pc)
    (hG : G.Grace) (hR : G.R = Tadj d) (h0 : (0 : ℕ) ∈ G.S) (hu : G.f 0 = 0)
    (hfresh : ∀ w, w % 8 = X → 1 ≤ w / 8 → w / 8 ≤ L + 1 → w ∉ G.S)
    (hT : ∀ s, (s ∈ G.S ∨ (s % 8 = X ∧ 1 ≤ s / 8 ∧ s / 8 ≤ L)) ↔ s ∈ Tset a b c d 2 2) :
    CanonGraceful a b c d 2 2 := by
  have hr : armRoot X = 0 := armRoot_u hX
  obtain ⟨G', hG', hR', hS', _⟩ := leafRoot hd X L (by omega) (by omega) G hG hR
    (by rw [hr]; exact h0) (by rw [hr]; left; exact hu) hfresh
  exact canon_of_piece G' hG' hR' (fun s => by rw [hS']; exact hT s)

theorem hcore23_d1 (c : ℕ) : CanonGraceful 4 4 c 1 2 2 := by
  obtain ⟨G, hG, hR, hS, _, hf⟩ := numTreeG 1 [0, 10, 18, 26, 34, 11, 19, 27, 35, 1, 14, 22, 15, 23]
    [0, 0, 1, 2, 3, 0, 5, 6, 7, 0, 9, 10, 9, 12]
    [0, 13, 3, 10, 6, 12, 4, 9, 7, 11, 2, 1, 5, 8] (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
  have hm := mem_list_iff (names := [0, 10, 18, 26, 34, 11, 19, 27, 35, 1, 14, 22, 15, 23])
    (φ := fun z => z = 0 ∨ (z % 8 = 2 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 4) ∨ (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 4) ∨ z = 1 ∨ z = 14 ∨ z = 22 ∨ z = 15 ∨ z = 23) 40
    (by decide +kernel) (by decide +kernel) (by intro z hz; omega)
  have hS' : ∀ z, z ∈ G.S ↔ z = 0 ∨ (z % 8 = 2 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 4) ∨ (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 4) ∨ z = 1 ∨ z = 14 ∨ z = 22 ∨ z = 15 ∨ z = 23 := by
    intro z; rw [hS, hm z]
  refine core_leaf (d := 1) (by omega) 4 c (by omega) G hG hR (by rw [hS']; omega)
    (by have := hf 0 (by decide); simpa using this)
    (by intro w h1 h2 h3 hw; rw [hS'] at hw; omega) (fun s => ?_)
  rw [hS', tset22_iff (by omega)]; unfold ShU
  constructor
  · rintro ((h | h | h | h | h | h | h | h) | h) <;> omega
  · rintro ((h | h | h | h) | h | h | h | h | h | h) <;> omega

theorem hcore34_d1 (a : ℕ) : CanonGraceful a 4 4 1 2 2 := by
  obtain ⟨G, hG, hR, hS, _, hf⟩ := numTreeG 1 [0, 11, 19, 27, 35, 12, 20, 28, 36, 1, 14, 22, 15, 23]
    [0, 0, 1, 2, 3, 0, 5, 6, 7, 0, 9, 10, 9, 12]
    [0, 13, 3, 10, 6, 12, 4, 9, 7, 11, 2, 1, 5, 8] (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
  have hm := mem_list_iff (names := [0, 11, 19, 27, 35, 12, 20, 28, 36, 1, 14, 22, 15, 23])
    (φ := fun z => z = 0 ∨ (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 4) ∨ (z % 8 = 4 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 4) ∨ z = 1 ∨ z = 14 ∨ z = 22 ∨ z = 15 ∨ z = 23) 40
    (by decide +kernel) (by decide +kernel) (by intro z hz; omega)
  have hS' : ∀ z, z ∈ G.S ↔ z = 0 ∨ (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 4) ∨ (z % 8 = 4 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 4) ∨ z = 1 ∨ z = 14 ∨ z = 22 ∨ z = 15 ∨ z = 23 := by
    intro z; rw [hS, hm z]
  refine core_leaf (d := 1) (by omega) 2 a (by omega) G hG hR (by rw [hS']; omega)
    (by have := hf 0 (by decide); simpa using this)
    (by intro w h1 h2 h3 hw; rw [hS'] at hw; omega) (fun s => ?_)
  rw [hS', tset22_iff (by omega)]; unfold ShU
  constructor
  · rintro ((h | h | h | h | h | h | h | h) | h) <;> omega
  · rintro ((h | h | h | h) | h | h | h | h | h | h) <;> omega

theorem hcore23_d2 (c : ℕ) : CanonGraceful 4 4 c 2 2 2 := by
  obtain ⟨G, hG, hR, hS, _, hf⟩ := numTreeG 2 [0, 10, 18, 26, 34, 11, 19, 27, 35, 13, 1, 14, 22, 15, 23]
    [0, 0, 1, 2, 3, 0, 5, 6, 7, 0, 9, 10, 11, 10, 13]
    [0, 14, 3, 11, 7, 13, 4, 6, 1, 12, 2, 9, 10, 8, 5] (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
  have hm := mem_list_iff (names := [0, 10, 18, 26, 34, 11, 19, 27, 35, 13, 1, 14, 22, 15, 23])
    (φ := fun z => z = 0 ∨ (z % 8 = 2 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 4) ∨ (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 4) ∨ (z % 8 = 5 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 1) ∨ z = 1 ∨ z = 14 ∨ z = 22 ∨ z = 15 ∨ z = 23) 40
    (by decide +kernel) (by decide +kernel) (by intro z hz; omega)
  have hS' : ∀ z, z ∈ G.S ↔ z = 0 ∨ (z % 8 = 2 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 4) ∨ (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 4) ∨ (z % 8 = 5 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 1) ∨ z = 1 ∨ z = 14 ∨ z = 22 ∨ z = 15 ∨ z = 23 := by
    intro z; rw [hS, hm z]
  refine core_leaf (d := 2) (by omega) 4 c (by omega) G hG hR (by rw [hS']; omega)
    (by have := hf 0 (by decide); simpa using this)
    (by intro w h1 h2 h3 hw; rw [hS'] at hw; omega) (fun s => ?_)
  rw [hS', tset22_iff (by omega)]; unfold ShU
  constructor
  · rintro ((h | h | h | h | h | h | h | h | h) | h) <;> omega
  · rintro ((h | h | h | h) | h | h | h | h | h | h) <;> omega

theorem hcore34_d2 (a : ℕ) : CanonGraceful a 4 4 2 2 2 := by
  obtain ⟨G, hG, hR, hS, _, hf⟩ := numTreeG 2 [0, 11, 19, 27, 35, 12, 20, 28, 36, 13, 1, 14, 22, 15, 23]
    [0, 0, 1, 2, 3, 0, 5, 6, 7, 0, 9, 10, 11, 10, 13]
    [0, 14, 3, 11, 7, 13, 4, 6, 1, 12, 2, 9, 10, 8, 5] (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
  have hm := mem_list_iff (names := [0, 11, 19, 27, 35, 12, 20, 28, 36, 13, 1, 14, 22, 15, 23])
    (φ := fun z => z = 0 ∨ (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 4) ∨ (z % 8 = 4 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 4) ∨ (z % 8 = 5 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 1) ∨ z = 1 ∨ z = 14 ∨ z = 22 ∨ z = 15 ∨ z = 23) 40
    (by decide +kernel) (by decide +kernel) (by intro z hz; omega)
  have hS' : ∀ z, z ∈ G.S ↔ z = 0 ∨ (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 4) ∨ (z % 8 = 4 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 4) ∨ (z % 8 = 5 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 1) ∨ z = 1 ∨ z = 14 ∨ z = 22 ∨ z = 15 ∨ z = 23 := by
    intro z; rw [hS, hm z]
  refine core_leaf (d := 2) (by omega) 2 a (by omega) G hG hR (by rw [hS']; omega)
    (by have := hf 0 (by decide); simpa using this)
    (by intro w h1 h2 h3 hw; rw [hS'] at hw; omega) (fun s => ?_)
  rw [hS', tset22_iff (by omega)]; unfold ShU
  constructor
  · rintro ((h | h | h | h | h | h | h | h | h) | h) <;> omega
  · rintro ((h | h | h | h) | h | h | h | h | h | h) <;> omega

theorem hcore23_d6 (c : ℕ) : CanonGraceful 4 4 c 6 2 2 := by
  obtain ⟨G, hG, hR, hS, _, hf⟩ := numTreeG 6 [0, 10, 18, 26, 34, 11, 19, 27, 35, 13, 21, 29, 37, 45, 1, 14, 22, 15, 23]
    [0, 0, 1, 2, 3, 0, 5, 6, 7, 0, 9, 10, 11, 12, 13, 14, 15, 14, 17]
    [0, 18, 3, 15, 6, 17, 4, 14, 7, 16, 2, 13, 10, 5, 11, 9, 1, 12, 8] (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
  have hm := mem_list_iff (names := [0, 10, 18, 26, 34, 11, 19, 27, 35, 13, 21, 29, 37, 45, 1, 14, 22, 15, 23])
    (φ := fun z => z = 0 ∨ (z % 8 = 2 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 4) ∨ (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 4) ∨ (z % 8 = 5 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 5) ∨ z = 1 ∨ z = 14 ∨ z = 22 ∨ z = 15 ∨ z = 23) 48
    (by decide +kernel) (by decide +kernel) (by intro z hz; omega)
  have hS' : ∀ z, z ∈ G.S ↔ z = 0 ∨ (z % 8 = 2 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 4) ∨ (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 4) ∨ (z % 8 = 5 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 5) ∨ z = 1 ∨ z = 14 ∨ z = 22 ∨ z = 15 ∨ z = 23 := by
    intro z; rw [hS, hm z]
  refine core_leaf (d := 6) (by omega) 4 c (by omega) G hG hR (by rw [hS']; omega)
    (by have := hf 0 (by decide); simpa using this)
    (by intro w h1 h2 h3 hw; rw [hS'] at hw; omega) (fun s => ?_)
  rw [hS', tset22_iff (by omega)]; unfold ShU
  constructor
  · rintro ((h | h | h | h | h | h | h | h | h) | h) <;> omega
  · rintro ((h | h | h | h) | h | h | h | h | h | h) <;> omega

theorem hcore34_d6 (a : ℕ) : CanonGraceful a 4 4 6 2 2 := by
  obtain ⟨G, hG, hR, hS, _, hf⟩ := numTreeG 6 [0, 11, 19, 27, 35, 12, 20, 28, 36, 13, 21, 29, 37, 45, 1, 14, 22, 15, 23]
    [0, 0, 1, 2, 3, 0, 5, 6, 7, 0, 9, 10, 11, 12, 13, 14, 15, 14, 17]
    [0, 18, 3, 15, 6, 17, 4, 14, 7, 16, 2, 13, 10, 5, 11, 9, 1, 12, 8] (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
  have hm := mem_list_iff (names := [0, 11, 19, 27, 35, 12, 20, 28, 36, 13, 21, 29, 37, 45, 1, 14, 22, 15, 23])
    (φ := fun z => z = 0 ∨ (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 4) ∨ (z % 8 = 4 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 4) ∨ (z % 8 = 5 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 5) ∨ z = 1 ∨ z = 14 ∨ z = 22 ∨ z = 15 ∨ z = 23) 48
    (by decide +kernel) (by decide +kernel) (by intro z hz; omega)
  have hS' : ∀ z, z ∈ G.S ↔ z = 0 ∨ (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 4) ∨ (z % 8 = 4 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 4) ∨ (z % 8 = 5 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 5) ∨ z = 1 ∨ z = 14 ∨ z = 22 ∨ z = 15 ∨ z = 23 := by
    intro z; rw [hS, hm z]
  refine core_leaf (d := 6) (by omega) 2 a (by omega) G hG hR (by rw [hS']; omega)
    (by have := hf 0 (by decide); simpa using this)
    (by intro w h1 h2 h3 hw; rw [hS'] at hw; omega) (fun s => ?_)
  rw [hS', tset22_iff (by omega)]; unfold ShU
  constructor
  · rintro ((h | h | h | h | h | h | h | h | h) | h) <;> omega
  · rintro ((h | h | h | h) | h | h | h | h | h | h) <;> omega

theorem hcore23_d7 (c : ℕ) : CanonGraceful 4 4 c 7 2 2 := by
  obtain ⟨G, hG, hR, hS, _, hf⟩ := numTreeG 7 [0, 10, 18, 26, 34, 11, 19, 27, 35, 13, 21, 29, 37, 45, 53, 1, 14, 22, 15, 23]
    [0, 0, 1, 2, 3, 0, 5, 6, 7, 0, 9, 10, 11, 12, 13, 14, 15, 16, 15, 18]
    [0, 19, 3, 16, 6, 18, 4, 15, 7, 17, 2, 14, 8, 11, 9, 5, 12, 13, 10, 1] (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
  have hm := mem_list_iff (names := [0, 10, 18, 26, 34, 11, 19, 27, 35, 13, 21, 29, 37, 45, 53, 1, 14, 22, 15, 23])
    (φ := fun z => z = 0 ∨ (z % 8 = 2 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 4) ∨ (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 4) ∨ (z % 8 = 5 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 6) ∨ z = 1 ∨ z = 14 ∨ z = 22 ∨ z = 15 ∨ z = 23) 56
    (by decide +kernel) (by decide +kernel) (by intro z hz; omega)
  have hS' : ∀ z, z ∈ G.S ↔ z = 0 ∨ (z % 8 = 2 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 4) ∨ (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 4) ∨ (z % 8 = 5 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 6) ∨ z = 1 ∨ z = 14 ∨ z = 22 ∨ z = 15 ∨ z = 23 := by
    intro z; rw [hS, hm z]
  refine core_leaf (d := 7) (by omega) 4 c (by omega) G hG hR (by rw [hS']; omega)
    (by have := hf 0 (by decide); simpa using this)
    (by intro w h1 h2 h3 hw; rw [hS'] at hw; omega) (fun s => ?_)
  rw [hS', tset22_iff (by omega)]; unfold ShU
  constructor
  · rintro ((h | h | h | h | h | h | h | h | h) | h) <;> omega
  · rintro ((h | h | h | h) | h | h | h | h | h | h) <;> omega

theorem hcore34_d7 (a : ℕ) : CanonGraceful a 4 4 7 2 2 := by
  obtain ⟨G, hG, hR, hS, _, hf⟩ := numTreeG 7 [0, 11, 19, 27, 35, 12, 20, 28, 36, 13, 21, 29, 37, 45, 53, 1, 14, 22, 15, 23]
    [0, 0, 1, 2, 3, 0, 5, 6, 7, 0, 9, 10, 11, 12, 13, 14, 15, 16, 15, 18]
    [0, 19, 3, 16, 6, 18, 4, 15, 7, 17, 2, 14, 8, 11, 9, 5, 12, 13, 10, 1] (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
  have hm := mem_list_iff (names := [0, 11, 19, 27, 35, 12, 20, 28, 36, 13, 21, 29, 37, 45, 53, 1, 14, 22, 15, 23])
    (φ := fun z => z = 0 ∨ (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 4) ∨ (z % 8 = 4 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 4) ∨ (z % 8 = 5 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 6) ∨ z = 1 ∨ z = 14 ∨ z = 22 ∨ z = 15 ∨ z = 23) 56
    (by decide +kernel) (by decide +kernel) (by intro z hz; omega)
  have hS' : ∀ z, z ∈ G.S ↔ z = 0 ∨ (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 4) ∨ (z % 8 = 4 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 4) ∨ (z % 8 = 5 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 6) ∨ z = 1 ∨ z = 14 ∨ z = 22 ∨ z = 15 ∨ z = 23 := by
    intro z; rw [hS, hm z]
  refine core_leaf (d := 7) (by omega) 2 a (by omega) G hG hR (by rw [hS']; omega)
    (by have := hf 0 (by decide); simpa using this)
    (by intro w h1 h2 h3 hw; rw [hS'] at hw; omega) (fun s => ?_)
  rw [hS', tset22_iff (by omega)]; unfold ShU
  constructor
  · rintro ((h | h | h | h | h | h | h | h | h) | h) <;> omega
  · rintro ((h | h | h | h) | h | h | h | h | h | h) <;> omega

theorem hcore23_d8 (c : ℕ) : CanonGraceful 4 4 c 8 2 2 := by
  obtain ⟨G, hG, hR, hS, _, hf⟩ := numTreeG 8 [0, 10, 18, 26, 34, 11, 19, 27, 35, 13, 21, 29, 37, 45, 53, 61, 1, 14, 22, 15, 23]
    [0, 0, 1, 2, 3, 0, 5, 6, 7, 0, 9, 10, 11, 12, 13, 14, 15, 16, 17, 16, 19]
    [0, 20, 3, 17, 6, 19, 4, 16, 7, 18, 2, 15, 5, 13, 11, 10, 14, 8, 1, 9, 12] (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
  have hm := mem_list_iff (names := [0, 10, 18, 26, 34, 11, 19, 27, 35, 13, 21, 29, 37, 45, 53, 61, 1, 14, 22, 15, 23])
    (φ := fun z => z = 0 ∨ (z % 8 = 2 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 4) ∨ (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 4) ∨ (z % 8 = 5 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 7) ∨ z = 1 ∨ z = 14 ∨ z = 22 ∨ z = 15 ∨ z = 23) 64
    (by decide +kernel) (by decide +kernel) (by intro z hz; omega)
  have hS' : ∀ z, z ∈ G.S ↔ z = 0 ∨ (z % 8 = 2 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 4) ∨ (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 4) ∨ (z % 8 = 5 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 7) ∨ z = 1 ∨ z = 14 ∨ z = 22 ∨ z = 15 ∨ z = 23 := by
    intro z; rw [hS, hm z]
  refine core_leaf (d := 8) (by omega) 4 c (by omega) G hG hR (by rw [hS']; omega)
    (by have := hf 0 (by decide); simpa using this)
    (by intro w h1 h2 h3 hw; rw [hS'] at hw; omega) (fun s => ?_)
  rw [hS', tset22_iff (by omega)]; unfold ShU
  constructor
  · rintro ((h | h | h | h | h | h | h | h | h) | h) <;> omega
  · rintro ((h | h | h | h) | h | h | h | h | h | h) <;> omega

theorem hcore34_d8 (a : ℕ) : CanonGraceful a 4 4 8 2 2 := by
  obtain ⟨G, hG, hR, hS, _, hf⟩ := numTreeG 8 [0, 11, 19, 27, 35, 12, 20, 28, 36, 13, 21, 29, 37, 45, 53, 61, 1, 14, 22, 15, 23]
    [0, 0, 1, 2, 3, 0, 5, 6, 7, 0, 9, 10, 11, 12, 13, 14, 15, 16, 17, 16, 19]
    [0, 20, 3, 17, 6, 19, 4, 16, 7, 18, 2, 15, 5, 13, 11, 10, 14, 8, 1, 9, 12] (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
  have hm := mem_list_iff (names := [0, 11, 19, 27, 35, 12, 20, 28, 36, 13, 21, 29, 37, 45, 53, 61, 1, 14, 22, 15, 23])
    (φ := fun z => z = 0 ∨ (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 4) ∨ (z % 8 = 4 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 4) ∨ (z % 8 = 5 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 7) ∨ z = 1 ∨ z = 14 ∨ z = 22 ∨ z = 15 ∨ z = 23) 64
    (by decide +kernel) (by decide +kernel) (by intro z hz; omega)
  have hS' : ∀ z, z ∈ G.S ↔ z = 0 ∨ (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 4) ∨ (z % 8 = 4 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 4) ∨ (z % 8 = 5 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 7) ∨ z = 1 ∨ z = 14 ∨ z = 22 ∨ z = 15 ∨ z = 23 := by
    intro z; rw [hS, hm z]
  refine core_leaf (d := 8) (by omega) 2 a (by omega) G hG hR (by rw [hS']; omega)
    (by have := hf 0 (by decide); simpa using this)
    (by intro w h1 h2 h3 hw; rw [hS'] at hw; omega) (fun s => ?_)
  rw [hS', tset22_iff (by omega)]; unfold ShU
  constructor
  · rintro ((h | h | h | h | h | h | h | h | h) | h) <;> omega
  · rintro ((h | h | h | h) | h | h | h | h | h | h) <;> omega

theorem kcore_d2 (c : ℕ) : CanonGraceful 6 9 c 2 2 2 := by
  obtain ⟨G, hG, hR, hS, _, hf⟩ := numTreeG 2 [0, 10, 18, 26, 34, 42, 50, 11, 19, 27, 35, 43, 51, 59, 67, 75, 13, 1, 14, 22, 15, 23]
    [0, 0, 1, 2, 3, 4, 5, 0, 7, 8, 9, 10, 11, 12, 13, 14, 0, 16, 17, 18, 17, 20]
    [0, 21, 3, 18, 7, 15, 9, 20, 4, 17, 8, 1, 5, 10, 12, 13, 19, 2, 16, 6, 14, 11] (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
  have hm := mem_list_iff (names := [0, 10, 18, 26, 34, 42, 50, 11, 19, 27, 35, 43, 51, 59, 67, 75, 13, 1, 14, 22, 15, 23])
    (φ := fun z => z = 0 ∨ (z % 8 = 2 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 6) ∨ (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 9) ∨ (z % 8 = 5 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 1) ∨ z = 1 ∨ z = 14 ∨ z = 22 ∨ z = 15 ∨ z = 23) 80
    (by decide +kernel) (by decide +kernel) (by intro z hz; omega)
  have hS' : ∀ z, z ∈ G.S ↔ z = 0 ∨ (z % 8 = 2 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 6) ∨ (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 9) ∨ (z % 8 = 5 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 1) ∨ z = 1 ∨ z = 14 ∨ z = 22 ∨ z = 15 ∨ z = 23 := by
    intro z; rw [hS, hm z]
  refine core_leaf (d := 2) (by omega) 4 c (by omega) G hG hR (by rw [hS']; omega)
    (by have := hf 0 (by decide); simpa using this)
    (by intro w h1 h2 h3 hw; rw [hS'] at hw; omega) (fun s => ?_)
  rw [hS', tset22_iff (by omega)]; unfold ShU
  constructor
  · rintro ((h | h | h | h | h | h | h | h | h) | h) <;> omega
  · rintro ((h | h | h | h) | h | h | h | h | h | h) <;> omega

theorem kcore_d6 (c : ℕ) : CanonGraceful 6 9 c 6 2 2 := by
  obtain ⟨G, hG, hR, hS, _, hf⟩ := numTreeG 6 [0, 10, 18, 26, 34, 42, 50, 11, 19, 27, 35, 43, 51, 59, 67, 75, 13, 21, 29, 37, 45, 1, 14, 22, 15, 23]
    [0, 0, 1, 2, 3, 4, 5, 0, 7, 8, 9, 10, 11, 12, 13, 14, 0, 16, 17, 18, 19, 20, 21, 22, 21, 24]
    [0, 25, 3, 22, 6, 19, 9, 24, 4, 21, 7, 18, 10, 1, 8, 13, 23, 2, 20, 5, 17, 11, 15, 16, 14, 12] (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
  have hm := mem_list_iff (names := [0, 10, 18, 26, 34, 42, 50, 11, 19, 27, 35, 43, 51, 59, 67, 75, 13, 21, 29, 37, 45, 1, 14, 22, 15, 23])
    (φ := fun z => z = 0 ∨ (z % 8 = 2 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 6) ∨ (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 9) ∨ (z % 8 = 5 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 5) ∨ z = 1 ∨ z = 14 ∨ z = 22 ∨ z = 15 ∨ z = 23) 80
    (by decide +kernel) (by decide +kernel) (by intro z hz; omega)
  have hS' : ∀ z, z ∈ G.S ↔ z = 0 ∨ (z % 8 = 2 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 6) ∨ (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 9) ∨ (z % 8 = 5 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 5) ∨ z = 1 ∨ z = 14 ∨ z = 22 ∨ z = 15 ∨ z = 23 := by
    intro z; rw [hS, hm z]
  refine core_leaf (d := 6) (by omega) 4 c (by omega) G hG hR (by rw [hS']; omega)
    (by have := hf 0 (by decide); simpa using this)
    (by intro w h1 h2 h3 hw; rw [hS'] at hw; omega) (fun s => ?_)
  rw [hS', tset22_iff (by omega)]; unfold ShU
  constructor
  · rintro ((h | h | h | h | h | h | h | h | h) | h) <;> omega
  · rintro ((h | h | h | h) | h | h | h | h | h | h) <;> omega

theorem kcore_d7 (c : ℕ) : CanonGraceful 6 9 c 7 2 2 := by
  obtain ⟨G, hG, hR, hS, _, hf⟩ := numTreeG 7 [0, 10, 18, 26, 34, 42, 50, 11, 19, 27, 35, 43, 51, 59, 67, 75, 13, 21, 29, 37, 45, 53, 1, 14, 22, 15, 23]
    [0, 0, 1, 2, 3, 4, 5, 0, 7, 8, 9, 10, 11, 12, 13, 14, 0, 16, 17, 18, 19, 20, 21, 22, 23, 22, 25]
    [0, 26, 3, 23, 6, 20, 9, 25, 4, 22, 7, 19, 10, 15, 8, 16, 24, 2, 21, 5, 18, 12, 14, 11, 1, 13, 17] (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
  have hm := mem_list_iff (names := [0, 10, 18, 26, 34, 42, 50, 11, 19, 27, 35, 43, 51, 59, 67, 75, 13, 21, 29, 37, 45, 53, 1, 14, 22, 15, 23])
    (φ := fun z => z = 0 ∨ (z % 8 = 2 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 6) ∨ (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 9) ∨ (z % 8 = 5 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 6) ∨ z = 1 ∨ z = 14 ∨ z = 22 ∨ z = 15 ∨ z = 23) 80
    (by decide +kernel) (by decide +kernel) (by intro z hz; omega)
  have hS' : ∀ z, z ∈ G.S ↔ z = 0 ∨ (z % 8 = 2 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 6) ∨ (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 9) ∨ (z % 8 = 5 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 6) ∨ z = 1 ∨ z = 14 ∨ z = 22 ∨ z = 15 ∨ z = 23 := by
    intro z; rw [hS, hm z]
  refine core_leaf (d := 7) (by omega) 4 c (by omega) G hG hR (by rw [hS']; omega)
    (by have := hf 0 (by decide); simpa using this)
    (by intro w h1 h2 h3 hw; rw [hS'] at hw; omega) (fun s => ?_)
  rw [hS', tset22_iff (by omega)]; unfold ShU
  constructor
  · rintro ((h | h | h | h | h | h | h | h | h) | h) <;> omega
  · rintro ((h | h | h | h) | h | h | h | h | h | h) <;> omega

theorem t555_d1 : CanonGraceful 5 5 5 1 2 2 := by
  obtain ⟨G, hG, hR, hS, _, _⟩ := numTreeG 1 [0, 10, 18, 26, 34, 42, 11, 19, 27, 35, 43, 12, 20, 28, 36, 44, 1, 14, 22, 15, 23]
    [0, 0, 1, 2, 3, 4, 0, 6, 7, 8, 9, 0, 11, 12, 13, 14, 0, 16, 17, 16, 19]
    [0, 20, 4, 16, 10, 15, 19, 5, 14, 1, 2, 18, 3, 11, 8, 12, 17, 6, 13, 7, 9] (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
  have hm := mem_list_iff (names := [0, 10, 18, 26, 34, 42, 11, 19, 27, 35, 43, 12, 20, 28, 36, 44, 1, 14, 22, 15, 23])
    (φ := fun z => z = 0 ∨ (z % 8 = 2 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 5) ∨ (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 5) ∨ (z % 8 = 4 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 5) ∨ z = 1 ∨ z = 14 ∨ z = 22 ∨ z = 15 ∨ z = 23) 48
    (by decide +kernel) (by decide +kernel) (by intro z hz; omega)
  have hS' : ∀ z, z ∈ G.S ↔ z = 0 ∨ (z % 8 = 2 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 5) ∨ (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 5) ∨ (z % 8 = 4 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 5) ∨ z = 1 ∨ z = 14 ∨ z = 22 ∨ z = 15 ∨ z = 23 := by
    intro z; rw [hS, hm z]
  refine canon_of_piece G hG hR (fun s => ?_)
  rw [hS', tset22_iff (by omega)]; unfold ShU
  constructor
  · rintro (h | h | h | h | h | h | h | h | h) <;> omega
  · rintro ((h | h | h | h) | h | h | h | h | h | h) <;> omega

