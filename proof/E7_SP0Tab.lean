
theorem sp0_t22_2 (d : ℕ) : SPG d 0 2 2 2 := by
  obtain ⟨G, hG, hR, hS, hE, hf⟩ := numTreeGU d [0, 10, 18, 11, 19, 12, 20]
    [0, 0, 1, 0, 3, 0, 5]
    [0, 6, 2, 5, 4, 3, 1] (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  have hm := mem_list_iff (names := [0, 10, 18, 11, 19, 12, 20]) (φ := fun z => z = 0 ∨ (z % 8 = 2 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 2) ∨ (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 2) ∨ (z % 8 = 4 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 2)) 24
    (by decide +kernel) (by decide +kernel) (by intro z hz; omega)
  refine ⟨G, hG, hR, fun z => by rw [hS, hm z]; rfl, by rw [hE]; rfl, Or.inl ?_⟩
  have := hf 0 (by decide)
  simpa using this


theorem sp0_t22_3 (d : ℕ) : SPG d 0 2 2 3 := by
  obtain ⟨G, hG, hR, hS, hE, hf⟩ := numTreeGU d [0, 10, 18, 11, 19, 12, 20, 28]
    [0, 0, 1, 0, 3, 0, 5, 6]
    [0, 7, 3, 6, 4, 5, 2, 1] (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  have hm := mem_list_iff (names := [0, 10, 18, 11, 19, 12, 20, 28]) (φ := fun z => z = 0 ∨ (z % 8 = 2 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 2) ∨ (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 2) ∨ (z % 8 = 4 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 3)) 32
    (by decide +kernel) (by decide +kernel) (by intro z hz; omega)
  refine ⟨G, hG, hR, fun z => by rw [hS, hm z]; rfl, by rw [hE]; rfl, Or.inl ?_⟩
  have := hf 0 (by decide)
  simpa using this


theorem sp0_t22_4 (d : ℕ) : SPG d 0 2 2 4 := by
  obtain ⟨G, hG, hR, hS, hE, hf⟩ := numTreeGU d [0, 10, 18, 11, 19, 12, 20, 28, 36]
    [0, 0, 1, 0, 3, 0, 5, 6, 7]
    [0, 8, 3, 7, 5, 6, 2, 1, 4] (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  have hm := mem_list_iff (names := [0, 10, 18, 11, 19, 12, 20, 28, 36]) (φ := fun z => z = 0 ∨ (z % 8 = 2 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 2) ∨ (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 2) ∨ (z % 8 = 4 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 4)) 40
    (by decide +kernel) (by decide +kernel) (by intro z hz; omega)
  refine ⟨G, hG, hR, fun z => by rw [hS, hm z]; rfl, by rw [hE]; rfl, Or.inl ?_⟩
  have := hf 0 (by decide)
  simpa using this


theorem sp0_t22_5 (d : ℕ) : SPG d 0 2 2 5 := by
  obtain ⟨G, hG, hR, hS, hE, hf⟩ := numTreeGU d [0, 10, 18, 11, 19, 12, 20, 28, 36, 44]
    [0, 0, 1, 0, 3, 0, 5, 6, 7, 8]
    [0, 9, 3, 8, 4, 7, 5, 2, 1, 6] (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  have hm := mem_list_iff (names := [0, 10, 18, 11, 19, 12, 20, 28, 36, 44]) (φ := fun z => z = 0 ∨ (z % 8 = 2 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 2) ∨ (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 2) ∨ (z % 8 = 4 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 5)) 48
    (by decide +kernel) (by decide +kernel) (by intro z hz; omega)
  refine ⟨G, hG, hR, fun z => by rw [hS, hm z]; rfl, by rw [hE]; rfl, Or.inl ?_⟩
  have := hf 0 (by decide)
  simpa using this


theorem sp0_t22_6 (d : ℕ) : SPG d 0 2 2 6 := by
  obtain ⟨G, hG, hR, hS, hE, hf⟩ := numTreeGU d [0, 10, 18, 11, 19, 12, 20, 28, 36, 44, 52]
    [0, 0, 1, 0, 3, 0, 5, 6, 7, 8, 9]
    [0, 10, 3, 9, 4, 8, 5, 7, 1, 2, 6] (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  have hm := mem_list_iff (names := [0, 10, 18, 11, 19, 12, 20, 28, 36, 44, 52]) (φ := fun z => z = 0 ∨ (z % 8 = 2 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 2) ∨ (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 2) ∨ (z % 8 = 4 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 6)) 56
    (by decide +kernel) (by decide +kernel) (by intro z hz; omega)
  refine ⟨G, hG, hR, fun z => by rw [hS, hm z]; rfl, by rw [hE]; rfl, Or.inl ?_⟩
  have := hf 0 (by decide)
  simpa using this


theorem sp0_t22_7 (d : ℕ) : SPG d 0 2 2 7 := by
  obtain ⟨G, hG, hR, hS, hE, hf⟩ := numTreeGU d [0, 10, 18, 11, 19, 12, 20, 28, 36, 44, 52, 60]
    [0, 0, 1, 0, 3, 0, 5, 6, 7, 8, 9, 10]
    [0, 11, 3, 10, 4, 9, 2, 7, 6, 8, 5, 1] (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  have hm := mem_list_iff (names := [0, 10, 18, 11, 19, 12, 20, 28, 36, 44, 52, 60]) (φ := fun z => z = 0 ∨ (z % 8 = 2 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 2) ∨ (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 2) ∨ (z % 8 = 4 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 7)) 64
    (by decide +kernel) (by decide +kernel) (by intro z hz; omega)
  refine ⟨G, hG, hR, fun z => by rw [hS, hm z]; rfl, by rw [hE]; rfl, Or.inl ?_⟩
  have := hf 0 (by decide)
  simpa using this


theorem sp0_t22_8 (d : ℕ) : SPG d 0 2 2 8 := by
  obtain ⟨G, hG, hR, hS, hE, hf⟩ := numTreeGU d [0, 10, 18, 11, 19, 12, 20, 28, 36, 44, 52, 60, 68]
    [0, 0, 1, 0, 3, 0, 5, 6, 7, 8, 9, 10, 11]
    [0, 12, 3, 11, 4, 10, 2, 8, 5, 9, 7, 6, 1] (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  have hm := mem_list_iff (names := [0, 10, 18, 11, 19, 12, 20, 28, 36, 44, 52, 60, 68]) (φ := fun z => z = 0 ∨ (z % 8 = 2 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 2) ∨ (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 2) ∨ (z % 8 = 4 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 8)) 72
    (by decide +kernel) (by decide +kernel) (by intro z hz; omega)
  refine ⟨G, hG, hR, fun z => by rw [hS, hm z]; rfl, by rw [hE]; rfl, Or.inl ?_⟩
  have := hf 0 (by decide)
  simpa using this


theorem sp0_tE_2 (d : ℕ) : SPG d 0 4 4 4 := by
  obtain ⟨G, hG, hR, hS, hE, hf⟩ := numTreeGU d [0, 10, 18, 26, 34, 11, 19, 27, 35, 12, 20, 28, 36]
    [0, 0, 1, 2, 3, 0, 5, 6, 7, 0, 9, 10, 11]
    [0, 12, 3, 9, 7, 11, 4, 8, 5, 10, 2, 1, 6] (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  have hm := mem_list_iff (names := [0, 10, 18, 26, 34, 11, 19, 27, 35, 12, 20, 28, 36]) (φ := fun z => z = 0 ∨ (z % 8 = 2 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 4) ∨ (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 4) ∨ (z % 8 = 4 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 4)) 40
    (by decide +kernel) (by decide +kernel) (by intro z hz; omega)
  refine ⟨G, hG, hR, fun z => by rw [hS, hm z]; rfl, by rw [hE]; rfl, Or.inl ?_⟩
  have := hf 0 (by decide)
  simpa using this


theorem sp0_tE_3 (d : ℕ) : SPG d 0 6 6 6 := by
  obtain ⟨G, hG, hR, hS, hE, hf⟩ := numTreeGU d [0, 10, 18, 26, 34, 42, 50, 11, 19, 27, 35, 43, 51, 12, 20, 28, 36, 44, 52]
    [0, 0, 1, 2, 3, 4, 5, 0, 7, 8, 9, 10, 11, 0, 13, 14, 15, 16, 17]
    [0, 18, 3, 15, 6, 9, 1, 17, 4, 14, 7, 8, 12, 16, 2, 13, 11, 5, 10] (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  have hm := mem_list_iff (names := [0, 10, 18, 26, 34, 42, 50, 11, 19, 27, 35, 43, 51, 12, 20, 28, 36, 44, 52]) (φ := fun z => z = 0 ∨ (z % 8 = 2 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 6) ∨ (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 6) ∨ (z % 8 = 4 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 6)) 56
    (by decide +kernel) (by decide +kernel) (by intro z hz; omega)
  refine ⟨G, hG, hR, fun z => by rw [hS, hm z]; rfl, by rw [hE]; rfl, Or.inl ?_⟩
  have := hf 0 (by decide)
  simpa using this


theorem sp0_tE_4 (d : ℕ) : SPG d 0 8 8 8 := by
  obtain ⟨G, hG, hR, hS, hE, hf⟩ := numTreeGU d [0, 10, 18, 26, 34, 42, 50, 58, 66, 11, 19, 27, 35, 43, 51, 59, 67, 12, 20, 28, 36, 44, 52, 60, 68]
    [0, 0, 1, 2, 3, 4, 5, 6, 7, 0, 9, 10, 11, 12, 13, 14, 15, 0, 17, 18, 19, 20, 21, 22, 23]
    [0, 24, 3, 21, 6, 18, 9, 1, 8, 23, 4, 20, 7, 17, 11, 14, 13, 22, 2, 19, 5, 16, 12, 10, 15] (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  have hm := mem_list_iff (names := [0, 10, 18, 26, 34, 42, 50, 58, 66, 11, 19, 27, 35, 43, 51, 59, 67, 12, 20, 28, 36, 44, 52, 60, 68]) (φ := fun z => z = 0 ∨ (z % 8 = 2 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 8) ∨ (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 8) ∨ (z % 8 = 4 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 8)) 72
    (by decide +kernel) (by decide +kernel) (by intro z hz; omega)
  refine ⟨G, hG, hR, fun z => by rw [hS, hm z]; rfl, by rw [hE]; rfl, Or.inl ?_⟩
  have := hf 0 (by decide)
  simpa using this


theorem sp0_tE_5 (d : ℕ) : SPG d 0 10 10 10 := by
  obtain ⟨G, hG, hR, hS, hE, hf⟩ := numTreeGU d [0, 10, 18, 26, 34, 42, 50, 58, 66, 74, 82, 11, 19, 27, 35, 43, 51, 59, 67, 75, 83, 12, 20, 28, 36, 44, 52, 60, 68, 76, 84]
    [0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 0, 11, 12, 13, 14, 15, 16, 17, 18, 19, 0, 21, 22, 23, 24, 25, 26, 27, 28, 29]
    [0, 30, 3, 27, 6, 24, 9, 21, 13, 12, 1, 29, 4, 26, 7, 23, 10, 20, 14, 19, 16, 28, 2, 25, 5, 22, 8, 17, 15, 11, 18] (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  have hm := mem_list_iff (names := [0, 10, 18, 26, 34, 42, 50, 58, 66, 74, 82, 11, 19, 27, 35, 43, 51, 59, 67, 75, 83, 12, 20, 28, 36, 44, 52, 60, 68, 76, 84]) (φ := fun z => z = 0 ∨ (z % 8 = 2 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 10) ∨ (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 10) ∨ (z % 8 = 4 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 10)) 88
    (by decide +kernel) (by decide +kernel) (by intro z hz; omega)
  refine ⟨G, hG, hR, fun z => by rw [hS, hm z]; rfl, by rw [hE]; rfl, Or.inl ?_⟩
  have := hf 0 (by decide)
  simpa using this


theorem sp0_tE_6 (d : ℕ) : SPG d 0 12 12 12 := by
  obtain ⟨G, hG, hR, hS, hE, hf⟩ := numTreeGU d [0, 10, 18, 26, 34, 42, 50, 58, 66, 74, 82, 90, 98, 11, 19, 27, 35, 43, 51, 59, 67, 75, 83, 91, 99, 12, 20, 28, 36, 44, 52, 60, 68, 76, 84, 92, 100]
    [0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 0, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 0, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35]
    [0, 36, 3, 33, 6, 30, 9, 27, 12, 24, 17, 15, 1, 35, 4, 32, 7, 29, 10, 26, 13, 23, 19, 20, 11, 34, 2, 31, 5, 28, 8, 25, 14, 22, 16, 21, 18] (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  have hm := mem_list_iff (names := [0, 10, 18, 26, 34, 42, 50, 58, 66, 74, 82, 90, 98, 11, 19, 27, 35, 43, 51, 59, 67, 75, 83, 91, 99, 12, 20, 28, 36, 44, 52, 60, 68, 76, 84, 92, 100]) (φ := fun z => z = 0 ∨ (z % 8 = 2 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 12) ∨ (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 12) ∨ (z % 8 = 4 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 12)) 104
    (by decide +kernel) (by decide +kernel) (by intro z hz; omega)
  refine ⟨G, hG, hR, fun z => by rw [hS, hm z]; rfl, by rw [hE]; rfl, Or.inl ?_⟩
  have := hf 0 (by decide)
  simpa using this


theorem sp0_tE_7 (d : ℕ) : SPG d 0 14 14 14 := by
  obtain ⟨G, hG, hR, hS, hE, hf⟩ := numTreeGU d [0, 10, 18, 26, 34, 42, 50, 58, 66, 74, 82, 90, 98, 106, 114, 11, 19, 27, 35, 43, 51, 59, 67, 75, 83, 91, 99, 107, 115, 12, 20, 28, 36, 44, 52, 60, 68, 76, 84, 92, 100, 108, 116]
    [0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 0, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 0, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41]
    [0, 42, 3, 39, 6, 36, 9, 33, 12, 30, 15, 1, 14, 22, 19, 41, 4, 38, 7, 35, 10, 32, 13, 29, 17, 26, 20, 24, 23, 40, 2, 37, 5, 34, 8, 31, 11, 28, 18, 25, 27, 16, 21] (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  have hm := mem_list_iff (names := [0, 10, 18, 26, 34, 42, 50, 58, 66, 74, 82, 90, 98, 106, 114, 11, 19, 27, 35, 43, 51, 59, 67, 75, 83, 91, 99, 107, 115, 12, 20, 28, 36, 44, 52, 60, 68, 76, 84, 92, 100, 108, 116]) (φ := fun z => z = 0 ∨ (z % 8 = 2 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 14) ∨ (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 14) ∨ (z % 8 = 4 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 14)) 120
    (by decide +kernel) (by decide +kernel) (by intro z hz; omega)
  refine ⟨G, hG, hR, fun z => by rw [hS, hm z]; rfl, by rw [hE]; rfl, Or.inl ?_⟩
  have := hf 0 (by decide)
  simpa using this
