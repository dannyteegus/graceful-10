/-! ## SP0 cores with tails, and SP0 for every spider -/

/-- `(2,2,c)`, `c ≥ 9`: the α-core `S(2,2,5)` plus a final graceful tail -/
theorem sp0_225 (d c : ℕ) (hc : 9 ≤ c) : SPG d 0 2 2 c := by
  obtain ⟨A, hS, hE, he, ht⟩ := numTreeAU d 5 0 [0, 10, 18, 11, 19, 12, 20, 28, 36, 44]
    [0, 0, 1, 0, 3, 0, 5, 6, 7, 8] [0, 6, 2, 9, 1, 7, 4, 5, 3, 8] (by decide) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by omega)
  have hm := mem_list_iff (names := [0, 10, 18, 11, 19, 12, 20, 28, 36, 44])
    (φ := fun z => z = 0 ∨ (z % 8 = 2 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 2) ∨ (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 2) ∨
      (z % 8 = 4 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 5)) 48
    (by decide +kernel) (by decide +kernel) (by intro z hz; omega)
  have hS' : ∀ z, z ∈ A.P.S ↔ z = 0 ∨ (z % 8 = 2 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 2) ∨
      (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 2) ∨ (z % 8 = 4 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 5) := by
    intro z; rw [hS, hm z]
  have t44 : A.tau (4 + 8 * 5) = 3 := by have := ht 9 (by decide); simpa using this
  have e0 : A.eps 0 = 0 := by have := he 0 (by decide); simpa using this
  have h0 : (0 : ℕ) ∈ A.P.S := by rw [hS']; left; rfl
  obtain ⟨G, hG, hR, hSG, hEG, hf⟩ := A.attachGArm 4 5 (c - 5) (by omega) (by omega) (by omega)
    (by rw [hS']; omega)
    (by intro i hi hm; rw [hS'] at hm; omega)
    (by intro hm; rw [hS'] at hm; omega)
    (fun e => by omega) (fun e => by omega)
    (by rw [t44]; omega)
  refine ⟨G, hG, hR, fun z => by rw [hSG, hS']; unfold ShU; omega, by rw [hEG, hE]; simp only [List.length_cons, List.length_nil]; omega, ?_⟩
  rcases hf 0 h0 with e | e <;> rw [e0] at e
  · left; exact e
  · right; omega

/-- `(2k)^3`, `k ≥ 8`, `k ≠ 12`: the α-core `S(1,7,1)` plus tails -/
theorem sp0_even_c1 (d k : ℕ) (hk : 8 ≤ k) (hk12 : k ≠ 12) : SPG d 0 (2 * k) (2 * k) (2 * k) := by
  obtain ⟨A, hS, hE, he, ht⟩ := numTreeAU d 4 0 [0, 12, 10, 18, 26, 34, 42, 50, 58, 11]
    [0, 0, 0, 2, 3, 4, 5, 6, 7, 0] [0, 6, 9, 1, 5, 2, 4, 3, 8, 7] (by decide) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by omega)
  have hm := mem_list_iff (names := [0, 12, 10, 18, 26, 34, 42, 50, 58, 11])
    (φ := fun z => z = 0 ∨ (z % 8 = 2 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 7) ∨ (z % 8 = 3 ∧ z / 8 = 1) ∨
      (z % 8 = 4 ∧ z / 8 = 1)) 64
    (by decide +kernel) (by decide +kernel) (by intro z hz; omega)
  have hS0 : ∀ z, z ∈ A.P.S ↔ z = 0 ∨ (z % 8 = 2 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 7) ∨
      (z % 8 = 3 ∧ z / 8 = 1) ∨ (z % 8 = 4 ∧ z / 8 = 1) := by
    intro z; rw [hS, hm z]
  have t58 : A.tau (2 + 8 * 7) = 4 := by have := ht 8 (by decide); simpa using this
  have t11 : A.tau (3 + 8 * 1) = 3 := by have := ht 9 (by decide); simpa using this
  have t12 : A.tau (4 + 8 * 1) = 2 := by have := ht 1 (by decide); simpa using this
  have e0 : A.eps 0 = 0 := by have := he 0 (by decide); simpa using this
  have p58 : par d (2 + 8 * 7) = 1 := by rw [par_arm d 2 7 (by omega) (by omega)]; simp
  have p11 : par d (3 + 8 * 1) = 1 := by rw [par_arm d 3 1 (by omega) (by omega)]; simp
  have p12 : par d (4 + 8 * 1) = 1 := by rw [par_arm d 4 1 (by omega) (by omega)]; simp
  have m0 : (0 : ℕ) ∈ A.P.S := by rw [hS0]; left; rfl
  have m11 : 3 + 8 * 1 ∈ A.P.S := by rw [hS0]; omega
  have m12 : 4 + 8 * 1 ∈ A.P.S := by rw [hS0]; omega
  obtain ⟨B, hSB, hEB, heB, htB, _⟩ := A.attachArm 2 7 (2 * k - 7) (by omega) (by omega) (by omega)
    (by rw [hS0]; omega) (by intro i hi h; rw [hS0] at h; omega) (by intro h; rw [hS0] at h; omega)
    (fun e => by omega) (fun e => by omega)
    (by rw [t58]; exact ⟨by omega, by omega, by omega⟩)
  have hSB' : ∀ z, z ∈ B.P.S ↔ z = 0 ∨ (z % 8 = 2 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 2 * k) ∨
      (z % 8 = 3 ∧ z / 8 = 1) ∨ (z % 8 = 4 ∧ z / 8 = 1) := by
    intro z; rw [hSB, hS0]; omega
  have tB11 : B.tau (3 + 8 * 1) = 3 + (2 * k - 7) / 2 := by
    rw [htB _ m11, t11, p11, p58]; omega
  have tB12 : B.tau (4 + 8 * 1) = 2 + (2 * k - 7) / 2 := by
    rw [htB _ m12, t12, p12, p58]; omega
  have mB0 : (0 : ℕ) ∈ B.P.S := by rw [hSB']; left; rfl
  have mB11 : 3 + 8 * 1 ∈ B.P.S := by rw [hSB']; omega
  have mB12 : 4 + 8 * 1 ∈ B.P.S := by rw [hSB']; omega
  obtain ⟨C, hSC, hEC, heC, htC, _⟩ := B.attachArm 3 1 (2 * k - 1) (by omega) (by omega) (by omega)
    mB11 (by intro i hi h; rw [hSB'] at h; omega) (by intro h; rw [hSB'] at h; omega)
    (fun e => by omega) (fun e => by omega)
    (by rw [tB11]; exact ⟨by omega, by omega, by omega⟩)
  have hSC' : ∀ z, z ∈ C.P.S ↔ z = 0 ∨ (z % 8 = 2 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 2 * k) ∨
      (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 2 * k) ∨ (z % 8 = 4 ∧ z / 8 = 1) := by
    intro z; rw [hSC, hSB']; omega
  have tC12 : C.tau (4 + 8 * 1) = 2 + (2 * k - 7) / 2 + (2 * k - 1) / 2 := by
    rw [htC _ mB12, tB12, p12, p11]; omega
  obtain ⟨G, hG, hR, hSG, hEG, hf⟩ := C.attachGArm 4 1 (2 * k - 1) (by omega) (by omega)
    (by omega) (by rw [hSC']; omega)
    (by intro i hi h; rw [hSC'] at h; omega) (by intro h; rw [hSC'] at h; omega)
    (fun e => by omega) (fun e => by omega)
    (by rw [tC12]; omega)
  refine ⟨G, hG, hR, fun z => by rw [hSG, hSC']; unfold ShU; omega,
    by rw [hEG, hEC, hEB, hE]; simp only [List.length_cons, List.length_nil]; omega, ?_⟩
  have e0' : C.eps 0 = 0 := by rw [heC _ mB0, heB _ m0, e0]
  have mC0 : (0 : ℕ) ∈ C.P.S := by rw [hSC']; left; rfl
  rcases hf 0 mC0 with e | e <;> rw [e0'] at e
  · left; exact e
  · right; omega

/-- `(2k)^3`, `k ≥ 9`, `k ≠ 14`: the α-core `S(1,7,3)` plus tails -/
theorem sp0_even_c3 (d k : ℕ) (hk : 9 ≤ k) (hk14 : k ≠ 14) : SPG d 0 (2 * k) (2 * k) (2 * k) := by
  obtain ⟨A, hS, hE, he, ht⟩ := numTreeAU d 5 0 [0, 12, 10, 18, 26, 34, 42, 50, 58, 11, 19, 27]
    [0, 0, 0, 2, 3, 4, 5, 6, 7, 0, 9, 10] [0, 9, 11, 1, 5, 4, 6, 3, 10, 8, 2, 7] (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by omega)
  have hm := mem_list_iff (names := [0, 12, 10, 18, 26, 34, 42, 50, 58, 11, 19, 27])
    (φ := fun z => z = 0 ∨ (z % 8 = 2 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 7) ∨ (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 3) ∨
      (z % 8 = 4 ∧ z / 8 = 1)) 64
    (by decide +kernel) (by decide +kernel) (by intro z hz; omega)
  have hS0 : ∀ z, z ∈ A.P.S ↔ z = 0 ∨ (z % 8 = 2 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 7) ∨
      (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 3) ∨ (z % 8 = 4 ∧ z / 8 = 1) := by
    intro z; rw [hS, hm z]
  have t58 : A.tau (2 + 8 * 7) = 5 := by have := ht 8 (by decide); simpa using this
  have t27 : A.tau (3 + 8 * 3) = 2 := by have := ht 11 (by decide); simpa using this
  have t12 : A.tau (4 + 8 * 1) = 4 := by have := ht 1 (by decide); simpa using this
  have e0 : A.eps 0 = 0 := by have := he 0 (by decide); simpa using this
  have p58 : par d (2 + 8 * 7) = 1 := by rw [par_arm d 2 7 (by omega) (by omega)]; simp
  have p27 : par d (3 + 8 * 3) = 1 := by rw [par_arm d 3 3 (by omega) (by omega)]; simp
  have p12 : par d (4 + 8 * 1) = 1 := by rw [par_arm d 4 1 (by omega) (by omega)]; simp
  have m0 : (0 : ℕ) ∈ A.P.S := by rw [hS0]; left; rfl
  have m27 : 3 + 8 * 3 ∈ A.P.S := by rw [hS0]; omega
  have m12 : 4 + 8 * 1 ∈ A.P.S := by rw [hS0]; omega
  obtain ⟨B, hSB, hEB, heB, htB, _⟩ := A.attachArm 2 7 (2 * k - 7) (by omega) (by omega) (by omega)
    (by rw [hS0]; omega) (by intro i hi h; rw [hS0] at h; omega) (by intro h; rw [hS0] at h; omega)
    (fun e => by omega) (fun e => by omega)
    (by rw [t58]; exact ⟨by omega, by omega, by omega⟩)
  have hSB' : ∀ z, z ∈ B.P.S ↔ z = 0 ∨ (z % 8 = 2 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 2 * k) ∨
      (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 3) ∨ (z % 8 = 4 ∧ z / 8 = 1) := by
    intro z; rw [hSB, hS0]; omega
  have tB27 : B.tau (3 + 8 * 3) = 2 + (2 * k - 7) / 2 := by
    rw [htB _ m27, t27, p27, p58]; omega
  have tB12 : B.tau (4 + 8 * 1) = 4 + (2 * k - 7) / 2 := by
    rw [htB _ m12, t12, p12, p58]; omega
  have mB0 : (0 : ℕ) ∈ B.P.S := by rw [hSB']; left; rfl
  have mB27 : 3 + 8 * 3 ∈ B.P.S := by rw [hSB']; omega
  have mB12 : 4 + 8 * 1 ∈ B.P.S := by rw [hSB']; omega
  obtain ⟨C, hSC, hEC, heC, htC, _⟩ := B.attachArm 3 3 (2 * k - 3) (by omega) (by omega) (by omega)
    mB27 (by intro i hi h; rw [hSB'] at h; omega) (by intro h; rw [hSB'] at h; omega)
    (fun e => by omega) (fun e => by omega)
    (by rw [tB27]; exact ⟨by omega, by omega, by omega⟩)
  have hSC' : ∀ z, z ∈ C.P.S ↔ z = 0 ∨ (z % 8 = 2 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 2 * k) ∨
      (z % 8 = 3 ∧ 1 ≤ z / 8 ∧ z / 8 ≤ 2 * k) ∨ (z % 8 = 4 ∧ z / 8 = 1) := by
    intro z; rw [hSC, hSB']; omega
  have tC12 : C.tau (4 + 8 * 1) = 4 + (2 * k - 7) / 2 + (2 * k - 3) / 2 := by
    rw [htC _ mB12, tB12, p12, p27]; omega
  obtain ⟨G, hG, hR, hSG, hEG, hf⟩ := C.attachGArm 4 1 (2 * k - 1) (by omega) (by omega)
    (by omega) (by rw [hSC']; omega)
    (by intro i hi h; rw [hSC'] at h; omega) (by intro h; rw [hSC'] at h; omega)
    (fun e => by omega) (fun e => by omega)
    (by rw [tC12]; omega)
  refine ⟨G, hG, hR, fun z => by rw [hSG, hSC']; unfold ShU; omega,
    by rw [hEG, hEC, hEB, hE]; simp only [List.length_cons, List.length_nil]; omega, ?_⟩
  have e0' : C.eps 0 = 0 := by rw [heC _ mB0, heB _ m0, e0]
  have mC0 : (0 : ℕ) ∈ C.P.S := by rw [hSC']; left; rfl
  rcases hf 0 mC0 with e | e <;> rw [e0'] at e
  · left; exact e
  · right; omega

/-- **SP0 for every spider** `a ≤ b ≤ c` -/
theorem sp0_all (d a b c : ℕ) (hd : 1 ≤ d) (ha : 1 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) :
    SPG d 0 a b c := by
  by_cases h22 : a = 2 ∧ b = 2
  · obtain ⟨rfl, rfl⟩ := h22
    by_cases hc : 9 ≤ c
    · exact sp0_225 d c hc
    · interval_cases c
      · exact sp0_t22_2 d
      · exact sp0_t22_3 d
      · exact sp0_t22_4 d
      · exact sp0_t22_5 d
      · exact sp0_t22_6 d
      · exact sp0_t22_7 d
      · exact sp0_t22_8 d
  by_cases he : a = b ∧ b = c ∧ a % 2 = 0
  · obtain ⟨rfl, rfl, h2⟩ := he
    obtain ⟨k, rfl⟩ : ∃ k, a = 2 * k := ⟨a / 2, by omega⟩
    by_cases hk : 8 ≤ k
    · by_cases hk12 : k = 12
      · exact sp0_even_c3 d k (by omega) (by omega)
      · exact sp0_even_c1 d k hk hk12
    · have : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega
      rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact absurd ⟨rfl, rfl⟩ h22
      · exact sp0_tE_2 d
      · exact sp0_tE_3 d
      · exact sp0_tE_4 d
      · exact sp0_tE_5 d
      · exact sp0_tE_6 d
      · exact sp0_tE_7 d
  -- generic: IVL0 on the arms `2, 3` and a final segment on `4`
  have h3 : Arms3 2 3 4 := ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
  obtain ⟨G, hG, hR, hS, hE, hf⟩ := sp0_gen (d := d) (x := a) (y := b) (z := c) h3
    (ivl0_all (x := a) (y := b) hd h3.arms2 ha (by omega) (by omega)) (by omega) (by omega)
  exact ⟨G, hG, hR, fun z => by rw [hS]; rfl, hE, by rcases hf with h | h <;> simp [h]⟩
