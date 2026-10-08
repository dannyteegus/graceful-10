/-! ## Graceful spiders with the centre at `1` (all but 13 spiders) and at `2` -/

theorem arms_234 : Arms3 2 3 4 := ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
theorem arms_324 : Arms3 3 2 4 := ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
theorem arms_423 : Arms3 4 2 3 := ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
theorem arms_243 : Arms3 2 4 3 := ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩

theorem spg_spA_abc {d σ a b c : ℕ} (hd : 1 ≤ d) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (h1 : AeplOK (a + 1) σ) (h2 : AeplOK b (a / 2 - σ)) (h3 : a / 2 - σ + b / 2 ≤ c - 1) :
    SPG d σ a b c :=
  spg_of_spx arms_234 (spA_prog hd arms_234 ha hb hc h1 h2 h3) (by simp) (by simp) (by simp)

theorem spg_spA_bac {d σ a b c : ℕ} (hd : 1 ≤ d) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (h1 : AeplOK (b + 1) σ) (h2 : AeplOK a (b / 2 - σ)) (h3 : b / 2 - σ + a / 2 ≤ c - 1) :
    SPG d σ a b c :=
  spg_of_spx arms_324 (spA_prog hd arms_324 hb ha hc h1 h2 h3) (by simp) (by simp) (by simp)

theorem spg_spA_cab {d σ a b c : ℕ} (hd : 1 ≤ d) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (h1 : AeplOK (c + 1) σ) (h2 : AeplOK a (c / 2 - σ)) (h3 : c / 2 - σ + a / 2 ≤ b - 1) :
    SPG d σ a b c :=
  spg_of_spx arms_423 (spA_prog hd arms_423 hc ha hb h1 h2 h3) (by simp) (by simp) (by simp)

theorem spg_spA_acb {d σ a b c : ℕ} (hd : 1 ≤ d) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (h1 : AeplOK (a + 1) σ) (h2 : AeplOK c (a / 2 - σ)) (h3 : a / 2 - σ + c / 2 ≤ b - 1) :
    SPG d σ a b c :=
  spg_of_spx arms_243 (spA_prog hd arms_243 ha hc hb h1 h2 h3) (by simp) (by simp) (by simp)

theorem spg_sw1_abc {d a b c : ℕ} (hd : 1 ≤ d) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (h22 : ¬ (a = 2 ∧ b = 2)) (h3 : a / 2 + b / 2 + 4 ≤ c) : SPG d 1 a b c :=
  spg_of_spx arms_234 (sw1_prog hd arms_234 (ivl0_all hd arms_234.arms2 ha hb h22) h3)
    (by simp) (by simp) (by simp)

theorem spg_sw2_abc {d a b c : ℕ} (hd : 1 ≤ d) (ha : 1 ≤ a) (hb : 3 ≤ b) (hc : 1 ≤ c)
    (hok : AeplOK (b - 2) (a / 2 + 1)) (hK : a / 2 + b / 2 ≤ c) : SPG d 1 a b c :=
  spg_of_spx arms_234 (sw2_prog hd arms_234 ha hb hc hok hK) (by simp) (by simp) (by simp)

theorem spg_sw2_acb {d a b c : ℕ} (hd : 1 ≤ d) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 3 ≤ c)
    (hok : AeplOK (c - 2) (a / 2 + 1)) (hK : a / 2 + c / 2 ≤ b) : SPG d 1 a b c :=
  spg_of_spx arms_243 (sw2_prog hd arms_243 ha hc hb hok hK) (by simp) (by simp) (by simp)

/-- the 13 spiders without an SP1 program -/
def F1 (a b c : ℕ) : Prop :=
  (a = 1 ∧ b = 1 ∧ c = 1) ∨ (a = 1 ∧ b = 4 ∧ c = 4) ∨ (a = 4 ∧ b = 4 ∧ c = 4) ∨
  (a = 4 ∧ b = 4 ∧ c = 6) ∨ (a = 4 ∧ b = 4 ∧ c = 7) ∨ (a = 4 ∧ b = 6 ∧ c = 6) ∨
  (a = 4 ∧ b = 6 ∧ c = 7) ∨ (a = 4 ∧ b = 6 ∧ c = 8) ∨ (a = 4 ∧ b = 7 ∧ c = 7) ∨
  (a = 4 ∧ b = 7 ∧ c = 8) ∨ (a = 4 ∧ b = 8 ∧ c = 8) ∨ (a = 5 ∧ b = 5 ∧ c = 5) ∨
  (a = 6 ∧ b = 9 ∧ c = 9)

/-- **SP1**: a graceful spider at `u` with `u` at `1` (or `m - 1`) for every sorted spider not in `F1` -/
theorem sp1_all (d a b c : ℕ) (hd : 1 ≤ d) (ha : 1 ≤ a) (hab : a ≤ b) (hbc : b ≤ c)
    (hF : ¬ F1 a b c) : SPG d 1 a b c := by
  by_cases hA : 2 ≤ a ∧ a ≠ 4 ∧ ¬ (b % 4 = 1 ∧ 1 < b ∧ 4 * (a / 2 - 1) = b - 1)
  · exact spg_spA_abc hd ha (by omega) (by omega) ⟨by omega, by omega, by omega⟩
      ⟨by omega, by omega, by omega⟩ (by omega)
  by_cases h1 : a = 1
  · subst h1
    by_cases hb1 : b = 1
    · subst hb1
      by_cases hc4 : 4 ≤ c
      · exact spg_sw1_abc hd (by omega) (by omega) (by omega) (by omega)
      · have : c = 1 ∨ c = 2 ∨ c = 3 := by omega
        rcases this with rfl | rfl | rfl
        · exact (hF (by unfold F1; decide)).elim
        · exact spg_spA_cab hd (by omega) (by omega) (by omega) ⟨by omega, by omega, by omega⟩
            ⟨by omega, by omega, by omega⟩ (by omega)
        · exact spg_spA_cab hd (by omega) (by omega) (by omega) ⟨by omega, by omega, by omega⟩
            ⟨by omega, by omega, by omega⟩ (by omega)
    by_cases hb23 : b = 2 ∨ b = 3
    · exact spg_spA_bac hd (by omega) (by omega) (by omega) ⟨by omega, by omega, by omega⟩
        ⟨by omega, by omega, by omega⟩ (by omega)
    by_cases hb7 : b = 7
    · exact spg_sw1_abc hd (by omega) (by omega) (by omega) (by omega)
    by_cases hb4 : b = 4
    · subst hb4
      by_cases hc6 : 6 ≤ c
      · exact spg_sw1_abc hd (by omega) (by omega) (by omega) (by omega)
      · have : c = 4 ∨ c = 5 := by omega
        rcases this with rfl | rfl
        · exact (hF (by unfold F1; decide)).elim
        · exact spg_sw2_acb hd (by omega) (by omega) (by omega) ⟨by omega, by omega, by omega⟩
            (by omega)
    · exact spg_sw2_abc hd (by omega) (by omega) (by omega) ⟨by omega, by omega, by omega⟩
        (by omega)
  by_cases h4 : a = 4
  · subst h4
    by_cases hb9 : 9 ≤ b ∧ b ≠ 15
    · exact spg_sw2_abc hd (by omega) (by omega) (by omega) ⟨by omega, by omega, by omega⟩
        (by omega)
    by_cases hs : 4 / 2 + b / 2 + 4 ≤ c
    · exact spg_sw1_abc hd (by omega) (by omega) (by omega) hs
    have hb8 : b ≤ 8 := by omega
    have hc9 : c ≤ 9 := by omega
    interval_cases b <;> interval_cases c <;>
      first
      | omega
      | exact (hF (by unfold F1; decide)).elim
      | exact spg_spA_cab hd (by omega) (by omega) (by omega) ⟨by omega, by omega, by omega⟩
          ⟨by omega, by omega, by omega⟩ (by omega)
      | exact spg_spA_bac hd (by omega) (by omega) (by omega) ⟨by omega, by omega, by omega⟩
          ⟨by omega, by omega, by omega⟩ (by omega)
      | exact spg_sw2_acb hd (by omega) (by omega) (by omega) ⟨by omega, by omega, by omega⟩
          (by omega)
  -- the exceptional `b = 4⌊a/2⌋ - 3`
  have hx : b % 4 = 1 ∧ 1 < b ∧ 4 * (a / 2 - 1) = b - 1 := by
    by_contra hn; exact hA ⟨by omega, h4, hn⟩
  by_cases hs : a / 2 + b / 2 + 4 ≤ c
  · exact spg_sw1_abc hd (by omega) (by omega) (by omega) hs
  have hab' : (a = 5 ∧ b = 5) ∨ (a = 6 ∧ b = 9) ∨ (a = 7 ∧ b = 9) ∨ (a = 8 ∧ b = 13) ∨
      (a = 9 ∧ b = 13) := by omega
  rcases hab' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have : c = 5 ∨ c = 6 ∨ c = 7 := by omega
    rcases this with rfl | rfl | rfl
    · exact (hF (by unfold F1; decide)).elim
    · exact spg_spA_acb hd (by omega) (by omega) (by omega) ⟨by omega, by omega, by omega⟩
        ⟨by omega, by omega, by omega⟩ (by omega)
    · exact spg_spA_acb hd (by omega) (by omega) (by omega) ⟨by omega, by omega, by omega⟩
        ⟨by omega, by omega, by omega⟩ (by omega)
  · have : c = 9 ∨ c = 10 := by omega
    rcases this with rfl | rfl
    · exact (hF (by unfold F1; decide)).elim
    · exact spg_spA_acb hd (by omega) (by omega) (by omega) ⟨by omega, by omega, by omega⟩
        ⟨by omega, by omega, by omega⟩ (by omega)
  · exact spg_spA_bac hd (by omega) (by omega) (by omega) ⟨by omega, by omega, by omega⟩
      ⟨by omega, by omega, by omega⟩ (by omega)
  · exact spg_sw2_abc hd (by omega) (by omega) (by omega) ⟨by omega, by omega, by omega⟩ (by omega)
  · exact spg_sw2_abc hd (by omega) (by omega) (by omega) ⟨by omega, by omega, by omega⟩ (by omega)

/-- the v-side with `τ = 2` at the junction `u`-neighbour, for `d ∈ {4,5}` or `d ≥ 9` -/
theorem vsp2_ok (d : ℕ) (h : d = 4 ∨ d = 5 ∨ 9 ≤ d) : VSP d (d - 1) 2 := by
  apply vsp2 d (d - 1) (by omega)
  by_cases h13 : d = 13
  · subst h13; right; right; right; exact ⟨by omega, by omega, by omega, by omega⟩
  · rcases h with rfl | rfl | h
    · left; rfl
    · right; left; rfl
    · right; right; left; exact ⟨by omega, by omega, by omega, by omega⟩

/-- the v-side with `τ = 1`, for every `d ≠ 3` -/
theorem vsp1_ok (d : ℕ) (hd : 1 ≤ d) (h3 : d ≠ 3) : VSP d (d - 1) 1 := by
  apply vsp1 d (d - 1) (by omega)
  by_cases h1 : d = 1
  · left; omega
  by_cases h2 : d = 2
  · right; right; left; omega
  by_cases h6 : d = 6
  · right; right; right; omega
  · right; left; exact ⟨by omega, by omega, by omega⟩
