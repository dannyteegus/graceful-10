/-! ## Flexible gluing (FGL) -/

/-- join `A` (α, threshold `th`) and `B` by the edge `x - w`. -/
noncomputable def Pc.join (A B : Pc) (th x w : ℕ) : Pc where
  S := A.S ∪ B.S
  R := fun p q => (p ∈ A.S ∧ q ∈ A.S ∧ A.R p q) ∨ (p ∈ B.S ∧ q ∈ B.S ∧ B.R p q) ∨
    (p = x ∧ q = w) ∨ (p = w ∧ q = x)
  f := fun z => if z ∈ A.S then (if A.f z < th then A.f z else A.f z + B.E.card + 1)
    else th + B.f z

/-- ordered version of an unordered pair -/
def opair (x w : ℕ) : ℕ × ℕ := (min x w, max x w)

theorem Pc.join_E {A B : Pc} {th x w : ℕ} (hd : Disjoint A.S B.S) (hx : x ∈ A.S) (hw : w ∈ B.S) :
    (Pc.join A B th x w).E = A.E ∪ B.E ∪ {opair x w} := by
  classical
  have hxw : x ≠ w := fun h => Finset.disjoint_left.mp hd hx (h ▸ hw)
  ext ⟨p, q⟩
  simp only [Pc.mem_E, Finset.mem_union, Finset.mem_singleton, Pc.join, opair, Prod.mk.injEq]
  constructor
  · rintro ⟨hp, hq, hpq, hr⟩
    rcases hr with ⟨a1, a2, a3⟩ | ⟨b1, b2, b3⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl (Or.inl ⟨a1, a2, hpq, a3⟩)
    · exact Or.inl (Or.inr ⟨b1, b2, hpq, b3⟩)
    · right; constructor <;> omega
    · right; constructor <;> omega
  · rintro ((⟨a1, a2, a3, a4⟩ | ⟨b1, b2, b3, b4⟩) | ⟨h1, h2⟩)
    · exact ⟨Or.inl a1, Or.inl a2, a3, Or.inl ⟨a1, a2, a4⟩⟩
    · exact ⟨Or.inr b1, Or.inr b2, b3, Or.inr (Or.inl ⟨b1, b2, b4⟩)⟩
    · have hne : x < w ∨ w < x := by omega
      rcases hne with h | h
      · have e1 : p = x := by omega
        have e2 : q = w := by omega
        subst e1; subst e2
        exact ⟨Or.inl hx, Or.inr hw, h, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
      · have e1 : p = w := by omega
        have e2 : q = x := by omega
        subst e1; subst e2
        exact ⟨Or.inr hw, Or.inl hx, h, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩

theorem Pc.join_card_E {A B : Pc} {th x w : ℕ} (hd : Disjoint A.S B.S) (hx : x ∈ A.S)
    (hw : w ∈ B.S) : (Pc.join A B th x w).E.card = A.E.card + B.E.card + 1 := by
  classical
  rw [Pc.join_E hd hx hw]
  have d1 : Disjoint A.E B.E := by
    rw [Finset.disjoint_left]
    intro e he he'
    exact Finset.disjoint_left.mp hd (Pc.mem_E.mp he).1 (Pc.mem_E.mp he').1
  have d2 : Disjoint (A.E ∪ B.E) {opair x w} := by
    rw [Finset.disjoint_singleton_right, Finset.mem_union]
    rintro (h | h)
    · have := Pc.mem_E.mp h
      simp only [opair] at this
      rcases le_total x w with hl | hl
      · rw [max_eq_right hl] at this
        exact Finset.disjoint_left.mp hd this.2.1 hw
      · rw [min_eq_right hl] at this
        exact Finset.disjoint_left.mp hd this.1 hw
    · have := Pc.mem_E.mp h
      simp only [opair] at this
      rcases le_total x w with hl | hl
      · rw [min_eq_left hl] at this
        exact Finset.disjoint_left.mp hd hx this.1
      · rw [max_eq_left hl] at this
        exact Finset.disjoint_left.mp hd hx this.2.1
  rw [Finset.card_union_of_disjoint d2, Finset.card_union_of_disjoint d1, Finset.card_singleton]

theorem Pc.join_f_lowA {A B : Pc} {th x w z : ℕ} (hz : z ∈ A.S) (hl : A.f z < th) :
    (Pc.join A B th x w).f z = A.f z := by
  simp [Pc.join, hz, hl]

theorem Pc.join_f_highA {A B : Pc} {th x w z : ℕ} (hz : z ∈ A.S) (hl : th ≤ A.f z) :
    (Pc.join A B th x w).f z = A.f z + B.E.card + 1 := by
  have : ¬ A.f z < th := by omega
  simp [Pc.join, hz, this]

theorem Pc.join_f_B {A B : Pc} {th x w z : ℕ} (hd : Disjoint A.S B.S) (hz : z ∈ B.S) :
    (Pc.join A B th x w).f z = th + B.f z := by
  have : z ∉ A.S := fun h => Finset.disjoint_left.mp hd h hz
  simp [Pc.join, this]

theorem Pc.Grace.dist_pos {P : Pc} (hP : P.Grace) {e : ℕ × ℕ} (he : e ∈ P.E) :
    1 ≤ Nat.dist (P.f e.1) (P.f e.2) := by
  obtain ⟨_, _, hinj, _, _⟩ := hP
  obtain ⟨h1, h2, h3, _⟩ := Pc.mem_E.mp he
  have hne : P.f e.1 ≠ P.f e.2 := fun h => absurd (hinj _ h1 _ h2 h) (by omega)
  simp only [Nat.dist]; omega

theorem Pc.Grace.dist_le {P : Pc} (hP : P.Grace) {e : ℕ × ℕ} (he : e ∈ P.E) :
    Nat.dist (P.f e.1) (P.f e.2) ≤ P.E.card := by
  obtain ⟨_, _, _, hle, _⟩ := hP
  obtain ⟨h1, h2, _, _⟩ := Pc.mem_E.mp he
  have := hle _ h1
  have := hle _ h2
  simp only [Nat.dist]; omega

theorem Pc.fgl {A B : Pc} {th x w : ℕ} (hA : A.Alpha th) (hB : B.Grace) (hd : Disjoint A.S B.S)
    (hx : x ∈ A.S) (hw : w ∈ B.S)
    (hc : (A.f x < th ∧ B.f w + (th - 1 - A.f x) = B.E.card) ∨ (th ≤ A.f x ∧ B.f w + th = A.f x)) :
    (Pc.join A B th x w).Grace := by
  classical
  have hAg := hA.1
  obtain ⟨hAsym, hAcard, hAinj, hAle, hAedge⟩ := hA.1
  have hth := hA.2.1
  have hAalt := hA.2.2
  obtain ⟨hBsym, hBcard, hBinj, hBle, hBedge⟩ := hB
  have hBg : B.Grace := ⟨hBsym, hBcard, hBinj, hBle, hBedge⟩
  have hcardE := Pc.join_card_E (th := th) hd hx hw
  have hE := Pc.join_E (th := th) hd hx hw
  set J := Pc.join A B th x w with hJ
  set mB := B.E.card with hmB
  have notB : ∀ z ∈ A.S, z ∉ B.S := fun z hz hzB => Finset.disjoint_left.mp hd hz hzB
  -- label of an A-edge
  have eA : ∀ e ∈ A.E, Nat.dist (J.f e.1) (J.f e.2) = Nat.dist (A.f e.1) (A.f e.2) + mB + 1 := by
    intro e he
    obtain ⟨h1, h2, _, hr⟩ := Pc.mem_E.mp he
    have alt := hAalt _ h1 _ h2 hr
    by_cases hl : A.f e.1 < th
    · have hh : th ≤ A.f e.2 := alt.mp hl
      rw [Pc.join_f_lowA h1 hl, Pc.join_f_highA h2 hh]
      simp only [Nat.dist]; omega
    · have hh : A.f e.2 < th := by
        by_contra hc'; exact hl (alt.mpr (by omega))
      rw [Pc.join_f_highA h1 (by omega), Pc.join_f_lowA h2 hh]
      simp only [Nat.dist]; omega
  have eB : ∀ e ∈ B.E, Nat.dist (J.f e.1) (J.f e.2) = Nat.dist (B.f e.1) (B.f e.2) := by
    intro e he
    obtain ⟨h1, h2, _, _⟩ := Pc.mem_E.mp he
    rw [Pc.join_f_B hd h1, Pc.join_f_B hd h2]
    simp only [Nat.dist]; omega
  have eJ : Nat.dist (J.f (opair x w).1) (J.f (opair x w).2) = mB + 1 := by
    have key : Nat.dist (J.f x) (J.f w) = mB + 1 := by
      rw [Pc.join_f_B hd hw]
      rcases hc with ⟨hl, hc⟩ | ⟨hh, hc⟩
      · rw [Pc.join_f_lowA hx hl]; simp only [Nat.dist]; omega
      · rw [Pc.join_f_highA hx hh]; simp only [Nat.dist]; omega
    simp only [opair]
    rcases le_total x w with hl | hl
    · rw [min_eq_left hl, max_eq_right hl]; exact key
    · rw [min_eq_right hl, max_eq_left hl, Nat.dist_comm]; exact key
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro p q h
    simp only [J, Pc.join] at h ⊢
    rcases h with ⟨a1, a2, a3⟩ | ⟨b1, b2, b3⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨a2, a1, hAsym _ _ a3⟩
    · exact Or.inr (Or.inl ⟨b2, b1, hBsym _ _ b3⟩)
    · exact Or.inr (Or.inr (Or.inr ⟨h2, h1⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨h2, h1⟩))
  · rw [hcardE]
    simp only [J, Pc.join]
    rw [Finset.card_union_of_disjoint hd]
    omega
  · intro p hp q hq hpq
    simp only [J, Pc.join, Finset.mem_union] at hp hq
    rcases hp with hp | hp <;> rcases hq with hq | hq
    · by_cases l1 : A.f p < th <;> by_cases l2 : A.f q < th
      · rw [Pc.join_f_lowA hp l1, Pc.join_f_lowA hq l2] at hpq; exact hAinj _ hp _ hq hpq
      · rw [Pc.join_f_lowA hp l1, Pc.join_f_highA hq (by omega)] at hpq; omega
      · rw [Pc.join_f_highA hp (by omega), Pc.join_f_lowA hq l2] at hpq; omega
      · rw [Pc.join_f_highA hp (by omega), Pc.join_f_highA hq (by omega)] at hpq
        exact hAinj _ hp _ hq (by omega)
    · rw [Pc.join_f_B hd hq] at hpq
      have := hBle _ hq
      by_cases l1 : A.f p < th
      · rw [Pc.join_f_lowA hp l1] at hpq; omega
      · rw [Pc.join_f_highA hp (by omega)] at hpq; omega
    · rw [Pc.join_f_B hd hp] at hpq
      have := hBle _ hp
      by_cases l1 : A.f q < th
      · rw [Pc.join_f_lowA hq l1] at hpq; omega
      · rw [Pc.join_f_highA hq (by omega)] at hpq; omega
    · rw [Pc.join_f_B hd hp, Pc.join_f_B hd hq] at hpq
      exact hBinj _ hp _ hq (by omega)
  · intro p hp
    rw [hcardE]
    simp only [J, Pc.join, Finset.mem_union] at hp
    rcases hp with hp | hp
    · have := hAle _ hp
      by_cases l1 : A.f p < th
      · rw [Pc.join_f_lowA hp l1]; omega
      · rw [Pc.join_f_highA hp (by omega)]; omega
    · rw [Pc.join_f_B hd hp]
      have := hBle _ hp
      omega
  · intro e he e' he' heq
    rw [hE] at he he'
    simp only [Finset.mem_union, Finset.mem_singleton] at he he'
    rcases he with (he | he) | he <;> rcases he' with (he' | he') | he'
    · rw [eA e he, eA e' he'] at heq; exact hAedge e he e' he' (by omega)
    · rw [eA e he, eB e' he'] at heq
      have := hBg.dist_le he'; omega
    · rw [eA e he, he', eJ] at heq
      have := hAg.dist_pos he; omega
    · rw [eB e he, eA e' he'] at heq
      have := hBg.dist_le he; omega
    · rw [eB e he, eB e' he'] at heq; exact hBedge e he e' he' heq
    · rw [eB e he, he', eJ] at heq
      have := hBg.dist_le he; omega
    · rw [he, eJ, eA e' he'] at heq
      have := hAg.dist_pos he'; omega
    · rw [he, eJ, eB e' he'] at heq
      have := hBg.dist_le he'; omega
    · rw [he, he']

theorem Pc.fgl_alpha {A B : Pc} {th thB x w : ℕ} (hA : A.Alpha th) (hB : B.Alpha thB)
    (hd : Disjoint A.S B.S) (hx : x ∈ A.S) (hw : w ∈ B.S)
    (hc : (A.f x < th ∧ B.f w + (th - 1 - A.f x) = B.E.card) ∨ (th ≤ A.f x ∧ B.f w + th = A.f x))
    (hcls : A.f x < th ↔ thB ≤ B.f w) :
    (Pc.join A B th x w).Alpha (th + thB) := by
  classical
  have hG := Pc.fgl hA hB.1 hd hx hw hc
  refine ⟨hG, ?_, ?_⟩
  · rw [Pc.join_card_E hd hx hw]
    have := hA.2.1
    have := hB.2.1
    omega
  · have hAalt := hA.2.2
    have hBalt := hB.2.2
    have hthA := hA.2.1
    have hthB := hB.2.1
    intro p hp q hq hr
    simp only [Pc.join, Finset.mem_union] at hp hq hr
    rcases hr with ⟨a1, a2, a3⟩ | ⟨b1, b2, b3⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have alt := hAalt _ a1 _ a2 a3
      by_cases l1 : A.f p < th
      · have h2 : th ≤ A.f q := alt.mp l1
        rw [Pc.join_f_lowA a1 l1, Pc.join_f_highA a2 h2]
        omega
      · have h2 : A.f q < th := by
          by_contra hc'; exact l1 (alt.mpr (by omega))
        rw [Pc.join_f_highA a1 (by omega), Pc.join_f_lowA a2 h2]
        omega
    · have alt := hBalt _ b1 _ b2 b3
      rw [Pc.join_f_B hd b1, Pc.join_f_B hd b2]
      omega
    · subst h1; subst h2
      rw [Pc.join_f_B hd hw]
      by_cases l1 : A.f p < th
      · rw [Pc.join_f_lowA hx l1]; have := hcls.mp l1; omega
      · rw [Pc.join_f_highA hx (by omega)]
        have : ¬ thB ≤ B.f q := fun h => l1 (hcls.mpr h)
        omega
    · subst h1; subst h2
      rw [Pc.join_f_B hd hw]
      by_cases l1 : A.f q < th
      · rw [Pc.join_f_lowA hx l1]; have := hcls.mp l1; omega
      · rw [Pc.join_f_highA hx (by omega)]
        have : ¬ thB ≤ B.f p := fun h => l1 (hcls.mpr h)
        omega

/-- complement of a piece's labeling -/
noncomputable def Pc.cmp (P : Pc) : Pc where
  S := P.S
  R := P.R
  f := fun z => P.E.card - P.f z

theorem Pc.cmp_E (P : Pc) : P.cmp.E = P.E := rfl

theorem Pc.cmp_grace {P : Pc} (hP : P.Grace) : P.cmp.Grace := by
  obtain ⟨hsym, hcard, hinj, hle, hedge⟩ := hP
  refine ⟨hsym, hcard, ?_, ?_, ?_⟩
  · intro x hx y hy h
    simp only [Pc.cmp] at h
    have := hle x hx; have := hle y hy
    exact hinj x hx y hy (by omega)
  · intro x _
    show P.E.card - P.f x ≤ P.cmp.E.card
    rw [Pc.cmp_E]; omega
  · intro e he e' he' h
    rw [Pc.cmp_E] at he he'
    apply hedge e he e' he'
    obtain ⟨a1, a2, _, _⟩ := Pc.mem_E.mp he
    obtain ⟨b1, b2, _, _⟩ := Pc.mem_E.mp he'
    have := hle _ a1; have := hle _ a2; have := hle _ b1; have := hle _ b2
    simp only [Pc.cmp, Nat.dist] at h ⊢
    omega

theorem Pc.cmp_alpha {P : Pc} {th : ℕ} (hP : P.Alpha th) : P.cmp.Alpha (P.E.card + 1 - th) := by
  refine ⟨Pc.cmp_grace hP.1, ?_, ?_⟩
  · rw [Pc.cmp_E]; omega
  · intro x hx y hy hr
    have alt := hP.2.2 x hx y hy hr
    have := hP.1.2.2.2.1 x hx
    have := hP.1.2.2.2.1 y hy
    have := hP.2.1
    simp only [Pc.cmp]
    omega
