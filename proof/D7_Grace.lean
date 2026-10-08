/-! ## Graceful (not necessarily α) pieces: EPL, final segments, joins, leaf chains -/

/-- `L` is a graceful labeling of the path `0 - 1 - ⋯ - (n-1)` -/
def PathGrace (n : ℕ) (L : ℕ → ℕ) : Prop :=
  (∀ i j, i < n → j < n → L i = L j → i = j) ∧
  (∀ i, i < n → L i ≤ n - 1) ∧
  (∀ i j, i + 1 < n → j + 1 < n →
      Nat.dist (L i) (L (i + 1)) = Nat.dist (L j) (L (j + 1)) → i = j)

theorem PathAlpha.grace {n lam : ℕ} {L : ℕ → ℕ} (h : PathAlpha n L lam) : PathGrace n L :=
  ⟨h.1, h.2.1, h.2.2.1⟩

theorem pathPc_grace {n : ℕ} {nm pos L : ℕ → ℕ} (hn : 1 ≤ n)
    (hinj : ∀ i j, i < n → j < n → nm i = nm j → i = j) (hpos : ∀ i, i < n → pos (nm i) = i)
    (hL : PathGrace n L) : (pathPc n nm pos L).Grace := by
  classical
  obtain ⟨Linj, Lle, Ledge⟩ := hL
  have hE := pathPc_card_E (pos := pos) (L := L) hinj
  have fval : ∀ i, i < n → (pathPc n nm pos L).f (nm i) = L i := by
    intro i hi; simp [pathPc, hpos i hi]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro p q ⟨i, hi, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩
    · exact ⟨i, hi, Or.inr ⟨rfl, rfl⟩⟩
    · exact ⟨i, hi, Or.inl ⟨rfl, rfl⟩⟩
  · rw [pathPc_card_S hinj, hE]; omega
  · intro x hx y hy hxy
    obtain ⟨i, hi, rfl⟩ := pathPc_mem_S.mp hx
    obtain ⟨j, hj, rfl⟩ := pathPc_mem_S.mp hy
    rw [fval i hi, fval j hj] at hxy
    rw [Linj i j hi hj hxy]
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := pathPc_mem_S.mp hx
    rw [fval i hi, hE]; exact Lle i hi
  · intro e he e' he' h
    rw [pathPc_E hinj, Finset.mem_image] at he he'
    obtain ⟨i, hi, rfl⟩ := he
    obtain ⟨j, hj, rfl⟩ := he'
    simp only [Finset.mem_range] at hi hj
    have dd : ∀ k, k + 1 < n → Nat.dist ((pathPc n nm pos L).f (opair (nm k) (nm (k + 1))).1)
        ((pathPc n nm pos L).f (opair (nm k) (nm (k + 1))).2) = Nat.dist (L k) (L (k + 1)) := by
      intro k hk
      simp only [opair]
      rcases le_total (nm k) (nm (k + 1)) with a | a
      · rw [min_eq_left a, max_eq_right a, fval k (by omega), fval (k + 1) (by omega)]
      · rw [min_eq_right a, max_eq_left a, fval k (by omega), fval (k + 1) (by omega), Nat.dist_comm]
    rw [dd i (by omega), dd j (by omega)] at h
    rw [Ledge i j (by omega) (by omega) h]

theorem ipathPc_grace {R : ℕ → ℕ → Prop} {n : ℕ} {nm pos L : ℕ → ℕ} (hn : 1 ≤ n)
    (hsym : ∀ p q, R p q → R q p)
    (hinj : ∀ i j, i < n → j < n → nm i = nm j → i = j) (hpos : ∀ i, i < n → pos (nm i) = i)
    (hcons : ∀ i, i + 1 < n → R (nm i) (nm (i + 1)))
    (hchord : ∀ i j, i < n → j < n → R (nm i) (nm j) → i = j + 1 ∨ j = i + 1)
    (hL : PathGrace n L) :
    (ipathPc R n nm pos L).Grace := by
  refine Pc.grace_congr (pathPc_grace hn hinj hpos hL) rfl ?_ (fun _ _ => rfl) hsym
  intro x hx y hy
  obtain ⟨i, hi, rfl⟩ := pathPc_mem_S.mp hx
  obtain ⟨j, hj, rfl⟩ := pathPc_mem_S.mp hy
  simp only [pathPc, ipathPc]
  constructor
  · rintro ⟨k, hk, (⟨h1, h2⟩ | ⟨h1, h2⟩)⟩
    · rw [h1, h2]; exact hcons k hk
    · rw [h1, h2]; exact hsym _ _ (hcons k hk)
  · intro h
    rcases hchord i j hi hj h with e | e
    · exact ⟨j, by omega, Or.inr ⟨by rw [e], rfl⟩⟩
    · exact ⟨i, by omega, Or.inl ⟨rfl, by rw [e]⟩⟩

/-- complement of a graceful path labeling -/
theorem PathGrace.comp {n : ℕ} {L : ℕ → ℕ} (h : PathGrace n L) : PathGrace n (fun i => n - 1 - L i) := by
  obtain ⟨hinj, hle, hedge⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro i j hi hj e
    have := hle i hi; have := hle j hj
    have e' : n - 1 - L i = n - 1 - L j := e
    exact hinj i j hi hj (by omega)
  · intro i _; show n - 1 - L i ≤ n - 1; omega
  · intro i j hi hj e
    apply hedge i j hi hj
    have := hle i (by omega); have := hle (i + 1) hi; have := hle j (by omega); have := hle (j + 1) hj
    simp only [Nat.dist] at e ⊢
    omega

/-- **EPL.** The path on `n` vertices has a graceful labeling with first label `t`, `t ≤ n-1`. -/
theorem epl (n t : ℕ) (hn : 1 ≤ n) (ht : t ≤ n - 1) : ∃ L : ℕ → ℕ, PathGrace n L ∧ L 0 = t := by
  classical
  by_cases h1 : AeplOK n t
  · obtain ⟨L, hL, h0⟩ := aepl n t h1
    exact ⟨L, hL.grace, h0⟩
  by_cases h2 : AeplOK n (n - 1 - t)
  · obtain ⟨L, hL, h0⟩ := aepl n (n - 1 - t) h2
    exact ⟨fun i => n - 1 - L i, hL.grace.comp, by show n - 1 - L 0 = t; omega⟩
  -- exceptional: n = 4q+1, t ∈ {q, 3q}
  have hex : ∃ q, 1 ≤ q ∧ n = 4 * q + 1 ∧ (t = q ∨ t = 3 * q) := by
    unfold AeplOK at h1 h2
    refine ⟨(n - 1) / 4, ?_, ?_, ?_⟩ <;> omega
  obtain ⟨q, hq, hn', ht'⟩ := hex
  -- the case t = q, by FGL of α-EPL(3q, q) and a zigzag of q+1 vertices
  have main : ∃ L : ℕ → ℕ, PathGrace n L ∧ L 0 = q := by
    have hok : AeplOK (3 * q) q := ⟨by omega, by omega, by omega⟩
    obtain ⟨L1, hL1, h10⟩ := aepl (3 * q) q hok
    set lam1 := (3 * q - 1) / 2 with hlam1
    have hl0 : L1 0 ≤ lam1 := by rw [h10]; omega
    have hlast := ptau_last hL1 (by omega) hl0
    set A := pathPc (3 * q) id id L1 with hA
    have hAa := pathPc_alpha (pos := id) (nm := id) (by omega) (fun i j _ _ e => e) (fun i _ => rfl) hL1
      (by omega)
    have hAE : A.E.card = 3 * q - 1 := pathPc_card_E (fun i j _ _ e => e)
    -- second piece
    set g : ℕ → ℕ := if L1 (3 * q - 1) ≤ lam1 then zz (q + 1) else fun i => q - zz (q + 1) i with hg
    have hgG : PathGrace (q + 1) g := by
      rw [hg]
      split_ifs
      · exact (zz_alpha (q + 1) (by omega)).grace
      · have := (zz_alpha (q + 1) (by omega)).grace.comp
        simpa using this
    set B := pathPc (q + 1) (fun i => i + 3 * q) (fun z => z - 3 * q) g with hB
    have hBinj : ∀ i j, i < q + 1 → j < q + 1 → i + 3 * q = j + 3 * q → i = j := by
      intro i j _ _ e; omega
    have hBg := pathPc_grace (nm := fun i => i + 3 * q) (pos := fun z => z - 3 * q) (by omega) hBinj
      (fun i _ => by simp) hgG
    have hBE : B.E.card = q := by rw [hB, pathPc_card_E hBinj]; omega
    have hd : Disjoint A.S B.S := by
      rw [Finset.disjoint_left]
      intro z hzA hzB
      obtain ⟨i, hi, rfl⟩ := pathPc_mem_S.mp hzA
      obtain ⟨j, hj, e⟩ := pathPc_mem_S.mp hzB
      simp only [id] at e; omega
    have hx : 3 * q - 1 ∈ A.S := pathPc_mem_S.mpr ⟨3 * q - 1, by omega, rfl⟩
    have hw : 3 * q ∈ B.S := pathPc_mem_S.mpr ⟨0, by omega, by simp⟩
    have hfx : A.f (3 * q - 1) = L1 (3 * q - 1) := rfl
    have hfw : B.f (3 * q) = g 0 := by show g (3 * q - 3 * q) = g 0; simp
    have hle1 := hL1.2.1 (3 * q - 1) (by omega)
    have hc : (A.f (3 * q - 1) < lam1 + 1 ∧ B.f (3 * q) + (lam1 + 1 - 1 - A.f (3 * q - 1)) = B.E.card) ∨
        (lam1 + 1 ≤ A.f (3 * q - 1) ∧ B.f (3 * q) + (lam1 + 1) = A.f (3 * q - 1)) := by
      rw [hfx, hfw, hBE]
      unfold ptau at hlast
      by_cases hl : L1 (3 * q - 1) ≤ lam1
      · left
        rw [if_pos hl] at hlast
        refine ⟨by omega, ?_⟩
        rw [hg, if_pos hl]; simp [zz]; omega
      · right
        rw [if_neg hl] at hlast
        refine ⟨by omega, ?_⟩
        rw [hg, if_neg hl]; simp [zz]; omega
    have hJ := Pc.fgl hAa hBg hd hx hw hc
    set J := Pc.join A B (lam1 + 1) (3 * q - 1) (3 * q) with hJdef
    have hJE : J.E.card = 3 * q - 1 + q + 1 := by
      rw [hJdef, Pc.join_card_E hd hx hw, hAE, hBE]
    have hJS : ∀ i, i ∈ J.S ↔ i < n := by
      intro i
      show i ∈ A.S ∪ B.S ↔ _
      rw [Finset.mem_union, pathPc_mem_S, pathPc_mem_S]
      constructor
      · rintro (⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩)
        · show id j < n; simp only [id]; omega
        · omega
      · intro hi
        by_cases h : i < 3 * q
        · exact Or.inl ⟨i, h, rfl⟩
        · exact Or.inr ⟨i - 3 * q, by omega, by omega⟩
    have hJR : ∀ i, i + 1 < n → J.R i (i + 1) := by
      intro i hi
      show (i ∈ A.S ∧ i + 1 ∈ A.S ∧ A.R i (i + 1)) ∨ (i ∈ B.S ∧ i + 1 ∈ B.S ∧ B.R i (i + 1)) ∨
        (i = 3 * q - 1 ∧ i + 1 = 3 * q) ∨ (i = 3 * q ∧ i + 1 = 3 * q - 1)
      by_cases h : i + 1 < 3 * q
      · left
        exact ⟨pathPc_mem_S.mpr ⟨i, by omega, rfl⟩, pathPc_mem_S.mpr ⟨i + 1, h, rfl⟩,
          ⟨i, h, Or.inl ⟨rfl, rfl⟩⟩⟩
      · by_cases h' : i + 1 = 3 * q
        · right; right; left; omega
        · right; left
          refine ⟨pathPc_mem_S.mpr ⟨i - 3 * q, by omega, by omega⟩,
            pathPc_mem_S.mpr ⟨i + 1 - 3 * q, by omega, by omega⟩, ⟨i - 3 * q, by omega, ?_⟩⟩
          left; constructor <;> simp <;> omega
    obtain ⟨_, _, Jinj, Jle, Jedge⟩ := hJ
    refine ⟨fun i => J.f i, ⟨?_, ?_, ?_⟩, ?_⟩
    · intro i j hi hj e
      exact Jinj i ((hJS i).mpr hi) j ((hJS j).mpr hj) e
    · intro i hi
      have := Jle i ((hJS i).mpr hi)
      show J.f i ≤ n - 1
      omega
    · intro i j hi hj e
      have mi : opair i (i + 1) ∈ J.E := by
        rw [Pc.mem_E]; simp only [opair, min_eq_left (Nat.le_succ i), max_eq_right (Nat.le_succ i)]
        exact ⟨(hJS i).mpr (by omega), (hJS (i + 1)).mpr hi, by omega, hJR i hi⟩
      have mj : opair j (j + 1) ∈ J.E := by
        rw [Pc.mem_E]; simp only [opair, min_eq_left (Nat.le_succ j), max_eq_right (Nat.le_succ j)]
        exact ⟨(hJS j).mpr (by omega), (hJS (j + 1)).mpr hj, by omega, hJR j hj⟩
      have := Jedge _ mi _ mj (by
        simp only [opair, min_eq_left (Nat.le_succ i), max_eq_right (Nat.le_succ i),
          min_eq_left (Nat.le_succ j), max_eq_right (Nat.le_succ j)]
        exact e)
      simp only [opair, min_eq_left (Nat.le_succ i), max_eq_right (Nat.le_succ i),
        min_eq_left (Nat.le_succ j), max_eq_right (Nat.le_succ j), Prod.mk.injEq] at this
      exact this.1
    · have h0' : A.f 0 < lam1 + 1 := by show L1 (id 0) < lam1 + 1; simp only [id]; omega
      show J.f 0 = q
      have := Pc.join_f_lowA (B := B) (x := 3 * q - 1) (w := 3 * q)
        (pathPc_mem_S.mpr ⟨0, by omega, rfl⟩ : (0 : ℕ) ∈ A.S) h0'
      rw [hJdef, this]
      show L1 (id 0) = q
      exact h10
  rcases ht' with rfl | rfl
  · exact main
  · obtain ⟨L, hL, h0⟩ := main
    exact ⟨fun i => n - 1 - L i, hL.comp, by show n - 1 - L 0 = 3 * q; omega⟩
