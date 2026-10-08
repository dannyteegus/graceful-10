/-! ## Induced pieces: all pieces share one global symmetric adjacency `R` -/

theorem Pc.E_congr {P Q : Pc} (hS : P.S = Q.S)
    (hR : ∀ x ∈ P.S, ∀ y ∈ P.S, P.R x y ↔ Q.R x y) : P.E = Q.E := by
  classical
  ext e
  rw [Pc.mem_E, Pc.mem_E, ← hS]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨h1, h2, h3, (hR _ h1 _ h2).mp h4⟩
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨h1, h2, h3, (hR _ h1 _ h2).mpr h4⟩

theorem Pc.grace_congr {P Q : Pc} (hP : P.Grace) (hS : P.S = Q.S)
    (hR : ∀ x ∈ P.S, ∀ y ∈ P.S, P.R x y ↔ Q.R x y) (hf : ∀ x ∈ P.S, P.f x = Q.f x)
    (hsym : ∀ x y, Q.R x y → Q.R y x) : Q.Grace := by
  obtain ⟨_, hcard, hinj, hle, hedge⟩ := hP
  have hE := Pc.E_congr hS hR
  refine ⟨hsym, ?_, ?_, ?_, ?_⟩
  · rw [← hS, ← hE]; exact hcard
  · intro x hx y hy h
    rw [← hS] at hx hy
    rw [← hf x hx, ← hf y hy] at h
    exact hinj x hx y hy h
  · intro x hx
    rw [← hS] at hx
    rw [← hf x hx, ← hE]; exact hle x hx
  · intro e he e' he' h
    rw [← hE] at he he'
    obtain ⟨a1, a2, _, _⟩ := Pc.mem_E.mp he
    obtain ⟨b1, b2, _, _⟩ := Pc.mem_E.mp he'
    rw [← hf _ a1, ← hf _ a2, ← hf _ b1, ← hf _ b2] at h
    exact hedge e he e' he' h

theorem Pc.alpha_congr {P Q : Pc} {th : ℕ} (hP : P.Alpha th) (hS : P.S = Q.S)
    (hR : ∀ x ∈ P.S, ∀ y ∈ P.S, P.R x y ↔ Q.R x y) (hf : ∀ x ∈ P.S, P.f x = Q.f x)
    (hsym : ∀ x y, Q.R x y → Q.R y x) : Q.Alpha th := by
  refine ⟨Pc.grace_congr hP.1 hS hR hf hsym, ?_, ?_⟩
  · rw [← Pc.E_congr hS hR]; exact hP.2.1
  · intro x hx y hy hr
    rw [← hS] at hx hy
    rw [← hf x hx, ← hf y hy]
    exact hP.2.2 x hx y hy ((hR x hx y hy).mpr hr)

/-- the induced join: same global `R`, labeling as in `Pc.join`. -/
noncomputable def Pc.ijoin (A B : Pc) (th x w : ℕ) : Pc where
  S := A.S ∪ B.S
  R := A.R
  f := (Pc.join A B th x w).f

theorem Pc.ijoin_R {A B : Pc} {th x w : ℕ} (hR : A.R = B.R) (hsym : ∀ p q, A.R p q → A.R q p)
    (hd : Disjoint A.S B.S) (hxw : A.R x w)
    (hcross : ∀ p ∈ A.S, ∀ q ∈ B.S, A.R p q → p = x ∧ q = w) :
    ∀ p ∈ (Pc.join A B th x w).S, ∀ q ∈ (Pc.join A B th x w).S,
      (Pc.join A B th x w).R p q ↔ (Pc.ijoin A B th x w).R p q := by
  intro p hp q hq
  simp only [Pc.join, Pc.ijoin, Finset.mem_union] at hp hq ⊢
  constructor
  · rintro (⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact h
    · rw [hR]; exact h
    · exact hxw
    · exact hsym _ _ hxw
  · intro h
    rcases hp with hp | hp <;> rcases hq with hq | hq
    · exact Or.inl ⟨hp, hq, h⟩
    · obtain ⟨rfl, rfl⟩ := hcross p hp q hq h
      exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
    · obtain ⟨rfl, rfl⟩ := hcross q hq p hp (hsym _ _ h)
      exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))
    · exact Or.inr (Or.inl ⟨hp, hq, by rw [← hR]; exact h⟩)

theorem Pc.ifgl {A B : Pc} {th x w : ℕ} (hA : A.Alpha th) (hB : B.Grace) (hR : A.R = B.R)
    (hd : Disjoint A.S B.S) (hx : x ∈ A.S) (hw : w ∈ B.S) (hxw : A.R x w)
    (hcross : ∀ p ∈ A.S, ∀ q ∈ B.S, A.R p q → p = x ∧ q = w)
    (hc : (A.f x < th ∧ B.f w + (th - 1 - A.f x) = B.E.card) ∨ (th ≤ A.f x ∧ B.f w + th = A.f x)) :
    (Pc.ijoin A B th x w).Grace :=
  Pc.grace_congr (Pc.fgl hA hB hd hx hw hc) rfl
    (Pc.ijoin_R hR hA.1.1 hd hxw hcross) (fun _ _ => rfl) hA.1.1

theorem Pc.ifgl_alpha {A B : Pc} {th thB x w : ℕ} (hA : A.Alpha th) (hB : B.Alpha thB)
    (hR : A.R = B.R) (hd : Disjoint A.S B.S) (hx : x ∈ A.S) (hw : w ∈ B.S) (hxw : A.R x w)
    (hcross : ∀ p ∈ A.S, ∀ q ∈ B.S, A.R p q → p = x ∧ q = w)
    (hc : (A.f x < th ∧ B.f w + (th - 1 - A.f x) = B.E.card) ∨ (th ≤ A.f x ∧ B.f w + th = A.f x))
    (hcls : A.f x < th ↔ thB ≤ B.f w) :
    (Pc.ijoin A B th x w).Alpha (th + thB) :=
  Pc.alpha_congr (Pc.fgl_alpha hA hB hd hx hw hc hcls) rfl
    (Pc.ijoin_R hR hA.1.1 hd hxw hcross) (fun _ _ => rfl) hA.1.1

theorem Pc.ijoin_card_E {A B : Pc} {th x w : ℕ} (hR : A.R = B.R) (hsym : ∀ p q, A.R p q → A.R q p)
    (hd : Disjoint A.S B.S) (hx : x ∈ A.S) (hw : w ∈ B.S) (hxw : A.R x w)
    (hcross : ∀ p ∈ A.S, ∀ q ∈ B.S, A.R p q → p = x ∧ q = w) :
    (Pc.ijoin A B th x w).E.card = A.E.card + B.E.card + 1 := by
  have h := Pc.E_congr (P := Pc.join A B th x w) (Q := Pc.ijoin A B th x w) rfl
    (Pc.ijoin_R hR hsym hd hxw hcross)
  rw [← h, Pc.join_card_E hd hx hw]

/-- an induced path piece with global adjacency `R`. -/
noncomputable def ipathPc (R : ℕ → ℕ → Prop) (n : ℕ) (nm pos L : ℕ → ℕ) : Pc where
  S := (Finset.range n).image nm
  R := R
  f := fun z => L (pos z)

theorem ipathPc_alpha {R : ℕ → ℕ → Prop} {n lam : ℕ} {nm pos L : ℕ → ℕ} (hn : 1 ≤ n)
    (hsym : ∀ p q, R p q → R q p)
    (hinj : ∀ i j, i < n → j < n → nm i = nm j → i = j) (hpos : ∀ i, i < n → pos (nm i) = i)
    (hcons : ∀ i, i + 1 < n → R (nm i) (nm (i + 1)))
    (hchord : ∀ i j, i < n → j < n → R (nm i) (nm j) → i = j + 1 ∨ j = i + 1)
    (hL : PathAlpha n L lam) (hlam : lam < n) :
    (ipathPc R n nm pos L).Alpha (lam + 1) := by
  refine Pc.alpha_congr (pathPc_alpha hn hinj hpos hL hlam) rfl ?_ (fun _ _ => rfl) hsym
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
