-- H core d=6: names u, a1..a4, b1..b4, d1..d5, v, e1, e2, f1, f2
example : ∃ G : Pc, G.Grace ∧ G.R = Tadj 6 ∧
    (∀ z, z ∈ G.S ↔ ∃ i, i < 19 ∧ [0, 10, 18, 26, 34, 11, 19, 27, 35, 13, 21, 29, 37, 45, 1, 14, 22, 15, 23].getD i 0 = z) ∧
    G.E.card = 18 ∧ True := by
  obtain ⟨G, h1, h2, h3, h4, h5⟩ := numTreeG 6 [0, 10, 18, 26, 34, 11, 19, 27, 35, 13, 21, 29, 37, 45, 1, 14, 22, 15, 23]
    [0, 0, 1, 2, 3, 0, 5, 6, 7, 0, 9, 10, 11, 12, 13, 14, 15, 14, 17]
    [0, 18, 3, 15, 6, 17, 4, 14, 7, 16, 2, 13, 10, 5, 11, 9, 1, 12, 8] (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  exact ⟨G, h1, h2, h3, h4, trivial⟩
