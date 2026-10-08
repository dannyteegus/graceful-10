example (d : ℕ) : ∀ i, i < 3 → ∀ j, j < 3 →
    (tadjB d ([0, 10, 18].getD i 0) ([0, 10, 18].getD j 0) = true ↔
      (i ≠ 0 ∧ [0, 0, 1].getD i 0 = j) ∨ (j ≠ 0 ∧ [0, 0, 1].getD j 0 = i)) := by
  decide +kernel
