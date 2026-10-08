def tpa : ℕ → ℕ := fun i => [0, 0, 1, 2, 3, 4, 5, 0, 7, 8, 9, 10, 11, 0, 13, 14, 15, 16, 17].getD i 0
def tlab : ℕ → ℕ := fun i => [0, 18, 3, 15, 6, 9, 1, 17, 4, 14, 7, 8, 12, 16, 2, 13, 11, 5, 10].getD i 0
example : treeCheck 19 0 false tpa tlab = true := by decide
def tpa2 : ℕ → ℕ := fun i => ([0] ++ (List.range 42)).getD i 0
example : treeCheck 43 0 false (fun i => if i = 0 then 0 else i - 1) (fun i => if i % 2 = 0 then i / 2 else 42 - i / 2) = true := by decide
