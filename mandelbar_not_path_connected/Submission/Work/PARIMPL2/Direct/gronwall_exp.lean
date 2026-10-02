import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.PARIMPL2.Direct

/-- Discrete Gronwall inequality (exponential form).

If `y (j+1) ≤ (1 + c j) * y j + b j` for all `j < n`, with nonnegative `c`, `b`,
and if `∑_{j<n} c j ≤ C` and `∑_{j<n} b j ≤ B`, then `y n ≤ exp C * (y 0 + B)`. -/
theorem gronwall_exp (y c b : ℕ → ℝ) (n : ℕ) (C B : ℝ)
    (hC0 : 0 ≤ C) (hB0 : 0 ≤ B) (hc0 : ∀ j, 0 ≤ c j) (hy : ∀ j, 0 ≤ y j)
    (hb : ∀ j, 0 ≤ b j)
    (hstep : ∀ j < n, y (j + 1) ≤ (1 + c j) * y j + b j)
    (hC : ∑ j ∈ Finset.range n, c j ≤ C) (hB : ∑ j ∈ Finset.range n, b j ≤ B) :
    y n ≤ Real.exp C * (y 0 + B) := by
  -- Stronger induction: with partial sums `Ce m = ∑_{j<m} c j`, `Be m = ∑_{j<m} b j`,
  -- one has `y m ≤ exp (Ce m) * (y 0 + Be m)`.
  have key : ∀ m ≤ n,
      y m ≤ Real.exp (∑ j ∈ Finset.range m, c j) * (y 0 + ∑ j ∈ Finset.range m, b j) := by
    intro m
    induction m with
    | zero =>
      intro _
      simp
    | succ k ih =>
      intro hk
      have hk' : k ≤ n := Nat.le_of_succ_le hk
      have hkn : k < n := by omega
      have hik : y k ≤ Real.exp (∑ j ∈ Finset.range k, c j) * (y 0 + ∑ j ∈ Finset.range k, b j) :=
        ih hk'
      have hstepk : y (k + 1) ≤ (1 + c k) * y k + b k := hstep k hkn
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      set Ce := ∑ j ∈ Finset.range k, c j with hCe
      set Be := ∑ j ∈ Finset.range k, b j with hBe
      have hCe0 : 0 ≤ Ce := by rw [hCe]; exact Finset.sum_nonneg (fun _ _ => hc0 _)
      have hBe0 : 0 ≤ Be := by rw [hBe]; exact Finset.sum_nonneg (fun _ _ => hb _)
      have hT0 : 0 ≤ y 0 + Be := add_nonneg (hy 0) hBe0
      have hA : y (k + 1) ≤ (1 + c k) * y k + b k := hstepk
      have hB' : (1 + c k) * y k ≤ (1 + c k) * (Real.exp Ce * (y 0 + Be)) :=
        mul_le_mul_of_nonneg_left hik (by linarith [hc0 k])
      have hfac : (1 + c k) * Real.exp Ce ≤ Real.exp (Ce + c k) := by
        rw [Real.exp_add]
        calc (1 + c k) * Real.exp Ce
            ≤ Real.exp (c k) * Real.exp Ce :=
              mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp (c k)])
                (Real.exp_nonneg _)
          _ = Real.exp Ce * Real.exp (c k) := by ring
      have hC' : (1 + c k) * (Real.exp Ce * (y 0 + Be)) ≤ Real.exp (Ce + c k) * (y 0 + Be) := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right hfac hT0
      have hD' : b k ≤ Real.exp (Ce + c k) * b k := by
        have h1 : (1:ℝ) ≤ Real.exp (Ce + c k) := Real.one_le_exp (by linarith [hc0 k, hCe0])
        simpa using mul_le_mul_of_nonneg_right h1 (hb k)
      have hE : Real.exp (Ce + c k) * (y 0 + (Be + b k))
          = Real.exp (Ce + c k) * (y 0 + Be) + Real.exp (Ce + c k) * b k := by ring
      rw [hE]
      linarith [hA, hB', hC', hD']
  have hn := key n le_rfl
  calc y n ≤ Real.exp (∑ j ∈ Finset.range n, c j) * (y 0 + ∑ j ∈ Finset.range n, b j) := hn
    _ ≤ Real.exp C * (y 0 + ∑ j ∈ Finset.range n, b j) :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hC)
          (add_nonneg (hy 0) (Finset.sum_nonneg (fun _ _ => hb _)))
    _ ≤ Real.exp C * (y 0 + B) :=
        mul_le_mul_of_nonneg_left (by linarith [hB]) (Real.exp_nonneg C)

end Work.PARIMPL2.Direct
