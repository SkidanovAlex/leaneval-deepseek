import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.PARIMPL2.Direct

theorem oidSplitJ0 (A C : ℕ → ℝ) (n j0 : ℕ) (h1 : j0 ≤ n) :
    (∑ j ∈ Finset.range n, A j * ∏ i ∈ Finset.Ico (j + 1) n, (1 + C i))
      = (∏ i ∈ Finset.Ico j0 n, (1 + C i))
          * ((∑ j ∈ Finset.range n, A j)
            + (∑ j ∈ Finset.range j0, (-A j) * (1 - ∏ i ∈ Finset.Ico (j + 1) j0, (1 + C i))))
        + (∑ j ∈ Finset.Ico j0 n, A j
            * ((∏ i ∈ Finset.Ico (j + 1) n, (1 + C i))
              - ∏ i ∈ Finset.Ico j0 n, (1 + C i))) := by
  -- Splitting a product of `(1 + C i)` over an interval, from `j+1` up to `n`,
  -- at the point `j0`: `Pj = P * Qj` where `P = ∏_{i∈[j0,n)}` and `Qj = ∏_{i∈[j+1,j0)}`.
  have hsplit : ∀ j, j < j0 →
      ∏ i ∈ Finset.Ico (j + 1) n, (1 + C i)
        = (∏ i ∈ Finset.Ico j0 n, (1 + C i)) * ∏ i ∈ Finset.Ico (j + 1) j0, (1 + C i) := by
    intro j hj
    have hj1 : j + 1 ≤ j0 := hj
    have hc := Finset.prod_Ico_consecutive (fun i => (1 + C i)) hj1 h1
    rw [← hc]
    ring
  -- `P * (∑_{[j0,n)} A) + ∑_{[j0,n)} A (Pj - P) = ∑_{[j0,n)} A · Pj`.
  have h2 : (∏ i ∈ Finset.Ico j0 n, (1 + C i)) * (∑ j ∈ Finset.Ico j0 n, A j)
      + (∑ j ∈ Finset.Ico j0 n, A j
          * ((∏ i ∈ Finset.Ico (j + 1) n, (1 + C i)) - ∏ i ∈ Finset.Ico j0 n, (1 + C i)))
      = ∑ j ∈ Finset.Ico j0 n, A j * ∏ i ∈ Finset.Ico (j + 1) n, (1 + C i) := by
    rw [Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro j hj; ring
  -- `P * (∑_{[0,j0)} A) + P * (∑_{[0,j0)} (-A)(1 - Qj)) = ∑_{[0,j0)} A (P * Qj)`.
  have h3 : (∏ i ∈ Finset.Ico j0 n, (1 + C i)) * (∑ j ∈ Finset.range j0, A j)
      + (∏ i ∈ Finset.Ico j0 n, (1 + C i))
        * (∑ j ∈ Finset.range j0, (-A j) * (1 - ∏ i ∈ Finset.Ico (j + 1) j0, (1 + C i)))
      = ∑ j ∈ Finset.range j0, A j * ((∏ i ∈ Finset.Ico j0 n, (1 + C i))
          * ∏ i ∈ Finset.Ico (j + 1) j0, (1 + C i)) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro j hj; ring
  -- `∑_{[0,j0)} A (P * Qj) = ∑_{[0,j0)} A · Pj` via `hsplit`.
  have h4 : (∑ j ∈ Finset.range j0, A j * ((∏ i ∈ Finset.Ico j0 n, (1 + C i))
          * ∏ i ∈ Finset.Ico (j + 1) j0, (1 + C i)))
      = ∑ j ∈ Finset.range j0, A j * ∏ i ∈ Finset.Ico (j + 1) n, (1 + C i) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [hsplit j (Finset.mem_range.mp hj)]
  -- Split `∑_{[0,n)} A` into the two partial sums.
  have hS : (∑ j ∈ Finset.range n, A j)
      = (∑ j ∈ Finset.range j0, A j) + (∑ j ∈ Finset.Ico j0 n, A j) := by
    rw [Finset.sum_range_add_sum_Ico _ h1]
  -- Regroup the right-hand side.
  have e1 : (∏ i ∈ Finset.Ico j0 n, (1 + C i))
        * (((∑ j ∈ Finset.range j0, A j) + (∑ j ∈ Finset.Ico j0 n, A j))
          + (∑ j ∈ Finset.range j0, (-A j) * (1 - ∏ i ∈ Finset.Ico (j + 1) j0, (1 + C i))))
      + (∑ j ∈ Finset.Ico j0 n, A j
            * ((∏ i ∈ Finset.Ico (j + 1) n, (1 + C i)) - ∏ i ∈ Finset.Ico j0 n, (1 + C i)))
    = (∏ i ∈ Finset.Ico j0 n, (1 + C i)) * (∑ j ∈ Finset.range j0, A j)
      + (∏ i ∈ Finset.Ico j0 n, (1 + C i))
        * (∑ j ∈ Finset.range j0, (-A j) * (1 - ∏ i ∈ Finset.Ico (j + 1) j0, (1 + C i)))
      + ((∏ i ∈ Finset.Ico j0 n, (1 + C i)) * (∑ j ∈ Finset.Ico j0 n, A j)
         + (∑ j ∈ Finset.Ico j0 n, A j
            * ((∏ i ∈ Finset.Ico (j + 1) n, (1 + C i)) - ∏ i ∈ Finset.Ico j0 n, (1 + C i)))) := by
    ring
  rw [hS, e1, h3, h4, h2]
  rw [Finset.sum_range_add_sum_Ico _ h1]

end Work.PARIMPL2.Direct
