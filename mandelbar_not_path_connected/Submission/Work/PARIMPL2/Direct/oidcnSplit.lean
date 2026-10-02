import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.PARIMPL2.Direct

theorem oidcnSplit (A C : ℕ → ℝ) (n j0 : ℕ) (h1 : j0 < n) (h2 : ∀ j < j0, A j ≤ 0) :
    (∑ j ∈ Finset.range n, A j * ∏ i ∈ Finset.Ico (j + 1) n, (1 + C i))
      = (∏ i ∈ Finset.Ico (j0 + 1) n, (1 + C i)) * (∑ j ∈ Finset.range n, A j)
        + (∑ j ∈ Finset.range j0, |A j| * (∏ i ∈ Finset.Ico (j0 + 1) n, (1 + C i))
            * (1 - ∏ i ∈ Finset.Ico (j + 1) (j0 + 1), (1 + C i)))
        + (∑ j ∈ Finset.Ico j0 n, A j
            * ((∏ i ∈ Finset.Ico (j + 1) n, (1 + C i))
              - ∏ i ∈ Finset.Ico (j0 + 1) n, (1 + C i))) := by
  -- Key suffix-product decomposition: for j < j0,
  --   ∏_{i=j+1}^{n-1} g_i = (∏_{i=j+1}^{j0} g_i) * (∏_{i=j0+1}^{n-1} g_i).
  have hkey : ∀ j, j < j0 →
      (∏ i ∈ Finset.Ico (j + 1) n, (1 + C i))
        = (∏ i ∈ Finset.Ico (j + 1) (j0 + 1), (1 + C i))
          * (∏ i ∈ Finset.Ico (j0 + 1) n, (1 + C i)) := by
    intro j hj
    exact (Finset.prod_Ico_consecutive (fun i => 1 + C i) (m := j + 1) (n := j0 + 1) (k := n)
      (by omega) (by omega)).symm
  have habs : ∀ j, j < j0 → |A j| = -A j := fun j hj => abs_of_nonpos (h2 j hj)
  -- The `range j0` block of the RHS equals `∑_{j<j0} A_j * (P_j - P0)`.
  have hT1 : (∑ j ∈ Finset.range j0, |A j| * (∏ i ∈ Finset.Ico (j0 + 1) n, (1 + C i))
        * (1 - ∏ i ∈ Finset.Ico (j + 1) (j0 + 1), (1 + C i)))
      = ∑ j ∈ Finset.range j0, A j * ((∏ i ∈ Finset.Ico (j + 1) n, (1 + C i))
          - ∏ i ∈ Finset.Ico (j0 + 1) n, (1 + C i)) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : j < j0 := Finset.mem_range.mp hj
    rw [habs j hj', hkey j hj']
    ring
  -- Split `range n` into `range j0` and `Ico j0 n`.
  have hsplit : (∑ j ∈ Finset.range j0, A j * ((∏ i ∈ Finset.Ico (j + 1) n, (1 + C i))
          - ∏ i ∈ Finset.Ico (j0 + 1) n, (1 + C i)))
      + (∑ j ∈ Finset.Ico j0 n, A j * ((∏ i ∈ Finset.Ico (j + 1) n, (1 + C i))
          - ∏ i ∈ Finset.Ico (j0 + 1) n, (1 + C i)))
      = ∑ j ∈ Finset.range n, A j * ((∏ i ∈ Finset.Ico (j + 1) n, (1 + C i))
          - ∏ i ∈ Finset.Ico (j0 + 1) n, (1 + C i)) :=
    Finset.sum_range_add_sum_Ico
      (fun j => A j * ((∏ i ∈ Finset.Ico (j + 1) n, (1 + C i))
        - ∏ i ∈ Finset.Ico (j0 + 1) n, (1 + C i))) (le_of_lt h1)
  -- Distribute the difference inside the sum.
  have hL : (∑ j ∈ Finset.range n, A j * ((∏ i ∈ Finset.Ico (j + 1) n, (1 + C i))
          - ∏ i ∈ Finset.Ico (j0 + 1) n, (1 + C i)))
      = (∑ j ∈ Finset.range n, A j * ∏ i ∈ Finset.Ico (j + 1) n, (1 + C i))
        - (∏ i ∈ Finset.Ico (j0 + 1) n, (1 + C i)) * (∑ j ∈ Finset.range n, A j) := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
    ring
  rw [hT1]
  symm
  calc (∏ i ∈ Finset.Ico (j0 + 1) n, (1 + C i)) * (∑ j ∈ Finset.range n, A j)
      + (∑ j ∈ Finset.range j0, A j * ((∏ i ∈ Finset.Ico (j + 1) n, (1 + C i))
          - ∏ i ∈ Finset.Ico (j0 + 1) n, (1 + C i)))
      + (∑ j ∈ Finset.Ico j0 n, A j * ((∏ i ∈ Finset.Ico (j + 1) n, (1 + C i))
          - ∏ i ∈ Finset.Ico (j0 + 1) n, (1 + C i)))
      = (∏ i ∈ Finset.Ico (j0 + 1) n, (1 + C i)) * (∑ j ∈ Finset.range n, A j)
        + ((∑ j ∈ Finset.range j0, A j * ((∏ i ∈ Finset.Ico (j + 1) n, (1 + C i))
            - ∏ i ∈ Finset.Ico (j0 + 1) n, (1 + C i)))
          + (∑ j ∈ Finset.Ico j0 n, A j * ((∏ i ∈ Finset.Ico (j + 1) n, (1 + C i))
            - ∏ i ∈ Finset.Ico (j0 + 1) n, (1 + C i)))) := by ring
    _ = (∏ i ∈ Finset.Ico (j0 + 1) n, (1 + C i)) * (∑ j ∈ Finset.range n, A j)
        + (∑ j ∈ Finset.range n, A j * ((∏ i ∈ Finset.Ico (j + 1) n, (1 + C i))
          - ∏ i ∈ Finset.Ico (j0 + 1) n, (1 + C i))) := by rw [hsplit]
    _ = (∏ i ∈ Finset.Ico (j0 + 1) n, (1 + C i)) * (∑ j ∈ Finset.range n, A j)
        + ((∑ j ∈ Finset.range n, A j * ∏ i ∈ Finset.Ico (j + 1) n, (1 + C i))
          - (∏ i ∈ Finset.Ico (j0 + 1) n, (1 + C i)) * (∑ j ∈ Finset.range n, A j)) := by rw [hL]
    _ = (∑ j ∈ Finset.range n, A j * ∏ i ∈ Finset.Ico (j + 1) n, (1 + C i)) := by ring

end Work.PARIMPL2.Direct
