import Mathlib
import Submission.Work.HP.LsetAux.GridDefs
import Submission.Work.HP.LsetAux.exists_grid_net

/-!
# The grid covering of `Lset`

Every degenerate form `a ∈ Lset d n` (unit ball, a real zero `x` on the unit sphere at which the
gradient vanishes) lies in one of the slab-type sets `gS d n N C1 C2 z` indexed by the grid: the
net point `gw n N z` close to `x` has small value and small gradient by the Taylor and Lipschitz
hypotheses.
-/

set_option autoImplicit false
noncomputable section
open Classical Finset MvPolynomial MeasureTheory
open scoped BigOperators ENNReal

namespace Work.HP.LsetAux

theorem grid_subset (d n N : ℕ) (hN : 2 * (n + 1) ≤ N) {C1 C2 : ℝ} (hC1 : 0 ≤ C1)
    (hC2 : 0 ≤ C2)
    (hgrad : ∀ (a : Mon d n → ℝ) (x y : Fin (n + 1) → ℝ), rNorm x ≤ 2 → rNorm y ≤ 2 →
        rNorm (gradVec d n a y - gradVec d n a x) ≤ C1 * rNorm a * rNorm (y - x))
    (htay : ∀ (a : Mon d n → ℝ) (x y : Fin (n + 1) → ℝ), rNorm x ≤ 2 → rNorm y ≤ 2 →
        |formEvalR d n a y - formEvalR d n a x - dotR (gradVec d n a x) (y - x)|
          ≤ C2 * rNorm a * (rNorm (y - x)) ^ 2) :
    Lset d n ⊆ ⋃ z ∈ (gbox n N).filter (fun z => z ≠ 0), gS d n N C1 C2 z := by
  intro a ha
  obtain ⟨ha1, x, hx1, hfx, hgx⟩ := ha
  obtain ⟨z, hzmem, hznz, hgw, hdist⟩ := exists_grid_net n N hN hx1
  have hdist' : rNorm (gw n N z - x) ≤ 2 * Real.sqrt ((n : ℝ) + 1) / (N : ℝ) := by
    rw [rNorm_sub_comm]; exact hdist
  have hR2 : Real.sqrt ((n : ℝ) + 1) ^ 2 = ((n : ℝ) + 1) := Real.sq_sqrt (by positivity)
  have hx2 : rNorm x ≤ 2 := by rw [hx1]; norm_num
  have hw2 : rNorm (gw n N z) ≤ 2 := by rw [hgw]; norm_num
  refine Set.mem_iUnion.mpr ⟨z, Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
  · exact Finset.mem_filter.mpr ⟨hzmem, hznz⟩
  · refine ⟨ha1, ?_, ?_⟩
    · have ht := htay a x (gw n N z) hx2 hw2
      have hdot : dotR (gradVec d n a x) (gw n N z - x) = 0 := by
        rw [hgx]; simp [dotR]
      rw [hdot, hfx, sub_zero, sub_zero] at ht
      have hprod : C2 * rNorm a * rNorm (gw n N z - x) ^ 2 ≤
          C2 * 1 * (2 * Real.sqrt ((n : ℝ) + 1) / (N : ℝ)) ^ 2 := by
        refine mul_le_mul ?_ ?_ (by positivity) (by positivity)
        · exact mul_le_mul_of_nonneg_left ha1 hC2
        · exact pow_le_pow_left₀ (rNorm_nonneg _) hdist' 2
      have htarget : C2 * 1 * (2 * Real.sqrt ((n : ℝ) + 1) / (N : ℝ)) ^ 2 = gEps n N C2 := by
        rw [gEps, div_pow, mul_pow, hR2]
        ring
      calc |formEvalR d n a (gw n N z)| ≤ C2 * rNorm a * rNorm (gw n N z - x) ^ 2 := ht
        _ ≤ C2 * 1 * (2 * Real.sqrt ((n : ℝ) + 1) / (N : ℝ)) ^ 2 := hprod
        _ = gEps n N C2 := htarget
    · intro j
      have hgd := hgrad a x (gw n N z) hx2 hw2
      have hstep : rNorm (gradVec d n a (gw n N z)) ≤
          C1 * 1 * (2 * Real.sqrt ((n : ℝ) + 1) / (N : ℝ)) := by
        calc rNorm (gradVec d n a (gw n N z))
            = rNorm (gradVec d n a (gw n N z) - gradVec d n a x) := by rw [hgx, sub_zero]
          _ ≤ C1 * rNorm a * rNorm (gw n N z - x) := hgd
          _ ≤ C1 * 1 * (2 * Real.sqrt ((n : ℝ) + 1) / (N : ℝ)) :=
              mul_le_mul (mul_le_mul_of_nonneg_left ha1 hC1) hdist' (rNorm_nonneg _)
                (mul_nonneg hC1 zero_le_one)
      have htarget : C1 * 1 * (2 * Real.sqrt ((n : ℝ) + 1) / (N : ℝ)) = gDel n N C1 := by
        rw [gDel]; ring
      calc |gradVec d n a (gw n N z) j| ≤ rNorm (gradVec d n a (gw n N z)) :=
            abs_apply_le_rNorm _ _
        _ ≤ C1 * 1 * (2 * Real.sqrt ((n : ℝ) + 1) / (N : ℝ)) := hstep
        _ = gDel n N C1 := htarget

end Work.HP.LsetAux
