import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS_RegExport.C4.ae_integrableOn_mixed_sq_w_C4
import Submission.Work.FTS.StrongEps.HkMem_of_tendsto
import Submission.Work.FTS.StrongEps.EComparison.EllPkgClsSliceAux
import Submission.Work.FTS.H2.LinfQ

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Slice and slot lemmas for the `C⁴` mixed calculus

* `contDiffOn_uncurry_mixed_shift`, `contDiffOn_uncurry_mixed_Q0`, `contDiffOn_slice_mixed`:
  the finite-order `D`-calculus on the open quadrant and its `θ`-slices;
* `mixed_slot_sq_w_le_HkIntegrand`: a mixed slot with the radial weight `w` is dominated by
  `sin(2θ)^γ · HkIntegrand α 4 f`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXA1w

/-- `D_z^j D_θ^i` lowers the differentiability order by `i + j` on an open set. -/
theorem contDiffOn_uncurry_mixed_shift {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (j i n : ℕ) (h : ContDiffOn ℝ (n + i + j) (Function.uncurry G) V) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.mixed j i G)) V := by
  have heq : ((n : WithTop ℕ∞) + i + j) = ((n : WithTop ℕ∞) + j + i) := by abel
  have h1 : ContDiffOn ℝ (n + j + i) (Function.uncurry G) V := by
    rw [← heq]; exact h
  have h2 : ContDiffOn ℝ (n + j) (Function.uncurry (Work.Spaces.DthIter i G)) V :=
    Work.FTS.StrongEps.contDiffOn_uncurry_DthIter_shift hV i (n + j) h1
  exact Work.FTS.StrongEps.contDiffOn_uncurry_DzIter_shift hV j n h2

/-- The mixed slot `D_z^jD_θ^if` is `C^n` on the open quadrant, for `n + i + j ≤ 4`. -/
theorem contDiffOn_uncurry_mixed_Q0 {f : ℝ → ℝ → ℝ}
    (h4 : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (j i n : ℕ) (h : n + i + j ≤ 4) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.mixed j i f)) Work.FTS.EllipticEst.Q0 :=
  contDiffOn_uncurry_mixed_shift Work.FTS.EllipticEst.isOpen_Q0 j i n
    (h4.of_le (Nat.cast_le.mpr h))

/-- The `θ`-slice of a mixed slot is `C^n` on `(0,π/2)`. -/
theorem contDiffOn_slice_mixed {f : ℝ → ℝ → ℝ}
    (h4 : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (j i n : ℕ) (h : n + i + j ≤ 4) {z : ℝ} (hz : 0 < z) :
    ContDiffOn ℝ n (fun θ => Work.Spaces.mixed j i f z θ) (Set.Ioo 0 (Real.pi / 2)) :=
  Work.FTS.StrongEps.EComparison.contDiffOn_slice_t hz (contDiffOn_uncurry_mixed_Q0 h4 j i n h)

/-- **A mixed slot with weight `w` is dominated by the `ℋ⁴`-integrand.**

For an interior angle `θ` where `sin(2θ) > 0`, `(D_z^jD_θ^if · w)²` is at most
`sin(2θ)^γ · HkIntegrand α 4 f`, because the slot occurs in `HkIntegrand` with the full
weight `W = w sin(2θ)^{-γ/2}`. -/
theorem mixed_slot_sq_w_le_HkIntegrand {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ} (j i : ℕ)
    (hi : 1 ≤ i) (hij : i + j ≤ 4) (z : ℝ) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    (Work.Spaces.mixed j i f z θ * Work.Spaces.w z) ^ 2
      ≤ (Real.sin (2 * θ)) ^ (Work.Spaces.gam α) * Work.Spaces.HkIntegrand α 4 f z θ := by
  have hsin : 0 < Real.sin (2 * θ) := Work.FTS.H2.sin_two_pos_of_mem_Ioo hθ
  have hi5 : i < 5 := by omega
  have hj5 : j < 5 := by omega
  have hterm : (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 4 f z θ := by
    have hinner : ∀ i' ∈ Finset.range 5,
        (if 1 ≤ i' ∧ i' + j ≤ 4 then (Work.Spaces.mixed j i' f z θ * Work.Spaces.Wt α z θ) ^ 2
          else 0)
          ≤ ∑ j' ∈ Finset.range 5,
              (if 1 ≤ i' ∧ i' + j' ≤ 4
                then (Work.Spaces.mixed j' i' f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) := by
      intro i' _
      refine Finset.single_le_sum
        (f := fun j' => if 1 ≤ i' ∧ i' + j' ≤ 4
          then (Work.Spaces.mixed j' i' f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
        (fun j' _ => ?_) (Finset.mem_range.mpr hj5)
      split_ifs with h
      · exact sq_nonneg _
      · exact le_refl 0
    have houter : ∀ i' ∈ Finset.range 5,
        0 ≤ ∑ j' ∈ Finset.range 5,
              (if 1 ≤ i' ∧ i' + j' ≤ 4
                then (Work.Spaces.mixed j' i' f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) := by
      intro i' _
      refine Finset.sum_nonneg fun j' _ => ?_
      split_ifs with h
      · exact sq_nonneg _
      · exact le_refl 0
    rw [Work.Spaces.HkIntegrand]
    refine le_trans ?_ (le_add_of_nonneg_left
      (Finset.sum_nonneg fun i' _ => sq_nonneg _))
    calc (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2
        = (if 1 ≤ i ∧ i + j ≤ 4
            then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) := by
          rw [if_pos ⟨hi, hij⟩]
      _ ≤ ∑ j' ∈ Finset.range 5,
              (if 1 ≤ i ∧ i + j' ≤ 4
                then (Work.Spaces.mixed j' i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) :=
          hinner i (Finset.mem_range.mpr hi5)
      _ ≤ ∑ i' ∈ Finset.range 5, ∑ j' ∈ Finset.range 5,
              (if 1 ≤ i' ∧ i' + j' ≤ 4
                then (Work.Spaces.mixed j' i' f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) :=
          Finset.single_le_sum houter (Finset.mem_range.mpr hi5)
  have hwedge : (Work.Spaces.mixed j i f z θ * Work.Spaces.w z) ^ 2
      = (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (Work.Spaces.gam α) := by
    rw [show Work.Spaces.Wt α z θ
        = Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)) from rfl]
    rw [show (Work.Spaces.mixed j i f z θ
          * (Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)))) ^ 2
        = (Work.Spaces.mixed j i f z θ * Work.Spaces.w z) ^ 2
          * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2 from by ring]
    rw [show ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
        = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) from by
      rw [sq, ← Real.rpow_add hsin]; congr 1; ring]
    rw [mul_assoc, ← Real.rpow_add hsin,
      show -(Work.Spaces.gam α) + Work.Spaces.gam α = 0 by ring, Real.rpow_zero, mul_one]
  calc (Work.Spaces.mixed j i f z θ * Work.Spaces.w z) ^ 2
      = (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (Work.Spaces.gam α) := hwedge
    _ ≤ Work.Spaces.HkIntegrand α 4 f z θ * (Real.sin (2 * θ)) ^ (Work.Spaces.gam α) :=
        mul_le_mul_of_nonneg_right hterm (Real.rpow_nonneg hsin.le _)
    _ = (Real.sin (2 * θ)) ^ (Work.Spaces.gam α) * Work.Spaces.HkIntegrand α 4 f z θ := by
        ring

end Work.FTS_RegExport.RXA1w
