/-
# `Transfer/E2pkg/rB_sq_w_integrable.lean`

The `w²`-weighted square of the explicit `(z∂_z)`-iterates `rB j` of the projector profile
`z²/(1+z)³` is integrable on `[0,∞)`, for all `j ≤ 4`.

Write `rB j z = z² N_j(z)/(1+z)^{j+3}` with `N_j` the polynomial recorded in `dzdIter_defs`.
Since `w z = (1+z)²/z²`, the factor `z⁴` of `(rB j z)²` cancels the denominator of `w z²` and

  `(rB j z)² · w(z)² = N_j(z)²/(1+z)^{2j+2}`   (`z ≠ 0`),

bounded by `C/(1+z)²` on `(0,∞)`; the point `z = 0` is null (`w 0 = rB j 0 = 0` there).
Integrability of `(1+z)^{-2}` on `(0,∞)` is `integrableOn_add_rpow_Ioi_of_lt` at exponent `-2`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.dzdIter_defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set

namespace Work.FTS.CoercivityFix.Transfer.E2pkg

/-- Continuity on `(0,∞)` of the function under consideration, in the generic shape
`(z² P(z)/(1+z)^k)² · ((1+z)²/z²)²` in which the five cases of `rB` present themselves. -/
private theorem rB_contOn_generic (P : ℝ → ℝ) (k : ℕ) (hP : Continuous P) :
    ContinuousOn (fun z : ℝ => (z ^ 2 * P z / (1 + z) ^ k) ^ 2 * ((1 + z) ^ 2 / z ^ 2) ^ 2)
      (Set.Ioi 0) := by
  have h1 : ContinuousOn (fun z : ℝ => z ^ 2 * P z / (1 + z) ^ k) (Set.Ioi 0) := by
    apply ContinuousOn.div₀
    · fun_prop
    · fun_prop
    · intro x hx
      exact pow_ne_zero k (by linarith [Set.mem_Ioi.mp hx])
  have h2 : ContinuousOn (fun z : ℝ => (1 + z) ^ 2 / z ^ 2) (Set.Ioi 0) := by
    apply ContinuousOn.div₀
    · fun_prop
    · fun_prop
    · intro x hx
      exact pow_ne_zero 2 (ne_of_gt hx)
  exact (h1.pow 2).mul (h2.pow 2)

/-- `z ↦ (rB j z)² w(z)²` is continuous on `(0,∞)` for `j ≤ 4`. -/
private theorem rB_contOn (j : ℕ) (hj : j ≤ 4) :
    ContinuousOn (fun z : ℝ => (rB j z) ^ 2 * (Work.Spaces.w z) ^ 2) (Set.Ioi 0) := by
  interval_cases j
  · simpa only [rB_zero, Work.Spaces.w, mul_one] using
      rB_contOn_generic (fun _ => (1 : ℝ)) 3 continuous_const
  · simpa only [rB_one, Work.Spaces.w] using
      rB_contOn_generic (fun z => (2 : ℝ) - z) 4 (by fun_prop)
  · simpa only [rB_two, Work.Spaces.w] using
      rB_contOn_generic (fun z => (4 : ℝ) - 7 * z + z ^ 2) 5 (by fun_prop)
  · simpa only [rB_three, Work.Spaces.w] using
      rB_contOn_generic (fun z => (8 : ℝ) - 33 * z + 18 * z ^ 2 - z ^ 3) 6 (by fun_prop)
  · simpa only [rB_four, Work.Spaces.w] using
      rB_contOn_generic (fun z => (16 : ℝ) - 131 * z + 171 * z ^ 2 - 41 * z ^ 3 + z ^ 4) 7
        (by fun_prop)

/-- Pointwise domination of `(rB j z)² w(z)²` by `40000/(1+z)²` for `z > 0` and `j ≤ 4`.
The constant `40000 = 200²` dominates the square of the largest coefficient (`171`) occurring
in the five numerators, and `200 (1+z)^j` dominates the corresponding `N_j`. -/
private theorem rB_case_le (j : ℕ) (hj : j ≤ 4) {z : ℝ} (hz : 0 < z) :
    (rB j z) ^ 2 * (Work.Spaces.w z) ^ 2 ≤ 40000 * (1 / (1 + z) ^ 2) := by
  interval_cases j <;>
    simp only [rB_zero, rB_one, rB_two, rB_three, rB_four, Work.Spaces.w] <;>
    field_simp <;>
    nlinarith [sq_nonneg z, sq_nonneg (z * z), sq_nonneg (z ^ 3)]

theorem rB_sq_w_integrable : ∀ j ≤ 4, MeasureTheory.IntegrableOn
    (fun z : ℝ => (rB j z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz := by
  intro j hj
  change MeasureTheory.IntegrableOn
    (fun z : ℝ => (rB j z) ^ 2 * (Work.Spaces.w z) ^ 2) (Set.Ici 0)
  refine (integrableOn_Ici_iff_integrableOn_Ioi
    (f := fun z : ℝ => (rB j z) ^ 2 * (Work.Spaces.w z) ^ 2) (b := 0)).mpr ?_
  -- the dominating function `40000/(1+z)²` is integrable on `(0,∞)`
  have hdom : MeasureTheory.Integrable (fun z : ℝ => 40000 * (1 / (1 + z) ^ 2))
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
    have h1 : MeasureTheory.IntegrableOn (fun z : ℝ => 1 / (1 + z) ^ 2) (Set.Ioi 0) := by
      have hpow : MeasureTheory.IntegrableOn (fun z : ℝ => (z + 1) ^ (-2 : ℝ)) (Set.Ioi 0) :=
        integrableOn_add_rpow_Ioi_of_lt (a := -2) (c := 0) (m := 1) (by norm_num) (by norm_num)
      refine hpow.congr_fun (fun z hz => ?_) measurableSet_Ioi
      have hz1 : (0 : ℝ) < z + 1 := by linarith [Set.mem_Ioi.mp hz]
      show (z + 1) ^ (-2 : ℝ) = 1 / (1 + z) ^ 2
      rw [Real.rpow_neg (le_of_lt hz1), Real.rpow_two, inv_eq_one_div]
      ring_nf
    exact MeasureTheory.Integrable.const_mul h1 40000
  refine MeasureTheory.Integrable.mono' hdom ?_ ?_
  · exact (rB_contOn j hj).aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
    have hz' : (0 : ℝ) < z := hz
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
    exact rB_case_le j hj hz'

end Work.FTS.CoercivityFix.Transfer.E2pkg
