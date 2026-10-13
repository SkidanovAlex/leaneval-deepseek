/-
Copyright: work module for the Elgindi finite-time singularity project.

# The weighted Hardy inequality on a right tail (`HardyRightTail`)

For `U : ℝ → ℝ` differentiable on `(1,∞)` with derivative `U'`, vanishing at `+∞`, and with
`∫_1^∞ (t U'(t))² dt < ∞`, one has for every `z > 1`

  `U(z)² ≤ 2 z^{-1/2} ∫_z^∞ (t U'(t))² t^{-1/2} dt`.

This is the sharp weighted Hardy inequality used in the elliptic section of

  T. M. Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the
  incompressible Euler equations on `ℝ³`*, Annals of Math. **194** (2021) 771--887.

## Proof

Since `U → 0` at `+∞`, the fundamental theorem of calculus on the half line gives
`∫_z^∞ U' = -U(z)`.  Cauchy--Schwarz on `(z,∞)` applied to

  `U'(t) = (√((t U'(t))²) · t^{-1/4}) · t^{-3/4}`

together with `∫_z^∞ t^{-3/2} dt = 2 z^{-1/2}` yields
`(∫_z^∞ U')² ≤ (∫_z^∞ (t U')² t^{-1/2}) · 2 z^{-1/2}`, which is the claim.

The two analytic pieces are `Work.Elliptic.tail_l2_cauchy_schwarz` (the weighted
Cauchy--Schwarz step) and `Work.Elliptic.integrableOn_tail_of_weighted` (integrability of `U'`
on the tail, which is the first conjunct of the conclusion).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Submission.Work.Elliptic.integrableOn_tail_of_weighted
import Submission.Work.Elliptic.tail_l2_cauchy_schwarz

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Elliptic

set_option autoImplicit false

theorem HardyRightTail (U U' : ℝ → ℝ)
    (hderiv : ∀ z ∈ Set.Ioi (1:ℝ), HasDerivAt U (U' z) z)
    (htend : Filter.Tendsto U Filter.atTop (nhds 0))
    (hint : MeasureTheory.IntegrableOn (fun z => (z * U' z) ^ 2) (Set.Ioi 1)) :
    ∀ z ∈ Set.Ioi (1:ℝ),
      MeasureTheory.IntegrableOn U' (Set.Ioi z) ∧
      (U z) ^ 2 ≤ 2 * z ^ (-(1/2:ℝ)) *
        ∫ t in Set.Ioi z, (t * U' t) ^ 2 * t ^ (-(1/2:ℝ)) := by
  intro z hz
  have hz1 : (1:ℝ) < z := hz
  have hzpos : (0:ℝ) < z := lt_trans one_pos hz1
  -- The weighted square `(t U' t)² t^{-1/2}` is integrable on `(1,∞)`: on `(1,∞)` the extra
  -- weight `t^{-1/2}` is at most `1`, so it is dominated by the integrable `(t U' t)²`.
  have hG1 : IntegrableOn (fun t : ℝ => (t * U' t) ^ 2 * t ^ (-(1/2:ℝ))) (Set.Ioi 1) := by
    have hAESM : AEStronglyMeasurable (fun t : ℝ => (t * U' t) ^ 2 * t ^ (-(1/2:ℝ)))
        (volume.restrict (Set.Ioi (1:ℝ))) := by
      have h1 : AEStronglyMeasurable (fun t : ℝ => (t * U' t) ^ 2)
          (volume.restrict (Set.Ioi (1:ℝ))) := hint.aestronglyMeasurable
      have h2 : AEStronglyMeasurable (fun t : ℝ => t ^ (-(1/2:ℝ)))
          (volume.restrict (Set.Ioi (1:ℝ))) :=
        (continuousOn_id.rpow_const
          (fun t ht => Or.inl (ne_of_gt (lt_trans one_pos (mem_Ioi.mp ht))))).aestronglyMeasurable
          measurableSet_Ioi
      exact h1.mul h2
    refine hint.mono' hAESM ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htp : (0:ℝ) < t := lt_trans one_pos (mem_Ioi.mp ht)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg htp.le _))]
    refine mul_le_of_le_one_right (sq_nonneg _) ?_
    have h := Real.rpow_le_rpow_of_exponent_le (le_of_lt (mem_Ioi.mp ht))
      (show (-(1/2:ℝ)) ≤ 0 by norm_num)
    rwa [Real.rpow_zero] at h
  have hGz : IntegrableOn (fun t : ℝ => (t * U' t) ^ 2 * t ^ (-(1/2:ℝ))) (Set.Ioi z) :=
    hG1.mono_set (Ioi_subset_Ioi hz1.le)
  -- `U'` agrees with `deriv U` on `(z,∞)` (`z > 1`), hence is a.e. strongly measurable there.
  have hU'meas : AEStronglyMeasurable U' (volume.restrict (Set.Ioi z)) := by
    have hd : AEStronglyMeasurable (deriv U) (volume.restrict (Set.Ioi z)) :=
      (measurable_deriv U).aestronglyMeasurable
    refine hd.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (hderiv t (mem_Ioi.mpr (lt_trans hz1 (mem_Ioi.mp ht)))).deriv
  have hU'int : IntegrableOn U' (Set.Ioi z) :=
    integrableOn_tail_of_weighted z hzpos U' hU'meas hGz
  have hcs := tail_l2_cauchy_schwarz z hzpos U' hU'meas hU'int hGz
  -- The fundamental theorem of calculus on `(z,∞)`: `∫_z^∞ U' = 0 - U z`.
  have hFTC : ∫ t in Set.Ioi z, U' t = - U z := by
    have hcont : ContinuousWithinAt U (Set.Ici z) z :=
      (hderiv z hz).continuousAt.continuousWithinAt
    have hd : ∀ x ∈ Set.Ioi z, HasDerivAt U (U' x) x :=
      fun x hx => hderiv x (mem_Ioi.mpr (lt_trans hz1 (mem_Ioi.mp hx)))
    have key := integral_Ioi_of_hasDerivAt_of_tendsto hcont hd hU'int htend
    simpa using key
  refine ⟨hU'int, ?_⟩
  calc (U z) ^ 2 = (∫ t in Set.Ioi z, U' t) ^ 2 := by rw [hFTC]; ring
    _ ≤ (∫ t in Set.Ioi z, (t * U' t) ^ 2 * t ^ (-(1/2:ℝ))) * (2 * z ^ (-(1/2:ℝ))) := hcs
    _ = 2 * z ^ (-(1/2:ℝ)) * ∫ t in Set.Ioi z, (t * U' t) ^ 2 * t ^ (-(1/2:ℝ)) := by ring

end Work.Elliptic
