/-
# `Transfer/E1Norm/amp_iter_bounds.lean` — a uniform bound on the `E1`-norm of `ampB`

The `E1`-defect `E1 α f = (D_θΓ)·radA α f` of the transfer is `α`-small; the price of this is
that one has to control the *radial* profiles.  This file records the soft half of that control
for the projector profile `ampB α z = 2z²/(1+z)³`: the quantity

  `∫_{[0,∞)} ∑_{j<4} (D_z^j (ampB α) z)² · w(z)² dz`,  `w(z) = (1+z)²/z²`,

is bounded by a constant *independent of `α`* (indeed `ampB` does not depend on `α` at all).
This is the statement that the (finite) `E1`-norm pieces contributed by `ampB` do not blow up
as `α → 0`, which is what makes the transfer estimate `E1 ≲ α` uniform.

## The proof

`ampB α = 2·fB` with `fB z = z²/(1+z)³`, and on `(0,∞)` the `(z∂_z)`-iterates of `fB` are the
closed forms `rB j z = z²·N_j(z)/(1+z)^{j+3}` (`E2pkg.rB_iter`, `j ≤ 4`).  Since
`(rB j z)² w(z)² = N_j(z)²/(1+z)^{2j+2}`, a coefficient-wise bound on the five explicit
numerator polynomials gives

  `(D_z^j (ampB α) z)² w(z)² ≤ 160000/(1+z)²`   (`j ≤ 4`, `z > 0`),

and `∫_{Ioi 0} (1+z)^{-2} = 1` by the fundamental theorem of calculus
(`d/dz (-(1+z)^{-1}) = (1+z)^{-2}`, limit `0` at infinity).  The sum over `j < 4` is then
compared with `4 · 160000 = 640000`.

All of this is integrable by `E2pkg.dzdIter_coeff_bound`, so only a.e.-monotonicity of the
integral is needed to pass from the pointwise bound to the integral; the point `z = 0` is null,
which is why the estimates are carried out on `Ioi 0` and transported to `Iz = Ici 0`.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.dzdIter_coeff_bound
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.rB_sq_w_integrable
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.dzdIter_defs
import Submission.Work.Coercivity.L2CoercivityTransport

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.CoercivityFix.Transfer.E1Norm

/-! ## The two elementary one-dimensional ingredients -/

/-- `z ↦ (1+z)^{-2}` is integrable on `(0,∞)`; this is the shift by `1` of the integrability of
`z ↦ z^{-2}` (Mathlib's `integrableOn_add_rpow_Ioi_of_lt` at exponent `-2`). -/
private theorem integrableOn_one_div_one_add_sq :
    IntegrableOn (fun z : ℝ => 1 / (1 + z) ^ 2) (Set.Ioi (0 : ℝ)) := by
  have hpow : IntegrableOn (fun z : ℝ => (z + 1) ^ (-2 : ℝ)) (Set.Ioi (0 : ℝ)) :=
    integrableOn_add_rpow_Ioi_of_lt (a := -2) (c := 0) (m := 1) (by norm_num) (by norm_num)
  refine hpow.congr_fun (fun z hz => ?_) measurableSet_Ioi
  have hz1 : (0 : ℝ) < z + 1 := by linarith [Set.mem_Ioi.mp hz]
  show (z + 1) ^ (-2 : ℝ) = 1 / (1 + z) ^ 2
  rw [Real.rpow_neg (le_of_lt hz1), Real.rpow_two, inv_eq_one_div]
  ring_nf

/-- `∫_0^∞ (1+z)^{-2} dz = 1`, by the fundamental theorem of calculus applied to
`z ↦ -(1+z)^{-1}` (whose derivative is `(1+z)^{-2}` and whose limit at `+∞` is `0`). -/
private theorem integral_Ioi_one_div_one_add_sq :
    ∫ z in Set.Ioi (0 : ℝ), 1 / (1 + z) ^ 2 = 1 := by
  have hderiv : ∀ x ∈ Set.Ici (0 : ℝ),
      HasDerivAt (fun z : ℝ => -((1 + z)⁻¹)) (1 / (1 + x) ^ 2) x := by
    intro x hx
    have h0 : (1 + x) ≠ 0 := by
      have : (0 : ℝ) ≤ x := hx
      intro h
      linarith
    have h1 : HasDerivAt (fun z : ℝ => 1 + z) 1 x := by
      simpa using (hasDerivAt_id x).const_add 1
    have h3 := (h1.inv h0).neg
    convert h3 using 1
    field_simp
  have htend : Tendsto (fun z : ℝ => -((1 + z)⁻¹)) atTop (𝓝 0) := by
    have h : Tendsto (fun z : ℝ => (1 + z)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left atTop (1 : ℝ) tendsto_id)
    simpa using h.neg
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' (a := (0 : ℝ))
    (f := fun z : ℝ => -((1 + z)⁻¹)) (f' := fun z : ℝ => 1 / (1 + z) ^ 2) (m := 0)
    hderiv integrableOn_one_div_one_add_sq htend
  simpa using h

/-! ## The pointwise bound on the weighted iterates of `ampB` -/

/-- Pointwise domination of `(D_z^j (ampB α) z)² w(z)²` by `160000/(1+z)²`, for `z > 0` and
`j ≤ 4`.  The constant is four times the one carried by `E2pkg.rB_sq_w_integrable`
(`40000 = 200²`), the factor `4` coming from the square of the factor `2` in `ampB = 2·fB`. -/
private theorem ampB_iter_sq_w_le (α : ℝ) (j : ℕ) (hj : j ≤ 4) {z : ℝ} (hz : 0 < z) :
    (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
      * (Work.Spaces.w z) ^ 2 ≤ 160000 * (1 / (1 + z) ^ 2) := by
  rw [congrFun (Work.FTS.CoercivityFix.Transfer.E2pkg.dzdIter_ampB_eq α j) z,
    Work.FTS.CoercivityFix.Transfer.E2pkg.rB_iter j hj z hz]
  interval_cases j <;>
    simp only [Work.FTS.CoercivityFix.Transfer.E2pkg.rB_zero,
      Work.FTS.CoercivityFix.Transfer.E2pkg.rB_one,
      Work.FTS.CoercivityFix.Transfer.E2pkg.rB_two,
      Work.FTS.CoercivityFix.Transfer.E2pkg.rB_three,
      Work.FTS.CoercivityFix.Transfer.E2pkg.rB_four,
      Work.Spaces.w] <;>
    field_simp <;>
    nlinarith [sq_nonneg z, sq_nonneg (z * z), sq_nonneg (z ^ 3)]

/-! ## The target -/

theorem amp_iter_bounds :
    ∃ Kb : ℝ, 0 < Kb ∧ ∀ α : ℝ, 0 < α → α ≤ 1 →
      (∫ z in Work.Spaces.Iz, ∑ j ∈ Finset.range 4,
        (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
          * (Work.Spaces.w z) ^ 2) ≤ Kb := by
  refine ⟨640000, by norm_num, ?_⟩
  intro α hα hα1
  set F : ℕ → ℝ → ℝ := fun j z =>
    (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
      * (Work.Spaces.w z) ^ 2 with hF
  have hInt : ∀ j ≤ 4, IntegrableOn (F j) Work.Spaces.Iz := by
    intro j hj
    rw [hF]
    exact (Work.FTS.CoercivityFix.Transfer.E2pkg.dzdIter_coeff_bound α hα hα1).2 j hj
  have hmeas : volume.restrict (Set.Ioi (0 : ℝ)) = volume.restrict Work.Spaces.Iz :=
    Measure.restrict_congr_set (Ioi_ae_eq_Ici (a := (0 : ℝ)))
  have hterm : ∀ j ∈ Finset.range 4, (∫ z in Work.Spaces.Iz, F j z) ≤ 160000 := by
    intro j hj
    have hj4 : j ≤ 4 := by
      have h := Finset.mem_range.mp hj
      omega
    calc (∫ z in Work.Spaces.Iz, F j z)
        = ∫ z in Set.Ioi (0 : ℝ), F j z := by rw [← hmeas]
      _ ≤ ∫ z in Set.Ioi (0 : ℝ), 160000 * (1 / (1 + z) ^ 2) := by
          refine MeasureTheory.integral_mono_ae ?_ ?_ ?_
          · exact (hInt j hj4).mono_set Set.Ioi_subset_Ici_self
          · exact integrableOn_one_div_one_add_sq.const_mul 160000
          · filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
            rw [hF]
            exact ampB_iter_sq_w_le α j hj4 hz
      _ = 160000 := by
          rw [MeasureTheory.integral_const_mul, integral_Ioi_one_div_one_add_sq, mul_one]
  calc (∫ z in Work.Spaces.Iz, ∑ j ∈ Finset.range 4, F j z)
      = ∑ j ∈ Finset.range 4, ∫ z in Work.Spaces.Iz, F j z :=
        MeasureTheory.integral_finsetSum (Finset.range 4)
          (fun j hj => hInt j (by have h := Finset.mem_range.mp hj; omega))
    _ ≤ ∑ _j ∈ Finset.range 4, (160000 : ℝ) := Finset.sum_le_sum hterm
    _ = 640000 := by norm_num

end Work.FTS.CoercivityFix.Transfer.E1Norm
