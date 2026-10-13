/-
# `Transfer/E2norm/ampB_DzdIter_sq_w_sq_le` — a uniform bound on the weighted iterates of `ampB`

The `D_z`-defect `E2 α f = Ê₂ f + Γ(θ)·radS α f z` of the transfer carries the radial profile

  `ampB α z = 2z²/(1+z)³`  (the projector correction),

and bounding `E2` in the weighted `ℋⁿ`-norm requires the `w²`-weighted squares of its
`(z∂_z)`-iterates to be **uniformly in `α` integrable with a uniform bound** (a mere
integrability statement is not enough there: the profile is multiplied by other radial
factors, so one needs actual numbers in order to feed Cauchy–Schwarz/AM–GM).  This file
supplies exactly that: a single constant `K` such that for every `α ∈ (0,1]` and every `c ≤ 4`

  `∫_{[0,∞)} (D_z^c (ampB α) z)² w(z)² dz ≤ K`,  `w(z) = (1+z)²/z²`,

together with the integrability that makes the left-hand side a genuine integral.

Note first that `ampB` does not depend on `α` at all (`ampB α = 2·fB`, `fB z = z²/(1+z)³` as
*functions*, `E2pkg.ampB_eq_two_mul_fB`), so the statement is really about a single function.

## The proof

* Integrability is `E2pkg.dzdIter_coeff_bound` (the `ampB` half of the coefficient bound).
* On `(0,∞)` the iterates of `fB` are the closed forms `E2pkg.rB c`, i.e.
  `rB c z = z²·N_c(z)/(1+z)^{c+3}` (`E2pkg.rB_iter`), whence
  `(D_z^c (ampB α) z)² w(z)² = 4·N_c(z)²/(1+z)^{2c+2}`.  A coefficient-wise bound on the
  five numerator polynomials `N_0, …, N_4` (all coefficients `≤ 200` in absolute value,
  `E2pkg.rB_sq_w_integrable`) gives the pointwise domination

  `(D_z^c (ampB α) z)² w(z)² ≤ 160000/(1+z)²`  (`c ≤ 4`, `z > 0`).

* `∫_{Ioi 0} (1+z)^{-2} = 1` by the fundamental theorem of calculus: the derivative of
  `z ↦ -(1+z)^{-1}` is `(1+z)^{-2}` and its limit at `+∞` is `0`
  (`integral_Ioi_of_hasDerivAt_of_tendsto'`).
* The point `z = 0` is null, which is why the pointwise estimate is carried out on `Ioi 0` and
  transported to `Iz = Ici 0` (the two restricted measures agree).

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Submission.Work.FTS.CoercivityFix.Transfer.Profiles
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.dzdIter_coeff_bound
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.rB_iter
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.rB_sq_w_integrable
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.dzdIter_defs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Transfer.E2norm

/-! ## The two elementary one-dimensional ingredients -/

/-- `z ↦ (1+z)^{-2}` is integrable on `(0,∞)`: this is the shift by `1` of the integrability of
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

/-- Pointwise domination of `(D_z^c (ampB α) z)² w(z)²` by `160000/(1+z)²`, for `z > 0` and
`c ≤ 4`.  The constant is four times the one carried by the explicit closed forms
(`40000 = 200²`, the square of the largest coefficient occurring in the numerators `N_c`), the
factor `4` coming from the square of the factor `2` in `ampB = 2·fB`. -/
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

theorem ampB_DzdIter_sq_w_sq_le :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ c : ℕ, c ≤ 4 →
      MeasureTheory.IntegrableOn
        (fun z : ℝ => (Work.Elliptic.DzdIter c (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
          * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz ∧
      ∫ z in Work.Spaces.Iz,
        (Work.Elliptic.DzdIter c (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
          * (Work.Spaces.w z) ^ 2 ≤ K := by
  refine ⟨160000, by norm_num, ?_⟩
  intro α hα hα1 c hc
  have hInt : MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.Elliptic.DzdIter c (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
        * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz :=
    (Work.FTS.CoercivityFix.Transfer.E2pkg.dzdIter_coeff_bound α hα hα1).2 c hc
  refine ⟨hInt, ?_⟩
  -- `Iz = [0,∞)` and `(0,∞)` differ by the null set `{0}`
  have hmeas : volume.restrict (Set.Ioi (0 : ℝ)) = volume.restrict Work.Spaces.Iz :=
    Measure.restrict_congr_set (Ioi_ae_eq_Ici (a := (0 : ℝ)))
  calc ∫ z in Work.Spaces.Iz,
        (Work.Elliptic.DzdIter c (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
          * (Work.Spaces.w z) ^ 2
      = ∫ z in Set.Ioi (0 : ℝ),
          (Work.Elliptic.DzdIter c (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
            * (Work.Spaces.w z) ^ 2 := by rw [← hmeas]
    _ ≤ ∫ z in Set.Ioi (0 : ℝ), 160000 * (1 / (1 + z) ^ 2) := by
        refine MeasureTheory.integral_mono_ae ?_ ?_ ?_
        · exact hInt.mono_set Set.Ioi_subset_Ici_self
        · exact integrableOn_one_div_one_add_sq.const_mul 160000
        · filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
          exact ampB_iter_sq_w_le α c hc hz
    _ = 160000 := by
        rw [MeasureTheory.integral_const_mul, integral_Ioi_one_div_one_add_sq, mul_one]

end Work.FTS.CoercivityFix.Transfer.E2norm
