import Mathlib.Tactic.Have
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.UBBInputs9.B.integral_chiB_mul_partialDeriv_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.UBBInputs9.B

open MeasureTheory

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false

/-- **Chain rule for the scaled cutoff** `chiScale a x = χ(a⁻¹ • x)`:
differentiating the rescaling `y ↦ a⁻¹ • y` and using that `χ` is `C^∞` gives

    `d(chiScale a)_y(v) = a⁻¹ · dχ_{a⁻¹•y}(v)`. -/
lemma fderiv_chiScale_apply' (s : ℝ) (x v : ℝ³) :
    fderiv ℝ (Submission.BoseGases.chiScale s) x v
      = s⁻¹ * fderiv ℝ Submission.BoseGases.chi ((s⁻¹) • x) v := by
  have hchi : DifferentiableAt ℝ Submission.BoseGases.chi ((s⁻¹) • x) :=
    Submission.BoseGases.chi_contDiff.differentiable (by norm_num) _
  have hlin : HasFDerivAt (fun y : ℝ³ => (s⁻¹) • y)
      ((s⁻¹) • ContinuousLinearMap.id ℝ ℝ³) x :=
    (hasFDerivAt_id x).const_smul (s⁻¹)
  have hcomp : HasFDerivAt
      (Submission.BoseGases.chi ∘ fun y : ℝ³ => (s⁻¹) • y)
      ((fderiv ℝ Submission.BoseGases.chi ((s⁻¹) • x)) ∘SL
        ((s⁻¹) • ContinuousLinearMap.id ℝ ℝ³)) x :=
    hchi.hasFDerivAt.comp x hlin
  have hfun : Submission.BoseGases.chiScale s
      = (Submission.BoseGases.chi ∘ fun y : ℝ³ => (s⁻¹) • y) := rfl
  rw [hfun, hcomp.fderiv]
  rw [ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_eq_mul]

/-- The `L²`-normalisation of the *derivative* of the scaled bump along the sliding
substitution: for `0 < a` and any centre `c` and direction `e`,

    `∫ u, (d(chiScale a)_{c − a•u}(e))² du = (∫ z, (dχ_z(e))² dz) / a²`,

the scaling law for the `L²` norm of the derivative under the scaling `x ↦ a⁻¹ • x`. -/
theorem integral_fderiv_chiScale_sub_smul_sq (a : ℝ) (ha : 0 < a)
    (c e : EuclideanSpace ℝ (Fin 3)) :
    (∫ u : EuclideanSpace ℝ (Fin 3),
      (fderiv ℝ (Submission.BoseGases.chiScale a) (c - a • u) e) ^ 2)
      = (∫ z : EuclideanSpace ℝ (Fin 3),
          (fderiv ℝ Submission.BoseGases.chi z e) ^ 2) / a ^ 2 := by
  have ha' : a ≠ 0 := ne_of_gt ha
  -- Pointwise chain rule, with the argument pulled to the sliding variable.
  have hpoint : ∀ u : ℝ³, fderiv ℝ (Submission.BoseGases.chiScale a) (c - a • u) e
      = a⁻¹ * fderiv ℝ Submission.BoseGases.chi (a⁻¹ • c - u) e := by
    intro u
    rw [fderiv_chiScale_apply' a (c - a • u) e]
    have harg : a⁻¹ • (c - a • u) = a⁻¹ • c - u := by
      rw [smul_sub, smul_smul, inv_mul_cancel₀ ha', one_smul]
    rw [harg]
  -- Squaring turns the prefactor `a⁻¹` into the divisor `a²`.
  have hsq : ∀ u : ℝ³, (fderiv ℝ (Submission.BoseGases.chiScale a) (c - a • u) e) ^ 2
      = (fderiv ℝ Submission.BoseGases.chi (a⁻¹ • c - u) e) ^ 2 / a ^ 2 := by
    intro u
    rw [hpoint u, mul_pow, inv_pow, div_eq_inv_mul]
  calc (∫ u : ℝ³, (fderiv ℝ (Submission.BoseGases.chiScale a) (c - a • u) e) ^ 2)
      = ∫ u : ℝ³, (fderiv ℝ Submission.BoseGases.chi (a⁻¹ • c - u) e) ^ 2 / a ^ 2 := by
        simp_rw [hsq]
    _ = (∫ u : ℝ³, (fderiv ℝ Submission.BoseGases.chi (a⁻¹ • c - u) e) ^ 2) / a ^ 2 := by
        rw [integral_div]
    _ = (∫ z : ℝ³, (fderiv ℝ Submission.BoseGases.chi z e) ^ 2) / a ^ 2 := by
        rw [integral_sub_left_eq_self (fun s : ℝ³ => (fderiv ℝ Submission.BoseGases.chi s e) ^ 2)
          volume (a⁻¹ • c)]

end Work.UBBInputs9.B
