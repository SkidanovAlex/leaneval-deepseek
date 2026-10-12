import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.UBBInputs9.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.UBBInputs9.B.integral_chiScale_sub_smul_sq`

The `L²`-normalisation of the scaled bump `chiScale a` along the scaling used by the
sliding localisation: for `0 < a` and any centre `x`,

    `∫ u, chiScale a (x - a • u)² du = 1`.

Since `chiScale a y = chi (a⁻¹ • y)`, the integrand is `chi (a⁻¹ • x - u)²`, so the identity is
the translation/reflection invariance of Lebesgue measure (`∫ u, f (c - u) du = ∫ f`) together
with the normalisation `∫ chi² = 1` (`Submission.BoseGases.chi_L2`).  Note that this is the
*exact* `L²`-partition of the big-box family of FS `lem:LocKinEn`; the small-box (product) window
`chiB` does **not** have this property, see `Work.UBBInputs9.Defs` §2.
-/

namespace Work.UBBInputs9.B

open MeasureTheory

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false

/-- Pointwise form of the substitution: `chiScale a (x - a•u) = chi (a⁻¹•x - u)`. -/
lemma chiScale_sub_smul_eq (a : ℝ) (ha : a ≠ 0) (x u : EuclideanSpace ℝ (Fin 3)) :
    Submission.BoseGases.chiScale a (x - a • u) = Submission.BoseGases.chi ((a⁻¹) • x - u) := by
  rw [Submission.BoseGases.chiScale, smul_sub, smul_smul, inv_mul_cancel₀ ha, one_smul]

/-- **The `L²`-normalisation of the sliding family**: `∫ u, chiScale a (x - a•u)² du = 1`. -/
theorem integral_chiScale_sub_smul_sq (a : ℝ) (ha : 0 < a) (x : EuclideanSpace ℝ (Fin 3)) :
    (∫ u : EuclideanSpace ℝ (Fin 3), (Submission.BoseGases.chiScale a (x - a • u)) ^ 2) = 1 := by
  have ha' : a ≠ 0 := ne_of_gt ha
  have hpoint : ∀ u : EuclideanSpace ℝ (Fin 3),
      Submission.BoseGases.chiScale a (x - a • u) = Submission.BoseGases.chi ((a⁻¹) • x - u) :=
    fun u => chiScale_sub_smul_eq a ha' x u
  simp_rw [hpoint]
  rw [MeasureTheory.integral_sub_left_eq_self
    (fun s : EuclideanSpace ℝ (Fin 3) => (Submission.BoseGases.chi s) ^ 2)
    MeasureTheory.volume ((a⁻¹) • x)]
  exact Submission.BoseGases.chi_L2

end Work.UBBInputs9.B
