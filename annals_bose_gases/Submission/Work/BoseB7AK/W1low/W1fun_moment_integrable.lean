import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixR.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseB7AK/W1low/W1fun_moment_integrable.lean`

**Finiteness of the second absolute moment of the renormalised kernel `W₁`:**

    W₁ = Work.BoseFixR.W1fun v h ℓ = wScaled ℓ (g0 v h) = g₀/(χ⋆χ)(·/ℓ)

is integrable against the weight `‖x‖²`, i.e.

    ∫ ‖x‖² |W₁(x)| dx < ∞.

This is the input of the quadratic Fourier estimate
(`Work.BoseB7AK.W1low.chat_sub_le_abs`: `|Ŵ₁(k) − Ŵ₁(0)| ≤ ½‖k‖²∫‖y‖²|W₁(y)|dy`)
used for the low-momentum positivity `Ŵ₁ ≥ 0` of `thm:BogHamDiag`'s proof
(`Work.BoseB7AK.W1low.W1_low_nonneg`).

## Proof

Everything is dominated by `g₀`, whose support lies in `ball 0 R`:

* if `R ≤ ‖x‖` then `g₀ v h x = 0` (`Submission.BoseGases.g0_zero_of_norm_ge`)
  and hence `W₁(x) = 0`, so the two sides both vanish;
* if `‖x‖ < R` then `‖x‖² ≤ R²` and, in the dilute regime `R ≤ ℓ·chiR0` where
  `(χ⋆χ)(·/ℓ) ≥ 1/2` on `ball 0 R`, `|W₁(x)| ≤ 2|g₀(x)|`
  (`Submission.BoseGases.wScaled_abs_le_two`).

So `‖x‖²|W₁(x)| ≤ 2R²|g₀(x)|` *pointwise*, and `∫|g₀| < ∞`
(`Submission.BoseGases.g0_integrable`).  Measurability of the weight comes from
`LocallyIntegrable (v(1−w))` (a field of `IsScatteringSolution`) and the
continuity of `convScale ℓ`.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseB7AK.W1low

-- `ℝ³` is the *global* notation `EuclideanSpace ℝ (Fin 3)` of
-- `Submission.Work.BoseKinLoc.Defs`, which is in this file's import cone;
-- redeclaring it locally makes the term ambiguous.

/-- The real-space bound behind the moment estimate: `|W₁(x)| ≤ 2|g₀(x)|`.
`W₁ = g₀/(χ⋆χ)(·/ℓ)` is (pointwise) at most `2|g₀|` once `(χ⋆χ)(·/ℓ) ≥ 1/2` on
the support `ball 0 R` of `g₀`. -/
private theorem W1fun_abs_le_two_g0 {v : ℝ³ → ℝ} {R ℓ : ℝ}
    (hR : 0 < R) (hℓ : 0 < ℓ) (hv_supp : tsupport v ⊆ Metric.ball 0 R)
    (h : Work.UBB.ScatSol v) (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0) (x : ℝ³) :
    |Work.BoseFixR.W1fun v h ℓ x| ≤ 2 * |Submission.BoseGases.g0 v h x| := by
  simpa [Work.BoseFixR.W1fun] using
    Submission.BoseGases.wScaled_abs_le_two hℓ hR.le hRℓ
      (fun z hz => Submission.BoseGases.g0_zero_of_norm_ge hv_supp hz h) x

/-- **The second absolute moment of `W₁ = wScaled ℓ (g0 v h)` is finite.**

`g₀` is supported in `ball 0 R`, so `W₁` is too and there
`‖x‖²|W₁(x)| ≤ 2R²|g₀(x)|`; the domination is pointwise and `g₀` is integrable. -/
theorem W1fun_moment_integrable {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R ℓ : ℝ} (hR : 0 < R)
    (hℓ : 0 < ℓ) (hv_supp : tsupport v ⊆ Metric.ball 0 R)
    (h : Work.UBB.ScatSol v) (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0) :
    MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin 3) =>
      ‖x‖ ^ 2 * |Work.BoseFixR.W1fun v h ℓ x|) := by
  have hgi : MeasureTheory.Integrable (Submission.BoseGases.g0 v h) :=
    Submission.BoseGases.g0_integrable hR hv_supp h
  have hmaj : MeasureTheory.Integrable
      (fun x : EuclideanSpace ℝ (Fin 3) => 2 * R ^ 2 * |Submission.BoseGases.g0 v h x|) :=
    hgi.abs.const_mul (2 * R ^ 2)
  have hmeas : AEStronglyMeasurable
      (fun x : EuclideanSpace ℝ (Fin 3) => ‖x‖ ^ 2 * |Work.BoseFixR.W1fun v h ℓ x|) := by
    have hinvm : Measurable
        (fun z : EuclideanSpace ℝ (Fin 3) => (Submission.BoseGases.convScale ℓ z)⁻¹) := by
      have hinv : Measurable fun t : ℝ => t⁻¹ := by fun_prop
      exact hinv.comp (Submission.BoseGases.convScale_continuous ℓ).measurable
    have hW : AEStronglyMeasurable (Work.BoseFixR.W1fun v h ℓ) := by
      have hEq : Work.BoseFixR.W1fun v h ℓ
          = fun z : EuclideanSpace ℝ (Fin 3) =>
              Submission.BoseGases.g0 v h z * (Submission.BoseGases.convScale ℓ z)⁻¹ := by
        funext z
        simp [Work.BoseFixR.W1fun, Submission.BoseGases.wScaled, div_eq_mul_inv]
      rw [hEq]
      exact hgi.aestronglyMeasurable.mul hinvm.aestronglyMeasurable
    have h1 : AEStronglyMeasurable (fun x : EuclideanSpace ℝ (Fin 3) => ‖x‖ ^ 2) := by
      fun_prop
    have h2 : AEStronglyMeasurable
        (fun x : EuclideanSpace ℝ (Fin 3) => |Work.BoseFixR.W1fun v h ℓ x|) := by
      simpa [Real.norm_eq_abs] using hW.norm
    exact h1.mul h2
  refine MeasureTheory.Integrable.mono' hmaj hmeas ?_
  filter_upwards with x
  rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (abs_nonneg _))]
  by_cases hx : R ≤ ‖x‖
  · have hz : Submission.BoseGases.g0 v h x = 0 :=
      Submission.BoseGases.g0_zero_of_norm_ge hv_supp hx h
    have hz2 : Work.BoseFixR.W1fun v h ℓ x = 0 := by
      simp [Work.BoseFixR.W1fun, Submission.BoseGases.wScaled, hz]
    simp [hz, hz2]
  · have hxlt : ‖x‖ < R := lt_of_not_ge hx
    have hWle := W1fun_abs_le_two_g0 hR hℓ hv_supp h hRℓ x
    have hx2 : ‖x‖ ^ 2 ≤ R ^ 2 := by nlinarith [norm_nonneg x]
    calc ‖x‖ ^ 2 * |Work.BoseFixR.W1fun v h ℓ x|
        ≤ R ^ 2 * |Work.BoseFixR.W1fun v h ℓ x| :=
          mul_le_mul_of_nonneg_right hx2 (abs_nonneg _)
      _ ≤ R ^ 2 * (2 * |Submission.BoseGases.g0 v h x|) :=
          mul_le_mul_of_nonneg_left hWle (sq_nonneg R)
      _ = 2 * R ^ 2 * |Submission.BoseGases.g0 v h x| := by ring

end Work.BoseB7AK.W1low
