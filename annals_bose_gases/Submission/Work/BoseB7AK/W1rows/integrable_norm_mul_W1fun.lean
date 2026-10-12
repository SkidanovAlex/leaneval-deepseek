import ChallengeDeps
import Submission.Work.BoseFixR.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseB7AK/W1rows/integrable_norm_mul_W1fun.lean`

**The first-moment (`‖x‖`-weighted `L¹`) row for the corpus's `W₁`:**

    Integrable (fun x => ‖x‖ * ‖W₁(x)‖),      W₁ = Work.BoseFixR.W1fun v h ℓ,

i.e. `∫ ‖x‖ |W₁(x)| dx < ∞`.  This is the real-space input of the
*gradient* row of FS's `eq:W1estimate` (`hW1grad` of `Work.BoseK15.K15Input`):
`fderiv Ŵ₁` is the Fourier transform of `x ↦ −i x W₁(x)`, so it is dominated by
`∫‖x‖|W₁|` (`norm_fderiv_fourier_le` / differentiation under the integral).

## Route

Everything is *support*, not smoothness: `W₁ = wScaled ℓ (g₀ v h)`, and the
numerator `g₀` vanishes for `R ≤ ‖x‖` (`Submission.BoseGases.g0_zero_of_norm_ge`,
from `tsupport v ⊆ ball 0 R`), hence so does `W₁`.  Therefore

    ‖x‖ · ‖W₁(x)‖ ≤ R · ‖W₁(x)‖          (pointwise, both sides `0` off the ball),

and `R • W₁` is integrable because `W₁ ∈ L¹` in the dilute regime
`R ≤ ℓ·chiR0` (`Submission.BoseGases.wScaled_g0_integrable`, i.e. the
`(χ⋆χ)(·/ℓ) ≥ 1/2`-on-`ball 0 R` normalisation estimate).  Integrability then
follows from `Integrable.mono'`.

No diluteness constant is used besides `hRℓ` through that `L¹`-fact: in
particular the hypothesis is *true* for every nonnegative radial `v` of range
`R ≤ ℓ·chiR0` with `ScatSol v`, and needs none of the regularity that
`hW1decay`/`hW1grad` require (`FINDING_W1rows.md` §3).
-/

namespace Work.BoseB7AK.W1rows

noncomputable section

open MeasureTheory
open scoped Real Topology BigOperators

theorem integrable_norm_mul_W1fun {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R ℓ : ℝ} (hR : 0 < R) (hℓ : 0 < ℓ)
    (hv_nonneg : ∀ x : EuclideanSpace ℝ (Fin 3), 0 ≤ v x)
    (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R)
    (h : Work.UBB.ScatSol v) (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0) :
    MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin 3) =>
      ‖x‖ * ‖Work.BoseFixR.W1fun v h ℓ x‖) := by
  -- `W₁ = wScaled ℓ (g₀ v h)` is `L¹` in the dilute regime.
  have hW1 : MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin 3) =>
      Work.BoseFixR.W1fun v h ℓ x) :=
    Submission.BoseGases.wScaled_g0_integrable hR hv_supp h hℓ hRℓ
  -- `W₁` vanishes outside `ball 0 R`, because its numerator `g₀` does.
  have hsupp : ∀ x : EuclideanSpace ℝ (Fin 3), Work.BoseFixR.W1fun v h ℓ x ≠ 0 → ‖x‖ < R := by
    intro x hx
    refine lt_of_not_ge (fun hge => hx ?_)
    have hz : Submission.BoseGases.g0 v h x = 0 :=
      Submission.BoseGases.g0_zero_of_norm_ge hv_supp hge h
    simp [Work.BoseFixR.W1fun, Submission.BoseGases.wScaled, hz]
  have hmeas : AEStronglyMeasurable (fun x : EuclideanSpace ℝ (Fin 3) =>
      ‖x‖ * ‖Work.BoseFixR.W1fun v h ℓ x‖) volume :=
    (continuous_norm.aestronglyMeasurable).mul hW1.aestronglyMeasurable.norm
  refine MeasureTheory.Integrable.mono' (hW1.norm.const_mul R) hmeas ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg (x : EuclideanSpace ℝ (Fin 3)))
      (norm_nonneg (Work.BoseFixR.W1fun v h ℓ x)))]
  by_cases hx : Work.BoseFixR.W1fun v h ℓ x = 0
  · simp [hx]
  · exact mul_le_mul_of_nonneg_right (hsupp x hx).le (norm_nonneg _)

end

end Work.BoseB7AK.W1rows
