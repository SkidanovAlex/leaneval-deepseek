import Mathlib
import Submission.Work.BourgainPlan.Maximal.opMul_l2_bound
import Submission.Work.BourgainPlan.Maximal.eLpNorm_count_ftLp

namespace Work.BourgainPlan.Maximal

open MeasureTheory
open scoped ENNReal

/-- **The `ℓ²` endpoint of a Fourier multiplier with a pointwise-bounded symbol**, in the `eLpNorm` shape consumed by the interpolation: for `f ∈ ℓ²(ℤ)` and `‖Φ‖ ≤ μ` almost everywhere on the circle, `eLpNorm (opMul Φ f) (ofReal 2) ≤ ofReal μ · eLpNorm f (ofReal 2)` against the counting measure. -/
theorem eLpNorm_two_opMul_le {Φ : MeasureTheory.Lp ℂ ⊤ (AddCircle.haarAddCircle (T := 1))} {f : ℤ → ℂ}
    (hf : Memℓp f 2) {μ : ℝ} (hμ : 0 ≤ μ)
    (hΦ : ∀ᵐ ξ ∂(AddCircle.haarAddCircle (T := 1)),
      ‖(Φ : Work.BourgainPlan.IonescuWainger.Circle → ℂ) ξ‖ ≤ μ) :
    MeasureTheory.eLpNorm (Work.BourgainPlan.IonescuWainger.opMul Φ f hf) (ENNReal.ofReal 2)
        MeasureTheory.Measure.count
      ≤ ENNReal.ofReal μ * MeasureTheory.eLpNorm f (ENNReal.ofReal 2) MeasureTheory.Measure.count := by
  -- The symbol class has `L^∞`-norm at most `μ` (the Haar measure of the circle is finite).
  have hΦnorm : ‖Φ‖ ≤ μ := by
    have := MeasureTheory.Lp.norm_le_of_ae_bound (p := ⊤) (f := Φ) hμ hΦ
    simpa using this
  -- Hence the `L²(𝕋)`-norms are comparable: `‖Φ • 𝓕f‖ ≤ μ ‖𝓕f‖`.
  have hnorm : ‖Work.BourgainPlan.IonescuWainger.opMulLp Φ f hf‖
      ≤ μ * ‖Work.BourgainPlan.IonescuWainger.ftLp f hf‖ := by
    rw [Work.BourgainPlan.IonescuWainger.opMulLp]
    calc ‖Φ • Work.BourgainPlan.IonescuWainger.ftLp f hf‖
          ≤ ‖Φ‖ * ‖Work.BourgainPlan.IonescuWainger.ftLp f hf‖ :=
          MeasureTheory.Lp.norm_smul_le _ _
      _ ≤ μ * ‖Work.BourgainPlan.IonescuWainger.ftLp f hf‖ :=
          mul_le_mul_of_nonneg_right hΦnorm (norm_nonneg _)
  -- Translate both sides into `L²(𝕋)`-norms of the Fourier transforms and conclude.
  rw [Work.BourgainPlan.Maximal.eLpNorm_count_ftLp
        (Work.BourgainPlan.IonescuWainger.opMul_memℓp Φ f hf),
      Work.BourgainPlan.Maximal.eLpNorm_count_ftLp hf,
      Work.BourgainPlan.IonescuWainger.ftLp_opMul, ← ENNReal.ofReal_mul hμ]
  exact ENNReal.ofReal_le_ofReal hnorm

end Work.BourgainPlan.Maximal
