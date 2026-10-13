import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Real

namespace Work.FTS.StrongPersist.N6Trans.T1SixAux.TermSixAux

/-- The angular slice `θ ↦ S z θ` of a function continuous on the open quadrant `Q0` is
integrable on the closed angle interval `Iθ = [0, π/2]`, as soon as it is dominated pointwise
on the *open* interval by `|A·B|` with `A²` and `B²` integrable there: on `(0, π/2)` the
arithmetic–geometric mean bound `|A·B| ≤ A² + B²` gives an integrable majorant, and the two
endpoints `0`, `π/2` are `volume`-null. -/
theorem sliceIntCS {S A B : ℝ → ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (hSc : ContinuousOn (Function.uncurry S) Work.FTS.EllipticEst.Q0)
    (hA : MeasureTheory.IntegrableOn (fun θ : ℝ => (A z θ) ^ 2) Work.Spaces.Iθ)
    (hB : MeasureTheory.IntegrableOn (fun θ : ℝ => (B z θ) ^ 2) Work.Spaces.Iθ)
    (hle : ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 → |S z θ| ≤ |A z θ * B z θ|) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => S z θ) Work.Spaces.Iθ := by
  -- Step 1: integrability on the open interval.  There the slice is continuous (it is the
  -- composition of `θ ↦ (z, θ)` with `uncurry S`, and `z > 0`), and it is dominated by the
  -- integrable function `A² + B²`.
  have hIoo : IntegrableOn (fun θ : ℝ => S z θ) (Set.Ioo 0 (π / 2)) := by
    have hcont : ContinuousOn (fun θ : ℝ => S z θ) (Set.Ioo 0 (π / 2)) :=
      hSc.comp (continuous_const.prodMk continuous_id).continuousOn (fun θ hθ => ⟨hz, hθ⟩)
    have hA' : IntegrableOn (fun θ : ℝ => (A z θ) ^ 2) (Set.Ioo 0 (π / 2)) :=
      hA.mono_set Set.Ioo_subset_Icc_self
    have hB' : IntegrableOn (fun θ : ℝ => (B z θ) ^ 2) (Set.Ioo 0 (π / 2)) :=
      hB.mono_set Set.Ioo_subset_Icc_self
    refine (hA'.add hB').mono' (hcont.aestronglyMeasurable measurableSet_Ioo) ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with θ hθ
    have h1 : |S z θ| ≤ |A z θ * B z θ| := hle θ hθ.1 hθ.2
    rw [Real.norm_eq_abs]
    calc |S z θ| ≤ |A z θ * B z θ| := h1
      _ ≤ (A z θ) ^ 2 + (B z θ) ^ 2 := by
          rw [abs_mul]
          nlinarith [sq_nonneg (|A z θ| - |B z θ|), sq_abs (A z θ), sq_abs (B z θ),
            mul_nonneg (abs_nonneg (A z θ)) (abs_nonneg (B z θ))]
  -- Step 2: `Iθ = [0, π/2]` and `(0, π/2)` differ by the null set `{0, π/2}`.
  exact (integrableOn_congr_set_ae
    (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := π / 2))).mp hIoo

end Work.FTS.StrongPersist.N6Trans.T1SixAux.TermSixAux
