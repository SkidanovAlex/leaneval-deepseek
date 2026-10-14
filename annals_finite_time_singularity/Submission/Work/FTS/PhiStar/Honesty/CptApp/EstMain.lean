import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PhiStar.Honesty.CptApp.Est.err_mixedSlot_le
import Submission.Work.FTS.PhiStar.Honesty.CptApp.EstCrux
import Submission.Work.FTS.StrongEps.LocUnif.D5.deriv_slot_lintegral_bounds
import Submission.Work.H2W.weakSliceZContinuousAe
import Submission.Work.Spaces.sin_two_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty.CptApp

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- **The `θ`-integral estimate for the error's `ℋᵏ`-integrand.** -/
theorem theta_lintegral_le (k : ℕ) (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ) (F : ℝ → ℝ → ℝ), 3 ≤ n →
      Work.FTS.EllipticEst.SmoothOpen F → Work.FTS.PhiStar.ThetaTraces α k F →
      ∀ z ∈ Work.Spaces.Iz,
        (∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal (Work.Spaces.HkIntegrand α k (err n F) z θ))
          ≤ ENNReal.ofReal C
              * ((∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (omegaPart α k n F z θ))
                + ENNReal.ofReal ((Work.Spaces.w z) ^ 2
                    * ∑ m ∈ Finset.range (k + 1),
                        (Work.Spaces.DzIter m (fun z' _ : ℝ => mu n F z') z 0) ^ 2)
                  * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (rhoProf α k θ))) := by
  obtain ⟨C1, hC1, h1⟩ := Work.FTS.PhiStar.Honesty.CptApp.Est.err_dzSlot_le k
  obtain ⟨C2, hC2, h2⟩ := Work.FTS.PhiStar.Honesty.CptApp.Est.err_mixedSlot_le k
  obtain ⟨CH, hCH, hH⟩ := Work.FTS.PhiStar.Honesty.CptApp.Est.hardyShrink_slice k α hα hα1
  refine ⟨2 * ((k : ℝ) + 1) ^ 2 * max C1 C2 * ((k : ℝ) * CH + 1) + 1, by positivity, ?_⟩
  intro n F hn hsm htr z hz
  have hCmax : 0 ≤ max C1 C2 := le_trans hC1.le (le_max_left _ _)
  have h1' : DzSlotLe k (max C1 C2) := fun α n F hα hα1 hn hsm i hi z hz θ hθ =>
    le_trans (h1 α n F hα hα1 hn hsm i hi z hz θ hθ)
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Good_nonneg α k n F hθ))
  have h2' : MixedSlotLe k (max C1 C2) := fun α n F hα hα1 hn hsm i j hi hj z hz θ hθ =>
    le_trans (h2 α n F hα hα1 hn hsm i j hi hj z hz θ hθ)
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (Good_nonneg α k n F hθ))
  exact err_theta_lintegral_le k α hCmax hCH.le h1' h2' hH n F hα hα1 hn hsm htr z hz

/-! ## Finiteness of the right-hand side -/

/-- The `Ω_n`-part of the `ℋᵏ`-energy is bounded by the full `θ`-slice energy of `F`. -/
theorem lintegral_ofReal_omegaPart_le {α : ℝ} {k : ℕ} {F : ℝ → ℝ → ℝ}
    (hF : Work.Spaces.HkMem α k F) {n : ℕ} {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (omegaPart α k n F z θ))
      ≤ ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ) := by
  calc (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (omegaPart α k n F z θ))
      ≤ ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α k F z θ) :=
        lintegral_mono fun θ => ENNReal.ofReal_le_ofReal (omegaPart_le_HkIntegrand α k n F z θ)
    _ = ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ) :=
        (MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hF.1 z hz)
          (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k F z θ)).symm

end Work.FTS.PhiStar.Honesty.CptApp
