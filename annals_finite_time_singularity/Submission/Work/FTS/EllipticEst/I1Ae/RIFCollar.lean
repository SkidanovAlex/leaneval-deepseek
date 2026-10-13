import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.AeI1Fts.Defs
import Submission.Work.FTS.EllipticEst.AeI1Fts.identity_defs
import Submission.Work.FTS.EllipticEst.AeI1Fts.slice_theta_ibp_cut
import Submission.Work.FTS.EllipticEst.AeI1Fts.N_bound
import Submission.Work.FTS.EllipticEst.SliceMixedAux.smoothCutoffIoo
import Submission.Work.FTS.EllipticEst.AngSecond.cut_deriv_uniform
import Submission.Work.FTS.EllipticEst.Dispatch.aeJointIntegrableF
import Submission.Work.FTS.EllipticEst.Dispatch.aeFirstEnergyDTools
import Submission.Work.FTS.EllipticEst.interpol_trunc_defs
import Submission.Work.FTS.EllipticEst.I1Ae.RIFLimits

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.I1Ae

set_option autoImplicit false
set_option maxHeartbeats 1600000

local notation "Iθo" => Set.Ioo (0 : ℝ) (Real.pi / 2)
local notation "χ" => Work.FTS.EllipticEst.cut
local notation "ψ" => Work.FTS.EllipticEst.SliceMixedAux.cut

open Work.FTS.EllipticEst.AeI1Fts (U V Hh AA BB sigE sig1 sig2 II nuQ Fp Fd)

section Collar

/-- The `σ`-weighted square of a slice is integrable for an `ℋ⁰`-honest datum at every
positive `z`. -/
theorem slice_integrable_sq {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hm : Work.Spaces.HkMem α 0 f) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => (f z θ) ^ 2 * sigE θ) Iθo := by
  have hzmem : z ∈ Work.Spaces.Iz := le_of_lt hz
  have hwpos : 0 < Work.Spaces.w z := by rw [Work.Spaces.w]; positivity
  have h1 : MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.w z) ^ 2 * ((f z θ) ^ 2 * sigE θ)) Work.Spaces.Iθ :=
    (hm.1 z hzmem).congr_fun (fun θ hθ => by
      simp only []
      rw [Work.FTS.EllipticEst.AeI1Fts.hkIntegrand_zero_eq_of_mem α f hθ]; ring)
      measurableSet_Icc
  have h2 : MeasureTheory.IntegrableOn
      (fun θ => ((Work.Spaces.w z) ^ 2)⁻¹
        * ((Work.Spaces.w z) ^ 2 * ((f z θ) ^ 2 * sigE θ))) Work.Spaces.Iθ :=
    h1.const_mul _
  have h3 : MeasureTheory.IntegrableOn (fun θ => (f z θ) ^ 2 * sigE θ) Work.Spaces.Iθ :=
    h2.congr_fun (fun θ _ => by
      simp only []
      rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 2 (ne_of_gt hwpos)), one_mul])
      measurableSet_Icc
  exact h3.congr_set_ae
    (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := Real.pi / 2))

/-- The weighted `V`-energy `z ↦ w(z)²∫_θ σ V²` is integrable on `(0,∞)`. -/
theorem integrable_w2_Vsl {α : ℝ} {u : ℝ → ℝ → ℝ}
    (hV : Work.Spaces.HkMem α 0 (V u)) :
    MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2 * ∫ θ in Iθo, sigE θ * (V u z θ) ^ 2)
      (Set.Ioi (0 : ℝ)) := by
  have h1 : MeasureTheory.IntegrableOn
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 (V u) z θ)
      Work.Spaces.Iz := hV.2
  have h2 : MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ, sigE θ * (V u z θ) ^ 2)
      Work.Spaces.Iz :=
    h1.congr_fun (fun z _ => by
      simp only []
      rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
      rw [Work.FTS.EllipticEst.AeI1Fts.hkIntegrand_zero_eq_of_mem α (V u) hθ]; ring)
      measurableSet_Ici
  have h3 : MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ, sigE θ * (V u z θ) ^ 2)
      (Set.Ioi (0 : ℝ)) :=
    h2.mono_set (fun z hz => Set.mem_Ici.mpr (le_of_lt hz))
  refine h3.congr_fun (fun z _ => ?_) measurableSet_Ioi
  simp only []
  congr 1
  exact (MeasureTheory.setIntegral_congr_set (f := fun θ => sigE θ * (V u z θ) ^ 2)
    (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
      (b := Real.pi / 2))).symm

end Collar

end Work.FTS.EllipticEst.I1Ae
