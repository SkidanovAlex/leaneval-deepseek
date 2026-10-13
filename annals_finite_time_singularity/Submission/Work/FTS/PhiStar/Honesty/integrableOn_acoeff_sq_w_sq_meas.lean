import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.PhiStar.Series.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.EllipticEst.ModalSolution.cmode_bessel
import Submission.Work.FTS.PhiStar.Honesty.integrableOn_sliceMass_div_z4_of_HkMem
import Submission.Work.FTS.PhiStar.Honesty.integrableOn_sliceMass_Ioi_one_of_HkMem
import Submission.Work.FTS.PhiStar.Honesty.integrableOn_sq_sEta_of_HkMem
import Submission.Work.FTS.PhiStar.Honesty.eNorm_mul_cmode_sq_le_sliceMass
import Submission.Work.FTS.PhiStar.Honesty.radGreen_sq_w_sq_meas_engine

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

open MeasureTheory Set Filter

-- `hsm` is part of the (fixed) statement but is not needed by the proof: the only regularity
-- of `F` that the argument consumes is `HkMem α 0 F` (measurability of the clamped `cmode`
-- is a hypothesis).
set_option linter.unusedVariables false


/-! ## The Green's function only sees `c` on `(0,∞)` -/

/-- For `z > 0` the value `radGreen α m c z` depends only on the values of `c` on the open
half-line `(0,∞)`: both integrals in `radGreen` are taken over subsets of `(0,∞)`
(namely `(0,z]` and `(z,∞)`). -/
private lemma radGreen_congr_of_eqOn_Ioi {α : ℝ} {m : ℕ} {c₁ c₂ : ℝ → ℝ}
    (h : ∀ t : ℝ, 0 < t → c₁ t = c₂ t) {z : ℝ} (hz : 0 < z) :
    Work.FTS.PhiStar.Radial.radGreen α m c₁ z
      = Work.FTS.PhiStar.Radial.radGreen α m c₂ z := by
  have h1 : (∫ t in (0 : ℝ)..z, c₁ t * t ^ ((2 * (m : ℝ) + 5) / α - 1))
      = ∫ t in (0 : ℝ)..z, c₂ t * t ^ ((2 * (m : ℝ) + 5) / α - 1) := by
    rw [intervalIntegral.integral_of_le hz.le, intervalIntegral.integral_of_le hz.le]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
      (fun t ht => by rw [h t ht.1])
  have h2 : (∫ t in Set.Ioi z, c₁ t * t ^ (-(2 * (m : ℝ) / α) - 1))
      = ∫ t in Set.Ioi z, c₂ t * t ^ (-(2 * (m : ℝ) / α) - 1) :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      (fun t ht => by rw [h t (lt_trans hz ht)])
  rw [Work.FTS.PhiStar.Radial.radGreen, Work.FTS.PhiStar.Radial.radGreen, h1, h2]

/-! ## The target -/

theorem integrableOn_acoeff_sq_w_sq_meas {α : ℝ} {m : ℕ} {F : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hm : 1 ≤ m)
    (hsm : Work.FTS.EllipticEst.SmoothOpen F) (hF : Work.Spaces.HkMem α 0 F)
    (hc : AEMeasurable (fun z : ℝ => if 0 < z then Work.FTS.PhiStar.Series.cmode m F z else 0)) :
    MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.FTS.PhiStar.Series.acoeff α m F z) ^ 2 * (Work.Spaces.w z) ^ 2)
      Work.Spaces.Iz := by
  classical
  set cl : ℝ → ℝ := fun z => if 0 < z then Work.FTS.PhiStar.Series.cmode m F z else 0 with hcl
  have hcl_eq : ∀ t : ℝ, 0 < t → cl t = Work.FTS.PhiStar.Series.cmode m F t := by
    intro t ht
    simp [hcl, ht]
  have hENpos : 0 < Work.EllipticEst.ModalSolution.eNorm m :=
    Work.EllipticEst.ModalSolution.eNorm_pos m
  -- the slice mass uniformly dominates the squared mode coefficient
  have hbnd : ∀ z : ℝ, 0 < z → (cl z) ^ 2
      ≤ (∫ θ in Work.Spaces.Iθ, (F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        / Work.EllipticEst.ModalSolution.eNorm m := by
    intro z hz
    have h := eNorm_mul_cmode_sq_le_sliceMass (m := m) (F := F) (z := z)
      (integrableOn_sq_sEta_of_HkMem hF hz)
    have h' : (Work.FTS.PhiStar.Series.cmode m F z) ^ 2
        * Work.EllipticEst.ModalSolution.eNorm m
        ≤ ∫ θ in Work.Spaces.Iθ,
            (F z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
      rw [mul_comm]; exact h
    rw [hcl_eq z hz]
    exact (le_div_iff₀ hENpos).mpr h'
  -- near `0`: `∫_0^1 c²/t⁴ < ∞`
  have hnear : MeasureTheory.IntegrableOn (fun t : ℝ => (cl t) ^ 2 / t ^ 4) (Set.Ioo 0 1) := by
    have hdom : MeasureTheory.IntegrableOn
        (fun t : ℝ => (Work.EllipticEst.ModalSolution.eNorm m)⁻¹
          * ((∫ θ in Work.Spaces.Iθ,
              (F t θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) / t ^ 4))
        (Set.Ioo 0 1) :=
      MeasureTheory.Integrable.const_mul (integrableOn_sliceMass_div_z4_of_HkMem hF) _
    refine MeasureTheory.Integrable.mono' (MeasureTheory.IntegrableOn.integrable hdom) ?_ ?_
    · exact (AEMeasurable.div
        ((hc.mono_measure MeasureTheory.Measure.restrict_le_self).pow_const 2)
        ((measurable_id.pow_const 4).aemeasurable)).aestronglyMeasurable
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
      have ht0 : 0 < t := ht.1
      have hb := hbnd t ht0
      rw [Real.norm_of_nonneg (by positivity)]
      calc (cl t) ^ 2 / t ^ 4
          ≤ ((∫ θ in Work.Spaces.Iθ,
                (F t θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
              / Work.EllipticEst.ModalSolution.eNorm m) / t ^ 4 :=
            div_le_div_of_nonneg_right hb (by positivity)
        _ = (Work.EllipticEst.ModalSolution.eNorm m)⁻¹
              * ((∫ θ in Work.Spaces.Iθ,
                  (F t θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) / t ^ 4) := by
            ring_nf
  -- far `∞`: `∫_1^∞ c² < ∞`
  have hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (cl t) ^ 2) (Set.Ioi 1) := by
    have hdom : MeasureTheory.IntegrableOn
        (fun t : ℝ => (Work.EllipticEst.ModalSolution.eNorm m)⁻¹
          * (∫ θ in Work.Spaces.Iθ,
              (F t θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))))
        (Set.Ioi 1) :=
      MeasureTheory.Integrable.const_mul (integrableOn_sliceMass_Ioi_one_of_HkMem hF) _
    refine MeasureTheory.Integrable.mono' (MeasureTheory.IntegrableOn.integrable hdom) ?_ ?_
    · exact ((hc.mono_measure MeasureTheory.Measure.restrict_le_self).pow_const 2).aestronglyMeasurable
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0 < t := lt_trans one_pos ht
      have hb := hbnd t ht0
      rw [Real.norm_of_nonneg (by positivity)]
      calc (cl t) ^ 2
          ≤ ((∫ θ in Work.Spaces.Iθ,
                (F t θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
              / Work.EllipticEst.ModalSolution.eNorm m) := hb
        _ = (Work.EllipticEst.ModalSolution.eNorm m)⁻¹
              * (∫ θ in Work.Spaces.Iθ,
                  (F t θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
            rw [div_eq_inv_mul]
  -- the radial Green's-function estimate
  have hE : MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.FTS.PhiStar.Radial.radGreen α m cl z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (Set.Ioi 0) :=
    radGreen_sq_w_sq_meas_engine hα hα4 hm hc hnear hfar
  -- replace the clamped coefficient by `cmode m F` (they agree on `(0,∞)`)
  have hEq : Set.EqOn
      (fun z : ℝ => (Work.FTS.PhiStar.Radial.radGreen α m cl z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (fun z : ℝ => (Work.FTS.PhiStar.Radial.radGreen α m
        (fun t : ℝ => Work.FTS.PhiStar.Series.cmode m F t) z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (Set.Ioi 0) := by
    intro z hz
    show (Work.FTS.PhiStar.Radial.radGreen α m cl z) ^ 2 * (Work.Spaces.w z) ^ 2
      = (Work.FTS.PhiStar.Radial.radGreen α m
          (fun t : ℝ => Work.FTS.PhiStar.Series.cmode m F t) z) ^ 2 * (Work.Spaces.w z) ^ 2
    rw [radGreen_congr_of_eqOn_Ioi (fun t ht => hcl_eq t ht) hz]
  have hE' := MeasureTheory.IntegrableOn.congr_fun hE hEq measurableSet_Ioi
  have hE'' := MeasureTheory.IntegrableOn.congr_set_ae hE'
    (MeasureTheory.Ioi_ae_eq_Ici).symm
  simpa only [Work.FTS.PhiStar.Series.acoeff, Work.Spaces.Iz] using hE''

end Work.FTS.PhiStar.Honesty
