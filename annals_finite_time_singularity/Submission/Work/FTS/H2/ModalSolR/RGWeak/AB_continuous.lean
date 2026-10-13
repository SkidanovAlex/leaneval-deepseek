import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Submission.Work.EllipticEst.ModalSolution.RGW.srcM_integrable
import Submission.Work.EllipticEst.ModalSolution.RGW.srcP_integrable
import Submission.Work.EllipticEst.ModalSolution.RGW.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.ModalSolR.RGWeak

open MeasureTheory Set

/-- Continuity of the lower antiderivative `z ↦ ∫_0^z f` on `[a,b]`, `0 < a`, for `f`
integrable on `(0,b]`.  (A general-purpose fact, isolated because it is used twice.) -/
lemma continuousOn_intervalIntegral_zero {f : ℝ → ℝ} {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hf : IntegrableOn f (Ioc 0 b)) :
    ContinuousOn (fun z => ∫ t in (0 : ℝ)..z, f t) (Icc a b) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hInt : IntervalIntegrable f volume 0 b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hb.le).2 hf
  have hcont : ContinuousOn (fun z => ∫ t in (0 : ℝ)..z, f t) (uIcc 0 b) :=
    intervalIntegral.continuousOn_primitive_interval' hInt left_mem_uIcc
  rw [uIcc_of_le hb.le] at hcont
  exact hcont.mono fun z hz => ⟨le_trans ha.le hz.1, hz.2⟩

/-- Continuity of the tail integral `z ↦ ∫_z^∞ f` on `[a,b]`, `0 < a`, for `f` integrable
on `(a,∞)`. -/
lemma continuousOn_setIntegral_Ioi {f : ℝ → ℝ} {a b : ℝ} (hf : IntegrableOn f (Ioi a)) :
    ContinuousOn (fun z => ∫ t in Ioi z, f t) (Icc a b) :=
  hf.continuousOn_Ici_primitive_Ioi.mono fun _ hz => hz.1

theorem AB_continuous {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (m : ℕ) {c : ℝ → ℝ}
    (hc : MeasureTheory.IntegrableOn (fun t => c t ^ 2) (Set.Ioi 0))
    (hcm : MeasureTheory.AEStronglyMeasurable c (MeasureTheory.volume.restrict (Set.Ioi 0)))
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ContinuousOn (fun z => ∫ t in (0 : ℝ)..z,
        Work.EllipticEst.ModalSolution.RadGreenWeak.srcM α m c t) (Set.Icc a b) ∧
      ContinuousOn (fun z => ∫ t in Set.Ioi z,
        Work.EllipticEst.ModalSolution.RadGreenWeak.srcP α m c t) (Set.Icc a b) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  refine ⟨continuousOn_intervalIntegral_zero ha hab ?_, continuousOn_setIntegral_Ioi ?_⟩
  · exact Work.EllipticEst.ModalSolution.RGW.srcM_integrable hα hα1 m hc hcm hb
  · exact Work.EllipticEst.ModalSolution.RGW.srcP_integrable hα hα1 m hc hcm ha

end Work.FTS.H2.ModalSolR.RGWeak
