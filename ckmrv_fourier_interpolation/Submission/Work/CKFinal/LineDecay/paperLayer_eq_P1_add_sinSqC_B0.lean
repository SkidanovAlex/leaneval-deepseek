import Mathlib
import Submission.Work.CKFinal.LineDecay.Defs
import Submission.Work.CKFinal.LineDecay.shift_helpers
import Submission.Work.CKFinal.LineDecay.Aexp_gauss_integrable
import Submission.Work.Asymptotics.TSasm.LayerAgreementClean
import Submission.Work.LayerCont.FarTail.CuspFar
import Submission.Work.Asymptotics.NonCoincidence.jInvariantFun_ne_imagAxis_of_re_notInt_im_gt_half
import Submission.Work.Asymptotics.FunnelAsm.aexpClosed

namespace Work.CKFinal.LineDecay

open MeasureTheory UpperHalfPlane
open scoped Topology

theorem paperLayer_eq_P1_add_sinSqC_B0 (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : UpperHalfPlane) {r : ℝ} (hr : 2 < r ^ 2) (hD : τ ∈ Work.Asymptotics.DomainD)
    (hre : τ.re = 1 / 2 ∨ τ.re = -1 / 2) (him : 12 ≤ τ.im) :
    Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ r
      = Work.CKFinal.P1 (Work.Kernels.Kfun ℓ d) r τ
        + Work.Asymptotics.sinSqC r * (∫ t in Set.Ioi 1, Work.CKFinal.LineDecay.A0fun ℓ d τ r t) := by
  have hrne : r ≠ 0 := by
    intro h0
    rw [h0] at hr
    norm_num at hr
  have hτ : Work.Asymptotics.Funnel τ := ⟨hD, by linarith⟩
  have hreg : d = 8 ∨ 2 < r ^ 2 := Or.inr hr
  -- integrability on `(1,∞)`
  have htail : IntegrableOn (fun t : ℝ => (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
      - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t) * Work.Asymptotics.gaussWeight r t)
      (Set.Ioi 1) :=
    (Work.LayerCont.FarTail.tail_integrableOn_of_mem_DomainD ℓ d hd hD r).mono_set
      Set.Ioi_subset_Ici_self
  have hexp : IntegrableOn (fun t : ℝ => Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t
      * Work.Asymptotics.gaussWeight r t) (Set.Ioi 1) :=
    (Aexp_gauss_integrable ℓ d τ hr).mono_set Set.Ioi_subset_Ici_self
  have hKaxInt : IntegrableOn (fun t : ℝ => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
      * Work.Asymptotics.gaussWeight r t) (Set.Ioi 1) :=
    (htail.add hexp).congr_fun (fun t _ => by simp only [Pi.add_apply]; ring) measurableSet_Ioi
  -- `paperLayer = layerLow + layerTrunc + highPart`
  have hlow : Work.Asymptotics.layerLow ℓ d τ r = Work.CKFinal.P1 (Work.Kernels.Kfun ℓ d) r τ := by
    simp only [Work.Asymptotics.layerLow, Work.CKFinal.P1, Work.CKFinal.hsplit,
      Work.CKFinal.Kax_eq_Kaxis, Work.Asymptotics.gaussWeight,
      Work.CKFinal.LineDecay.sinSq_eq_sinSqC]
  have htrunc : Work.Asymptotics.layerTrunc (Work.Asymptotics.Gcusp ℓ d) ℓ d τ r
      = Work.Asymptotics.sinSq r * (∫ t in Set.Ioi 1, (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
          - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t) * Work.Asymptotics.gaussWeight r t) := by
    simp only [Work.Asymptotics.layerTrunc, Work.Asymptotics.gaussWeight,
      MeasureTheory.integral_Ici_eq_integral_Ioi]
  have hhigh : Work.Asymptotics.highPart (Work.Asymptotics.Gcusp ℓ d) τ r
      = Work.Asymptotics.sinSq r * (∫ t in Set.Ioi 1, Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d)
          τ t * Work.Asymptotics.gaussWeight r t) :=
    Work.Asymptotics.FunnelAsm.highPart_eq_integral ℓ d hd hτ hrne hreg
  -- split the cusp-subtracted integral
  have hsub : (∫ t in Set.Ioi 1, (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
        - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t) * Work.Asymptotics.gaussWeight r t)
      = (∫ t in Set.Ioi 1, Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
          * Work.Asymptotics.gaussWeight r t)
        - (∫ t in Set.Ioi 1, Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t
          * Work.Asymptotics.gaussWeight r t) := by
    rw [← MeasureTheory.integral_sub hKaxInt hexp]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun t _ => by ring)
  have hA0 : (∫ t in Set.Ioi 1, Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
        * Work.Asymptotics.gaussWeight r t)
      = (∫ t in Set.Ioi 1, Work.CKFinal.LineDecay.A0fun ℓ d τ r t) := by
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun t _ => by
      simp only [Work.CKFinal.LineDecay.A0fun, Work.CKFinal.Kax_eq_Kaxis])
  simp only [Work.Asymptotics.paperLayer]
  rw [hlow, htrunc, hhigh, hsub, hA0, Work.CKFinal.LineDecay.sinSq_eq_sinSqC]
  ring

end Work.CKFinal.LineDecay
