import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.H2.ModalSolR.RGWeakAux
import Submission.Work.EllipticEst.ModalSolution.RGW.lagrange_ibp
import Submission.Work.EllipticEst.ModalSolution.RGW.Lneg_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.ModalSolR.RGWeak

open Work.EllipticEst.ModalSolution.RadGreenWeak
open Work.FTS.PhiStar.Radial
open MeasureTheory Set Filter
open scoped Real Topology

theorem qm_formula {α : ℝ} (hα : 0 < α) (m : ℕ) {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 2 ψ)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hvan : ∀ z : ℝ, z ∉ Set.Ioo a b → ψ z = 0 ∧ deriv ψ z = 0) :
    ∀ t ∈ Set.Icc a b,
      (∫ z in t..b, z ^ (Work.EllipticEst.ModalSolution.RadGreenWeak.sM α m) *
          (Work.EllipticEst.ModalSolution.RadGreenWeak.wgt α z *
            Work.EllipticEst.ModalSolution.RadGreenWeak.Lneg α ψ z))
        = - Work.FTS.PhiStar.Radial.lamR m *
            (∫ z in t..b, z ^ (Work.EllipticEst.ModalSolution.RadGreenWeak.sM α m) *
              (Work.EllipticEst.ModalSolution.RadGreenWeak.wgt α z * ψ z))
          + Work.FTS.H2.ModalSolR.RGWeak.Fgen α (Work.EllipticEst.ModalSolution.RadGreenWeak.sM α m) ψ t := by
  intro t ht
  have ht0 : 0 < t := lt_of_lt_of_le ha ht.1
  have htb : t ≤ b := ht.2
  have hψon : ContDiffOn ℝ 2 ψ (Set.Ioi 0) := hψ.contDiffOn
  have hs : α ^ 2 * (sM α m) ^ 2 + 5 * α * (sM α m) = lamR m :=
    indicial_sM (ne_of_gt hα) m
  have hFb : Fgen α (sM α m) ψ b = 0 := by
    obtain ⟨h0, h1⟩ := hvan b (by simp [Set.mem_Ioo])
    exact Fgen_eq_zero h0 h1
  have hsub : Set.Icc t b ⊆ Set.Ioi (0 : ℝ) := fun z hz => lt_of_lt_of_le ht0 hz.1
  have hpow : ContinuousOn (fun z : ℝ => z ^ (sM α m)) (Set.Ioi 0) := fun z hz =>
    (Real.continuousAt_rpow_const z (sM α m) (Or.inl (ne_of_gt hz))).continuousWithinAt
  have hwgtc : ContinuousOn (wgt α) (Set.Ioi 0) := fun z hz =>
    (Real.continuousAt_rpow_const z (qW α) (Or.inl (ne_of_gt hz))).continuousWithinAt
  have hLc : ContinuousOn (Lneg α ψ) (Set.Ioi 0) :=
    Work.EllipticEst.ModalSolution.RGW.Lneg_continuousOn α hψon
  have hcontA : ContinuousOn (fun z => z ^ (sM α m) * (wgt α z * Lneg α ψ z)) (Set.Icc t b) :=
    (hpow.mono hsub).mul ((hwgtc.mono hsub).mul (hLc.mono hsub))
  have hcontB : ContinuousOn (fun z => z ^ (sM α m) * wgt α z * ψ z) (Set.Icc t b) :=
    ((hpow.mono hsub).mul (hwgtc.mono hsub)).mul
      ((hψ.continuous.continuousOn).mono hsub)
  have hIntA : IntervalIntegrable (fun z => z ^ (sM α m) * (wgt α z * Lneg α ψ z)) volume t b :=
    hcontA.intervalIntegrable_of_Icc htb
  have hIntB : IntervalIntegrable (fun z => z ^ (sM α m) * wgt α z * ψ z) volume t b :=
    hcontB.intervalIntegrable_of_Icc htb
  have hIntBc : IntervalIntegrable (fun z => lamR m * (z ^ (sM α m) * wgt α z * ψ z)) volume t b :=
    hIntB.const_mul (lamR m)
  have hIntD : IntervalIntegrable
      (fun z => z ^ (sM α m) * (wgt α z * Lneg α ψ z)
        + lamR m * (z ^ (sM α m) * wgt α z * ψ z)) volume t b :=
    hIntA.add hIntBc
  have hderiv : ∀ x ∈ Set.uIcc t b,
      HasDerivAt (Fgen α (sM α m) ψ)
        (-(x ^ (sM α m) * (wgt α x * Lneg α ψ x)
          + lamR m * (x ^ (sM α m) * wgt α x * ψ x))) x := by
    intro x hx
    rw [Set.uIcc_of_le htb] at hx
    exact Fgen_hasDerivAt hα hs hψon x (lt_of_lt_of_le ht0 hx.1)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hIntD.neg
  have hsplit :
      ∫ x in t..b, -(x ^ (sM α m) * (wgt α x * Lneg α ψ x)
          + lamR m * (x ^ (sM α m) * wgt α x * ψ x))
        = -((∫ x in t..b, x ^ (sM α m) * (wgt α x * Lneg α ψ x))
            + lamR m * (∫ x in t..b, x ^ (sM α m) * wgt α x * ψ x)) := by
    rw [intervalIntegral.integral_neg,
        intervalIntegral.integral_add (f := fun z => z ^ (sM α m) * (wgt α z * Lneg α ψ z))
          (g := fun z => lamR m * (z ^ (sM α m) * wgt α z * ψ z)) hIntA hIntBc,
        intervalIntegral.integral_const_mul]
  have hval : ∫ x in t..b, x ^ (sM α m) * (wgt α x * Lneg α ψ x)
      = Fgen α (sM α m) ψ t - lamR m * (∫ x in t..b, x ^ (sM α m) * wgt α x * ψ x) := by
    have h := hFTC
    rw [hsplit, hFb, zero_sub] at h
    linarith
  have hcongr : ∫ x in t..b, x ^ (sM α m) * (wgt α x * ψ x)
      = ∫ x in t..b, x ^ (sM α m) * wgt α x * ψ x :=
    intervalIntegral.integral_congr (fun x _ => by ring)
  rw [hcongr, hval]
  ring

end Work.FTS.H2.ModalSolR.RGWeak
