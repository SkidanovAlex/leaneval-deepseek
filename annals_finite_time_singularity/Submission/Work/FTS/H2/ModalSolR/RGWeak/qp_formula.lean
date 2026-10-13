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

theorem qp_formula {α : ℝ} (hα : 0 < α) (m : ℕ) {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 2 ψ)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hvan : ∀ z : ℝ, z ∉ Set.Ioo a b → ψ z = 0 ∧ deriv ψ z = 0) :
    ∀ t ∈ Set.Icc a b,
      (∫ z in a..t, z ^ (Work.EllipticEst.ModalSolution.RadGreenWeak.sP α m) *
          (Work.EllipticEst.ModalSolution.RadGreenWeak.wgt α z *
            Work.EllipticEst.ModalSolution.RadGreenWeak.Lneg α ψ z))
        = - Work.FTS.PhiStar.Radial.lamR m *
            (∫ z in a..t, z ^ (Work.EllipticEst.ModalSolution.RadGreenWeak.sP α m) *
              (Work.EllipticEst.ModalSolution.RadGreenWeak.wgt α z * ψ z))
          - Work.FTS.H2.ModalSolR.RGWeak.Fgen α (Work.EllipticEst.ModalSolution.RadGreenWeak.sP α m) ψ t := by
  intro t ht
  have ht0 : 0 < t := lt_of_lt_of_le ha ht.1
  have hat : a ≤ t := ht.1
  have hψon : ContDiffOn ℝ 2 ψ (Set.Ioi 0) := hψ.contDiffOn
  have hs : α ^ 2 * (sP α m) ^ 2 + 5 * α * (sP α m) = lamR m :=
    indicial_sP (ne_of_gt hα) m
  have hFa : Fgen α (sP α m) ψ a = 0 := by
    obtain ⟨h0, h1⟩ := hvan a (by simp [Set.mem_Ioo])
    exact Fgen_eq_zero h0 h1
  have hsub : Set.Icc a t ⊆ Set.Ioi (0 : ℝ) := fun z hz => lt_of_lt_of_le ha hz.1
  have hpow : ContinuousOn (fun z : ℝ => z ^ (sP α m)) (Set.Ioi 0) := fun z hz =>
    (Real.continuousAt_rpow_const z (sP α m) (Or.inl (ne_of_gt hz))).continuousWithinAt
  have hwgtc : ContinuousOn (wgt α) (Set.Ioi 0) := fun z hz =>
    (Real.continuousAt_rpow_const z (qW α) (Or.inl (ne_of_gt hz))).continuousWithinAt
  have hLc : ContinuousOn (Lneg α ψ) (Set.Ioi 0) :=
    Work.EllipticEst.ModalSolution.RGW.Lneg_continuousOn α hψon
  have hcontA : ContinuousOn (fun z => z ^ (sP α m) * (wgt α z * Lneg α ψ z))
      (Set.Icc a t) :=
    (hpow.mono hsub).mul ((hwgtc.mono hsub).mul (hLc.mono hsub))
  have hcontB : ContinuousOn (fun z => z ^ (sP α m) * wgt α z * ψ z) (Set.Icc a t) :=
    ((hpow.mono hsub).mul (hwgtc.mono hsub)).mul
      ((hψ.continuous.continuousOn).mono hsub)
  have hIntA : IntervalIntegrable
      (fun z => z ^ (sP α m) * (wgt α z * Lneg α ψ z)) volume a t :=
    hcontA.intervalIntegrable_of_Icc hat
  have hIntB : IntervalIntegrable (fun z => z ^ (sP α m) * wgt α z * ψ z) volume a t :=
    hcontB.intervalIntegrable_of_Icc hat
  have hIntBc : IntervalIntegrable
      (fun z => lamR m * (z ^ (sP α m) * wgt α z * ψ z)) volume a t :=
    hIntB.const_mul (lamR m)
  have hIntD : IntervalIntegrable
      (fun z => z ^ (sP α m) * (wgt α z * Lneg α ψ z)
        + lamR m * (z ^ (sP α m) * wgt α z * ψ z)) volume a t :=
    hIntA.add hIntBc
  have hderiv : ∀ x ∈ Set.uIcc a t,
      HasDerivAt (Fgen α (sP α m) ψ)
        (-(x ^ (sP α m) * (wgt α x * Lneg α ψ x)
          + lamR m * (x ^ (sP α m) * wgt α x * ψ x))) x := by
    intro x hx
    rw [Set.uIcc_of_le hat] at hx
    exact Fgen_hasDerivAt hα hs hψon x (lt_of_lt_of_le ha hx.1)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hIntD.neg
  have hsplit :
      ∫ x in a..t, -(x ^ (sP α m) * (wgt α x * Lneg α ψ x)
          + lamR m * (x ^ (sP α m) * wgt α x * ψ x))
        = -((∫ x in a..t, x ^ (sP α m) * (wgt α x * Lneg α ψ x))
            + lamR m * (∫ x in a..t, x ^ (sP α m) * wgt α x * ψ x)) := by
    rw [intervalIntegral.integral_neg,
        intervalIntegral.integral_add (f := fun z => z ^ (sP α m) * (wgt α z * Lneg α ψ z))
          (g := fun z => lamR m * (z ^ (sP α m) * wgt α z * ψ z)) hIntA hIntBc,
        intervalIntegral.integral_const_mul]
  have hval : ∫ x in a..t, x ^ (sP α m) * (wgt α x * Lneg α ψ x)
      = - lamR m * (∫ x in a..t, x ^ (sP α m) * wgt α x * ψ x)
        - Fgen α (sP α m) ψ t := by
    have h := hFTC
    rw [hsplit, hFa, sub_zero] at h
    linarith
  have hcongr : ∫ x in a..t, x ^ (sP α m) * (wgt α x * ψ x)
      = ∫ x in a..t, x ^ (sP α m) * wgt α x * ψ x :=
    intervalIntegral.integral_congr (fun x _ => by ring)
  rw [hcongr, hval]

end Work.FTS.H2.ModalSolR.RGWeak
