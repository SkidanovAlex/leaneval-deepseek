import Mathlib
import Submission.Work.C17.lead_defs
import Submission.Work.C17.lead_api
import Submission.Work.C17.reg_sigma
import Submission.Work.C17.sigma_defs
import Submission.Work.C17.rhoS_zpow_expand

namespace Work.C17
open Commons.FieldTheory.RatFunc
noncomputable section

theorem sigmaQ_mul_xQ_zpow (f : RatFunc ℚ) (e : ℤ) :
    sigmaQ f * xQ ^ (-e) = sigmaQ (f * xQ ^ (-e)) * rhoS ^ e := by
  have hx : xQ ≠ 0 := xQ_ne_zero
  have hr : rhoS ≠ 0 := rhoS_ne_zero
  have hsq : sigmaQ (xQ ^ (-e)) = xQ ^ (-e) * rhoS ^ (-e) := by
    rw [map_zpow₀ sigmaQ xQ (-e), sigmaQ_xQ_eq, mul_zpow]
  have h1 : rhoS ^ (-e) * rhoS ^ e = 1 := by
    rw [← zpow_add₀ hr, neg_add_cancel, zpow_zero]
  rw [map_mul, hsq,
    show sigmaQ f * (xQ ^ (-e) * rhoS ^ (-e)) * rhoS ^ e
      = sigmaQ f * xQ ^ (-e) * (rhoS ^ (-e) * rhoS ^ e) by ring]
  rw [h1, mul_one]

theorem ordAtT_mul_xQ_sq_ge {g : RatFunc ℚ} (hg : Reg g) :
    ((2:ℤ):WithTop ℤ) ≤ ordAtT (0:ℚ) (xQ^2 * g) := by
  rcases eq_or_ne g 0 with rfl | hg0
  · rw [mul_zero, ordAtT_zero]; exact le_top
  · rw [ordAtT_mul (0:ℚ) (pow_ne_zero 2 xQ_ne_zero) hg0, ordAtT_pow (0:ℚ) xQ_ne_zero 2, ordAtT_xQ]
    rw [Reg] at hg
    simpa using le_add_of_nonneg_right hg

theorem lead2_aux1 (l : ℚ) (e : ℤ) :
    ((2:ℤ):WithTop ℤ) ≤ ordAtT (0:ℚ) (algebraMap ℚ (RatFunc ℚ) l *
      (rhoS^e - algebraMap ℚ (RatFunc ℚ) ((-1:ℚ)^e)
        - algebraMap ℚ (RatFunc ℚ) ((-1:ℚ)^e * (e:ℚ)) * xQ)) := by
  obtain ⟨h, hreg, hexp⟩ := rhoS_zpow_expand e
  have hT : algebraMap ℚ (RatFunc ℚ) l *
      (rhoS^e - algebraMap ℚ (RatFunc ℚ) ((-1:ℚ)^e)
        - algebraMap ℚ (RatFunc ℚ) ((-1:ℚ)^e * (e:ℚ)) * xQ)
      = xQ^2 * (algebraMap ℚ (RatFunc ℚ) l * h) := by
    rw [hexp]; ring
  rw [hT]
  exact ordAtT_mul_xQ_sq_ge (reg_mul (reg_rat l) hreg)

theorem lead2_aux2 (m : ℚ) (e : ℤ) :
    ((2:ℤ):WithTop ℤ) ≤ ordAtT (0:ℚ) (algebraMap ℚ (RatFunc ℚ) m * xQ *
      (rhoS^(e+1) - algebraMap ℚ (RatFunc ℚ) ((-1:ℚ)^(e+1)))) := by
  obtain ⟨h, hreg, hexp⟩ := rhoS_zpow_expand (e+1)
  have hT : algebraMap ℚ (RatFunc ℚ) m * xQ * (rhoS^(e+1) - algebraMap ℚ (RatFunc ℚ) ((-1:ℚ)^(e+1)))
      = xQ^2 * (algebraMap ℚ (RatFunc ℚ) m *
          (algebraMap ℚ (RatFunc ℚ) ((-1:ℚ)^(e+1) * (((e+1:ℤ)):ℚ)) + xQ * h)) := by
    rw [hexp]; ring
  rw [hT]
  exact ordAtT_mul_xQ_sq_ge (reg_mul (reg_rat m) (reg_add (reg_rat _) (reg_mul reg_X hreg)))

theorem sigma_lead (f : RatFunc ℚ) (e : ℤ) (l m : ℚ)
    (h1 : LeadAt f e l) (h2 : Lead2At f e l m) :
    LeadAt (sigmaQ f) e ((-1 : ℚ) ^ e * l) ∧
    Lead2At (sigmaQ f) e ((-1 : ℚ) ^ e * l) ((-1 : ℚ) ^ e * ((e : ℚ) * l - m)) := by
  have hl : l ≠ 0 := h2.1
  have hmain : Lead2At (sigmaQ f) e ((-1 : ℚ) ^ e * l) ((-1 : ℚ) ^ e * ((e : ℚ) * l - m)) := by
    refine ⟨mul_ne_zero (zpow_ne_zero e (by norm_num : (-1:ℚ) ≠ 0)) hl, ?_⟩
    set A : RatFunc ℚ := f * xQ ^ (-e) with hAdef
    set B : RatFunc ℚ := A - algebraMap ℚ (RatFunc ℚ) l - algebraMap ℚ (RatFunc ℚ) m * xQ with hBdef
    have hBord : ((2:ℤ):WithTop ℤ) ≤ ordAtT (0:ℚ) B := by rw [hBdef, hAdef]; exact h2.2
    have hI : sigmaQ f * xQ ^ (-e) = sigmaQ A * rhoS ^ e := by
      rw [hAdef]; exact sigmaQ_mul_xQ_zpow f e
    have hAd : sigmaQ A = algebraMap ℚ (RatFunc ℚ) l + algebraMap ℚ (RatFunc ℚ) m * (xQ*rhoS)
        + sigmaQ B := by
      have hdec : A = algebraMap ℚ (RatFunc ℚ) l + algebraMap ℚ (RatFunc ℚ) m * xQ + B := by
        rw [hBdef]; ring
      nth_rewrite 1 [hdec]
      rw [map_add, map_add, map_mul, sigmaQ_xQ_eq, AlgEquiv.commutes, AlgEquiv.commutes]
    have hP : sigmaQ f * xQ^(-e) - algebraMap ℚ (RatFunc ℚ) ((-1:ℚ)^e * l)
        - algebraMap ℚ (RatFunc ℚ) ((-1:ℚ)^e * ((e:ℚ)*l - m)) * xQ
        = (algebraMap ℚ (RatFunc ℚ) l * (rhoS^e - algebraMap ℚ (RatFunc ℚ) ((-1:ℚ)^e)
              - algebraMap ℚ (RatFunc ℚ) ((-1:ℚ)^e * (e:ℚ)) * xQ))
          + ((algebraMap ℚ (RatFunc ℚ) m * xQ
                * (rhoS^(e+1) - algebraMap ℚ (RatFunc ℚ) ((-1:ℚ)^(e+1))))
            + sigmaQ B * rhoS^e) := by
      have hY1 : rhoS * rhoS ^ e = rhoS ^ (e+1) := by
        rw [mul_comm rhoS (rhoS^e), ← zpow_add_one₀ rhoS_ne_zero]
      have hZr : (xQ * rhoS) * rhoS ^ e = xQ * rhoS ^ (e+1) := by rw [mul_assoc, hY1]
      have hCe'arg : (-1:ℚ)^(e+1) = -((-1:ℚ)^e) := by
        rw [zpow_add_one₀ (by norm_num : (-1:ℚ) ≠ 0)]; ring
      have hCe' : algebraMap ℚ (RatFunc ℚ) ((-1:ℚ)^(e+1))
          = -algebraMap ℚ (RatFunc ℚ) ((-1:ℚ)^e) := by rw [hCe'arg, map_neg]
      have hCee : algebraMap ℚ (RatFunc ℚ) ((-1:ℚ)^e * (e:ℚ))
          = algebraMap ℚ (RatFunc ℚ) ((-1:ℚ)^e) * algebraMap ℚ (RatFunc ℚ) (e:ℚ) := by rw [map_mul]
      have hl' : algebraMap ℚ (RatFunc ℚ) ((-1:ℚ)^e * l)
          = algebraMap ℚ (RatFunc ℚ) ((-1:ℚ)^e) * algebraMap ℚ (RatFunc ℚ) l := by rw [map_mul]
      have hm' : algebraMap ℚ (RatFunc ℚ) ((-1:ℚ)^e * ((e:ℚ)*l - m))
          = algebraMap ℚ (RatFunc ℚ) ((-1:ℚ)^e)
            * (algebraMap ℚ (RatFunc ℚ) (e:ℚ) * algebraMap ℚ (RatFunc ℚ) l
                - algebraMap ℚ (RatFunc ℚ) m) := by
        rw [map_mul, map_sub, map_mul]
      rw [hI, hAd, hl', hm', hCee, hCe',
        show (algebraMap ℚ (RatFunc ℚ) l + algebraMap ℚ (RatFunc ℚ) m * (xQ * rhoS) + sigmaQ B) * rhoS^e
          = algebraMap ℚ (RatFunc ℚ) l * rhoS^e
            + algebraMap ℚ (RatFunc ℚ) m * ((xQ*rhoS)*rhoS^e) + sigmaQ B * rhoS^e by ring,
        hZr]
      ring
    have hT1 := lead2_aux1 l e
    have hT2 := lead2_aux2 m e
    have hT3 : ((2:ℤ):WithTop ℤ) ≤ ordAtT (0:ℚ) (sigmaQ B * rhoS^e) := by
      have hσB : ((2:ℤ):WithTop ℤ) ≤ ordAtT (0:ℚ) (sigmaQ B) := by
        rw [regSigma.ordAtT_sigmaQ]; exact hBord
      have hreg : ((0:ℤ):WithTop ℤ) ≤ ordAtT (0:ℚ) (rhoS^e) := reg_zpow unit0_rhoS e
      have h := ordAtT_mul_ge (a := sigmaQ B) (b := rhoS^e) (j := 2) (k := 0) hσB hreg
      simpa using h
    have hT23 : ((2:ℤ):WithTop ℤ) ≤ ordAtT (0:ℚ)
        (algebraMap ℚ (RatFunc ℚ) m * xQ
            * (rhoS^(e+1) - algebraMap ℚ (RatFunc ℚ) ((-1:ℚ)^(e+1))) + sigmaQ B * rhoS^e) :=
      ordAtT_add_ge' hT2 hT3
    have hT123 : ((2:ℤ):WithTop ℤ) ≤ ordAtT (0:ℚ)
        (algebraMap ℚ (RatFunc ℚ) l * (rhoS^e - algebraMap ℚ (RatFunc ℚ) ((-1:ℚ)^e)
              - algebraMap ℚ (RatFunc ℚ) ((-1:ℚ)^e * (e:ℚ)) * xQ)
          + (algebraMap ℚ (RatFunc ℚ) m * xQ
              * (rhoS^(e+1) - algebraMap ℚ (RatFunc ℚ) ((-1:ℚ)^(e+1))) + sigmaQ B * rhoS^e)) :=
      ordAtT_add_ge' hT1 hT23
    rw [hP]; exact hT123
  exact ⟨hmain.to_LeadAt, hmain⟩

end
end Work.C17
