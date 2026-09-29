import Mathlib
import Submission.Work.C17.lead_defs
import Submission.Work.C17.lead_api
import Submission.Work.C17.reg_sigma
import Submission.Work.C17.sigma_defs
import Submission.Work.C17.rhoS_zpow_expand

namespace Work.C17

open Commons.FieldTheory.RatFunc

noncomputable section

/-- The leading term at `0` of every integer power of the unit `rhoS = (xQ - 1)⁻¹`:
`rhoS^e = (-1)^e + O(x)`.  This follows from the second order expansion
`rhoS^e = (-1)^e + (-1)^e·e·x + x²·h` of `Work.C17.rhoS_zpow_expand`. -/
theorem rhoS_zpow_lead_aux (e : ℤ) : LeadAt (rhoS ^ e) 0 ((-1 : ℚ) ^ e) := by
  obtain ⟨h, hreg, hexp⟩ := rhoS_zpow_expand e
  refine leadAt_of_eq_mul_X (f := rhoS ^ e) (e := 0) (l := (-1 : ℚ) ^ e)
    (hl := zpow_ne_zero e (by norm_num : (-1 : ℚ) ≠ 0))
    (g := algebraMap ℚ (RatFunc ℚ) ((-1 : ℚ) ^ e * (e : ℚ)) + xQ * h) ?_ ?_
  · exact reg_add (reg_rat _) (reg_mul reg_X hreg)
  · rw [hexp]; simp only [neg_zero, zpow_zero, mul_one]; ring

/-- Since `sigmaQ xQ = xQ * rhoS`, the deck involution commutes with the normalisation
`· xQ ^ (-e)` up to the unit `rhoS ^ e`. -/
theorem sigmaQ_mul_xQ_zpow_aux (f : RatFunc ℚ) (e : ℤ) :
    sigmaQ f * xQ ^ (-e) = sigmaQ (f * xQ ^ (-e)) * rhoS ^ e := by
  have hsq : sigmaQ (xQ ^ (-e)) = xQ ^ (-e) * rhoS ^ (-e) := by
    rw [map_zpow₀ sigmaQ xQ (-e), sigmaQ_xQ_eq, mul_zpow]
  have hcancel : rhoS ^ (-e) * rhoS ^ e = 1 := by
    rw [← zpow_add₀ rhoS_ne_zero, neg_add_cancel, zpow_zero]
  rw [map_mul, hsq,
    show sigmaQ f * (xQ ^ (-e) * rhoS ^ (-e)) * rhoS ^ e
      = sigmaQ f * xQ ^ (-e) * (rhoS ^ (-e) * rhoS ^ e) by ring,
    hcancel, mul_one]

/-- The deck involution `sigmaQ` acts on the local parameter at its fixed point `0` with
differential `-1`: it preserves the leading term up to the sign `(-1)^e`. -/
theorem sigma_lead1 (f : RatFunc ℚ) (e : ℤ) (l : ℚ) (h1 : LeadAt f e l) :
    LeadAt (sigmaQ f) e ((-1 : ℚ) ^ e * l) := by
  obtain ⟨hl, h1'⟩ := h1
  -- Step 1: `sigmaQ` preserves the order of vanishing at `0`.
  have hσG : ((1 : ℤ) : WithTop ℤ) ≤
      ordAtT (0 : ℚ) (sigmaQ (f * xQ ^ (-e)) - algebraMap ℚ (RatFunc ℚ) l) := by
    have heq : sigmaQ (f * xQ ^ (-e)) - algebraMap ℚ (RatFunc ℚ) l
        = sigmaQ (f * xQ ^ (-e) - algebraMap ℚ (RatFunc ℚ) l) := by
      rw [map_sub, AlgEquiv.commutes]
    rw [heq, regSigma.ordAtT_sigmaQ]
    exact h1'
  -- Step 2: the leading term of `rhoS ^ e`.
  have hρ : ((1 : ℤ) : WithTop ℤ) ≤
      ordAtT (0 : ℚ) (rhoS ^ e - algebraMap ℚ (RatFunc ℚ) ((-1 : ℚ) ^ e)) := by
    simpa using (rhoS_zpow_lead_aux e).2
  refine ⟨mul_ne_zero (zpow_ne_zero e (by norm_num : (-1 : ℚ) ≠ 0)) hl, ?_⟩
  -- Step 3: pass to the normalised coordinates `sigmaQ f * x^(-e) = sigmaQ(f x^(-e)) * rhoS^e`.
  rw [sigmaQ_mul_xQ_zpow_aux f e]
  have hsplit : sigmaQ (f * xQ ^ (-e)) * rhoS ^ e - algebraMap ℚ (RatFunc ℚ) ((-1 : ℚ) ^ e * l)
      = (sigmaQ (f * xQ ^ (-e)) - algebraMap ℚ (RatFunc ℚ) l) * rhoS ^ e
        + algebraMap ℚ (RatFunc ℚ) l
          * (rhoS ^ e - algebraMap ℚ (RatFunc ℚ) ((-1 : ℚ) ^ e)) := by
    rw [map_mul, map_mul]; ring
  rw [hsplit]
  refine ordAtT_add_ge' (j := 1) ?_ ?_
  · have hreg : ((0 : ℤ) : WithTop ℤ) ≤ ordAtT (0 : ℚ) (rhoS ^ e) := reg_zpow unit0_rhoS e
    simpa using ordAtT_mul_ge (j := 1) (k := 0) hσG hreg
  · simpa using ordAtT_mul_ge (j := 0) (k := 1)
      (le_of_eq (ordAtT_rat hl).symm) hρ

end

end Work.C17
