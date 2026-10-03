import Mathlib
import Submission.Work.FIRed6Axis.Defs6Axis
import Submission.Work.FITop4.Defs6

namespace Work.FIRed6Axis

attribute [local instance] Classical.propDecidable

/-- **The far-piece class split** (task (2) of the round-6 axis repair).

Copy the pointwise proof of `Work.FITop4.classRestrict_isBetaCoeff6`
(`Submission/Work/FITop4/Defs6.lean`) and replace its `SameClass8 ∧ IsAxisFree` mask by the single
`SameClass8` mask, supplying the missing `IsAxisFree` conjunct from the far hypothesis: for
`z` with `InPolarBox Pa φ z` one has `IsAxisFree Pa z` by `Work.FIRed6Axis.FarPiece_isAxisFree`,
which consumes `Work.FITop6.Sector.arg_dist_implies_axisFree` BY NAME (FITop6 owns the two trig
stubs `Sector.TrigAux.abs_cos_gt_of_arg_dist` / `abs_sin_gt_of_arg_dist`; do not copy them).  The
first three conjuncts of `IsBetaCoeff6`'s support clause are the ones of `IsBetaCoeff`; split on
them and on `SameClass8 z z0` exactly as in the existing proof. -/
theorem farPiece_classRestrict_isBetaCoeff6 {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt}
    {β : GaussianInt → ℂ} (h : Work.FITop4.IsBetaCoeff Pa φ β)
    (hfar : Work.FIRed6Axis.FarPiece Pa φ) :
    Work.FITop4.IsBetaCoeff6 Pa φ z0 (Work.FIRed6Axis.clsRestrict z0 β) := by
  obtain ⟨q, p, hc1, hc2, hq0, hq1, hqsupp, hqd, hp0, hp1, hpsupp, hpd, hβ⟩ := h
  refine ⟨q, p, hc1, hc2, hq0, hq1, hqsupp, hqd, hp0, hp1, hpsupp, hpd, ?_⟩
  intro z
  unfold clsRestrict
  by_cases h5 : Work.FITop4.InPolarBox Pa φ z ∧ Work.FITop4.NoSmallPrimes Pa z ∧
      (((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ) ∧ Work.FITop4.SameClass8 z z0
      ∧ Work.FITop4.IsAxisFree Pa z
  · have h3 : Work.FITop4.InPolarBox Pa φ z ∧ Work.FITop4.NoSmallPrimes Pa z ∧
        (((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ) := ⟨h5.1, h5.2.1, h5.2.2.1⟩
    have hD : Work.FITop4.SameClass8 z z0 := h5.2.2.2.1
    simp only [hβ z, if_pos hD, if_pos h3, if_pos h5]
  · by_cases hD : Work.FITop4.SameClass8 z z0
    · by_cases h3 : Work.FITop4.InPolarBox Pa φ z ∧ Work.FITop4.NoSmallPrimes Pa z ∧
          (((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ)
      · exact absurd ⟨h3.1, h3.2.1, h3.2.2, hD,
          Work.FIRed6Axis.FarPiece_isAxisFree hfar h3.1⟩ h5
      · simp only [hβ z, if_pos hD, if_neg h3, if_neg h5]
    · simp only [hβ z, if_neg hD, if_neg h5]

end Work.FIRed6Axis
