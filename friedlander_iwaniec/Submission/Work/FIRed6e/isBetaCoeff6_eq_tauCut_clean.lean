import Mathlib
import Submission.Work.FITop4.Areas6e

namespace Work.FIRed6e

attribute [local instance] Classical.propDecidable

/-- Node C1 of the amended composition (lead design `Submission/Work/FIArea6/AREA6_CONTRACT_LEAD.md`
§4.1): on an axis-free polar box, a round-6 coefficient `β` (FI (5.7)+(5.8)+(5.9), i.e.
`Work.FITop4.IsBetaCoeff6`) is the (5.9)-truncation `Work.FITop4.tauCut` of a coefficient of the
clean class `Work.FITop4.IsCleanCoeff6` (FI p. 985: "(5.9) no longer exists"), with the *same*
mollifiers `q, p`.  Proof: take `β'` to be the clean formula with the `q, p` extracted from `hβ`;
`funext` and split on `τ(|z|²) ≤ Pa.τ`.  Where `τ(|z|²) ≤ Pa.τ` the two if-conditions agree because
`hfar` turns `InPolarBox` into the `IsAxisFree` conjunct; where not, both sides vanish. -/
theorem isBetaCoeff6_eq_tauCut_clean {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt}
    {β : GaussianInt → ℂ} (hβ : Work.FITop4.IsBetaCoeff6 Pa φ z0 β)
    (hfar : ∀ z, Work.FITop4.InPolarBox Pa φ z → Work.FITop4.IsAxisFree Pa z) :
    ∃ β' : GaussianInt → ℂ, Work.FITop4.IsCleanCoeff6 Pa φ z0 β' ∧ β = Work.FITop4.tauCut Pa β' := by
  obtain ⟨q, p, hqcd, hpcd, hq0, hq1, hqsup, hqder, hp0, hp1, hpsup, hpder, hβf⟩ := hβ
  refine ⟨fun z => if Work.FITop4.InPolarBox Pa φ z ∧ Work.FITop4.NoSmallPrimes Pa z ∧
        Work.FITop4.SameClass8 z z0
      then ((q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z) : ℝ) : ℂ)
              * (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ)
              * (Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z) : ℂ)
      else 0, ?_, ?_⟩
  · refine ⟨q, p, hqcd, hpcd, hq0, hq1, hqsup, hqder, hp0, hp1, hpsup, hpder, ?_⟩
    intro z
    rfl
  · funext z
    rw [hβf z, Work.FITop4.tauCut]
    by_cases hc : Work.FITop4.InPolarBox Pa φ z ∧ Work.FITop4.NoSmallPrimes Pa z ∧
        Work.FITop4.SameClass8 z z0
    · by_cases hT : (((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ)
      · rw [if_pos ⟨hc.1, hc.2.1, hT, hc.2.2, hfar z hc.1⟩, if_pos hT, if_pos hc]
      · rw [if_neg (fun h => hT h.2.2.1), if_neg hT]
    · rw [if_neg (fun h => hc ⟨h.1, h.2.1, h.2.2.2.1⟩), if_neg hc]
      by_cases hT : (((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ)
      · rw [if_pos hT]
      · rw [if_neg hT]

end Work.FIRed6e
