import Mathlib
import Submission.Work.RPB.B5.regDefs

open scoped ContDiff

namespace Work.RPB.B5

/-- Joint smoothness of the regularised phase integrand `Work.RPB.B5.regF`, assuming the
regularised denominator is everywhere non-zero.
(Helper for `Work.RPB.B5.regularizedPhaseIntegrand`; import `Submission.Work.RPB.B5.regDefs`.) -/
theorem regF_contDiff (hc : ℝ → ℝ → ℝ → ℂ) (ρa : ℝ)
    (hc_sm : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) (fun z : ℝ × (ℝ × ℝ) => hc z.1 z.2.1 z.2.2))
    (hden : ∀ τ t s, Work.RPB.B5.regDen hc ρa τ t s ≠ 0) :
    ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞))
      (fun z : ℝ × (ℝ × ℝ) => Work.RPB.B5.regF hc ρa z.1 z.2.1 z.2.2) := by
  set T : WithTop ℕ∞ := ((⊤ : ℕ∞) : WithTop ℕ∞) with hT
  have hF : ContDiff ℝ T (fun z : ℝ × (ℝ × ℝ) => hc z.1 z.2.1 z.2.2) := hc_sm
  have hT1 : T + 1 ≤ T := by rw [hT]; simp
  have hfd : ContDiff ℝ T (fderiv ℝ (fun z : ℝ × (ℝ × ℝ) => hc z.1 z.2.1 z.2.2)) :=
    hF.fderiv_right hT1
  have hpds : ContDiff ℝ T (fun z : ℝ × (ℝ × ℝ) => pds hc z.1 z.2.1 z.2.2) := by
    unfold pds
    exact hfd.clm_apply contDiff_const
  have hre : ContDiff ℝ T (fun z : ℝ × (ℝ × ℝ) => (hc z.1 z.2.1 z.2.2).re) :=
    Complex.reCLM.contDiff.comp hF
  have him : ContDiff ℝ T (fun z : ℝ × (ℝ × ℝ) => (hc z.1 z.2.1 z.2.2).im) :=
    Complex.imCLM.contDiff.comp hF
  have hpdsre : ContDiff ℝ T (fun z : ℝ × (ℝ × ℝ) => (pds hc z.1 z.2.1 z.2.2).re) :=
    Complex.reCLM.contDiff.comp hpds
  have hpdsim : ContDiff ℝ T (fun z : ℝ × (ℝ × ℝ) => (pds hc z.1 z.2.1 z.2.2).im) :=
    Complex.imCLM.contDiff.comp hpds
  have hnum : ContDiff ℝ T (fun z : ℝ × (ℝ × ℝ) => regNum hc z.1 z.2.1 z.2.2) := by
    unfold regNum
    exact (hpdsim.mul hre).sub (hpdsre.mul him)
  have hden' : ContDiff ℝ T (fun z : ℝ × (ℝ × ℝ) => regDen hc ρa z.1 z.2.1 z.2.2) := by
    unfold regDen phaseBumpK phaseBumpT phaseBumpS
    refine (((hre.mul hre).add (him.mul him)).add ?_)
    fun_prop
  unfold regF
  exact hnum.div hden' (by rintro ⟨τ,t,s⟩; exact hden τ t s)

end Work.RPB.B5
