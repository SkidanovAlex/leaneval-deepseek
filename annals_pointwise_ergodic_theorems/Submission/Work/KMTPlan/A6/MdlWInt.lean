/-
# Integrability of the integration-by-parts weights `mdlW1`, `mdlW2`

The weights of the integration-by-parts identity (ii) of Krause--Mirek--Tao §6 are

  `mdlW1 P N t = N^{d-1}/P'(N t)`,   `mdlW2 P N t = N^d P''(N t)/P'(N t)^2`

(`Submission/Work/KMTPlan/A6/MdlDefs.lean`).  Both are *continuous* on `[1/2,1]` as soon as the
denominator `P'(N t)` does not vanish there (hypothesis `hP`: for a non-constant `P` and `N ≥ 1`
this holds automatically, `P'` having finitely many roots).  Since `[1/2,1]` has finite measure,
`ContinuousOn ⟹ IntegrableOn`, which is the content of this file: the two weights are integrable
on `(1/2,1]` against Lebesgue measure.

These are exactly the integrability side conditions needed to make sense of the boundary and
middle terms of the identity (ii) in
`Submission/Work/KMTPlan/A6/MdlBumpIntegIdent.lean`.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.MdlDefs

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial
open scoped ENNReal NNReal BigOperators Interval

/-- **Continuity of the weight `mdlW1 P N = N^{d-1}/P'(N ·)`** on `[1/2,1]`, under the
non-vanishing hypothesis on `P'(N ·)`. -/
theorem continuousOn_mdlW1 (P : Polynomial ℤ) (N : ℕ)
    (hP : ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, PderivR P ((N : ℝ) * t) ≠ 0) :
    ContinuousOn (mdlW1 P N) (Set.uIcc (1 / 2 : ℝ) 1) := by
  have hle : (1 / 2 : ℝ) ≤ 1 := by norm_num
  have hne : ∀ t ∈ Set.uIcc (1 / 2 : ℝ) 1, PderivR P ((N : ℝ) * t) ≠ 0 := by
    intro t ht
    rw [Set.uIcc_of_le hle] at ht
    exact hP t ht
  have hreal : ContinuousOn
      (fun t : ℝ => (N : ℝ) ^ (P.natDegree - 1) / PderivR P ((N : ℝ) * t))
      (Set.uIcc (1 / 2 : ℝ) 1) :=
    ContinuousOn.div continuousOn_const ((continuous_PderivR_comp P (N : ℝ)).continuousOn) hne
  change ContinuousOn
    (fun t : ℝ => (((N : ℝ) ^ (P.natDegree - 1) / PderivR P ((N : ℝ) * t) : ℝ) : ℂ))
    (Set.uIcc (1 / 2 : ℝ) 1)
  exact Complex.continuous_ofReal.comp_continuousOn hreal

/-- **Continuity of the weight `mdlW2 P N = N^d P''(N ·)/P'(N ·)^2`** on `[1/2,1]`, under the
non-vanishing hypothesis on `P'(N ·)`. -/
theorem continuousOn_mdlW2 (P : Polynomial ℤ) (N : ℕ)
    (hP : ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, PderivR P ((N : ℝ) * t) ≠ 0) :
    ContinuousOn (mdlW2 P N) (Set.uIcc (1 / 2 : ℝ) 1) := by
  have hle : (1 / 2 : ℝ) ≤ 1 := by norm_num
  have hne : ∀ t ∈ Set.uIcc (1 / 2 : ℝ) 1, PderivR P ((N : ℝ) * t) ≠ 0 := by
    intro t ht
    rw [Set.uIcc_of_le hle] at ht
    exact hP t ht
  have hnum : ContinuousOn
      (fun t : ℝ => (N : ℝ) ^ P.natDegree * Pderiv2R P ((N : ℝ) * t))
      (Set.uIcc (1 / 2 : ℝ) 1) :=
    continuousOn_const.mul ((continuous_PderivR_comp P.derivative (N : ℝ)).continuousOn)
  have hden : ContinuousOn (fun t : ℝ => (PderivR P ((N : ℝ) * t)) ^ 2)
      (Set.uIcc (1 / 2 : ℝ) 1) :=
    ((continuous_PderivR_comp P (N : ℝ)).continuousOn).pow 2
  have hdiv : ContinuousOn
      (fun t : ℝ => ((N : ℝ) ^ P.natDegree * Pderiv2R P ((N : ℝ) * t))
        / (PderivR P ((N : ℝ) * t)) ^ 2)
      (Set.uIcc (1 / 2 : ℝ) 1) :=
    ContinuousOn.div hnum hden (fun t ht => pow_ne_zero 2 (hne t ht))
  change ContinuousOn
    (fun t : ℝ => ((((N : ℝ) ^ P.natDegree * Pderiv2R P ((N : ℝ) * t))
      / (PderivR P ((N : ℝ) * t)) ^ 2 : ℝ) : ℂ))
    (Set.uIcc (1 / 2 : ℝ) 1)
  exact Complex.continuous_ofReal.comp_continuousOn hdiv

theorem MdlWInt (P : Polynomial ℤ) (N : ℕ)
    (hP : ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, Work.KMTPlan.A6.PderivR P ((N : ℝ) * t) ≠ 0) :
    MeasureTheory.Integrable (Work.KMTPlan.A6.mdlW1 P N) (MeasureTheory.volume.restrict (Set.Ioc (1 / 2 : ℝ) 1)) ∧
    MeasureTheory.Integrable (Work.KMTPlan.A6.mdlW2 P N) (MeasureTheory.volume.restrict (Set.Ioc (1 / 2 : ℝ) 1)) := by
  have hle : (1 / 2 : ℝ) ≤ 1 := by norm_num
  have key : ∀ w : ℝ → ℂ, ContinuousOn w (Set.uIcc (1 / 2 : ℝ) 1) →
      MeasureTheory.Integrable w (MeasureTheory.volume.restrict (Set.Ioc (1 / 2 : ℝ) 1)) := by
    intro w hw
    change MeasureTheory.IntegrableOn w (Set.Ioc (1 / 2 : ℝ) 1) MeasureTheory.volume
    rw [← Set.uIoc_of_le hle]
    exact intervalIntegrable_iff.mp (hw.intervalIntegrable)
  exact ⟨key _ (continuousOn_mdlW1 P N hP), key _ (continuousOn_mdlW2 P N hP)⟩

end

end Work.KMTPlan.A6
