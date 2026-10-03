/-
# The band realization of a circle function (Area A7Rep, envelope band extension)

Shared definitions for the proof of `Work.KMTAreas.A7Rep.envelopeBandExtendProof`.

The theorem needs, for each arithmetic frequency `α`, a **continuous function on the line** whose
values at the integers reproduce the sequence
`x ↦ ∑'_j cw m j · winModR (-α) u (x - j)` and whose (inverse) Fourier transform is supported in
the band `[-2δ, 2δ]`.  The construction realized here is

`W α = (𝓕⁻ (envRealize δ F α)) ∘ (fun t => -t)`,   `F α = periodize m · 𝓕(winModR (-α) u)`,

where `envRealize δ F` is `F` on the interval `envBandSet δ` (zero outside), with

`envBandSet δ = [-2δ, 2δ]` if `4δ < 1` (the band sits inside a fundamental domain of the circle),
otherwise the fundamental domain `(-1/2, 1/2]`.

In both cases `envBandSet δ ⊆ [-2δ, 2δ]` (which is the band condition of `HasRealFreqSupport`) and
`envBandSet δ ⊆ (-1/2, 1/2]` (which is what makes the realization integrable).
-/
import Mathlib
import Submission.Work.KMTAreas.A7Rep.RephaseDefs

namespace Work.KMTAreas.A7Rep

open MeasureTheory
open scoped BigOperators

noncomputable section

/-- The interval on which a circle function is realized on the line: the band `[-2δ, 2δ]` when it
fits strictly inside a fundamental domain (`4δ < 1`), and the fundamental domain `(-1/2, 1/2]`
otherwise. -/
def envBandSet (δ : ℝ) : Set ℝ :=
  if 4 * δ < 1 then Set.Icc (-(2 * δ)) (2 * δ) else Set.Ioc (-(1 / 2)) (1 / 2)

/-- The realization on the line of a circle function `F` in the band `envBandSet δ`: it equals
`F (ξ mod 1)` there and `0` outside. -/
noncomputable def envRealize (δ : ℝ) (F : Work.Analysis.IonescuWainger.Circle → ℂ) : ℝ → ℂ := by
  classical
  exact Set.indicator (envBandSet δ)
    fun ξ : ℝ => F ((ξ : ℝ) : Work.Analysis.IonescuWainger.Circle)

theorem envBandSet_of_lt {δ : ℝ} (h : 4 * δ < 1) : envBandSet δ = Set.Icc (-(2 * δ)) (2 * δ) := by
  rw [envBandSet, if_pos h]

theorem envBandSet_of_not_lt {δ : ℝ} (h : ¬ 4 * δ < 1) :
    envBandSet δ = Set.Ioc (-(1 / 2)) (1 / 2) := by
  rw [envBandSet, if_neg h]

theorem envBandSet_subset_Ioc {δ : ℝ} (hδ : 0 < δ) :
    envBandSet δ ⊆ Set.Ioc (-(1 / 2)) (1 / 2) := by
  by_cases h : 4 * δ < 1
  · rw [envBandSet_of_lt h]
    intro x hx
    rw [Set.mem_Icc] at hx
    rw [Set.mem_Ioc]
    constructor <;> linarith [hx.1, hx.2, hδ, h]
  · rw [envBandSet_of_not_lt h]

theorem envBandSet_subset_Icc {δ : ℝ} (hδ : 0 < δ) :
    envBandSet δ ⊆ Set.Icc (-(2 * δ)) (2 * δ) := by
  by_cases h : 4 * δ < 1
  · rw [envBandSet_of_lt h]
  · rw [envBandSet_of_not_lt h]
    intro x hx
    rw [Set.mem_Ioc] at hx
    rw [Set.mem_Icc]
    constructor <;> linarith [hx.1, hx.2, hδ, not_lt.mp h]

theorem envBandSet_measurableSet (δ : ℝ) : MeasurableSet (envBandSet δ) := by
  by_cases h : 4 * δ < 1
  · rw [envBandSet_of_lt h]; exact measurableSet_Icc
  · rw [envBandSet_of_not_lt h]; exact measurableSet_Ioc

theorem envRealize_apply {δ : ℝ} {F : Work.Analysis.IonescuWainger.Circle → ℂ} (ξ : ℝ) :
    envRealize δ F ξ = (envBandSet δ).indicator
      (fun ξ : ℝ => F ((ξ : ℝ) : Work.Analysis.IonescuWainger.Circle)) ξ := rfl

theorem envRealize_eq_zero_of_notMem {δ : ℝ} {F : Work.Analysis.IonescuWainger.Circle → ℂ}
    {ξ : ℝ} (h : ξ ∉ envBandSet δ) : envRealize δ F ξ = 0 := by
  rw [envRealize, Set.indicator_of_notMem h]

theorem envRealize_eq_zero_of_notMem_Icc {δ : ℝ} (hδ : 0 < δ)
    {F : Work.Analysis.IonescuWainger.Circle → ℂ} {ξ : ℝ}
    (h : ξ ∉ Set.Icc (-(2 * δ)) (2 * δ)) : envRealize δ F ξ = 0 :=
  envRealize_eq_zero_of_notMem fun hmem => h (envBandSet_subset_Icc hδ hmem)

end

end Work.KMTAreas.A7Rep
