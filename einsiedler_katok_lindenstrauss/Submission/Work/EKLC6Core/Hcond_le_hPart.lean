import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLC6Core.Hcond_mono
import Submission.Work.EKLC6Core.Sigma
import Submission.Work.EKLC6Core.PastJoin
import Submission.Work.EKLC6Core.HcondFam_partSigmaFam

/-!
# `EKLC6Core.Hcond_le_hPart`

The conditional entropy of a finite partition `P` given the *past* σ-algebra
`⋁_{k≥1} T^{-k}(partSigma P)` is at most the Kolmogorov–Sinai entropy `h_μ(T,P)`
(Walters, *Ergodic Theory*, Theorem 4.14 / the easy half of the conditional-entropy formula).

The proof is the standard chain-rule/telescoping argument:

* the punctured join `⋁_{k=1}^{N}T^{-k}P = T^{-1}(⋁_{k<N}T^{-k}P)` has σ-algebra
  `shiftSigma T P N ≤ pastSigmaShift T P`, so `Hcond μ P (pastSigmaShift T P) ≤ Hcond μ P (shiftSigma T P N)`;
* the entropy chain rule (`HcondFam_partSigmaFam`) together with `Hfam_shJoin_eq` and
  `Hfam_parts_inter_shJoin` turns this into the difference
  `d_N = Hfam μ (⋁_{k≤N}T^{-k}P) - Hfam μ (⋁_{k<N}T^{-k}P)`;
* summing `d_N` over `N ≤ M` telescopes to `Hfam μ (⋁_{k≤M}T^{-k}P)`, whence
  `Hcond μ P (pastSigmaShift T P) ≤ Hfam μ (⋁_{k≤M}T^{-k}P)/(M+1)` for every `M`;
* the infimum over `M` is `hPart μ T P`, by definition.

Note that the statement needs no measurability hypothesis on `T`: `MeasurePreserving` supplies it.
-/

open MeasureTheory Filter Topology
open scoped ENNReal BigOperators

noncomputable section

set_option linter.unusedVariables false

namespace Work.EKLC6Core

open Work.EKLContract
open Work.EKLComp.Core

variable {X : Type*} [mX : MeasurableSpace X]

open Work.EKLContract

/-- The entropy chain rule applied to the punctured join: the conditional entropy of `P` given
`⋁_{k=1}^{N}T^{-k}(partSigma P)` is the difference of the entropies of the `(N+1)`-fold and the
`N`-fold join of `P` along `T`. -/
theorem Hcond_shiftSigma (μ : Measure X) [IsProbabilityMeasure μ] {T : X → X}
    (hmp : MeasurePreserving T μ μ) (P : FinPart X) (N : ℕ) :
    @Hcond X mX μ P (shiftSigma T P N)
      = Hfam μ (joinSets T P (N+1)) - Hfam μ (joinSets T P N) := by
  have hT : Measurable T := hmp.measurable
  show HcondFam X μ P.parts (partSigmaFam (shJoin T P N)) = _
  rw [HcondFam_partSigmaFam μ P.parts (shJoin T P N)
    ⟨P.measurable, P.disjoint, P.cover⟩ (shJoin_isMPart hT P N)]
  rw [Hfam_parts_inter_shJoin μ T P N, Hfam_shJoin_eq μ hmp P N]

/-- **The conditional entropy over the past is at most `hPart`** (Walters Theorem 4.14, `≤`). -/
theorem Hcond_le_hPart {X : Type*} [mX : MeasurableSpace X] (μ : MeasureTheory.Measure X)
    [MeasureTheory.IsProbabilityMeasure μ] (T : X → X) (hmp : MeasureTheory.MeasurePreserving T μ μ)
    (P : @Work.EKLContract.FinPart X mX) :
    @Work.EKLContract.Hcond X mX μ P (⨆ k : ℕ, MeasurableSpace.comap (T^[k+1])
        (@Work.EKLContract.partSigma X mX P)) ≤ @Work.EKLContract.hPart X mX μ T P := by
  have hmp' : MeasurePreserving T μ μ := hmp
  change @Hcond X mX μ P (pastSigmaShift T P) ≤ @hPart X mX μ T P
  -- the difference sequence
  have hstep : ∀ N : ℕ, @Hcond X mX μ P (pastSigmaShift T P)
      ≤ Hfam μ (joinSets T P (N+1)) - Hfam μ (joinSets T P N) := by
    intro N
    have hle := Hcond_mono (X := X) μ P (shiftSigma T P N) (pastSigmaShift T P)
      (shiftSigma_le_pastSigma hmp'.measurable P N)
    rwa [Hcond_shiftSigma μ hmp' P N] at hle
  -- summing telescopes
  have hkey : ∀ M : ℕ, ((M : ℝ) + 1) * @Hcond X mX μ P (pastSigmaShift T P)
      ≤ Hfam μ (joinSets T P (M+1)) := by
    intro M
    have h1 : ∑ N ∈ Finset.range (M+1), @Hcond X mX μ P (pastSigmaShift T P)
        ≤ ∑ N ∈ Finset.range (M+1),
            (Hfam μ (joinSets T P (N+1)) - Hfam μ (joinSets T P N)) :=
      Finset.sum_le_sum fun N _ => hstep N
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h1
    rw [Finset.sum_range_sub (fun N => Hfam μ (joinSets T P N)) (M+1),
      Hfam_joinSets_zero μ T P, sub_zero] at h1
    simpa using h1
  -- divide by `M+1` and take the infimum
  unfold Work.EKLContract.hPart
  refine le_ciInf fun M => ?_
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < (M : ℝ) + 1)]
  simpa [mul_comm] using hkey M

end Work.EKLC6Core
