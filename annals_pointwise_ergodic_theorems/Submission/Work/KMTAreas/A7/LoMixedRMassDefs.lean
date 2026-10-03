/-
# The `l₂ = 0` case of the single-scale `ℓ¹(ℤ²)` mass bound of §6 (statement)

This module *only states* the `l₂ = 0` case of the analytic core of the §6 model approximation
(Proposition `mod-approx` of Krause--Mirek--Tao): the `ℓ¹(ℤ²)`-mass of the kernel
`hiKconc ρ P a l₁ 0 k₁ k₂ n − hiKmod ρ P a l₁ 0 k₁ k₂ n` of the difference of the concrete
halved-average column and the §6 model column is, on the guard scales, at most
`C(Λ)·modelWeight A ρ l₁ 0 k₁ k₂·⌊a n⌋⁻¹`.

It is the exact analogue of `Work.KMTAreas.A7.HiMassBound`
(`Submission/Work/KMTAreas/A7/HiMassBoundDefs.lean`, the *range* `1 ≤ l₁ ∧ 1 ≤ l₂`) at `l₂ = 0`,
where the model kernel simply **vanishes**:  `iwArithFreqsNew ρ 0 = ∅`
(`Work.KMTAreas.A7.iwArithFreqsNew_zero`), hence `arithKernelExact ρ P q l₁ 0 = 0`
(an empty inner sum) and `hiKmod ρ P a l₁ 0 k₁ k₂ n = 0`.  So the estimate is a bound for the
concrete column itself, and its content is the vanishing of the twist symbol on the fibres:
`m_Ẑ(γ₁,0) = E_{n ∈ ℤ/q} e(nγ₁) = 0` for `γ₁ ∈ diffFreqs ρ l₁` (which contains no `0` since
`l₁ ≥ 1`), so that the §6 symbol difference reduces to
`M₀(γ₁,0) = weylAvg P N γ₁ 0` of `Work.A7.M0SharpBound` /
`Work.A7.ModelApproxCore_M0_deriv_bound`, converted into a kernel-mass bound by
`Work.KMTPlan.A6.SymToolbox_tsum_coeff2_le` with `r₁ = N⁻¹`, `r₂ = N^{-d}`.

**Status.**  The statement is a `Prop`; the theorem `LoMixedRMass` proving it is requested at
`Submission/Work/KMTAreas/A7/LoMixedRMass.lean`.  Its *consumer*
`Work.KMTAreas.A7.LoMixedRSingleScale` uses it through
`Work.KMTAreas.A7.loMixedRSingleScale_of_mass`, and the lacunary assembly
`loMixedRight_of_singleScale` (`Submission/Work/KMTAreas/A7/LoMixedRight.lean`) turns the latter
into the target `LoMixedRightStatement`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.ModelApproxHiDefs
import Submission.Work.KMTAreas.A7.ModelApproxAux
import Submission.Work.KMTAreas.A7.LoDefs

set_option autoImplicit false

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.EndVar Work.KMTContract

/-- **The `l₂ = 0` case of the single-scale `ℓ¹(ℤ²)` mass bound of §6**: the kernel of the
difference of the concrete column and the (vanishing) §6 model is summable on the guard scales,
with mass at most `C(Λ)·modelWeight A ρ l₁ 0 k₁ k₂·⌊a n⌋⁻¹`. -/
def LoMixedRMassStatement (P : ℤ[X]) : Prop :=
  ∃ A : ℝ, 0 ≤ A ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ C : ℝ≥0 → ℝ≥0,
    (∀ (C₀ : ℕ) (a : ℕ → ℝ≥0) (l₁ k₁ k₂ : ℕ) (n : ℕ),
        loGuard ρ C₀ a l₁ 0 k₁ k₂ n →
        Summable fun p : ℤ × ℤ => ‖hiKconc ρ P a l₁ 0 k₁ k₂ n p.1 p.2
            - hiKmod ρ P a l₁ 0 k₁ k₂ n p.1 p.2‖) ∧
    (∀ (C₀ : ℕ) (a : ℕ → ℝ≥0) (Λ : ℝ≥0) (l₁ k₁ k₂ : ℕ),
        1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
        1 ≤ l₁ →
        ∀ n : ℕ, loGuard ρ C₀ a l₁ 0 k₁ k₂ n →
          (∑' p : ℤ × ℤ, ‖hiKconc ρ P a l₁ 0 k₁ k₂ n p.1 p.2
              - hiKmod ρ P a l₁ 0 k₁ k₂ n p.1 p.2‖)
            ≤ (C Λ : ℝ) * modelWeight A ρ l₁ 0 k₁ k₂ * ((Nat.floor (a n) : ℕ) : ℝ)⁻¹)

end

end Work.KMTAreas.A7
