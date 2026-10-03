/-
# The level-`0` clipped `g`-side family, and its variational estimate predicate

This module fixes the interface used by the proof of the `g`-side bounded-height packet estimate
`Work.KMTPlan.A6.LowModApproxBoundedH.sliceGBound`:

* `lvl0Fam ρ P C₀ a l₁ l₂ k₁ k₂ t F` — the **level-`0` (arithmetic-free) clipped family**
  `n ↦ 1_{core ρ C₀ l₁ l₂ k₁ k₂ a n} · Tle ρ 0 (φ̃_{N_n,t}) F`, `N_n = ⌊a n⌋`,
  `φ̃_{N,t} = varphitildeNt P P.natDegree N k₂ t`;
* `Lvl0 P r C₀ B ρ` — the **level-`0` clipped variational estimate** at the parameter `ρ`: the
  `ℓ²(ℤ)` norm of the `r`-variation of `lvl0Fam` is bounded by `C Λ · ‖F‖₂`, uniformly in the
  `Λ`-lacunary scale family, in the multi-index with `lcL l₁ l₂ k₁ k₂ ≤ B`, in `t ∈ [1/2,1]` and
  in the input `F`.  This is the `(p₁,p₂) = (2,2)`-instance of the paper's linear estimate
  (lin-2) at arithmetic height `0`, with the loss absorbed into a constant depending on `Λ`.

## Why level `0`

`Tle ρ 0 φ = iwConv (iwArithFreqs ρ 0) (periodize φ)` and `iwArithFreqs ρ 0 = {0}` for *every*
`ρ > 0` (since `iwP ρ 0 = Icc 1 1`), so the level-`0` operator is *independent of* `ρ`.  Every
`ρ`-dependence of the level-`l` operator `Tle ρ l` (for `l ≥ 1`) sits in the arithmetic frequency
set `iwArithFreqs ρ l`, which does depend on `ρ`; the lift `Tle_eq_sum_modulation` of
`LowModApproxBoundedH/mdlPartVar.lean` — a *finite* sum over `α ∈ iwArithFreqs ρ l` of modulated
level-`0` operators — is what makes the whole `ρ`-dependence reducible to the level-`0` case.

The level-`0` operator is *not* an arbitrary multiplier, however: the inputs `F` produced by the
lift are the *modulated* projections `Π_{≤l,≤k}` of the original input, and the arithmetic gain
`2^{-c l}` of the paper is provided by those projections (via the exact-height shells), not by the
lift itself.  The level-`0` estimate `Lvl0` is therefore an *input* of the reduction, and its
proof is independent of the lift.

The companion file `LowModApproxBoundedH/clipTransfer.lean` contains the general clip-transfer
bookkeeping lemma `eLpNorm_variationalNorm_clip_transfer` used to pass between the clips
`core ρ …` and `core ρ' …` for two different parameters `ρ`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.LargeInterface
import Submission.Work.KMTPlan.A6.LowDefs

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace Work.KMTPlan.A6.LowModApproxBoundedH

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.KMTAreas.A7

/-- **The level-`0` (arithmetic-free) clipped `g`-side family.**  For the `Λ`-lacunary family `a`
(`N_n = ⌊a n⌋`), the multi-index `(l₁,l₂,k₁,k₂)`, the parameter `t ∈ [1/2,1]` and the input `F`,
it is the family

  `n ↦ 1_{core ρ C₀ l₁ l₂ k₁ k₂ a n} · Tle ρ 0 (φ̃_{N_n,t}) F`. -/
def lvl0Fam (ρ : ℝ) (P : Polynomial ℤ) (C₀ : ℕ) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ)
    (F : ℤ → ℂ) : ℕ → ℤ → ℂ :=
  fun n x =>
    if Work.KMTAreas.A7.core ρ C₀ l₁ l₂ k₁ k₂ a n then
      Work.KMTAreas.A7.Tle ρ 0
        (Work.KMTAreas.A7.varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) F x
    else 0

/-- **The level-`0` clipped variational estimate at the parameter `ρ`.**  There is `C : ℝ≥0 → ℝ≥0`
such that for every `Λ`-lacunary family `a` with `a n ≥ 1`, every multi-index with
`lcL l₁ l₂ k₁ k₂ ≤ B`, every `t ∈ [1/2,1]` and every input `F`

  `‖ V^r (lvl0Fam ρ P C₀ a l₁ l₂ k₁ k₂ t F) ‖_{ℓ²(ℤ)} ≤ C Λ · ‖F‖_{ℓ²(ℤ)}`.

This is the paper's (lin-2) at arithmetic height `0` and at the exponents `(2,2)`, with the loss
absorbed into the constant (which is allowed because `lcL l₁ l₂ k₁ k₂ ≤ B` bounds every scale
parameter of the multi-index). -/
def Lvl0 (P : Polynomial ℤ) (r : NNReal) (C₀ : ℕ) (B : ℕ) (ρ : ℝ) : Prop :=
  ∃ C : NNReal → NNReal,
    ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (F : ℤ → ℂ),
      1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
      Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂ ≤ B → t ∈ Set.Icc (1 / 2 : ℝ) 1 →
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => lvl0Fam ρ P C₀ a l₁ l₂ k₁ k₂ t F n x)) 2 MeasureTheory.Measure.count
        ≤ (C Λ : ENNReal) * MeasureTheory.eLpNorm F 2 MeasureTheory.Measure.count

end

end Work.KMTPlan.A6.LowModApproxBoundedH
