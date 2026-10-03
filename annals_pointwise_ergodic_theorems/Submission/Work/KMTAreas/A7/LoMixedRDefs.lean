/-
# The single-scale statement of the mixed right case (`l₁ ≥ 1`, `l₂ = 0`)

This module fixes the *single-scale* estimate that the assembly `loMixedRight_of_singleScale`
(`Submission/Work/KMTAreas/A7/LoMixedRight.lean`) turns into the target
`Work.KMTAreas.A7.LoMixedRightStatement P p₁ p₂`.

## Why this is the right intermediate statement

`Work.KMTAreas.A7.LoCase` bounds the *variational* norm of the family
`n ↦ mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x − modelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x`.
For the mixed right case `l₁ ≥ 1`, `l₂ = 0` the exact-height model tuple **vanishes**
(`LoDefs.modelTuple_eq_zero_of_lo`, because `iwArithFreqsNew ρ 0 = ∅`), so the target is an
estimate for the concrete column `mainPartTuple` itself, and the only *analytic* input needed is
the single-scale (paper §6, Proposition `mod-approx`) bound

  `‖ mainPartTuple ρ P C₀ a f g l₁ 0 k₁ k₂ n ‖_{ℓ^p} ≤ C(Λ) · modelWeight A ρ l₁ 0 k₁ k₂ · ⌊a n⌋⁻¹
      · ‖f‖_{ℓ^{p₁}} ‖g‖_{ℓ^{p₂}}`,   `p = (p₁⁻¹+p₂⁻¹)⁻¹`.

The *passage* from this single-scale bound to the variational bound is the lacunary bookkeeping of
§5 (`VarNormTsumLp`, `invFloorSum_le`, `WeightArith`), which is done in the assembly; the
*single-scale* bound is the analytic core, and is the content of the statement below.

## The gain is `⌊a n⌋⁻¹` and it is genuine

In the mixed right case the concrete column is `Ã_N(Π_{l₁,≤s₁}f, Π_{≤0,≤s₂}g)`: the arithmetic
frequencies of the two factors are the exact-height set `(ℚ/ℤ)_{l₁}` (which does not contain `0`
for `l₁ ≥ 1`) and `(ℚ/ℤ)_{≤0} = {0}`.  The "twist" symbol of the column is
`m_Ẑ(α₁,α₂) = E_{n∈ℤ/q} e(α₁n + α₂P(n))`, and on the only fibres present here (`α₂ = 0`) it is
`E_{n∈ℤ/q} e(α₁n)`, which vanishes for every non-zero `α₁` of order dividing `q`.  Hence the
*model* term of §6 (`m_Ẑ · m̃`) vanishes identically and the whole column is at the level of the
symbol difference `M₀`:

  `M₀(α₁,0) = weylAvg P N α₁ 0 ξ₁ ξ₂ − m_Ẑ(α₁,0) m̃_{N,ℝ}(ξ₁,ξ₂) = weylAvg P N α₁ 0 ξ₁ ξ₂`,

whose sharp bound is `Work.A7.M0SharpBound` (`O(q²(1 + S²/N)/N)`) with the derivative bound
`Work.A7.ModelApproxCore_M0_deriv_bound`.  This is exactly the mechanism by which the right-mixed
case is *easier* than the left-mixed case `(0,l₂)`, `l₂ ≥ 1` (where the model is the non-zero
Weyl average `E_n e(α₂P(n))` and the paper's §8 tensor analysis is needed).

## What the prover has to do

* unfold `mainPartTuple` and use `mainPartTuple_apply` / `Work.Analysis.EndVar.varpPiece_eq_bilinOp_hiKconc`
  to write the concrete column as the bilinear convolution `bilinOp (hiKconc …) f g`
  (`hiKconc = kernComp (khalf ⌊a n⌋ P) (pieceKer …) (pieceKer …)`,
  `Submission/Work/KMTAreas/A7/ModelApproxHiDefs.lean`);
* bound the `ℓ¹(ℤ²)`-mass of `hiKconc` at `(l₁,0)`, `l₁ ≥ 1`, by the paper's `M₀` estimates
  converted through `crude-mult`(ii) (`Submission/Work/KMTPlan/A6/SymToolbox_tsum_coeff2_le`,
  or the equivalent `hiCrudeMult`); the fibre expansion of the column kernel is
  `Submission/Work/KMTPlan/A6/kconcA6_fibre`;
* convert the mass bound into the `ℓ^p` bound by `Work.KMTAreas.A7.BilinOpLp`, handling the
  degenerate cases `eLpNorm f p₁ = ⊤` / `eLpNorm g p₂ = ⊤` separately (`AreaA1` is available as a
  hypothesis even though the argument should not need it);
* absorb the constants: `modelWeight A ρ l₁ l₂ k₁ k₂ = (1 + lmaxR) ^ A · 2 ^ (A · 2 ^ (ρ · lmaxR))`
  with `A` chosen after `ρ` absorbs `perQ`-powers `2^{O(2^{ρL})}`, the factor `2^{2(k₁+d k₂)+3}` of
  the two §5 bumps, and the `(1 + S²/N)` of the `M₀` bound (the last because `N ≥ 1`), leaving the
  gain `⌊a n⌋⁻¹`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.LoDefs
import Submission.Work.KMTAreas.A7.ModelApproxAux

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.EndVar Work.KMTContract

/-- **The single-scale model approximation at the mixed arithmetic heights `(l₁,0)`, `l₁ ≥ 1`.**

For every `C₀ ≥ 1` and `ρ > 0` small (`ρ ≤ ρ₀`) there is an exponent `A ≥ 0` and a constant
`C(Λ)` such that, for every `Λ`-lacunary scale sequence `a` with `a n ≥ 1`, every quadruple with
`1 ≤ l₁`, `l₂ = 0`, every `f, g : ℤ → ℂ` and every scale index `n`,

  `‖ mainPartTuple ρ P C₀ a f g l₁ 0 k₁ k₂ n ‖_{ℓ^p} ≤ C(Λ) · modelWeight A ρ l₁ 0 k₁ k₂ ·
      ⌊a n⌋⁻¹ · ‖f‖_{ℓ^{p₁}} ‖g‖_{ℓ^{p₂}}`,   `p = (p₁⁻¹+p₂⁻¹)⁻¹`,

where `mainPartTuple` vanishes identically off its guard, so the estimate carries no restriction
on the scales.  The right-hand side is *not* the paper's `2^{O(2^{ρl}+s)}⌊N⌋⁻¹` but the weight
`modelWeight` of `Work.KMTAreas.A7.ModelApproxAux`, which is absorbed by `lossWeight` in the
assembly (the exponent `A` may depend on `ρ`, but not on the scale). -/
def LoMixedRSingleScaleStatement (P : ℤ[X]) (p₁ p₂ : ℝ≥0∞) (hdeg : 2 ≤ P.natDegree)
    (hA1 : Work.KMTContract.AreaA1) (hp₁ : 1 < p₁) (htp₁ : p₁ < ⊤) (hp₂ : 1 < p₂)
    (htp₂ : p₂ < ⊤) (hsum : p₁⁻¹ + p₂⁻¹ ≤ 1) : Prop :=
  ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
    ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ →
      ∃ A : ℝ, 0 ≤ A ∧
        ∀ (C₀ : ℕ), 1 ≤ C₀ → ∃ C : ℝ≥0 → ℝ≥0,
          ∀ (a : ℕ → ℝ≥0) (Λ : ℝ≥0) (l₁ l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
            1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
            1 ≤ l₁ → l₂ = 0 → ∀ n : ℕ,
            MeasureTheory.eLpNorm (fun x : ℤ =>
                mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
              (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count
            ≤ (C Λ : ENNReal) * ENNReal.ofReal (modelWeight A ρ l₁ l₂ k₁ k₂)
                * ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹)
                * MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count
                * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count

end

end Work.KMTAreas.A7
