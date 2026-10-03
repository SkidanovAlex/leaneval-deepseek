/-
# The large-scale per-residue fibre estimate of the mixed range (Area A7, KMT §8)

This module isolates the **one deep analytic input** of the mixed `g`-side fibre estimate
(`Work.KMTAreas.A7MixedG.FiberGuard`, whose reduction is in
`Submission/Work/KMTAreas/A7MixedG/FiberGuard.lean`):

`Work.KMTAreas.A7MixedG.FiberLargeResidue P p₂ hdeg` :

for `C₀ ≥ 1`, `r > 2`, `p₂ ∈ (1,∞)` there are `A ≥ 0`, `ρ₀ > 0` and a *scale threshold* `B` such
that, for every `ρ ∈ (0,ρ₀]`, there is `C : ℝ≥0 → ℝ≥0` with: for all `Λ`-lacunary
`a : ℕ → ℝ≥0` with `a n ≥ 1`, all scales `l₂ k₁ k₂` with `l₂ ≥ 1` and
`B < max l₂ (max k₁ k₂)` — the *large-scale* regime — all `t ∈ [1/2,1]`, all bounded `g`, and
**every residue `n₀ : ℤ`**,

  `‖ V^r_n ( fiberOpP ρ P l₂ m_* n₀ (GmixedFam ρ P C₀ a l₂ k₁ k₂ t g n) ) ‖_{ℓ^{p₂}}`
    `≤ (C Λ) · lossWeight A ρ 0 l₂ k₁ k₂ · ‖ V^r_n (GmixedFam … n) ‖_{ℓ^{p₂}}`,

where `m_* = GmixedKer ρ P l₂ k₁ k₂ = mStargF P.natDegree (loMixedU ρ P.natDegree l₂ k₁ k₂)`.

This is the paper's §8 (`form-1` plus the quantitative Shannon/decimation transfer) for the
*mixed* range: the fibre at the residue `n₀` is a translate of an Ionescu–Wainger projection with
the *modulated* narrow window `m_*` (`FiberOpRephase`), so on the range of the cut it is
variationally harmless; the residue average over `n₀` then costs nothing
(`eLpNorm_residueLp_le_of_single`), which is why the statement above is *per residue* and uniform
in `n₀`.

## The shape of the statement (why each hypothesis is there)

* `1 ≤ l₂`: the exact-height frequency set of the `g`-side is `iwArithFreqsNew ρ l₂`
  (`fiberOpP`), which is empty at `l₂ = 0`; the mixed range has `l₁ = 0`, `l₂ ≥ 1`.
* `B < max l₂ (max k₁ k₂)`: the *large-scale* regime.  For small scales the crude Young bound
  `Work.KMTAreas.A7.eLpNorm_residueLp_fiberOpP_le` already gives the estimate (with a constant
  depending on the (finite) box of scales), so the deep input is only needed here.
* `Lacunary Λ a`, `1 < Λ`: the family `GmixedFam` is the Ionescu–Wainger projection of the
  modulated `d`-fold bump `varphitildeNt P P.natDegree (⌊a n⌋) k₂ t`; its lacunarity is what makes
  the signed symbol sums bounded, hence the variational estimate available.
* `BddAbove (Set.range fun y => ‖g y‖)`: `g` is bounded (this is how the fibre `ℓ^p` bounds are
  stated in `MixedGSideAux`); the result is then extended to all `g` by the `eLpNorm = ⊤` case.
* `A`, `ρ₀` and `B` are chosen before `ρ`; the constant `C Λ` *after* `ρ` (and may depend on
  `C₀, r, p₂, P, ρ`), which matches the quantifier structure of `FiberGuard`.

## The route (for the prover)

1. `fiberOpP_eq_fiberOp` (`A7/fiberVarSamplingCoreG.lean`) turns the polynomial twist
   `P.eval n₀` into the linear twist of `fiberOp`; `Work.KMTAreas.A7Hi.FiberOpRephase` then gives
   `fiberOp ρ l₂ m (P.eval n₀) v = τ_{P n₀} (fiberOp ρ l₂ (mMod m (P.eval n₀)) 0 v)`.
2. `fiberOp ρ l₂ (mMod m M) 0 = τ_{-M} ∘ iwConv (iwArithFreqsNew ρ l₂) (periodize m)`
   (pure kernel algebra: modulating a bump shifts its inverse Fourier coefficients,
   `Work.KMTAreas.A7Hi.cw_mMod`), and the two shifts cancel, so the fibre applied to
   `GmixedFam … n` is the *same* family element for every residue `n₀`:
   `fiberOpP ρ P l₂ m n₀ (GmixedFam … n) = iwConv A (periodize m) (GmixedFam … n)` —
   i.e. the residue dependence disappears and only `iwConv A (periodize m)` (a fixed Ionescu–
   Wainger projection with the narrow window) remains.
   The composition `iwConv A (periodize m) ∘ Tm ρ l₂ (periodize ψ)` is computed with the
   *non-aliasing* of `iwArithFreqsNew ρ l₂` at the packet scale
   (`Work.Analysis.IonescuWainger.iwSymbolSet_mul`), which in the large-scale regime follows from
   `splitCut ρ L < ⌊a n⌋` (the `L`-large arithmetic split, cf.
   `Work.KMTAreas.A7.farey_and_strict_of_large_L`).
3. The remaining (crux) comparison `‖V^r (Q u)‖ ≤ C (1+l₂) ‖V^r u‖` for the *fixed* narrow-cut
   operator `Q` and the concrete family `u_n = Tm ρ l₂ (periodize (varphitildeNt …)) g` — the
   `V^r`-valued form of the Ionescu–Wainger multiplier theorem for the mixed range.  The
   `(1+l₂)^{O(1)}` loss is absorbed by `lossWeight A ρ 0 l₂ k₁ k₂` for `A ≥ 1`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7MixedG.FiberLargeResidueCore

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7MixedG

open MeasureTheory
open scoped ENNReal NNReal BigOperators

/-- **The large-scale per-residue fibre estimate of the mixed range** (`FiberGuard`'s crux, the
paper's §8 `form-1` + quantitative Shannon transfer). -/
def FiberLargeResidue (P : Polynomial ℤ) (p₂ : ENNReal) (hdeg : 2 ≤ P.natDegree)
    (hp₂ : 1 < p₂) (htp₂ : p₂ < ⊤) : Prop :=
  ∀ (C₀ : ℕ) (r : NNReal), 1 ≤ C₀ → (2 : NNReal) < r →
    ∃ A : ℝ, 0 ≤ A ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∃ B : ℕ,
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ C : NNReal → NNReal,
        ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₂ k₁ k₂ : ℕ) (t : ℝ) (g : ℤ → ℂ) (n₀ : ℤ),
          1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) → 1 ≤ l₂ →
          t ∈ Set.Icc (1/2 : ℝ) 1 → BddAbove (Set.range fun y : ℤ => ‖g y‖) →
          B < max l₂ (max k₁ k₂) →
          MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => Work.KMTAreas.A7.fiberOpP ρ P l₂
                (Work.KMTAreas.A7.GmixedKer ρ P l₂ k₁ k₂) n₀
                (Work.KMTAreas.A7.GmixedFam ρ P C₀ a l₂ k₁ k₂ t g n) x))
            p₂ MeasureTheory.Measure.count
          ≤ (↑(max 1 (C Λ)) : ENNReal) * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight A ρ 0 l₂ k₁ k₂) *
              MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
                (fun n : ℕ => Work.KMTAreas.A7.GmixedFam ρ P C₀ a l₂ k₁ k₂ t g n x))
                p₂ MeasureTheory.Measure.count

/-- The large-scale per-residue fibre estimate (proved in
`Submission/Work/KMTAreas/A7MixedG/FiberLargeResidueCore.lean`). -/
theorem fiberLargeResidue (P : Polynomial ℤ) (p₂ : ENNReal) (hdeg : 2 ≤ P.natDegree)
    (hp₂ : 1 < p₂) (htp₂ : p₂ < ⊤) :
    FiberLargeResidue P p₂ hdeg hp₂ htp₂ := by
  unfold FiberLargeResidue
  exact FiberLargeResidueCore P p₂ hdeg hp₂ htp₂

end Work.KMTAreas.A7MixedG
