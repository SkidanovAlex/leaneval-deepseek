/-
# The `(k₂,j₂) = (0,0)` (modulated "ball") height-`0` family: vocabulary

This module only fixes the predicate `BallZeroBound` used by the two sibling targets

* `Submission/Work/KMTPlan/A6/ballVarBound.lean`  (`Work.KMTPlan.A6.ballVarBound`), and
* `Submission/Work/KMTPlan/A6/ballVarBoundBdd.lean` (`Work.KMTPlan.A6.ballVarBoundBdd`),

so that the second can be stated (and proved) without importing the first.

The family in question is the *modulated* height-`0` family of the `g`-side model estimate: for a
`Λ`-lacunary family of scales `N_n = ⌊a n⌋`, a modulation parameter `t ∈ [1/2,1]` and an arbitrary
input `h : ℤ → ℂ`, it is

  `n ↦ Tle ρ 0 (φ̃_{N_n,t}) h`,   `φ̃_{N,t}(ξ) = φ̃_N(ξ) e(P(Nt) ξ) = varphitildeNtj P N 0 0 t ξ`,

i.e. the *low-pass* (`≤ 0` height) Ionescu--Wainger multiplier with the modulated `g`-side bump.
`BallZeroBound P R Λ` asserts the `R`-variational `ℓ²` bound for this family, uniformly in the
lacunary family `a`, in `t` and in `h`, with a constant allowed to depend on `ρ`, `Λ`, `P`, `R`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.LargeInterface
import Submission.Work.KMTPlan.A6.MdlDefs

set_option autoImplicit false

namespace Work.KMTPlan.A6

open MeasureTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

/-- **The modulated height-`0` ball bound.**  For `1 < Λ`, a `ρ ∈ (0,1]` and every `Λ`-lacunary
family `a` with `a n ≥ 1`, every `t ∈ [1/2,1]` and every `h : ℤ → ℂ`, the `R`-variation over `n` of
the height-`0` Ionescu--Wainger projections of the *modulated* bump `φ̃_{⌊a n⌋,t}` is bounded in
`ℓ²(ℤ)` by `C ‖h‖₂`. -/
def BallZeroBound (P : Polynomial ℤ) (R : NNReal) (Λ : NNReal) : Prop :=
  ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 → ∃ C : ℝ, 0 < C ∧
    ∀ (a : ℕ → NNReal), PointwiseErgodicTheorems.Lacunary Λ a → (∀ n : ℕ, 1 ≤ a n) →
    ∀ (t : ℝ), t ∈ Set.Icc (1 / 2 : ℝ) 1 → ∀ h : ℤ → ℂ,
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
        (fun n : ℕ => Work.KMTAreas.A7.Tle ρ 0
          (Work.KMTPlan.A6.varphitildeNtj P (Nat.floor (a n)) 0 0 t) h x))
        2 MeasureTheory.Measure.count
      ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm h 2 MeasureTheory.Measure.count

end

end Work.KMTPlan.A6
