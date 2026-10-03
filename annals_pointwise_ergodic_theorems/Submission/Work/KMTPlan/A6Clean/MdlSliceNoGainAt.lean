/-
# The loss-form (no-gain) slice bound, as a named predicate

`Work.KMTPlan.A6Clean.MdlSliceNoGainAt P hd hA1 C₀ r j₁ j₂` is the *named* form of the conclusion
of `Work.KMTPlan.A6Clean.mdlSliceNoGain` (`A6Clean/mdlSliceNoGain.lean`) at the fixed parameters
`(C₀, r, j₁, j₂)`: the frozen slice's `ℓ¹(ℤ;V^r)`-norm bounded by `K(Λ)·lossWeight c·‖f‖₂‖g‖₂`
with **no** arithmetic gain in `max(l₁,l₂)` and no restriction on the parameters — the A6 twin of
the PROVED `Work.KMTAreas.A7.ModelLargeBound` at `(p₁,p₂) = (2,2)`.

It is the second input of the case-splitting consumer
`Work.KMTPlan.A6Clean.MdlSliceCoreGainMemLp_of_pieces_split`: on the data with
`B ρ ≤ lcL l₁ l₂ k₁ k₂` the gated adelic form supplies the *gain*, while on the bounded-`lcL` data
the gain `2^{-c·max(l₁,l₂)}` is a `ρ`-constant and this loss-form bound suffices after absorbing
it into `K(Λ)`.  See `NOTES_A6_adelicCaseB_OBSTRUCTION_SESSION.md`.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.MdlDefs

set_option autoImplicit false

namespace Work.KMTPlan.A6Clean

open MeasureTheory
open scoped ENNReal NNReal BigOperators
open Work.KMTAreas.A7
open Work.KMTPlan.A6

/-- **The loss-form (no-gain) bound for the frozen slice at `(C₀, r, j₁, j₂)`.** -/
def MdlSliceNoGainAt (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (hA1 : Work.KMTContract.AreaA1)
    (C₀ : ℕ) (r : NNReal) (j₁ j₂ : ℤ) : Prop :=
  ∃ c : ℝ, 0 ≤ c ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ K : NNReal → NNReal,
    ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (f g : ℤ → ℂ),
      1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
      t ∈ Set.Icc (1 / 2 : ℝ) 1 →
      (k₁ = 0 → j₁ ≠ -1) → (k₂ = 0 → j₂ ≠ -1) →
      MemLp f 2 Measure.count → MemLp g 2 Measure.count →
      eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x))
        1 Measure.count
      ≤ (K Λ : ENNReal) * ENNReal.ofReal (lossWeight c ρ l₁ l₂ k₁ k₂)
        * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count

end Work.KMTPlan.A6Clean
