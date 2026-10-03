import Mathlib
import Submission.Work.FIArea4.prop_11_1_defs
import Submission.Work.FIArea4.WdyadSetup
import Submission.Work.FIArea4.WdyadDefs2

/-!
# A bump majorant for the dyadic dual variance (FI §11)

This small module fixes the interface between the abstract bump majorant of
`Submission.Work.FIArea4.Vflip.exists_bump_majorant` and the estimate of the flat part of the
dyadic dual variance `Work.FIArea4.Wdyad` (see `Submission/Work/FIArea4/flat_part_le.lean`).

`BumpData S f F C₀` bundles the properties that are actually used:

* `f : ℝ → ℝ` is continuous, `0 ≤ f ≤ 1`, and `f` vanishes off `[S/2, 5S/2]`;
* `F` is the Fourier transform of `f` (viewed as a complex function);
* `‖F ξ‖ ≤ C₀ S (1 + S|ξ|)^{-2}`.
-/

namespace Work.FIArea4

open scoped BigOperators FourierTransform

/-- The data of a bump majorant of the interval `(S, 2S]`: a continuous `f` with `0 ≤ f ≤ 1`
supported in `[S/2, 5S/2]`, together with its Fourier transform `F` and its decay constant. -/
def BumpData (S : ℕ) (f : ℝ → ℝ) (F : ℝ → ℂ) (C₀ : ℝ) : Prop :=
  (∀ x, 0 ≤ f x) ∧ (∀ x, f x ≤ 1) ∧
    (∀ x, f x ≠ 0 → (S : ℝ) / 2 ≤ x ∧ x ≤ 5 * (S : ℝ) / 2) ∧
    Continuous f ∧ 0 < C₀ ∧
    (∀ ξ, F ξ = FourierTransform.fourier (fun x : ℝ => (f x : ℂ)) ξ) ∧
    (∀ ξ, ‖F ξ‖ ≤ C₀ * (S : ℝ) * (1 + (S : ℝ) * |ξ|) ^ (-(2 : ℝ)))

end Work.FIArea4
