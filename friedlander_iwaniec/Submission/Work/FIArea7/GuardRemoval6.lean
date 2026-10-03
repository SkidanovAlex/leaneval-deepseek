/-
# `Submission.Work.FIArea7.GuardRemoval6` — the objects for the coprimality-guard removal (step 4)

`Work.FIArea7.uniModeChar` carries the guard `(z₁,z₂) = 1`; the §16 identity
`Work.FIArea7.section16_omegaDetect_expansion` does not.  This file defines the two objects the
removal is stated with (see `NOTES.md` §55 for the analysis):

* `nonCoprimePairWeight Pa β` — the number of pairs of the box on which `β` is supported and which
  are *not* coprime.  By (5.8) every prime of `gnorm z` exceeds `Pz` on the support, so such a pair
  shares a Gaussian prime of norm `> Pz` and the count is `≪ Pz⁻¹N²` up to logarithms (Mertens);
* `uniModeCharFree Pa b e β k ε` — the same sum as `uniModeChar` **without** the coprimality
  guard, keeping the `unitInd` factors.  Those factors force `(gnorm z_i, 4be) = 1`, which makes the
  `ω`-detection sum have at most one non-zero term (no `Q`-loss), the second mechanism of §55.2.
-/
import Mathlib
import Submission.Work.FIArea7.UniMollify6

set_option autoImplicit false

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- **The number of non-coprime supported pairs of the box.** -/
def nonCoprimePairWeight (Pa : Work.FITop.Params) (β : GaussianInt → ℂ) : ℝ :=
  ((((Work.FIPlan.gBox (Work.FITop.radN Pa))
      ×ˢ (Work.FIPlan.gBox (Work.FITop.radN Pa))).filter
        (fun p => ¬ IsCoprime p.1 p.2 ∧ β p.1 ≠ 0 ∧ β p.2 ≠ 0)).card : ℝ)

/-- **The unguarded pair sum of a Fourier mode** — `Work.FIArea7.uniModeChar` without the
coprimality guard (the `unitInd` factors are kept: they bound the `ω`-detection to one term). -/
def uniModeCharFree (Pa : Work.FITop.Params) (b e : ℕ) (β : GaussianInt → ℂ) (k : ℤ)
    (ε : GaussianInt → ℤ) : ℂ :=
  ∑ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
    ∑ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
      unitInd (4 * b * e) z1 * unitInd (4 * b * e) z2
        * (uniCoeff ε β k z1 * star (uniCoeff ε β k z2))
        * omegaDetect (4 * b * e) e z1 z2

/-- **The `(b,e)`-mode sum of the guarded char objects** — the mode decomposition of
`Work.FIArea7.WUniOmega6Pull6Moll` (by `Work.FIArea7.WUniOmega6Pull6Moll_eq_modes` together with
`Work.FIArea7.uniModePair_eq_uniModeChar`), written directly with `uniModeChar`.  Its per-`(b,e,k)`
terms are the left-hand sides of `Work.FIArea7.section16_omegaDetect_expansion`. -/
def uniModeSum (Pa : Work.FITop.Params) (X : ℕ) (β : GaussianInt → ℂ) (K : ℕ)
    (ε : GaussianInt → ℤ) : ℂ :=
  2 * ∑ b ∈ Finset.Icc 1 (uniB Pa),
        ∑ e ∈ Finset.Icc 1 X,
          (((ArithmeticFunction.moebius b : ℝ) / (b : ℝ) : ℝ) : ℂ)
            * ((((2 * Real.log 2 + Real.log 4 : ℝ)) : ℂ) * uniModeChar Pa b e β 0 ε
                + ∑ k ∈ evenFreq K,
                    (1 / (|k| : ℝ) : ℂ) * uniModeChar Pa b e β k ε)

/-- **The same sum with the coprimality guard dropped** — the object the §16 character expansion
is applied to (there the only pair criterion is the congruence inside `omegaDetect`, and the
`unitInd` factors control it by `NOTES.md` §55.2). -/
def uniModeSumFree (Pa : Work.FITop.Params) (X : ℕ) (β : GaussianInt → ℂ) (K : ℕ)
    (ε : GaussianInt → ℤ) : ℂ :=
  2 * ∑ b ∈ Finset.Icc 1 (uniB Pa),
        ∑ e ∈ Finset.Icc 1 X,
          (((ArithmeticFunction.moebius b : ℝ) / (b : ℝ) : ℝ) : ℂ)
            * ((((2 * Real.log 2 + Real.log 4 : ℝ)) : ℂ) * uniModeCharFree Pa b e β 0 ε
                + ∑ k ∈ evenFreq K,
                    (1 / (|k| : ℝ) : ℂ) * uniModeCharFree Pa b e β k ε)

end

end Work.FIArea7
