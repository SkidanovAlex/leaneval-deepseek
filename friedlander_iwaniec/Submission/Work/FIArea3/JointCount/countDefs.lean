/-
# `Submission.Work.FIArea3.JointCount.countDefs` — Finsets for the joint count

The counting statements of `card_filter_le` filter the polar box `polarBoxFinset Pa φ` by
predicates such as `d ∣ gnorm z₂ ∧ e ∣ absDelta z₁ z₂`.  Since `Finset.filter` needs a
`DecidablePred` instance, the `Finset`s are packaged here (in a file that installs
`Classical.propDecidable`), so that statements can be written without an inline `filter`.
-/
import Mathlib
import Submission.Work.FIArea3.BoxDefs
import Submission.Work.FIArea3.JointCount.polarBox_lattice_count_sharp

namespace Work.FIArea3.JointCount

open Finset Work.FIPlan

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The points of the polar box divisible by the Gaussian integer `w`. -/
def boxDvdFinset (Pa : Work.FITop.Params) (φ : ℝ) (w : GaussianInt) : Finset GaussianInt :=
  (Work.FIArea3.polarBoxFinset Pa φ).filter (fun z₂ => w ∣ z₂)

/-- The points of the polar box that are divisible by `w` and satisfy `e ∣ Δ(z₁,·)`.

CAUTION: this is *not* `polarBox ∩ jointPieceLat z₁ w e`.  With `s = star z₁ * w` and
`z₂ = y * w` one has `Δ(z₁,z₂) = Im (s*y) = s.re * y.im + s.im * y.re`, so the condition is
`e ∣ s.re * y.im + s.im * y.re`, whereas `jointPieceLat z₁ w e` is built from `yLat` with the
coefficients `s.im`, `s.re` (transposed).  The two lattices (hence their indices) agree, because
`jointPieceLat z₁ w e` is the image under `y ↦ conj y` of the image of
`yLat (star z₁*w).re (star z₁*w).im e` under `mulRight w`, and `gcd a b = gcd b a`. -/
def jointPieceBoxFinset (Pa : Work.FITop.Params) (φ : ℝ) (z₁ w : GaussianInt) (e : ℕ) :
    Finset GaussianInt :=
  (Work.FIArea3.polarBoxFinset Pa φ).filter
    (fun z₂ => w ∣ z₂ ∧ e ∣ Work.FIPlan.absDelta z₁ z₂)

/-- The points of the polar box with `d ∣ |z₂|²` and `e ∣ |Δ(z₁,z₂)|` — the set counted by
`card_filter_le`. -/
def pairBoxFinset (Pa : Work.FITop.Params) (φ : ℝ) (z₁ : GaussianInt) (d e : ℕ) :
    Finset GaussianInt :=
  (Work.FIArea3.polarBoxFinset Pa φ).filter
    (fun z₂ => d ∣ Work.FIPlan.gnorm z₂ ∧ e ∣ Work.FIPlan.absDelta z₁ z₂)

end

end Work.FIArea3.JointCount
