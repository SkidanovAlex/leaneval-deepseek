import Mathlib

/-!
# The two family conditions of the odd case on a general interval `[-R₁, R₂]`

The endgame of the odd-dimensional case (`Submission.Odd.OddFamilyData`) is stated for a profile
supported on an arbitrary interval `[-R₁, R₂]`, but the workspace's cap lemmas
(`Work.OddCaps.odd_cap_volume_half`, `Work.OddCaps.odd_cap_centroid_span`) are proved only for
`[-1, 1]`.  Since the odd chord curve produced by the paper's construction has its tips at
`±ρ(±1) ≠ ±1` (`Submission/Work/OddCurve/NOTES_SESSION5.md`), the endgame has to run on the
general interval; this file fixes the two conclusions as `Prop`s, so that the general versions of
the cap lemmas can be stated, delegated and then composed with the assembly.

* `VolumeHalfGeneral d R₁ R₂ f h` — every plane `x_last = s x_0 + h s`, `s > 0`, cuts the body of
  revolution `K = {x | x 0 ∈ Icc (-R₁) R₂ ∧ Σ_{i>0} x i ^2 ≤ f (x 0)^2}` in half its volume;
* `CentroidSpanGeneral d R₁ R₂ f h` — the corresponding centroid condition: the centroid of the
  cap lies on the line through the centroid of `K` in the direction `(-s, 0, …, 0, 1)`.

Both are the conclusions of the odd cap lemmas with `-1, 1` replaced by `-R₁, R₂`; the
hypotheses under which they are produced (smooth concave positive profile vanishing at the ends
and inside the interval, smooth bump with `h 0 = 0`, the two *odd* moment equations, and the
chord-endpoint equations `f (y s) = s y s + h s`, `f (-x s) = -(s (-x s) + h s)`) are recorded
verbatim in the requests `OddCurve/CapsGen/volume_half_general` and
`OddCurve/CapsGen/centroid_span_general`.
-/

namespace Work.OddCurve
namespace CapsGen

open MeasureTheory Set Filter
open scoped Topology ContDiff Pointwise BigOperators RealInnerProductSpace

noncomputable section

/-- **The first family condition on `[-R₁, R₂]`**: the cutting planes are at half the volume. -/
def VolumeHalfGeneral (d : ℕ) [NeZero d] (R₁ R₂ : ℝ) (f h : ℝ → ℝ) : Prop :=
  let K : Set (EuclideanSpace ℝ (Fin d)) :=
    {x | x 0 ∈ Set.Icc (-R₁) R₂ ∧ ∑ i ∈ Finset.Ioi (0 : Fin d), (x i) ^ 2 ≤ f (x 0) ^ 2}
  ∀ s : ℝ, 0 < s →
    MeasureTheory.volume.real
        (K ∩ {x | x ⟨d - 1, by have := Nat.pos_of_neZero d; omega⟩ ≤ s * x 0 + h s}) =
      MeasureTheory.volume.real K / 2

/-- **The second family condition on `[-R₁, R₂]`**: the centroid of the cap lies on the line
through the centroid of the body in the direction `(-s, 0, …, 0, 1)`. -/
def CentroidSpanGeneral (d : ℕ) [NeZero d] (R₁ R₂ : ℝ) (f h : ℝ → ℝ) : Prop :=
  let K : Set (EuclideanSpace ℝ (Fin d)) :=
    {x | x 0 ∈ Set.Icc (-R₁) R₂ ∧ ∑ i ∈ Finset.Ioi (0 : Fin d), (x i) ^ 2 ≤ f (x 0) ^ 2}
  ∀ s : ℝ, 0 < s →
    (⨍ x in K, x) -
        (⨍ x in (K ∩ {x | x ⟨d - 1, by have := Nat.pos_of_neZero d; omega⟩ ≤ s * x 0 + h s}), x) ∈
      ℝ ∙ ((-s) • EuclideanSpace.single (0 : Fin d) (1 : ℝ) +
        EuclideanSpace.single (⟨d - 1, by have := Nat.pos_of_neZero d; omega⟩ : Fin d) (1 : ℝ))

/-- **The centroid conclusion of the odd cap lemma**, with the direction vector written as
`(-s) • single 0 1 + single (d-1) 1` (the form in which the seed's cap lemmas state it). -/
def CentroidSpanGeneral' (d : ℕ) [NeZero d] (A B : ℝ) (f h : ℝ → ℝ) : Prop :=
  let K : Set (EuclideanSpace ℝ (Fin d)) :=
    {x | x 0 ∈ Set.Icc A B ∧ ∑ i ∈ Finset.Ioi (0 : Fin d), (x i) ^ 2 ≤ f (x 0) ^ 2}
  ∀ s : ℝ, 0 < s →
    (⨍ x in K, x) -
        (⨍ x in (K ∩ {x | x ⟨d - 1, by have := Nat.pos_of_neZero d; omega⟩ ≤
          s * x 0 + h s}), x) ∈
      ℝ ∙ ((-s) • EuclideanSpace.single (0 : Fin d) (1 : ℝ) +
        EuclideanSpace.single (⟨d - 1, by have := Nat.pos_of_neZero d; omega⟩ : Fin d) (1 : ℝ))

end

end CapsGen
end Work.OddCurve
