import Mathlib
import Submission.Work.Smooth.Plane.Consequence
import Submission.Work.Smooth.Plane.SlicedClean
import Submission.Work.Smooth.Plane.encard_pardonSlice_inter_lt_pardonsI

/-!
# The planar slice of Pardon's box carries no essential loop

This is the **consequence** of the planar innermost-disc chapter, in the exact form in which the
double-bubble core `Work.BoxShrink.CruxCore` consumes it.

Let `ψ` be a diffeomorphism of `ℝ³`, `F = ψ(F_standard)` the image torus
(`Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph`), `K` a knot in the class of the
standard `(p,q)`-torus knot (`himg`), and let

`D = Work.Smooth.Plane.PardonSlice s c σ u = PBox s c σ ∩ {y | y (σ 2) = c (σ 2) + u}`

be the slice of Pardon's box by the cutting plane.  Assume

* the distortion bound `d` is small: `countConst · d = 150 · d < min p q` (`hsmall`), and the plane
  count of `Work.BoxSweep.exists_plane_level` holds: the knot meets the slice `D` in at most
  `5(1+ε)/ε·d` parameters of its fundamental period (`hcount`);
* the planar innermost-disc cleaning step `CleansInConvexPlane P D` for the slice `D` (Pardon's two
  innermost arguments in the plane, see `Work.Smooth.Plane.Cleaning`);
* the surface `F` is a convex planar region slice: automatic, `D` is convex planar by
  `Work.Smooth.Plane.isConvexPlanar_PardonSlice`.

Then **`D` contains no essential loop of `F`**: its winding span vanishes.

The counting reduction is `Work.Smooth.Plane.encard_pardonSlice_inter_lt_pardonsI` (the number of
intersection *points* of the knot with `D` is at most the number of *parameters*, which is at most
`37.5·d < min p q = I(F,β)`), and the vanishing of the winding span is Pardon's counting argument
(`Work.Smooth.Plane.windingSpan_eq_bot_of_cleansInConvexPlane`): an essential loop inside `D` would
be cleaned into a simple essential compressing loop inside `D`, which must meet the knot at least
`I(F,β)` times, contradicting the count.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.Smooth.Plane

noncomputable section

variable {p q : ℕ}

/-- **The planar slice of Pardon's box carries no essential loop.**

See the module docstring for the exact hypotheses: the count of the swept plane
(`Work.BoxSweep.exists_plane_level`), the smallness of the distortion bound, and the planar
innermost-disc cleaning step for the slice. -/
theorem windingSpan_pardonSlice_eq_bot (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q)
    (ψ : Submission.Diffeo) (K : Knot) {d s u : ℝ} (hd : 0 ≤ d)
    (hsmall : Submission.countConst * d < (Nat.min p q : ℝ))
    (himg : Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ)
    {c : R3} {σ : Equiv.Perm (Fin 3)}
    (hclean : CleansInConvexPlane
      (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph) (PardonSlice s c σ u))
    (hcount : ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        K.curve t ∈ Submission.PBox s c σ ∧
        (K.curve t) (σ 2) = c (σ 2) + u}) : ENNReal))
      ≤ ENNReal.ofReal (5 * (1 + Submission.eps) / Submission.eps * d)) :
    Work.SurgeryInvariance.WindingSpan
      (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph)
      (PardonSlice s c σ u) = ⊥ :=
  windingSpan_eq_bot_of_cleansInConvexPlane
    (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
      (Work.CoreTopology.standardCurve p q))
    (PardonSlice s c σ u) hclean
    (encard_pardonSlice_inter_lt_pardonsI p q hp hq hc ψ K hd hsmall himg hcount)

/-- The same statement in the `ContainsEssentialLoop` vocabulary. -/
theorem not_containsEssentialLoop_pardonSlice (hp : 0 < p) (hq : 0 < q)
    (hc : Nat.Coprime p q) (ψ : Submission.Diffeo) (K : Knot) {d s u : ℝ} (hd : 0 ≤ d)
    (hsmall : Submission.countConst * d < (Nat.min p q : ℝ))
    (himg : Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ)
    {c : R3} {σ : Equiv.Perm (Fin 3)}
    (hclean : CleansInConvexPlane
      (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph) (PardonSlice s c σ u))
    (hcount : ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        K.curve t ∈ Submission.PBox s c σ ∧
        (K.curve t) (σ 2) = c (σ 2) + u}) : ENNReal))
      ≤ ENNReal.ofReal (5 * (1 + Submission.eps) / Submission.eps * d)) :
    ¬ (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph).ContainsEssentialLoop
      (PardonSlice s c σ u) := by
  rw [← Work.SurgeryInvariance.WindingSpan_eq_bot_iff]
  exact windingSpan_pardonSlice_eq_bot hp hq hc ψ K hd hsmall himg hclean hcount

/-- **The literal form asked for by the double-bubble core**: the *closed slice*
`PardonSlice s c σ u ∩ PBox s c σ` carries no essential loop.  (The two sets are equal, since the
slice is contained in the box, so this is `windingSpan_pardonSlice_eq_bot` up to rewriting the
region.) -/
theorem windingSpan_pardonSlice_inter_PBox_eq_bot (hp : 0 < p) (hq : 0 < q)
    (hc : Nat.Coprime p q) (ψ : Submission.Diffeo) (K : Knot) {d s u : ℝ} (hd : 0 ≤ d)
    (hsmall : Submission.countConst * d < (Nat.min p q : ℝ))
    (himg : Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ)
    {c : R3} {σ : Equiv.Perm (Fin 3)}
    (hclean : CleansInConvexPlane
      (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph) (PardonSlice s c σ u))
    (hcount : ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        K.curve t ∈ Submission.PBox s c σ ∧
        (K.curve t) (σ 2) = c (σ 2) + u}) : ENNReal))
      ≤ ENNReal.ofReal (5 * (1 + Submission.eps) / Submission.eps * d)) :
    Work.SurgeryInvariance.WindingSpan
      (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph)
      (PardonSlice s c σ u ∩ Submission.PBox s c σ) = ⊥ := by
  rw [Set.inter_eq_left.mpr (PardonSlice_subset_PBox s c σ u)]
  exact windingSpan_pardonSlice_eq_bot hp hq hc ψ K hd hsmall himg hclean hcount

/-! ## The form in which the double-bubble core disposes of the classical inputs

The crux `Work.BoxShrink.CruxCore` carries the global cut-and-paste hypothesis
`Work.InnermostDisk.CleansDiscs P`; the additional input needed for the *plane* is the general
position of the cutting plane with respect to the surface, recorded as `SlicedPlane P D` (the
planar analogue of `Work.BoxShrink.SlicedSphere`) or, in its classical form, as `TransversePlane P D`
together with the slicing input `PlaneSliceInput P` (a plane level is a regular value of the
restriction of the coordinate function to the surface). -/

/-- **The planar slice carries no essential loop**, from the general position `SlicedPlane` of the
cutting plane and the global cut-and-paste `Work.InnermostDisk.CleansDiscs`. -/
theorem windingSpan_pardonSlice_eq_bot_of_sliced (hp : 0 < p) (hq : 0 < q)
    (hc : Nat.Coprime p q) (ψ : Submission.Diffeo) (K : Knot) {d s u : ℝ} (hd : 0 ≤ d)
    (hsmall : Submission.countConst * d < (Nat.min p q : ℝ))
    (himg : Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ)
    {c : R3} {σ : Equiv.Perm (Fin 3)}
    (hcl : Work.InnermostDisk.CleansDiscs
      (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph))
    (hslice : SlicedPlane (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph)
      (PardonSlice s c σ u))
    (hcount : ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        K.curve t ∈ Submission.PBox s c σ ∧
        (K.curve t) (σ 2) = c (σ 2) + u}) : ENNReal))
      ≤ ENNReal.ofReal (5 * (1 + Submission.eps) / Submission.eps * d)) :
    Work.SurgeryInvariance.WindingSpan
      (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph)
      (PardonSlice s c σ u) = ⊥ :=
  windingSpan_pardonSlice_eq_bot hp hq hc ψ K hd hsmall himg
    (cleansInConvexPlane_of_slicedPlane hslice hcl) hcount

/-- **The planar slice carries no essential loop**, from the general position `TransversePlane` of
the cutting plane, the slicing input `PlaneSliceInput` and the global cut-and-paste. -/
theorem windingSpan_pardonSlice_eq_bot_of_sliceInput (hp : 0 < p) (hq : 0 < q)
    (hc : Nat.Coprime p q) (ψ : Submission.Diffeo) (K : Knot) {d s u : ℝ} (hd : 0 ≤ d)
    (hsmall : Submission.countConst * d < (Nat.min p q : ℝ))
    (himg : Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ)
    {c : R3} {σ : Equiv.Perm (Fin 3)}
    (hcl : Work.InnermostDisk.CleansDiscs
      (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph))
    (hinput : PlaneSliceInput (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph))
    (hT : TransversePlane (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph)
      (PardonSlice s c σ u))
    (hcount : ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        K.curve t ∈ Submission.PBox s c σ ∧
        (K.curve t) (σ 2) = c (σ 2) + u}) : ENNReal))
      ≤ ENNReal.ofReal (5 * (1 + Submission.eps) / Submission.eps * d)) :
    Work.SurgeryInvariance.WindingSpan
      (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph)
      (PardonSlice s c σ u) = ⊥ :=
  windingSpan_pardonSlice_eq_bot hp hq hc ψ K hd hsmall himg
    (cleansInConvexPlane_of_planeSliceInput hinput hcl
      (isConvexPlanar_PardonSlice s c σ u) hT) hcount

end

end Work.Smooth.Plane
