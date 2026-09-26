import Mathlib
import Submission.Work.Smooth.OneManifold.Bridge
import Submission.Work.Smooth.OneManifold.exists_finite_component_decomposition
import Submission.Work.Smooth.SphereJordan.LocalArc.compactPreconnectedLocallyArc_isCircle

/-!
# The classification of compact one-dimensional subsets of a surface

`isCircleUnion_of_isCompact_of_isLocallyEuclidean`: a compact subset `Z` of the surface
`F = torus ψ` which is *locally Euclidean of dimension one* (every point of `Z` has a
neighbourhood in `Z` homeomorphic to `ℝ`, i.e. every local arc is an embedded arc) is a finite
disjoint union of embedded circles of `F`.

The proof splits `Z` into finitely many components
(`Work.Smooth.OneManifold.exists_finite_component_decomposition`), parametrises each component by
a `2π`-periodic injective curve (`Work.Smooth.SphereJordan.LocalArc.compactPreconnectedLocallyArc_isCircle`,
the classification of compact connected `1`-manifolds) and reassembles.

`isCircleUnion_of_isCompact_of_isLocalArcEmbedding` is the same statement with the hypothesis
`Work.Smooth.Morse.IsLocalArc` replaced by its repaired form
`Work.Smooth.OneManifold.IsLocalArcEmbedding`; the literal hypothesis
`Work.Smooth.Morse.IsLocalArc` does **not** suffice (see `Counterexample.lean` and the README).
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.Smooth.OneManifold

noncomputable section

/-- **A compact connected locally Euclidean subset of the surface is a circle.**

`C` is parametrised by a continuous `2π`-periodic map which is injective on a fundamental period
and whose range is exactly `C`; since `C ⊆ F`, this is a `Work.CoreTopology.ClosedCurve` of the
surface, and it is simple in the sense of `Work.CoreTopology.IsSimple`. -/
theorem exists_closedCurve_of_component (ψ : Submission.Diffeo) {C : Set R3}
    (hCsub : C ⊆ (Work.Smooth.Morse.torus ψ).carrier) (hCcomp : IsCompact C)
    (hCpre : IsPreconnected C) (hCne : C.Nonempty) (hCloc : IsLocallyEuclidean C) :
    ∃ γ : Work.CoreTopology.ClosedCurve (Work.Smooth.Morse.torus ψ),
      Work.CoreTopology.IsSimple (Work.Smooth.Morse.torus ψ) γ ∧ Set.range γ.γ = C := by
  haveI : CompactSpace C := isCompact_iff_compactSpace.mp hCcomp
  haveI : PreconnectedSpace C := Subtype.preconnectedSpace hCpre
  haveI : Nonempty C := hCne.to_subtype
  obtain ⟨γ, hcont, hper, hinj, hrange⟩ :=
    Work.Smooth.SphereJordan.LocalArc.compactPreconnectedLocallyArc_isCircle (X := C) hCloc
  let γc : Work.CoreTopology.ClosedCurve (Work.Smooth.Morse.torus ψ) :=
    { γ := fun t => (γ t : R3)
      cont := continuous_subtype_val.comp hcont
      periodic := fun t => congrArg Subtype.val (hper t)
      mem := fun t => hCsub (γ t).2 }
  have hsimplec : Work.CoreTopology.IsSimple (Work.Smooth.Morse.torus ψ) γc := by
    intro t ht t' ht' h
    exact hinj ht ht' (Subtype.ext h)
  have hrangec : Set.range γc.γ = C := by
    show Set.range (fun t : ℝ => (γ t : R3)) = C
    rw [show (fun t : ℝ => (γ t : R3)) = (fun y : C => (y : R3)) ∘ γ from
        funext fun t => rfl,
      Set.range_comp, hrange, Subtype.coe_image_univ]
  exact ⟨γc, hsimplec, hrangec⟩

/-- **The classification of compact `1`-manifolds in the surface.**

A compact subset `Z` of the surface `F = torus ψ` which is locally Euclidean of dimension one is a
finite disjoint union of embedded circles of `F`. -/
theorem isCircleUnion_of_isCompact_of_isLocallyEuclidean (ψ : Submission.Diffeo) {Z : Set R3}
    (hZ : Z ⊆ (Work.Smooth.Morse.torus ψ).carrier) (hcomp : IsCompact Z)
    (hloc : IsLocallyEuclidean Z) : IsCircleUnion ψ Z := by
  obtain ⟨n, C, hCsub, hCne, hCpre, hCcomp, hCloc, hCdisj, hCcover⟩ :=
    exists_finite_component_decomposition hcomp hloc
  choose γ hγsimple hγrange using fun i =>
    exists_closedCurve_of_component ψ ((hCsub i).trans hZ) (hCcomp i) (hCpre i) (hCne i)
      (hCloc i)
  refine ⟨n, γ, hγsimple, ?_, ?_⟩
  · intro i j hij
    rw [hγrange i, hγrange j]
    exact hCdisj i j hij
  · rw [hCcover]
    exact Set.iUnion_congr fun i => (hγrange i).symm

/-- **The classification with the repaired local-arc hypothesis.** -/
theorem isCircleUnion_of_isCompact_of_isLocalArcEmbedding (ψ : Submission.Diffeo) {Z : Set R3}
    (hZ : Z ⊆ (Work.Smooth.Morse.torus ψ).carrier) (hcomp : IsCompact Z)
    (harc : IsLocalArcEmbedding ψ Z) : IsCircleUnion ψ Z :=
  isCircleUnion_of_isCompact_of_isLocallyEuclidean ψ hZ hcomp
    (isLocallyEuclidean_of_isLocalArcEmbedding ψ hZ harc)

/-- **The corrected classification input of the smooth level-set chapter.**

This is `Work.Smooth.Morse.CompactOneManifoldInput` with the local hypothesis repaired: a compact
subset of the surface which is locally Euclidean of dimension one (rather than merely "locally an
arc" in the weak sense of `Work.Smooth.Morse.IsLocalArc`, which also admits `U = Set.univ` and
therefore arbitrary injectively parametrised compact subsets of `ℝ³`) is a finite disjoint union of
embedded circles of the surface. -/
def CompactOneManifoldInput' (ψ : Submission.Diffeo) : Prop :=
  ∀ Z : Set R3, Z ⊆ (Work.Smooth.Morse.torus ψ).carrier → IsCompact Z →
    IsLocallyEuclidean Z → IsCircleUnion ψ Z

/-- **The corrected classification input holds, for every diffeomorphism.** -/
theorem compactOneManifoldInput'_holds (ψ : Submission.Diffeo) : CompactOneManifoldInput' ψ :=
  fun _ hZ hcomp hloc => isCircleUnion_of_isCompact_of_isLocallyEuclidean ψ hZ hcomp hloc

/-- **The corrected classification input, in the vocabulary of the repaired local-arc
hypothesis.** -/
theorem compactOneManifoldInput'_holds_of_isLocalArcEmbedding (ψ : Submission.Diffeo) :
    ∀ Z : Set R3, Z ⊆ (Work.Smooth.Morse.torus ψ).carrier → IsCompact Z →
      IsLocalArcEmbedding ψ Z → IsCircleUnion ψ Z :=
  fun _ hZ hcomp harc => isCircleUnion_of_isCompact_of_isLocalArcEmbedding ψ hZ hcomp harc

end

end Work.Smooth.OneManifold
