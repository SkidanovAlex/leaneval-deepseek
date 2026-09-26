import Mathlib
import Submission.Work.Smooth.Morse.Defs
import Submission.Work.Smooth.SphereJordan.LocalArc.Basic
import Submission.Work.Smooth.SphereJordan.LocalArc.IsLocallyArcOfIsOpen
import Submission.Work.SurgeryInvariance.Defs
import Submission.Work.CoreTopology.Basic

/-!
# The classification of compact one-dimensional subsets of a surface: vocabulary

This chapter proves the classification input of the smooth level-set chapter,
`Work.Smooth.Morse.CompactOneManifoldInput`:

```
def CompactOneManifoldInput (ψ : Submission.Diffeo) : Prop :=
  ∀ Z : Set R3, IsCompact Z → IsLocalArc ψ Z → IsCircleUnion ψ Z
```

A compact subset of the surface `F = torus ψ` which is *locally an arc* is a finite disjoint union
of embedded circles.  The proof is the classification of compact `1`-manifolds (a compact
`1`-manifold without boundary is a finite disjoint union of circles), in the form needed here.

## The local hypothesis

`Work.Smooth.Morse.IsLocalArc ψ Z` says that at every point `x ∈ Z` there is an open set `U` of
the surface and an injective continuous arc `ρ` mapping some open `I ⊆ ℝ` *onto* `U ∩ Z`.

Two remarks, which are the reason for the definitions in this file:

* the local structure that the applications actually produce (`regular level sets`, via the
  implicit function theorem) is the local structure of a **`1`-manifold**: a neighbourhood of `x`
  in `Z` homeomorphic to `ℝ`.  We call this `IsLocallyEuclidean` below; it is the hypothesis with
  which the classification is stated, and it is what makes `Z` a compact topological `1`-manifold
  without boundary.
* the literal definition of `IsLocalArc` also admits `U = Set.univ`, in which case it only asks
  that `Z` be (globally) the image of an injective continuous arc.  An injective continuous map
  from an open subset of `ℝ` need not be an embedding (a spiral can converge to its own centre),
  so that hypothesis is strictly weaker than "locally Euclidean", and the literal statement
  `∀ Z, IsCompact Z → IsLocalArc ψ Z → IsCircleUnion ψ Z` is **false**; see
  `Submission/Work/Smooth/OneManifold/Counterexample.lean` and the README for the counterexample.
  `IsLocalArcEmbedding` below is the minimal repair of the local hypothesis which rules out the
  degenerate case: the arc is required to be an embedding onto the piece of `Z` that it covers.

## Main definitions

* `IsLocallyEuclidean Z` — every point of `Z` has a neighbourhood in `Z` homeomorphic to `ℝ`;
  the hypothesis of the classification `isCircleUnion_of_isCompact_of_isLocallyEuclidean`;
* `IsLocalArcEmbedding ψ Z` — the repair of `Work.Smooth.Morse.IsLocalArc`: the local arc
  conditions together with the requirement that the arc be an open map onto `Z`;
  `isLocallyEuclidean_of_isLocalArcEmbedding` turns it into `IsLocallyEuclidean`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.Smooth.OneManifold

noncomputable section

/-- **`Z` is locally Euclidean of dimension one** (a topological `1`-manifold, as a subspace of
`ℝ³`): every point of `Z` has an open neighbourhood, in `Z`, homeomorphic to `ℝ`.

This is the same as `Work.Smooth.SphereJordan.IsLocallyArc ↥Z`; the name records that this is the
local model of a topological `1`-manifold, and is the hypothesis under which the classification of
compact one-manifolds is stated in this chapter. -/
def IsLocallyEuclidean (Z : Set R3) : Prop := Work.Smooth.SphereJordan.IsLocallyArc Z

/-- **An arc chart at a point of `Z`**: an open neighbourhood of `x` in `Z` together with a
homeomorphism of `ℝ` onto it.  This is `Work.Smooth.SphereJordan.ArcChart` with its type argument
specialised to `↥Z`. -/
abbrev ArcChartAt (Z : Set R3) (x : Z) := Work.Smooth.SphereJordan.ArcChart Z x

theorem isLocallyEuclidean_iff_isLocallyArc (Z : Set R3) :
    IsLocallyEuclidean Z ↔ Work.Smooth.SphereJordan.IsLocallyArc Z := Iff.rfl

theorem isLocallyEuclidean_iff (Z : Set R3) :
    IsLocallyEuclidean Z ↔ ∀ x : Z, Nonempty (ArcChartAt Z x) := Iff.rfl

/-- **The repaired local-arc hypothesis.**

It is `Work.Smooth.Morse.IsLocalArc ψ Z`, with the following two changes:

* the two conditions "the arc lies in `Z`" and "the arc covers `U ∩ Z`" are combined into
  `ρ '' I = U ∩ Z`, and
* the arc is required to be an **open map onto the part of `Z` that it cuts out**: for every open
  `O ⊆ ℝ` the image `ρ '' (O ∩ I)` is `W ∩ Z` for some `W` open in the surface.

The second condition (together with the covering) says exactly that `ρ` is a homeomorphism of `I`
onto `U ∩ Z`, hence that `Z` is locally Euclidean
(`isLocallyEuclidean_of_isLocalArcEmbedding`).  It is satisfied by every local arc produced by the
implicit function theorem for a regular level set (there the arc parametrises a graph), and it
fails precisely in the degenerate case `U = Set.univ` with `Z` a self-limiting spiral. -/
def IsLocalArcEmbedding (ψ : Submission.Diffeo) (Z : Set R3) : Prop :=
  ∀ x ∈ Z, ∃ (U : Set R3) (I : Set ℝ) (s₀ : ℝ) (ρ : ℝ → R3),
    Work.SurgeryInvariance.IsOpenInCarrier (Work.Smooth.Morse.torus ψ) U ∧ IsOpen I ∧ x ∈ U ∧
      s₀ ∈ I ∧ ContinuousOn ρ I ∧ ρ s₀ = x ∧ Set.InjOn ρ I ∧ ρ '' I = U ∩ Z ∧
      (∀ O : Set ℝ, IsOpen O → ∃ W : Set R3,
        Work.SurgeryInvariance.IsOpenInCarrier (Work.Smooth.Morse.torus ψ) W ∧
          W ∩ Z = ρ '' (O ∩ I))

/-- **`Z` is a finite disjoint union of embedded circles of the surface `F = torus ψ`.**

This is `Work.Smooth.Morse.IsCircleUnion`, restated here so that the chapter has the notion under
its own name. -/
abbrev IsCircleUnion (ψ : Submission.Diffeo) (Z : Set R3) : Prop :=
  Work.Smooth.Morse.IsCircleUnion ψ Z

/-- The empty set is a (zero-fold) circle union. -/
theorem isCircleUnion_empty (ψ : Submission.Diffeo) : IsCircleUnion ψ (∅ : Set R3) := by
  refine ⟨0, Fin.elim0, ?_, ?_, ?_⟩
  · intro i; exact i.elim0
  · intro i; exact i.elim0
  · simp

/-- `V` is open in the subspace `Z ⊆ ℝ³`. -/
def IsOpenInSet (Z V : Set R3) : Prop := IsOpen (Subtype.val ⁻¹' V : Set Z)

/-- `C` is a connected component of `Z` in the sense that it is the connected component of one of
its points. -/
def IsComponentOf (Z C : Set R3) : Prop := ∃ x : Z, C = Subtype.val '' connectedComponent x

theorem isOpenInSet_iff {Z V : Set R3} : IsOpenInSet Z V ↔ IsOpen (Subtype.val ⁻¹' V : Set Z) :=
  Iff.rfl

end

end Work.Smooth.OneManifold
