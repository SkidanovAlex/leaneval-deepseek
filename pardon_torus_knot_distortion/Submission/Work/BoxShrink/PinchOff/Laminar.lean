import Submission.Work.BoxShrink.PinchOff.Unconditional
import Submission.Work.BoxShrink.PinchOff.exists_disjoint_refinement

/-!
# A laminar covering of the slice by discs inside the box

`Unconditional.lean` gives Pardon's Lemma 3 conclusion for a slice covered by the interiors of
finitely many **pairwise disjoint** discs inside the box.  This module removes the disjointness
hypothesis, replacing it by the *laminar* structure which a family of discs bounded by level circles
of the slicing coordinate actually has (two such discs are disjoint or one contains the other -- the
Jordan separation theorem for the surface, `Work.Smooth.JordanSeparation`):

* `IsLaminar` -- the list of discs is laminar (for distinct members: disjoint carriers, or one
  carrier inside the other's interior, or equal interiors);
* **`SliceDiscCovering`** -- the structural datum of the circles-only case: a finite laminar family
  of embedded discs of the surface, each lying in the box, whose *interiors* cover the slice;
* **`bubbleHalf_of_sliceDiscCovering`** -- Pardon's Lemma 3 conclusion from such a covering;
* `smoothHalfS_of_sliceDiscCovering` -- the global conditional form.

The passage from laminar to disjoint is the abstract combinatorial lemma
`Work.BoxShrink.PinchOff.exists_disjoint_refinement`: keeping one representative per maximal element
of a laminar family preserves the union of the interiors and makes the carriers pairwise disjoint (a
disc contained in the interior of another is redundant, because its interior is contained in the
outer one's).
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

namespace Work.BoxShrink.PinchOff

noncomputable section

variable {ψ : Submission.Diffeo} {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}

/-- **A laminar family of embedded discs**: for distinct members, either their carriers are disjoint,
or one carrier lies in the interior of the other, or their interiors are equal. -/
def IsLaminar (L : List (Work.SurgeryInvariance.DiscRegion (surface ψ))) : Prop :=
  ∀ D ∈ L, ∀ D' ∈ L, D ≠ D' →
    Disjoint D.carrier D'.carrier ∨ D.carrier ⊆ D'.interior ∨ D'.carrier ⊆ D.interior ∨
      D.interior = D'.interior

/-- **The structural datum of the circles-only case**: a finite laminar family of embedded discs of
the surface, each lying in the region inside the box, whose *interiors* cover the slice.

For the slice circles `C_i` of the challenge one obtains such a family by taking, for each `C_i`, a
disc `D_i` slightly larger than the disc `Δ_i` bounded by `C_i` (so that `C_i ⊆ Δ̄_i ⊆ D_i.interior`
and `D_i.carrier ⊆ Ω`); the discs `Δ_i` are laminar (Jordan), hence so are the `D_i`.  This is the
bookkeeping discussed in `README.md` §3; it is *not* formalised here. -/
def SliceDiscCovering (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (u : ℝ) : Prop :=
  ∃ L : List (Work.SurgeryInvariance.DiscRegion (surface ψ)), L.Nodup ∧ IsLaminar L ∧
    (∀ D ∈ L, D.carrier ⊆ Omega ψ s c σ) ∧
    (∀ x ∈ Sigma ψ s c σ u, ∃ D ∈ L, x ∈ D.interior)

/-- **Pardon's Lemma 3 conclusion from a laminar covering of the slice by discs inside the box.**

The proof prunes the laminar family to a pairwise disjoint one with the same union of interiors
(`Work.BoxShrink.PinchOff.exists_disjoint_refinement`, applied to `carrier` and `interior`), and then
applies the unconditional disjoint-discs theorem `bubbleHalf_of_slice_in_discs`. -/
theorem bubbleHalf_of_sliceDiscCovering (h : SliceDiscCovering ψ s c σ u) :
    Work.BoxShrink.Bubble.BubbleHalf (surface ψ) s c σ u := by
  obtain ⟨L, hnodup, hlaminar, hsub, hslice⟩ := h
  obtain ⟨L', hL'nodup, hsub', hdisj, hcover⟩ :=
    exists_disjoint_refinement L
      (fun D : Work.SurgeryInvariance.DiscRegion (surface ψ) => D.carrier)
      (fun D => D.interior)
      (fun D _ => Work.SurgeryInvariance.DiscRegion.interior_subset_carrier D)
      hlaminar
  refine bubbleHalf_of_slice_in_discs L' hL'nodup hdisj
    (fun D hD => hsub D (hsub' D hD)) ?_
  intro x hx
  obtain ⟨D, hD, hxD⟩ := hslice x hx
  obtain ⟨D', hD', hle⟩ := hcover D hD
  exact ⟨D', hD', hle hxD⟩

/-- **The deliverable, from the hypothesis that the slice is always laminar-covered by discs inside
the box.**  With `smoothHalfS_of_sliceDiscCovering` the whole reduction chain of `Basic.lean` is
available: Pardon's equation (1) and the general position of the box-sphere trace then give the
challenge. -/
theorem smoothHalfS_of_sliceDiscCovering
    (h : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      SliceDiscCovering ψ s c σ u) :
    Work.BoxShrink.Pinch.SmoothHalfS :=
  fun ψ s c σ u _ _ => bubbleHalf_of_sliceDiscCovering (h ψ s c σ u)

/-! ## The challenge, from a laminar covering of every slice -/

/-- **Pardon's theorem, from the hypothesis that the slice is always laminar-covered by discs inside
the box.**  Everything else of the reduction is proved: the two classical inputs are the parameters
`h1` (Pardon's equation (1)) and `hnice` (the general position of the box-sphere trace), together
with the two classical inputs of the crux (`hdisc`, `hclean`, `hae`). -/
theorem pardon_torus_knot_distortion_of_sliceDiscCovering
    (hdisc : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.InnermostDisk.CleansInSphere
        (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph)
        (Work.BoxShrink.Core.cutDisc s c σ u))
    (h1 : Work.BoxShrink.Pinch.Equation1Input) (hnice : Work.BoxShrink.Pinch.BoxSliceNice)
    (h : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      SliceDiscCovering ψ s c σ u)
    (hclean : Work.BoxShrink.CleansDiscsAll) (hae : Work.BoxShrink.AeSlicedAll) :
    ∀ (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q) (K : Knot)
      (hclass : ∃ Φ : AmbientIsotopy, ∃ σ : CircleReparam,
        ∀ t, Φ.H 1 (K.curve t) = standardTorusCurve p q (σ.f t)),
      (1 / 160 : ℝ≥0∞) * (Nat.min p q : ℝ≥0∞) ≤ distortion K :=
  Work.BoxShrink.Pinch.pardon_torus_knot_distortion_of_smoothHalfS hdisc
    (smoothHalfS_of_sliceDiscCovering h) hclean hae

end

end Work.BoxShrink.PinchOff
