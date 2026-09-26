import Mathlib
import Submission.Work.Topology.SphereSlicing.Defs

/-!
# `RemovesOneCurve` from `CleanOneCurve`

The single cut-and-paste step of Pardon's second innermost argument exists in two vocabularies
in this development:

* `Work.InnermostDisk.RemovesOneCurve P` — the form in which it is consumed: an
  `InnermostDisc P S` (an essential curve `α` spanning a disc `e` inside a set `S`, whose
  interior meets `F` only in inessential curves) with at least one intersection curve can be
  replaced by an `InnermostDisc P S'` with the same boundary curve and strictly fewer
  intersection curves.
* `Work.Topology.SphereSlicing.CleanOneCurve P` — the form in which it is proved: the same
  statement for the local model `SliceDisc P`, an embedded disc in `ℝ³` whose boundary is a
  simple closed curve of `F` and whose interior meets `F` only in inessential simple curves.
  The ambient set `S`, the containment of the disc in `S` and the essentiality of the boundary
  curve are *not* part of `SliceDisc`, because the cut-and-paste never uses them.

This file proves that the local form implies the consumed form.  The passage is purely
structural: the two structures differ only in the fields `essential` (present in
`InnermostDisc`, absent in `SliceDisc`), `mem` and `e_mem` (the containment of the curve and of
the disc in the ambient set `S`), and in that `SliceDisc` is not conditioned on a set at all.
So an `InnermostDisc` is a `SliceDisc` (forget `essential`, `mem`, `e_mem`), the cut-and-paste
`CleanOneCurve` produces a `SliceDisc` with the same boundary and fewer curves, and that
`SliceDisc` is turned back into an `InnermostDisc` at the ambient set `S' = Set.range e'` —
which *is* the geometric meaning of the operation: the replacement disc is the new object, and
it is its own ambient set as far as the datum is concerned.  The essentiality of the boundary
is inherited from the original disc, whose boundary is unchanged
(`Work.InnermostDisk.cleansDiscs_of_removesOneCurve` then iterates the step to obtain
`Work.InnermostDisk.CleansDiscs P`).

The geometric content of Pardon's cut-and-paste is therefore entirely localized in
`CleanOneCurve P`, which is the statement proved in
`Work.Topology.SphereSlicing.Clean.*`; nothing about the ambient sphere survives the passage.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open Work.CoreTopology
open Work.InnermostDisk

namespace Work.Topology.SphereSlicing

noncomputable section

/-- **The single cut-and-paste step in the vocabulary it is proved in implies the single
cut-and-paste step in the vocabulary it is consumed in.**

`CleanOneCurve P` (a local statement about an embedded disc in `ℝ³` whose interior meets `F`
only in inessential simple curves) yields `RemovesOneCurve P` (the same statement for the
innermost-disc datum `InnermostDisc P S`).

The two structures differ only by the extra fields `essential`, `mem` and `e_mem` of
`InnermostDisc`, which the cut-and-paste does not touch: the datum is forgetfully regarded as a
`SliceDisc`, cleaned, and the resulting `SliceDisc` is re-read as an innermost datum at the
ambient set `Set.range e'` (the replacement disc is its own ambient set).  The boundary curve is
unchanged, so its essentiality is inherited from the original datum. -/
theorem removesOneCurve_of_cleanOneCurve {P : Work.CoreTopology.ParamTorus}
    (h : Work.Topology.SphereSlicing.CleanOneCurve P) :
    Work.InnermostDisk.RemovesOneCurve P := by
  intro S D hD
  -- Forget the fields of the innermost datum that `SliceDisc` does not have.
  let Ds : SliceDisc P :=
    { α := D.α, simple := D.simple, e := D.e, inj := D.inj, boundary := D.boundary,
      ι := D.ι, fintype := D.fintype, curves := D.curves,
      curves_simple := D.curves_simple, curves_inessential := D.curves_inessential,
      curves_disjoint := D.curves_disjoint, curves_subset := D.curves_subset,
      covers := D.covers }
  obtain ⟨Ds', hα, hlt⟩ := h Ds hD
  -- Re-read the cleaned disc as an innermost datum, at the ambient set `Set.range Ds'.e`.
  refine ⟨Set.range Ds'.e,
    { α := Ds'.α, simple := Ds'.simple, essential := hα ▸ D.essential,
      mem := fun t => ⟨circlePoint t, Ds'.boundary t⟩,
      e := Ds'.e, inj := Ds'.inj, boundary := Ds'.boundary,
      e_mem := fun z => ⟨z, rfl⟩,
      ι := Ds'.ι, fintype := Ds'.fintype, curves := Ds'.curves,
      curves_simple := Ds'.curves_simple, curves_inessential := Ds'.curves_inessential,
      curves_disjoint := Ds'.curves_disjoint, curves_subset := Ds'.curves_subset,
      covers := Ds'.covers }, ?_, ?_⟩
  · -- the boundary is unchanged
    exact hα
  · -- and the number of intersection curves strictly decreased
    exact hlt

end

end Work.Topology.SphereSlicing
