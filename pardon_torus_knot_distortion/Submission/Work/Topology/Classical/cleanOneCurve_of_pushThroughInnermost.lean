import Mathlib
import Submission.Work.Topology.Classical.Defs

/-!
# `CleanOneCurve P` from the cut-and-paste `PushThroughInnermost P`

The cut-and-paste of Pardon's second innermost argument, isolated in
`Work.Topology.Classical.PushThroughInnermost`, is stated on the local model
`Work.Topology.SphereSlicing.SliceDisc P` of an embedded disc in `ℝ³`: it replaces the disc `D`
by a disc `e'` with the *same boundary* `α = D.α` which no longer meets the surface along one of
its intersection curves `D.curves j`, all other curves being kept.

This file records the (purely combinatorial) consequence on the *intersection count*: the family
of curves left in the new disc is the family of `D` with the single index `j` removed, so a
`SliceDisc` with strictly fewer intersection curves exists.  That is exactly
`Work.Topology.SphereSlicing.CleanOneCurve P`, the cleaning half of the classical input of
Pardon's Lemma 4.2.

The new disc is `e'`, with index type `{i : D.ι // i ≠ j}` and curves `i ↦ D.curves i`; its
interior meets `F` only along those curves by the last clause of `PushThroughInnermost`, it is
embedded and has boundary `α` by the first two clauses, it inherits the simplicity,
inessentiality and disjointness of the curves of `D`, and the subset clause for the curves other
than `j` is the third clause of `PushThroughInnermost`.  The strict decrease of the cardinality is
`Fintype.card_subtype_lt` at the removed index.

Note that *no* use is made of the innermost-ness of `j` (`F.rank`), of the essentiality of `α`, or
of the ambient sphere: all of that is inside the classical input `PushThroughInnermost`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open Work.CoreTopology
open Work.InnermostDisk
open Work.Topology.SphereSlicing

namespace Work.Topology.Classical

/-- **The cut-and-paste removes one intersection curve.**  If `PushThroughInnermost P` holds, then
an embedded disc `D` in `ℝ³` whose boundary `α` is a simple closed curve of `F = P.carrier` and
whose interior meets `F` only along the finitely many pairwise disjoint inessential simple curves
`D.curves i` (`D.ι` nonempty) can be replaced by such a disc with the *same* boundary and strictly
fewer intersection curves: take the disc `e'` supplied by the cut-and-paste at the eliminated index
`j`, whose curves are those of `D` other than `j`.

Hence `Work.Topology.SphereSlicing.CleanOneCurve P`. -/
theorem cleanOneCurve_of_pushThroughInnermost {P : Work.CoreTopology.ParamTorus}
    (h : Work.Topology.Classical.PushThroughInnermost P) :
    Work.Topology.SphereSlicing.CleanOneCurve P := by
  classical
  intro D hcard
  obtain ⟨j, e', h_inj, h_bd, h_sub, h_int⟩ := h D hcard
  -- removing the eliminated index `j` strictly decreases the number of intersection curves
  have hcard' : Fintype.card {i : D.ι // i ≠ j} < Fintype.card D.ι :=
    Fintype.card_subtype_lt (p := fun i : D.ι => i ≠ j) (x := j) (by simp)
  exact ⟨{
    α := D.α
    simple := D.simple
    e := e'
    inj := h_inj
    boundary := h_bd
    ι := {i : D.ι // i ≠ j}
    fintype := inferInstance
    curves := fun k => D.curves k.1
    curves_simple := fun k => D.curves_simple k.1
    curves_inessential := fun k => D.curves_inessential k.1
    curves_disjoint := fun k l hkl =>
      D.curves_disjoint (fun hh : k.1 = l.1 => hkl (Subtype.ext hh))
    curves_subset := fun k => h_sub k.1 k.2
    covers := fun z hz hmem => by
      obtain ⟨i, hi, hcur⟩ := h_int z hz hmem
      exact ⟨⟨i, hi⟩, hcur⟩
  }, rfl, hcard'⟩

end Work.Topology.Classical
