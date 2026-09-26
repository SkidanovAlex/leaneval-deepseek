import Submission.Work.Topology.SphereSlicing.Defs
import Submission.Work.Topology.SphereSlicing.exists_rank_of_strict_order

/-!
# The nesting rank of a family of disjoint curves

The third classical ingredient of the slicing of a sphere by a surface is the *nesting* of the
curves of `S ∩ F`: of two disjoint simple closed curves of a 2-sphere, one lies on one side of the
other, and this relation is a strict partial order on the finitely many curves.  Only then can one
choose an *innermost* essential curve, which is Pardon's first step.

`Work.Topology.SphereSlicing.SliceData` records the nesting as the existence of a rank function
`rank` decreasing along the relation `NestRel` (`rank j < rank i` whenever the curve `j` meets the
interior of the disc of `i`).  This file records that

* irreflexivity of `NestRel` is automatic (`nestRel_irreflexive`);
* a transitive irreflexive relation on a finite type always admits such a rank
  (`exists_rank_of_nest_rel`, from the pure combinatorics of
  `Work.Topology.SphereSlicing.exists_rank_of_strict_order`).

So a formalizer who establishes the classical nesting in the form "`NestRel` is transitive" gets
the `rank`/`inside` fields of `SliceData` for free.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open Work.CoreTopology
open Work.InnermostDisk

namespace Work.Topology.SphereSlicing

noncomputable section

/-- **The nesting relation of a slicing datum is irreflexive.**  A curve cannot meet the interior
of its own disc: it is the boundary of that disc, and the disc is embedded. -/
theorem nestRel_irreflexive {P : ParamTorus} {S : Set R3} (h : SliceData P S) (i : h.ι) :
    ¬ NestRel h.c h.disc i i :=
  fun hh => absurd (h.inside i i hh) (lt_irrefl _)

/-- **The nesting rank exists as soon as the nesting relation is transitive.**  A transitive,
irreflexive relation on a finite type (here the finite family of components of `S ∩ F`) admits an
`ℕ`-valued rank decreasing along it — the *nesting rank* of the curves. -/
theorem exists_rank_of_nest_rel {ι : Type} [Fintype ι] {P : ParamTorus}
    (c : ι → ClosedCurve P) (disc : ι → C(Disc, R3))
    (hirr : ∀ i : ι, ¬ NestRel c disc i i)
    (htrans : ∀ i j k : ι, NestRel c disc i j → NestRel c disc j k → NestRel c disc i k) :
    ∃ rank : ι → ℕ, ∀ i j : ι, NestRel c disc i j → rank j < rank i :=
  exists_rank_of_strict_order (NestRel c disc) hirr htrans

end

end Work.Topology.SphereSlicing
