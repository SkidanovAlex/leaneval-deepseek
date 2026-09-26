import Submission.Work.Topology.SphereSlicing.Defs

/-!
# The cut-and-paste on the local model, and the innermost disc

`Work.Topology.SphereSlicing.CleanOneCurve P` is the single cut-and-paste of Pardon's second
innermost argument, stated on the local model `Work.Topology.SphereSlicing.SliceDisc P`: an
embedded disc in `ℝ³` whose boundary is a simple closed curve of `F` and whose interior meets `F`
only in finitely many pairwise disjoint inessential simple closed curves.

This file records the two translations between that local model and
`Work.InnermostDisk.InnermostDisc P S`:

* `sliceDiscOfInnermostDisc` — an innermost disc is a `SliceDisc` (forget the essentiality of its
  boundary, the ambient sphere `S` and the containment of the disc in `S`);
* `innermostDiscOfSliceDisc` — a `SliceDisc` whose boundary is *essential* is an innermost disc
  inside the ambient sphere `Set.range e` (the disc is its own ambient sphere, so `mem` and
  `e_mem` are immediate);

and consequently the converse of `Work.Topology.SphereSlicing.removesOneCurve_of_cleanOneCurve` in
the case in which the boundary curve is essential: the cut-and-paste on the local model is
*equivalent* to `Work.InnermostDisk.RemovesOneCurve` on essential discs.  So nothing is lost by
stating the classical input on `SliceDisc`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open Work.CoreTopology
open Work.InnermostDisk

namespace Work.Topology.SphereSlicing

noncomputable section

/-- **An innermost disc is a `SliceDisc`.**  Forgetting the essentiality of the boundary curve,
the ambient sphere and the containment of the disc in it leaves exactly the local model of the
cut-and-paste. -/
def sliceDiscOfInnermostDisc {P : ParamTorus} {S : Set R3} (D : InnermostDisc P S) :
    SliceDisc P where
  α := D.α
  simple := D.simple
  e := D.e
  inj := D.inj
  boundary := D.boundary
  ι := D.ι
  fintype := D.fintype
  curves := D.curves
  curves_simple := D.curves_simple
  curves_inessential := D.curves_inessential
  curves_disjoint := D.curves_disjoint
  curves_subset := D.curves_subset
  covers := D.covers

/-- **A `SliceDisc` with essential boundary is an innermost disc** in the ambient sphere consisting
of its own image: the boundary curve of a disc automatically lies in the image of the disc, and
containment in `<|the range|>` is trivial. -/
def innermostDiscOfSliceDisc {P : ParamTorus} (D : SliceDisc P) (hess : IsEssential P D.α) :
    InnermostDisc P (Set.range D.e) where
  α := D.α
  simple := D.simple
  essential := hess
  mem := fun t => by
    rw [← D.boundary t]
    exact Set.mem_range_self (circlePoint t)
  e := D.e
  inj := D.inj
  boundary := D.boundary
  e_mem := fun z => Set.mem_range_self z
  ι := D.ι
  fintype := D.fintype
  curves := D.curves
  curves_simple := D.curves_simple
  curves_inessential := D.curves_inessential
  curves_disjoint := D.curves_disjoint
  curves_subset := D.curves_subset
  covers := D.covers

@[simp] theorem card_innermostDiscOfSliceDisc {P : ParamTorus} (D : SliceDisc P)
    (hess : IsEssential P D.α) :
    Fintype.card (innermostDiscOfSliceDisc D hess).ι = Fintype.card D.ι := rfl

@[simp] theorem card_sliceDiscOfInnermostDisc {P : ParamTorus} {S : Set R3}
    (D : InnermostDisc P S) :
    Fintype.card (sliceDiscOfInnermostDisc D).ι = Fintype.card D.ι := rfl

/-- **The converse of `removesOneCurve_of_cleanOneCurve`, for essential boundaries.**  Pardon's
single cut-and-paste restated on `InnermostDisc` gives it on `SliceDisc` as soon as the boundary
curve of the disc is essential — which is the only case in which Pardon's argument uses it. -/
theorem cleanOneCurve_essential_of_removesOneCurve {P : ParamTorus} (h : RemovesOneCurve P) :
    ∀ D : SliceDisc P, IsEssential P D.α → 0 < Fintype.card D.ι →
      ∃ D' : SliceDisc P, D'.α = D.α ∧ Fintype.card D'.ι < Fintype.card D.ι := by
  intro D hess hpos
  obtain ⟨S', D', hα, hlt⟩ :=
    h (Set.range D.e) (innermostDiscOfSliceDisc D hess) (by simpa using hpos)
  exact ⟨sliceDiscOfInnermostDisc D', hα, by simpa using hlt⟩

end

end Work.Topology.SphereSlicing
