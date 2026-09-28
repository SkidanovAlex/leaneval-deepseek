import Mathlib
import Submission.Work.Serre.ThomCylDefs
import Submission.Work.Serre.DiscPair.cylPairDefs
import Submission.Work.Serre.cylRestrictHomeo
import Submission.Work.RatHurewicz.AttachPush.CellInterior
import Submission.Work.Serre.DiscPair.oldPartRelCohIso

/-!
# The "old part" identification for the mapping cylinder of an attachment

For `q : C(X, attachCells (D-2) Γ ι f)` and `S := Set.range (attachIncl (D-2) Γ ι f)`, the pair

  `( (cylRetract q) ⁻¹' S ∪ Set.range (cylIncl q),  Set.range (cylIncl q) )`

inside the mapping cylinder `cyl q` has the same relative rational cohomology as the pair

  `( cyl (restrictFibre q S),  Set.range (cylIncl (restrictFibre q S)) )`

of the mapping cylinder of the *restricted* fibration `q|_S`.  This is the identification that
transports the induction hypothesis for the Thom/Serre tower from the restricted fibration to the
pair of the cell step: the part `(cylRetract q) ⁻¹' S` is precisely the piece of the cylinder lying
over the old space `Γ`, and relative to the bottom copy `range (cylIncl q)` it is the cylinder of
the restricted map.

The mathematical content is:

* the closed-cover identification `(cylRetract q) ⁻¹' S ∪ Set.range (cylIncl q)` with the closed
  subspaces `(cylRetract q) ⁻¹' S` and `Set.range (cylIncl q)` (both are preimages of closed sets,
  so this is an excision in relative cohomology), together with
* the homeomorphism `cylRestrictHomeo q S` between `cyl (restrictFibre q S)` and
  `(cylRetract q) ⁻¹' S`, which carries `Set.range (cylIncl (restrictFibre q S))` onto
  `(cylRetract q) ⁻¹' S ∩ Set.range (cylIncl q)`, and
  `relCohHomeomorph`, the invariance of relative cohomology under a homeomorphism of pairs.

The proof of the resulting statement is carried out in the sibling development
`Submission/Work/Serre/DiscPair/oldPartRelCohIso.lean` (`Work.Serre.DiscPair.oldPartRelCohIso`),
which realises exactly this pair of cohomology groups: it works on rational homology (collar
deformations of the disc-pair bundle, open-cover excisions `Work.Serre.csrExcisionRat`, the
homeomorphism `Work.Serre.cylRestrictHomeo`) and dualises with the rational universal coefficient
theorem `Work.Serre.relKronEquiv`.  We import it rather than rebuild it.
-/

namespace Work.RatHurewicz

theorem oldPartIdentification (D : ℕ) (hD : 2 ≤ D) {Γ : Type} [TopologicalSpace Γ] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D - 2), Γ)) {X : Type} [TopologicalSpace X]
    (q : C(X, Work.RatHurewicz.attachCells (D - 2) Γ ι f)) (k : ℕ) :
    Nonempty (CategoryTheory.Iso
      (Work.Thom.RelCoh ℚ k
        ↥((Work.Serre.cylRetract q) ⁻¹' Set.range (Work.RatHurewicz.attachIncl (D - 2) Γ ι f)
          ∪ Set.range (Work.Serre.cylIncl q))
        {x | (x : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)})
      (Work.Thom.RelCoh ℚ k
        (Work.Serre.cyl (Work.Serre.restrictFibre q
          (Set.range (Work.RatHurewicz.attachIncl (D - 2) Γ ι f))))
        (Set.range (Work.Serre.cylIncl (Work.Serre.restrictFibre q
          (Set.range (Work.RatHurewicz.attachIncl (D - 2) Γ ι f))))))) :=
  Work.Serre.DiscPair.oldPartRelCohIso D hD ι f q k

end Work.RatHurewicz
