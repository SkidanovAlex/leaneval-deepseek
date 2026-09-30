import Mathlib
import Submission.Work.Serre.cylCMidDefs
import Submission.Work.Serre.CMidCollarDefs
import Submission.Work.Serre.C1Cyl
import Submission.Work.Serre.cylCollarShrink
import Submission.Work.Serre.relCohPreimageDefs
import Submission.Work.Serre.DiscPair.relPairFiveRat

/-!
# The point-collared pair `(cylBot q, q⁻¹{b}) ⊆ (Ucol q b, PUcol q b) ⊆ (CMid q b, Pmid q b)`

Vocabulary for the proof of `Work.RatHurewicz.cylCMidHomologyDecompSucc`: the pair
`(CMid q b, Pmid q b)` of the mapping cylinder modulo the "old part" `CMid q b = A ∪ P` (bottom copy
together with the fibre cone over `b`), its collar part `Ucol q b = CMid q b ∩ cylCollar q`, and the
cone `Pmid q b` over `b`.

* `PBot q b = q⁻¹{b}`, viewed inside the bottom copy `cylBot q`;
* `Pmid q b`, `Ucol q b`, `PUcol q b`;
* `collarIncl q b : cylBot q → Ucol q b`, the inclusion of the bottom copy into the collar part,
  and `collarIncl_mapsTo` (`PBot → PUcol`);
* `interior_Pmid_union_Ucol`: the interiors of `Pmid` and `Ucol` cover `CMid` — the classical
  excision hypothesis.
-/

namespace Work.RatHurewicz

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits

variable {B : Type} [TopologicalSpace B] {X : Type} [TopologicalSpace X]

/-- The fibre `q ⁻¹'{b}` of `q`, viewed inside the bottom copy `cylBot q`. -/
abbrev PBot (q : C(X, B)) (b : B) : Set ↥(Work.Serre.cylBot q) :=
  {y | (y : Work.Serre.cyl q) ∈ (Work.Serre.cylRetract q) ⁻¹' ({b} : Set B)}

/-- The fibre cone `(cylRetract q) ⁻¹'{b}`, viewed inside `CMid q b`. -/
abbrev Pmid (q : C(X, B)) (b : B) : Set ↥(Work.Serre.CMid q b) :=
  {y | (y : Work.Serre.cyl q) ∈ (Work.Serre.cylRetract q) ⁻¹' ({b} : Set B)}

/-- The collar part of `CMid q b`. -/
abbrev Ucol (q : C(X, B)) (b : B) : Set ↥(Work.Serre.CMid q b) :=
  {y | (y : Work.Serre.cyl q) ∈ Work.Serre.cylCollar q}

/-- The fibre cone, viewed inside the collar part `Ucol q b`. -/
abbrev PUcol (q : C(X, B)) (b : B) : Set ↥(Ucol q b) :=
  {y | (y : ↥(Work.Serre.CMid q b)) ∈ Pmid q b}

/-- **The inclusion of the bottom copy into the collar part of `CMid`.** -/
def collarIncl (q : C(X, B)) (b : B) : C(↥(Work.Serre.cylBot q), ↥(Ucol q b)) where
  toFun y := ⟨⟨(y : Work.Serre.cyl q), Or.inl y.2⟩, Work.Serre.cylBot_subset_cylCollar q y.2⟩
  continuous_toFun := Continuous.subtype_mk (Continuous.subtype_mk continuous_subtype_val _) _

@[simp] theorem collarIncl_coe (q : C(X, B)) (b : B) (y : ↥(Work.Serre.cylBot q)) :
    ((collarIncl q b y : ↥(Ucol q b)) : Work.Serre.cyl q) = (y : Work.Serre.cyl q) := rfl

@[simp] theorem collarIncl_mid (q : C(X, B)) (b : B) (y : ↥(Work.Serre.cylBot q)) :
    ((collarIncl q b y : ↥(Ucol q b)) : ↥(Work.Serre.CMid q b))
      = ⟨(y : Work.Serre.cyl q), Or.inl y.2⟩ := rfl

theorem collarIncl_mapsTo (q : C(X, B)) (b : B) :
    Set.MapsTo (collarIncl q b) (PBot q b) (PUcol q b) :=
  fun y hy => hy

/-- **The excision hypothesis**: the interiors of the fibre cone and of the collar part cover
`CMid q b`. -/
theorem interior_Pmid_union_Ucol (q : C(X, B)) (b : B) :
    interior (Pmid q b) ∪ interior (Ucol q b) = Set.univ :=
  Work.Serre.CMidCollar.interior_union_eq_univ q b

end Work.RatHurewicz
