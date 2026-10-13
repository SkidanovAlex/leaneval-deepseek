/-
Area DSCOH (curric-46) — the normalization comparison: the comparison maps between the
all-tuples, semi-ordered and ordered Čech complexes.

* `semiProj` : the projection from Mathlib's unnormalized Čech complex (all tuples, repetitions
  allowed) onto the semi-ordered complex (nondecreasing tuples);
* `ordProj` : the projection from the semi-ordered complex onto the ordered complex (strictly
  increasing tuples, i.e. subsets);
* `ordIncl` : the "zero off the strictly increasing tuples" map from the ordered complex to the
  semi-ordered complex, a section of `ordProj`.

The mathematical content proved elsewhere: `ordProj ≫ ordIncl = 𝟙` and
`ordIncl ≫ ordProj` homotopic to the identity (the classical degenerate-simplex argument), and
`semiProj` a quasi-isomorphism (the classical sorting/degeneracy argument).
-/
import Submission.Work.DSCOH.Norm.SemiOrd

namespace Work.DSCOH.Norm

open CategoryTheory Limits Opposite TopologicalSpace
open scoped Simplicial BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

universe u v w

variable {X : Type u} [TopologicalSpace X] {A : Type v} [CommRing A]
variable {ι : Type w} [LinearOrder ι] [HasProducts (ModuleCat A)]

/-- The projection from the all-tuples Čech term in degree `n` onto the semi-ordered term:
the `x`-th component of Mathlib's term is read off at the same tuple `x` for `x` nondecreasing. -/
noncomputable def semiProj (P : (Opens X)ᵒᵖ ⥤ ModuleCat A) (U : ι → Opens X) (n : ℕ) :
    ((cechComplexFunctor U).obj P).X n ⟶ semiTerm P U n :=
  Pi.lift fun x : SemiIdx ι n => Pi.π (fun y : (Fin (n + 1) → ι) => tupleMod P U y) x.val

/-- The projection from the semi-ordered term onto the ordered term. -/
noncomputable def ordProj (P : (Opens X)ᵒᵖ ⥤ ModuleCat A) (U : ι → Opens X) (n : ℕ) :
    semiTerm P U n ⟶ ordTerm P U n :=
  Pi.lift fun x : OrdIdx ι n => Pi.π (fun y : SemiIdx ι n => tupleMod P U y.val)
    ⟨x.val, x.property.monotone⟩

/-- The inclusion of the ordered term into the semi-ordered term: the identity on strictly
increasing tuples and zero on the other (not strictly increasing) tuples. -/
noncomputable def ordIncl (P : (Opens X)ᵒᵖ ⥤ ModuleCat A) (U : ι → Opens X) (n : ℕ) :
    ordTerm P U n ⟶ semiTerm P U n :=
  Pi.lift fun x : SemiIdx ι n =>
    if h : StrictMono x.val then
      (Pi.π (fun y : OrdIdx ι n => tupleMod P U y.val) ⟨x.val, h⟩ :
        ordTerm P U n ⟶ tupleMod P U x.val)
    else 0

end Work.DSCOH.Norm
