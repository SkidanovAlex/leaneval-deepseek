import Mathlib
import ChallengeDeps
import Submission.Blueprint.Interfaces
import Submission.Work.ANALYTIC.Bounded

/-!
# A model of `∏_ℕ ℤ` with explicit sections

In this development `∏_ℕ ℤ` is used in REFS/03 §2–§3 as the codomain of the comparison
`∏^bnd ℤ ⟶ ∏ℤ`.  The product `Work.ANALYTIC.prodZ` of copies of the constant sheaf is *definitionally*
a product, so its sections are opaque; for the purpose of AN2 it is much more convenient to model
`∏ℤ` by the sheaf whose `S`-points are the `ℕ`-indexed families of continuous `ℤ`-valued functions
on `S`, i.e. by the sheaf of continuous maps `S → ℤ^ℕ` (the currying isomorphism).

This file only defines the presheaf; the sheaf condition is proved in
`Submission/Work/ANALYTIC/prodZPresheaf_sheaf.lean`, and the resulting object
`prodZModel : LightCondAb` (with `boundedSeqSet S ⊆ ℕ → C(S,ℤ)` as its `S`-points) is used for AN2.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed

noncomputable section

namespace Work.ANALYTIC

open _root_.LightCondensed _root_.LightCondensed.Solid

/-- The presheaf of `ℕ`-indexed families of continuous `ℤ`-valued functions; it is `∏_ℕ ℤ`
(the constant sheaf `ℤ`), modelled with explicit sections. -/
def prodZPresheaf : LightProfiniteᵒᵖ ⥤ ModuleCat ℤ where
  obj S := ModuleCat.of ℤ (ℕ → C(S.unop, ℤ))
  map f := ModuleCat.ofHom
    { toFun := fun x n => (x n).comp (LightProfinite.toTopCat.map f.unop).hom
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_id _ := rfl
  map_comp _ _ := rfl

end Work.ANALYTIC
