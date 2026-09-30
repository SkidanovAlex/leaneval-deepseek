import Mathlib
import Submission.Work.Serre.fibreNonvanishing
import Submission.Work.Serre.csrDefs
import Submission.Work.Serre.ratPairBasic
import Submission.Work.StemsB.RelChainsR
import Submission.Work.Serre.C1Cyl
import Submission.Work.Serre.RatTower.Defs

/-!
# The pair `(cyl q, CMid q b)`: vocabulary

For a map `q : C(X,B)` and a point `b : B`, with `M = cyl q` the mapping cylinder,
`A = range (cylIncl q)` the bottom copy of `X` and `P = (cylRetract q)⁻¹{b}` the fibre of the
retraction over `b` (the cone on the fibre `q⁻¹b`), the set `CMid q b = A ∪ P` is the pair whose
relative homology computes the cofibre of the map of pairs `(X, q⁻¹b) → (B, {b})`.

This file contains only vocabulary (no proofs with `sorry`): the two comparison maps

* `collapseMap q b : C_*(X, q⁻¹b) → C_*(CMid q b, P)` — induced by the bottom inclusion, and
* `retractMap q b : C_*(cyl q, P) → C_*(B, {b})` — induced by the retraction `cylRetract q`,

together with the first map `inclMap q b` of the short exact sequence of the triple
`P ⊆ CMid q b ⊆ cyl q` (the ℚ-valued triple sequence of `Work.Serre.RatTower`).
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Serre

open CategoryTheory CategoryTheory.Limits

noncomputable section

variable {B : Type} [TopologicalSpace B] {X : Type} [TopologicalSpace X]

/-- The fibre of the retraction of the mapping cylinder over `b`. -/
abbrev fibreSet (q : C(X, B)) (b : B) : Set (cyl q) := (cylRetract q) ⁻¹' ({b} : Set B)

/-- `relChainsRPairMap` depends only on the underlying continuous maps. -/
theorem relChainsRPairMap_congr {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} {g g' : C(X, Y)} (hg : g = g')
    (h : Set.MapsTo g A B) (h' : Set.MapsTo g' A B) :
    relChainsRPairMap A B g h = relChainsRPairMap A B g' h' := by
  subst hg
  exact congrArg (fun w => relChainsRPairMap A B g w) (Subsingleton.elim h h')

/-- The inclusion of `X` as the bottom copy of the mapping cylinder, viewed as a map into `CMid q b`
(the bottom copy is contained in `CMid q b`). -/
def toCMid (q : C(X, B)) (b : B) : C(X, ↥(CMid q b)) where
  toFun x := ⟨cylIncl q x, CMid_subset q b ⟨x, rfl⟩⟩
  continuous_toFun := Continuous.subtype_mk (cylIncl q).continuous _

@[simp] lemma toCMid_coe (q : C(X, B)) (b : B) (x : X) :
    ((toCMid q b x : ↥(CMid q b)) : cyl q) = cylIncl q x := rfl

/-- **The collapse** `C_*(X, q⁻¹b) → C_*(CMid q b, P)` induced by the bottom inclusion. -/
noncomputable def collapseMap (q : C(X, B)) (b : B) :
    Work.StemsB.relChainsR ℚ (TopCat.of X) (q ⁻¹' ({b} : Set B)) ⟶
      Work.StemsB.relChainsR ℚ (TopCat.of ↥(CMid q b))
        {y : ↥(CMid q b) | (y : cyl q) ∈ fibreSet q b} :=
  relChainsRPairMap (q ⁻¹' ({b} : Set B))
    {y : ↥(CMid q b) | (y : cyl q) ∈ fibreSet q b}
    (toCMid q b) (by
      intro x hx
      show cylRetract q (cylIncl q x) = b
      rw [show cylRetract q (cylIncl q x) = q x from
        DFunLike.congr_fun (cylRetract_cylIncl q) x]
      simpa using hx)

/-- **The retraction** `C_*(M, P) → C_*(B, {b})` induced by `cylRetract q`. -/
noncomputable def retractMap (q : C(X, B)) (b : B) :
    Work.StemsB.relChainsR ℚ (TopCat.of (cyl q)) (fibreSet q b) ⟶
      Work.StemsB.relChainsR ℚ (TopCat.of B) ({b} : Set B) :=
  relChainsRPairMap (fibreSet q b) ({b} : Set B) (cylRetract q)
    (by intro x hx; exact hx)

/-- The inclusion map of the triple `P ⊆ CMid q b ⊆ cyl q`: `C_*(CMid q b, P) → C_*(cyl q, P)`. -/
noncomputable abbrev inclMap (q : C(X, B)) (b : B) :
    Work.StemsB.relChainsR ℚ (TopCat.of ↥(CMid q b))
        {y : ↥(CMid q b) | (y : cyl q) ∈ fibreSet q b} ⟶
      Work.StemsB.relChainsR ℚ (TopCat.of (cyl q)) (fibreSet q b) :=
  (Work.Serre.RatTower.tripleShortR (TopCat.of (cyl q)) (fibreSet q b) (CMid q b)
    Set.subset_union_right).f

end

end Work.Serre
