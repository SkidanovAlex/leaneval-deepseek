/-
Area DSCOH (curric-46) — the normalization comparison: the "semi-ordered" and "ordered"
Čech complexes and the comparison maps.

For a topological space `X`, a presheaf `P` of `A`-modules on `X` and a family `U : ι → Opens X`
with `ι` linearly ordered, this file defines

* `semiTerm P U n` : the `n`-th term of the *semi-ordered* Čech complex, the product over the
  nondecreasing tuples `x : Fin (n+1) → ι` of `P (⋂_a U (x a))`;
* `semiD` : its differential, the alternating sum of the "delete one entry and restrict" maps;
* `semiT` : the semi-ordered Čech complex;
* `ordTerm`, `ordD`, `ordT` : the same for *strictly increasing* tuples, i.e. the ordered
  (alternating, subset-indexed) Čech complex;
* `semiProj` : the projection `allT ⟶ semiT` from Mathlib's unnormalized Čech complex;
* `ordProj` : the projection `semiT ⟶ ordT`;
* `ordIncl` : the map `ordT ⟶ semiT` which is the identity on strictly increasing tuples and
  zero on the other (not strictly increasing) tuples.

The mathematics: `semiProj` and `ordProj` are quasi-isomorphisms, with `ordIncl` a chain
homotopy inverse of `ordProj` (the classical "degenerate simplices" argument), and the composite
`ordProj ≫ ordIncl` homotopic to the identity of `semiT`.
-/
import Submission.Work.DSCOH.Norm.Defs

namespace Work.DSCOH.Norm

open CategoryTheory Limits Opposite TopologicalSpace
open scoped Simplicial BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

universe u v w

variable {X : Type u} [TopologicalSpace X] {A : Type v} [CommRing A]
variable {ι : Type w} [LinearOrder ι]

/-! ## The restriction morphism attached to a deletion -/

/-- The canonical morphism `∏ᶜ (U ∘ x) ⟶ ∏ᶜ (U ∘ del x b)` in `Opens X`: the product over
the entries of `del x b` is a product over a sub-family of the factors of `∏ᶜ (U ∘ x)`. -/
noncomputable def opDel (U : ι → Opens X) {n : ℕ} (x : Fin (n + 2) → ι) (b : Fin (n + 2)) :
    tupleOp U x ⟶ tupleOp U (del x b) :=
  Pi.lift fun a => Pi.π _ (b.succAbove a)

/-- The restriction `tupleMod P U (del x b) ⟶ tupleMod P U x` used in the Čech differential:
sections over `⋂_{a} U (x a)` restrict to sections over `⋂_{a ≠ b} U (x a)`. -/
noncomputable def resDel (P : (Opens X)ᵒᵖ ⥤ ModuleCat A) (U : ι → Opens X) {n : ℕ}
    (x : Fin (n + 2) → ι) (b : Fin (n + 2)) :
    tupleMod P U (del x b) ⟶ tupleMod P U x :=
  P.map (homOfLE (leOfHom (opDel U x b))).op

variable [HasProducts (ModuleCat A)] (P : (Opens X)ᵒᵖ ⥤ ModuleCat A) (U : ι → Opens X)

/-! ## The semi-ordered complex -/

/-- The `n`-th term of the semi-ordered Čech complex. -/
noncomputable def semiTerm (n : ℕ) : ModuleCat A :=
  ∏ᶜ fun x : SemiIdx ι n => tupleMod P U x.val

/-- The differential of the semi-ordered Čech complex: the alternating sum, over the entries
`b` of a nondecreasing tuple `x`, of the restriction from the tuple with the `b`-th entry
deleted. -/
noncomputable def semiD (n : ℕ) : semiTerm P U n ⟶ semiTerm P U (n + 1) :=
  Pi.lift fun x : SemiIdx ι (n + 1) =>
    ∑ b : Fin (n + 2), (-1 : ℤ) ^ (b : ℕ) •
      (Pi.π _ ⟨del x.val b, monotone_del x.val b x.property⟩ ≫ resDel P U x.val b)

/-- The `n`-th term of the ordered (alternating) Čech complex. -/
noncomputable def ordTerm (n : ℕ) : ModuleCat A :=
  ∏ᶜ fun x : OrdIdx ι n => tupleMod P U x.val

/-- The differential of the ordered Čech complex. -/
noncomputable def ordD (n : ℕ) : ordTerm P U n ⟶ ordTerm P U (n + 1) :=
  Pi.lift fun x : OrdIdx ι (n + 1) =>
    ∑ b : Fin (n + 2), (-1 : ℤ) ^ (b : ℕ) •
      (Pi.π _ ⟨del x.val b, strictMono_del x.val b x.property⟩ ≫ resDel P U x.val b)

end Work.DSCOH.Norm
