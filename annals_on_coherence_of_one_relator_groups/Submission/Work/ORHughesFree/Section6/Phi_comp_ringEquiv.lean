/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `e ∘ Φ_φ = Φ_ψ` for an isomorphism of division closures intertwining `φ` and `ψ`

Let `φ : K[G] →+* U`, `ψ : K[G] →+* V` be ring homomorphisms and let
`e : D_{K[G],U} ≃+* D_{K[G],V}` be a ring isomorphism with `e (φ x) = ψ x` for all
`x : K[G]` (viewing `φ x`, `ψ x` as elements of the division closures).

Then `e` is a morphism of rational `Kˣ × G`-semirings: it preserves units, hence the
rational operation `⋄` (inversion on the units of the division closure, `0` elsewhere), and it
intertwines the two actions, which are multiplication by `φ (unitOf u)` and by
`ψ (unitOf u) = e (φ (unitOf u))`.  Since `Φ` is the universal morphism of rational
`Kˣ × G`-semirings (`RatU.lift`), uniqueness of that morphism gives `e ∘ Φ_φ = Φ_ψ`.

This is the statement of `Section6.Phi_comp_ringEquiv`; it is used to transport `G`-complexities
across an isomorphism of division closures
(`Section6/treeG_map_of_divisionClosure_ringEquiv.lean`), where it appears as a `private`
theorem.
-/
import Mathlib
import Submission.Work.ORHughesFree.Section6.RatStruct
import Submission.Work.ORHughesFree.Section6.Phi_surjective
import Submission.Work.ORHughesFree.Section6.treeG_map_of_divisionClosure_ringEquiv
import Submission.Work.ORHughesFree.Section6.imElem_isUnit

set_option autoImplicit false

namespace Work.ORHughesFree.Section6

open Work.ORHughesFree

variable {K : Type} [Field K] {G : Type} [Group G] {U : Type} [Ring U] {V : Type} [Ring V]

/-! ### `e` is compatible with the rational structure `ratStruct` -/

/-- **A ring isomorphism of subrings preserves the rational operation** "inverse if a unit, `0`
otherwise": it preserves units (in both directions, `e` and `e⁻¹` being ring homomorphisms) and
inverses. -/
private theorem ratOpClosure_ringEquiv {W W' : Type} [Ring W] [Ring W'] (D : Subring W)
    (D' : Subring W') (e : ↥D ≃+* ↥D') (x : ↥D) :
    e (ratOpClosure D x) = ratOpClosure D' (e x) := by
  classical
  have hiff : IsUnit (e x) ↔ IsUnit x :=
    isUnit_map_of_leftInverse (f := (e : ↥D →+* ↥D')) (g := (e.symm : ↥D' →+* ↥D))
      (fun y => RingEquiv.symm_apply_apply e y)
  by_cases h : IsUnit x
  · have h' : IsUnit (e x) := h.map (e : ↥D →+* ↥D')
    rw [ratOpClosure, dif_pos h, ratOpClosure, dif_pos h']
    have hh : h' = h.map (e : ↥D →+* ↥D') := Subsingleton.elim _ _
    rw [hh, IsUnit.unit_inv_map]
  · have h' : ¬ IsUnit (e x) := fun hh => h (hiff.mp hh)
    rw [ratOpClosure, dif_neg h, ratOpClosure, dif_neg h']
    exact map_zero e

/-- The left action of `ratStruct φ` is multiplication by `imElem φ u`: the coefficientwise
statement `ratStruct_smul`. -/
private theorem ratStruct_smul_eq (φ : MonoidAlgebra K G →+* U) (u : Kˣ × G)
    (x : ↥(divisionClosure (Set.range φ))) :
    (ratStruct φ).smul u x = imElem φ u * x := by
  apply Subtype.ext
  rw [ratStruct_smul]
  rfl

/-- The right action of `ratStruct φ` is multiplication by `imElem φ u`: the coefficientwise
statement `ratStruct_smulRight`. -/
private theorem ratStruct_smulRight_eq (φ : MonoidAlgebra K G →+* U)
    (x : ↥(divisionClosure (Set.range φ))) (u : Kˣ × G) :
    (ratStruct φ).smulRight x u = x * imElem φ u := by
  apply Subtype.ext
  rw [ratStruct_smulRight]
  rfl

/-- `e` carries the image of the group-like unit `λ·g` to the corresponding image: this is the
hypothesis `he` at `unitOf u`. -/
private theorem imElem_ringEquiv (φ : MonoidAlgebra K G →+* U) (ψ : MonoidAlgebra K G →+* V)
    (e : ↥(divisionClosure (Set.range φ)) ≃+* ↥(divisionClosure (Set.range ψ)))
    (he : ∀ x : MonoidAlgebra K G,
      e ⟨φ x, subset_divisionClosure (Set.range φ) ⟨x, rfl⟩⟩ =
        ⟨ψ x, subset_divisionClosure (Set.range ψ) ⟨x, rfl⟩⟩)
    (u : Kˣ × G) : e (imElem φ u) = imElem ψ u :=
  he (unitOf u)

/-- `e` intertwines the left `Kˣ × G`-actions of `ratStruct φ` and `ratStruct ψ`. -/
private theorem ratStruct_smul_ringEquiv (φ : MonoidAlgebra K G →+* U)
    (ψ : MonoidAlgebra K G →+* V)
    (e : ↥(divisionClosure (Set.range φ)) ≃+* ↥(divisionClosure (Set.range ψ)))
    (he : ∀ x : MonoidAlgebra K G,
      e ⟨φ x, subset_divisionClosure (Set.range φ) ⟨x, rfl⟩⟩ =
        ⟨ψ x, subset_divisionClosure (Set.range ψ) ⟨x, rfl⟩⟩)
    (u : Kˣ × G) (x : ↥(divisionClosure (Set.range φ))) :
    e ((ratStruct φ).smul u x) = (ratStruct ψ).smul u (e x) := by
  calc e ((ratStruct φ).smul u x) = e (imElem φ u * x) := by rw [ratStruct_smul_eq]
    _ = e (imElem φ u) * e x := map_mul _ _ _
    _ = imElem ψ u * e x := by rw [imElem_ringEquiv φ ψ e he u]
    _ = (ratStruct ψ).smul u (e x) := (ratStruct_smul_eq ψ u (e x)).symm

/-- `e` intertwines the right `Kˣ × G`-actions of `ratStruct φ` and `ratStruct ψ`. -/
private theorem ratStruct_smulRight_ringEquiv (φ : MonoidAlgebra K G →+* U)
    (ψ : MonoidAlgebra K G →+* V)
    (e : ↥(divisionClosure (Set.range φ)) ≃+* ↥(divisionClosure (Set.range ψ)))
    (he : ∀ x : MonoidAlgebra K G,
      e ⟨φ x, subset_divisionClosure (Set.range φ) ⟨x, rfl⟩⟩ =
        ⟨ψ x, subset_divisionClosure (Set.range ψ) ⟨x, rfl⟩⟩)
    (x : ↥(divisionClosure (Set.range φ))) (u : Kˣ × G) :
    e ((ratStruct φ).smulRight x u) = (ratStruct ψ).smulRight (e x) u := by
  calc e ((ratStruct φ).smulRight x u) = e (x * imElem φ u) := by rw [ratStruct_smulRight_eq]
    _ = e x * e (imElem φ u) := map_mul _ _ _
    _ = e x * imElem ψ u := by rw [imElem_ringEquiv φ ψ e he u]
    _ = (ratStruct ψ).smulRight (e x) u := (ratStruct_smulRight_eq ψ (e x) u).symm

/-- `e` intertwines the rational operations of `ratStruct φ` and `ratStruct ψ`. -/
private theorem ratStruct_ratOp_ringEquiv (φ : MonoidAlgebra K G →+* U)
    (ψ : MonoidAlgebra K G →+* V)
    (e : ↥(divisionClosure (Set.range φ)) ≃+* ↥(divisionClosure (Set.range ψ)))
    (x : ↥(divisionClosure (Set.range φ))) :
    e ((ratStruct φ).ratOp x) = (ratStruct ψ).ratOp (e x) := by
  rw [ratStruct_ratOp, ratStruct_ratOp]
  exact ratOpClosure_ringEquiv (divisionClosure (Set.range φ))
    (divisionClosure (Set.range ψ)) e x

/-- **`e ∘ Φ_φ = Φ_ψ`.**  The three compatibility lemmas above show that `e ∘ Φ_φ` is a morphism
of rational `Kˣ × G`-semirings `Rat(Kˣ × G) → D_{K[G],V}`; by uniqueness of the morphism of
rational semirings out of `Rat(Kˣ × G)` (`RatU.lift_unique`) it therefore agrees with
`Φ_ψ = RatU.lift _ (ratStruct ψ)`. -/
theorem Phi_comp_ringEquiv {K : Type} [Field K] {G : Type} [Group G] {U : Type} [Ring U]
    {V : Type} [Ring V] (φ : MonoidAlgebra K G →+* U) (ψ : MonoidAlgebra K G →+* V)
    (e : ↥(Work.ORHughesFree.divisionClosure (Set.range φ)) ≃+*
      ↥(Work.ORHughesFree.divisionClosure (Set.range ψ)))
    (he : ∀ x : MonoidAlgebra K G,
      e ⟨φ x, Work.ORHughesFree.subset_divisionClosure (Set.range φ) ⟨x, rfl⟩⟩ =
        ⟨ψ x, Work.ORHughesFree.subset_divisionClosure (Set.range ψ) ⟨x, rfl⟩⟩) :
    (e.toRingHom.comp (Work.ORHughesFree.Phi φ)) = Work.ORHughesFree.Phi ψ := by
  refine RatU.lift_unique _ (ratStruct ψ) _ ?_
  exact { map_rat := fun α => by
            change e ((Phi φ) (RatU.rational.ratOp α)) = (ratStruct ψ).ratOp (e ((Phi φ) α))
            rw [(Phi_isRational φ).map_rat α]
            exact ratStruct_ratOp_ringEquiv φ ψ e (Phi φ α)
          map_smul := fun u α => by
            change e ((Phi φ) (RatU.rational.smul u α)) = (ratStruct ψ).smul u (e ((Phi φ) α))
            rw [(Phi_isRational φ).map_smul u α]
            exact ratStruct_smul_ringEquiv φ ψ e he u (Phi φ α)
          map_smulRight := fun α u => by
            change e ((Phi φ) (RatU.rational.smulRight α u)) =
              (ratStruct ψ).smulRight (e ((Phi φ) α)) u
            rw [(Phi_isRational φ).map_smulRight α u]
            exact ratStruct_smulRight_ringEquiv φ ψ e he (Phi φ α) u }

end Work.ORHughesFree.Section6
