import Mathlib
import Submission.Work.ORTorsion.Defs

namespace Work.ORTorsion.Support

open Work.ORTorsion

variable {K : Type*} [Field K] {G : Type*} [Group G] {H : Subgroup G}

/-- `mapToG H` applied to a single monomial. -/
lemma mapToG_single_coeff (H : Subgroup G) (h : H) (c : K) :
    mapToG (K := K) (G := G) H (MonoidAlgebra.single h c) =
      MonoidAlgebra.single (h : G) c := by
  rw [mapToG, MonoidAlgebra.lift_single]
  simp only [MonoidHom.coe_mk, OneHom.coe_mk]
  rw [MonoidAlgebra.smul_single, smul_eq_mul, mul_one]

/-- The coefficients of `mapToG H x` are the coefficients of `x`, transported along the
inclusion `H ↪ G`. -/
lemma coeff_mapToG_subtype (H : Subgroup G) (x : MonoidAlgebra K H) :
    (mapToG (K := K) (G := G) H x).coeff =
      Finsupp.mapDomain (H.subtype : H → G) x.coeff := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy =>
      simp only [map_add, MonoidAlgebra.coeff_add, Finsupp.mapDomain_add, hx, hy]
  | single h c =>
      rw [mapToG_single_coeff, MonoidAlgebra.coeff_single, MonoidAlgebra.coeff_single,
        Finsupp.mapDomain_single]
      rfl

/-- Membership of a group element in the support of `mapToG H x` is membership of the
corresponding element of `H` in the support of `x`. -/
theorem mem_support_mapToG {K : Type*} [Field K] {G : Type*} [Group G] {H : Subgroup G}
    (x : MonoidAlgebra K H) (h : H) :
    (h : G) ∈ (mapToG H x).coeff.support ↔ h ∈ x.coeff.support := by
  rw [Finsupp.mem_support_iff, Finsupp.mem_support_iff]
  have key : (mapToG (K := K) (G := G) H x).coeff (h : G) = x.coeff h := by
    rw [coeff_mapToG_subtype H x]
    exact Finsupp.mapDomain_apply_of_injective (Subgroup.subtype_injective H) x.coeff h
  rw [key]

end Work.ORTorsion.Support
