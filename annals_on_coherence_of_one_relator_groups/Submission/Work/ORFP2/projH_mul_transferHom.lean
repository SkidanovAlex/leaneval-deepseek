import Mathlib
import Submission.Work.ORFP2.CosetProj

set_option autoImplicit false

namespace Work.ORFP2

/- Helper lemmas for `projH_mul_transferHom`, placed in a dedicated namespace so as not to
pollute `Work.ORFP2`. -/
namespace ProjHMul

variable (k : Type*) [CommRing k] {G : Type*} [Group G]

/-- The coefficient at an element `g ∈ H` of `transferHom k H a` is the corresponding
coefficient of `a`. -/
lemma transferHom_coeff_mem (H : Subgroup G) (a : MonoidAlgebra k H) (g : G) (hg : g ∈ H) :
    (transferHom k H a).coeff g = a.coeff ⟨g, hg⟩ := by
  classical
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y ihx ihy =>
      simp only [map_add, MonoidAlgebra.coeff_add, Finsupp.add_apply]
      rw [ihx, ihy]
  | single m r =>
      rw [transferHom_single, MonoidAlgebra.coeff_single_apply, MonoidAlgebra.coeff_single_apply]
      by_cases hcase : (m : G) = g
      · rw [if_pos hcase, if_pos (Subtype.ext_iff.mpr hcase)]
      · rw [if_neg hcase, if_neg (fun h => hcase (Subtype.ext_iff.mp h))]

/-- `transferHom k H a` is supported in `H`: its coefficient at any `g ∉ H` vanishes. -/
lemma transferHom_coeff_not_mem (H : Subgroup G) (a : MonoidAlgebra k H) (g : G)
    (hg : g ∉ H) : (transferHom k H a).coeff g = 0 := by
  classical
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y ihx ihy =>
      simp only [map_add, MonoidAlgebra.coeff_add, Finsupp.add_apply]
      rw [ihx, ihy, add_zero]
  | single m r =>
      rw [transferHom_single, MonoidAlgebra.coeff_single_apply]
      rw [if_neg]
      intro hcontra
      exact hg (by rw [← hcontra]; exact m.2)

/-- `projH k H` is a section of `transferHom k H`: the `H`-component of `transferHom k H a`
is `a` itself. -/
lemma projH_transferHom_aux (H : Subgroup G) (a : MonoidAlgebra k H) :
    projH k H (transferHom k H a) = a := by
  ext h
  rw [projH_coeff k H (transferHom k H a) (h : G) h.2,
      transferHom_coeff_mem k H a (h : G) h.2]

end ProjHMul

open ProjHMul

theorem projH_mul_transferHom (k : Type*) [CommRing k] {G : Type*} [Group G] (H : Subgroup G)
    (x : MonoidAlgebra k G) (a : MonoidAlgebra k H) :
    projH k H (x * transferHom k H a) = projH k H x * a := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp [projH_zero]
  | add x y ihx ihy =>
      calc projH k H ((x + y) * transferHom k H a)
          = projH k H (x * transferHom k H a) + projH k H (y * transferHom k H a) := by
            rw [add_mul, projH_add]
        _ = projH k H x * a + projH k H y * a := by rw [ihx, ihy]
        _ = (projH k H x + projH k H y) * a := by rw [add_mul]
        _ = projH k H (x + y) * a := by rw [projH_add]
  | single g c =>
      classical
      by_cases hg : g ∈ H
      · have h1 : MonoidAlgebra.single g c
            = transferHom k H (MonoidAlgebra.single ⟨g, hg⟩ c) := by
          rw [transferHom_single]
        calc projH k H (MonoidAlgebra.single g c * transferHom k H a)
            = projH k H (transferHom k H (MonoidAlgebra.single ⟨g, hg⟩ c)
                * transferHom k H a) := by rw [h1]
          _ = projH k H (transferHom k H (MonoidAlgebra.single ⟨g, hg⟩ c * a)) := by
                rw [← map_mul]
          _ = MonoidAlgebra.single ⟨g, hg⟩ c * a := by rw [projH_transferHom_aux]
          _ = projH k H (MonoidAlgebra.single g c) * a := by rw [h1, projH_transferHom_aux]
      · have hz : projH k H (MonoidAlgebra.single g c) = 0 := by
          rw [projH_eq_zero_iff]
          intro h hh
          rw [MonoidAlgebra.coeff_single_apply, if_neg]
          intro hcontra
          exact hg (by rw [hcontra]; exact hh)
        have hz2 : projH k H (MonoidAlgebra.single g c * transferHom k H a) = 0 := by
          rw [projH_eq_zero_iff]
          intro h hh
          have hnot : g⁻¹ * h ∉ H := by
            intro hcontra
            have hgH : g ∈ H := by
              have heq : g = h * (g⁻¹ * h)⁻¹ := by group
              rw [heq]
              exact mul_mem hh (inv_mem hcontra)
            exact hg hgH
          rw [MonoidAlgebra.coeff_single_mul_apply,
              transferHom_coeff_not_mem k H a (g⁻¹ * h) hnot, mul_zero]
        rw [hz, hz2, zero_mul]

end Work.ORFP2
