import Mathlib
import Submission.Work.ORTorsion.Defs

namespace Work.ORTorsion.Base

open Work.ORTorsion

/-- Left multiplication by a basis element `single a 1` of a group algebra permutes the support
of a finitely supported function by the bijection `g ↦ a * g`, hence preserves its cardinality. -/
theorem card_support_single_mul {K : Type*} [Field K] {G : Type*} [Group G] (a : G)
    (β : MonoidAlgebra K G) :
    (MonoidAlgebra.single a (1 : K) * β).coeff.support.card = β.coeff.support.card := by
  classical
  have hcoeff : ∀ h : G, (MonoidAlgebra.single a (1 : K) * β).coeff h = β.coeff (a⁻¹ * h) := by
    intro h
    rw [MonoidAlgebra.coeff_single_mul_apply β (1 : K) a h, one_mul]
  have hsupp : (MonoidAlgebra.single a (1 : K) * β).coeff.support
      = β.coeff.support.image (fun g => a * g) := by
    ext h
    rw [Finsupp.mem_support_iff, hcoeff h, Finset.mem_image]
    constructor
    · intro hh
      exact ⟨a⁻¹ * h, by rwa [Finsupp.mem_support_iff], by rw [mul_inv_cancel_left]⟩
    · rintro ⟨g, hg, rfl⟩
      rw [Finsupp.mem_support_iff] at hg
      simpa using hg
  rw [hsupp]
  exact Finset.card_image_of_injective _ (fun x y hxy => mul_left_cancel hxy)

end Work.ORTorsion.Base
