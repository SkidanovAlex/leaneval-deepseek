import Mathlib
import Submission.Work.ORHughesFree.StarRegular

namespace Work.ORHughesFree.StarRegular

universe u

/-- `IsStarRegular` is transported across a ring isomorphism that commutes with the involution. -/
theorem isStarRegular_of_ringEquiv {R S : Type u} [Ring R] [StarRing R] [Ring S] [StarRing S] (e : R ≃+* S) (hstar : ∀ x : R, e (star x) = star (e x)) (h : IsStarRegular R) : IsStarRegular S := by
  refine ⟨⟨fun y => ?_⟩, fun y hy => ?_⟩
  · obtain ⟨x, hx⟩ := h.vonNeumannRegular.exists_mul_inverse (e.symm y)
    refine ⟨e x, ?_⟩
    calc y * e x * y = e (e.symm y) * e x * e (e.symm y) := by rw [e.apply_symm_apply]
      _ = e (e.symm y * x * e.symm y) := by simp only [map_mul]
      _ = e (e.symm y) := by rw [hx]
      _ = y := e.apply_symm_apply y
  · have h1 : e (star (e.symm y) * e.symm y) = 0 := by
      rw [e.map_mul, hstar, e.apply_symm_apply, hy]
    have h3 : star (e.symm y) * e.symm y = 0 := by
      have : e (star (e.symm y) * e.symm y) = e 0 := by rw [h1, e.map_zero]
      exact e.injective this
    have h4 : e.symm y = 0 := h.proper _ h3
    calc y = e (e.symm y) := (e.apply_symm_apply y).symm
      _ = e 0 := by rw [h4]
      _ = 0 := e.map_zero

end Work.ORHughesFree.StarRegular
