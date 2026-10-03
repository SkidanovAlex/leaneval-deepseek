import Mathlib
import Submission.Work.ORBassSerre.CoprodTree.Defs

universe u v

namespace Work.ORBassSerre.CoprodTree

/-- The stabilizer of the vertex `vA g` under the action of the free product on the Bass--Serre
tree is the conjugate, by `g`, of the image of the first factor. -/
theorem vertexStab_vA {A : Type u} {B : Type v} [Group A] [Group B] (g : Monoid.Coprod A B) : MulAction.stabilizer (Monoid.Coprod A B) (Work.ORBassSerre.CoprodTree.vA g) = (Work.ORBassSerre.CoprodTree.SubA A B).map (MulEquiv.toMonoidHom (MulAut.conj g)) := by
  ext x
  rw [MulAction.mem_stabilizer_iff, smul_vA, vA_eq_vA_iff, Subgroup.mem_map]
  constructor
  · intro h
    refine ⟨g⁻¹ * x * g, ?_, ?_⟩
    · have h' : g⁻¹ * x⁻¹ * g ∈ SubA A B := by
        simpa [mul_inv_rev, mul_assoc] using h
      simpa [mul_inv_rev, inv_inv, mul_assoc] using (SubA A B).inv_mem h'
    · simp [MulAut.conj_apply, mul_assoc]
  · rintro ⟨a, ha, hx⟩
    rw [← hx]
    have h1 : (MulEquiv.toMonoidHom (MulAut.conj g)) a = g * a * g⁻¹ := by
      simp [MulAut.conj_apply]
    rw [h1]
    have : (g * a * g⁻¹ * g)⁻¹ * g = a⁻¹ := by
      simp [mul_assoc]
    rw [this]
    exact (SubA A B).inv_mem ha

end Work.ORBassSerre.CoprodTree
