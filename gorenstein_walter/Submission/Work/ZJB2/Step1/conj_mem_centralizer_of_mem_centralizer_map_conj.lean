import Mathlib

namespace Work.ZJB2.Step1

theorem conj_mem_centralizer_of_mem_centralizer_map_conj {G : Type*} [Group G] {W : Subgroup G} {m c : G} (hc : c ∈ Subgroup.centralizer (W.map (MulAut.conj m⁻¹).toMonoidHom : Set G)) : m * c * m⁻¹ ∈ Subgroup.centralizer (W : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hc ⊢
  intro w hw
  have hm : (MulAut.conj m⁻¹) w = m⁻¹ * w * m := by rw [MulAut.conj_apply, inv_inv]
  have h := hc (m⁻¹ * w * m) (by rw [SetLike.mem_coe, Subgroup.mem_map]; exact ⟨w, hw, hm⟩)
  have h2 : m * ((m⁻¹ * w * m) * c) * m⁻¹ = m * (c * (m⁻¹ * w * m)) * m⁻¹ := by rw [h]
  simpa [mul_assoc] using h2

end Work.ZJB2.Step1
