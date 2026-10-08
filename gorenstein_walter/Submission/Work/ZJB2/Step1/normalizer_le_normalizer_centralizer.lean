import Mathlib

namespace Work.ZJB2.Step1

theorem normalizer_le_normalizer_centralizer {G : Type*} [Group G] (V : Subgroup G) :
    Subgroup.normalizer (V : Set G) ≤
      Subgroup.normalizer ((Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_set_normalizer_iff] at hg ⊢
  intro c
  constructor
  · -- If `c` centralizes `V`, then so does `g * c * g⁻¹`.
    intro hc
    simp only [SetLike.mem_coe, Subgroup.mem_centralizer_iff] at hc ⊢
    intro v hv
    -- `g⁻¹ * v * g` lies in `V` because `g` normalizes `V`.
    have hvg : g⁻¹ * v * g ∈ (V : Set G) := by
      refine (hg (g⁻¹ * v * g)).mpr ?_
      have : g * (g⁻¹ * v * g) * g⁻¹ = v := by group
      rw [this]
      exact hv
    have hcc := hc (g⁻¹ * v * g) hvg
    calc v * (g * c * g⁻¹)
        = g * ((g⁻¹ * v * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * v * g)) * g⁻¹ := by rw [hcc]
      _ = (g * c * g⁻¹) * v := by group
  · -- Conversely, if `g * c * g⁻¹` centralizes `V`, then so does `c`.
    intro hc
    simp only [SetLike.mem_coe, Subgroup.mem_centralizer_iff] at hc ⊢
    intro v hv
    have hgv : g * v * g⁻¹ ∈ (V : Set G) := (hg v).mp hv
    have hcc := hc (g * v * g⁻¹) hgv
    have hcv : g * (v * c) * g⁻¹ = g * (c * v) * g⁻¹ := by
      calc g * (v * c) * g⁻¹ = (g * v * g⁻¹) * (g * c * g⁻¹) := by group
        _ = (g * c * g⁻¹) * (g * v * g⁻¹) := hcc
        _ = g * (c * v) * g⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel hcv)

end Work.ZJB2.Step1
