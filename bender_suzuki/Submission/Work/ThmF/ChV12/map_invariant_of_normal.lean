import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThmF.ChV12

/-- If `F ◁ D` acts on `A` through `ρ : D →* MulAut A`, and `U ≤ A` is invariant under
every `ρ t` with `t ∈ F`, then the image `U.map (ρ d).toMonoidHom` of `U` under any
single `ρ d` is again invariant under every `ρ t` with `t ∈ F`.

Indeed, if `x = ρ d u` with `u ∈ U`, then `ρ t x = ρ t (ρ d u) = ρ (t d) u`, and
`t d = d (d⁻¹ t d)` with `d⁻¹ t d ∈ F` by normality of `F`, so
`ρ t x = ρ d (ρ (d⁻¹ t d) u) ∈ U.map (ρ d).toMonoidHom`. -/
theorem map_invariant_of_normal {A D : Type} [Group A] [Group D] (ρ : D →* MulAut A)
    {F : Subgroup D} [F.Normal] {U : Subgroup A}
    (hU : ∀ t ∈ F, ∀ x : A, x ∈ U → ρ t x ∈ U) (d : D) :
    ∀ t ∈ F, ∀ x : A, x ∈ U.map (ρ d).toMonoidHom → ρ t x ∈ U.map (ρ d).toMonoidHom := by
  intro t ht x hx
  rw [Subgroup.mem_map] at hx ⊢
  obtain ⟨u, hu, rfl⟩ := hx
  have hF : d⁻¹ * t * d ∈ F := Subgroup.Normal.conj_mem' (inferInstance : F.Normal) t ht d
  refine ⟨ρ (d⁻¹ * t * d) u, hU _ hF u hu, ?_⟩
  have hA : ρ (d * (d⁻¹ * t * d)) = ρ d * ρ (d⁻¹ * t * d) := map_mul ρ d (d⁻¹ * t * d)
  have hB : ρ (t * d) = ρ t * ρ d := map_mul ρ t d
  have hC : ρ (d * (d⁻¹ * t * d)) = ρ (t * d) :=
    by rw [show d * (d⁻¹ * t * d) = t * d by group]
  calc (ρ d).toMonoidHom (ρ (d⁻¹ * t * d) u)
      = (ρ d * ρ (d⁻¹ * t * d)) u := rfl
    _ = (ρ (d * (d⁻¹ * t * d))) u := by rw [hA]
    _ = (ρ (t * d)) u := by rw [hC]
    _ = (ρ t * ρ d) u := by rw [hB]
    _ = ρ t ((ρ d).toMonoidHom u) := rfl

end Work.ThmF.ChV12
