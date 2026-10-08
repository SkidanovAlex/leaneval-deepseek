import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Higman.RedAux

theorem map_comap_mulEquiv {G H : Type*} [Group G] [Group H]
    (π : G →* H) (e : G ≃* G) (σ : H ≃* H)
    (hc : ∀ x : G, σ (π x) = π (e x)) (N : Subgroup H) :
    (N.comap π).map (e : G →* G) = (N.map (σ : H →* H)).comap π := by
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_comap]
  constructor
  · -- x = e y with y ∈ N.comap π, i.e. π y ∈ N: then σ (π y) = π (e y) = π x.
    rintro ⟨y, hy, rfl⟩
    exact ⟨π y, hy, hc y⟩
  · -- π x = σ n with n ∈ N: then π (e.symm x) = n ∈ N, and e (e.symm x) = x.
    rintro ⟨n, hn, hσn⟩
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    have h1 : σ (π (e.symm x)) = σ n := by
      rw [hc (e.symm x), MulEquiv.apply_symm_apply]
      exact hσn.symm
    rw [σ.injective h1]
    exact hn

end Work.Higman.RedAux
