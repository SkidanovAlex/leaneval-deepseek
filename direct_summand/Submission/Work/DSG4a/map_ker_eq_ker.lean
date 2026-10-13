import Mathlib

namespace Work.DSG4a

theorem map_ker_eq_ker {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {X Y P Q : Type*} [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    [AddCommGroup P] [Module S P] [AddCommGroup Q] [Module S Q]
    (g : TensorProduct R S X →ₗ[S] TensorProduct R S Y) (g' : P →ₗ[S] Q)
    (e : TensorProduct R S X ≃ₗ[S] P) (e' : TensorProduct R S Y ≃ₗ[S] Q)
    (h : ∀ x, e' (g x) = g' (e x)) :
    Submodule.map e.toLinearMap g.ker = g'.ker := by
  ext y
  constructor
  · intro hy
    rw [Submodule.mem_map] at hy
    obtain ⟨x, hx, hxy⟩ := hy
    rw [← hxy, LinearMap.mem_ker]
    rw [LinearMap.mem_ker] at hx
    exact (h x).symm.trans (by rw [hx, map_zero e'])
  · intro hy
    rw [Submodule.mem_map]
    refine ⟨e.symm y, ?_, ?_⟩
    · rw [LinearMap.mem_ker]
      rw [LinearMap.mem_ker] at hy
      apply e'.injective
      rw [map_zero e']
      rw [h (e.symm y), e.apply_symm_apply, hy]
    · show e (e.symm y) = y
      exact e.apply_symm_apply y

end Work.DSG4a
