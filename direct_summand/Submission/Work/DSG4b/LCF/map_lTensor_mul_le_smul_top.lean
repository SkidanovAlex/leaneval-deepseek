import Mathlib
import Submission.Work.DSG4b.LCF.Basic

namespace Work.DSG4b.LCF

/-- For any `R`-linear map `g : M →ₗ[R] N` and ideal `A`, the image of `A • ⊤` is contained in
`A • ⊤`.  Indeed `A • ⊤` is spanned by the elements `a • m` with `a ∈ A`, `m ∈ M`, and
`g (a • m) = a • g m` lies again in `A • ⊤`. -/
lemma map_smul_top_le {R M N : Type*} [CommRing R] [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] (A : Ideal R) (g : M →ₗ[R] N) :
    Submodule.map g (A • (⊤ : Submodule R M)) ≤ A • (⊤ : Submodule R N) := by
  rw [Submodule.map_smul'', Submodule.map_top]
  exact Submodule.smul_le.2 fun r hr n _ => Submodule.smul_mem_smul hr Submodule.mem_top

theorem map_lTensor_mul_le_smul_top {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (J I : Ideal R) (n : ℕ) :
    Submodule.map (LinearMap.lTensor M (Submodule.inclusion (Ideal.mul_le_right : J ^ n * I ≤ I))) ⊤ ≤
      J ^ n • (⊤ : Submodule R (TensorProduct R M I)) := by
  rw [Submodule.map_le_iff_le_comap]
  intro z _
  rw [Submodule.mem_comap]
  -- It suffices to check simple tensors `m ⊗ₜ y`.
  refine TensorProduct.inductionOn z ?_ ?_
  · intro m y
    rw [LinearMap.lTensor_tmul]
    -- `inclusion y` lies in `J ^ n • ⊤` inside `I`, because `y ∈ J ^ n * I = J ^ n • I`.
    have hw : (Submodule.inclusion (Ideal.mul_le_right : J ^ n * I ≤ I) y) ∈
        J ^ n • (⊤ : Submodule R I) := by
      rw [Submodule.mem_smul_top_iff, Ideal.smul_eq_mul]
      exact y.2
    -- Tensoring with `m` preserves `J ^ n • ⊤` by linearity.
    exact map_smul_top_le (J ^ n) (TensorProduct.mk R M I m) (Submodule.mem_map_of_mem hw)
  · intro x y hx hy
    rw [map_add]
    exact add_mem hx hy

end Work.DSG4b.LCF
