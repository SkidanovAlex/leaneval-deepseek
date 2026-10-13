import Mathlib

namespace Work.DSAM2

/-- Solvability of a linear equation descends along a faithfully flat algebra extension:
`L v = y` has a solution over `B` iff its base change `B' ⊗[B] L` hits `1 ⊗ₜ y`. -/
theorem exists_eq_of_lTensor_eq {B : Type*} [CommRing B] {B' : Type*} [CommRing B']
    [Algebra B B'] [Module.FaithfullyFlat B B'] {V : Type*} [AddCommGroup V] [Module B V]
    {W : Type*} [AddCommGroup W] [Module B W] (L : V →ₗ[B] W) (y : W) :
    (∃ v, L v = y) ↔ (∃ v' : TensorProduct B B' V,
      L.lTensor B' v' = TensorProduct.mk B B' W 1 y) := by
  open scoped TensorProduct in
  constructor
  · rintro ⟨v, rfl⟩
    refine ⟨TensorProduct.mk B B' V 1 v, ?_⟩
    simp [TensorProduct.mk_apply, LinearMap.lTensor_tmul]
  · rintro ⟨v', hv'⟩
    rw [← LinearMap.mem_range]
    -- The quotient projection kills the range of `L`, so after base change it kills
    -- `L.lTensor B' v' = 1 ⊗ₜ y`; faithfully flatness then detects `mkQ y = 0`.
    have hq : (Submodule.mkQ (LinearMap.range L)).comp L = 0 := by
      ext v
      rw [LinearMap.comp_apply, LinearMap.zero_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero]
      exact LinearMap.mem_range_self L v
    have hzero : (LinearMap.lTensor B' (Submodule.mkQ (LinearMap.range L)))
        (LinearMap.lTensor B' L v') = 0 := by
      rw [← LinearMap.lTensor_comp_apply, hq, LinearMap.lTensor_zero]
      simp
    rw [hv'] at hzero
    have hqy : (Submodule.mkQ (LinearMap.range L)) y = 0 := by
      refine (Module.FaithfullyFlat.one_tmul_eq_zero_iff (R := B)
        (M := W ⧸ LinearMap.range L) (A := B') _).mp ?_
      simpa [TensorProduct.mk_apply, LinearMap.lTensor_tmul] using hzero
    rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hqy

end Work.DSAM2
