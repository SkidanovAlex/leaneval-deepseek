import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThmF.ChV12

open TensorProduct

/-- For a field extension `F → K` and an `F`-module `V`, the "unit" element `1 : K` is
regular with respect to base change: the `F`-linear map `V → K ⊗[F] V`, `v ↦ 1 ⊗ v`
is injective. -/
private lemma tensorProduct_mk_one_injective
    {F K V : Type*} [Field F] [Field K] [Algebra F K]
    [AddCommGroup V] [Module F V] :
    Function.Injective (TensorProduct.mk F K V (1 : K)) := by
  -- a retraction of `F → K`, `x ↦ x • 1`, given by nondegeneracy of the field extension
  obtain ⟨π, hπ⟩ := (Algebra.linearMap F K).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (algebraMap F K).injective)
  have hπ1 : π 1 = 1 := by
    have h := LinearMap.congr_fun hπ (1 : F)
    simpa using h
  intro x y hxy
  have key : ∀ v : V, (TensorProduct.lid F V)
      (TensorProduct.map π (LinearMap.id : V →ₗ[F] V)
        (TensorProduct.mk F K V (1 : K) v)) = v := by
    intro v
    simp only [TensorProduct.mk_apply, TensorProduct.map_tmul, LinearMap.id_apply, hπ1,
      TensorProduct.lid_tmul, one_smul]
  have h := congrArg (fun t => (TensorProduct.lid F V)
      (TensorProduct.map π (LinearMap.id : V →ₗ[F] V) t)) hxy
  rwa [key x, key y] at h

theorem baseChange_action
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    {P : Type*} [Group P] {V : Type*} [AddCommGroup V] [Module F V]
    (ρ : P →* (V ≃ₗ[F] V)) (hfaith : Function.Injective ρ)
    {W : Type*} [Group W] (ι : W →* P) (hι : Function.Injective ι)
    (g : P) (σ : MulAut W) (hconj : ∀ w : W, ι (σ w) = g * ι w * g⁻¹) :
    ∃ (ρW : W →* Module.End K (TensorProduct F K V))
      (σV : TensorProduct F K V ≃ₗ[K] TensorProduct F K V),
      Function.Injective ρW ∧
      (∀ w : W, (σV : Module.End K (TensorProduct F K V)) * ρW w
        = ρW (σ w) * (σV : Module.End K (TensorProduct F K V))) ∧
      Module.finrank K (TensorProduct F K V) = Module.finrank F V := by
  -- the base-changed representation `w ↦ ρ (ι w) ⊗ 1`
  let ρW : W →* Module.End K (TensorProduct F K V) :=
    { toFun := fun w => (ρ (ι w)).toLinearMap.baseChange K
      map_one' := by
        rw [map_one, map_one]
        change (1 : Module.End F V).baseChange K = 1
        rw [LinearMap.baseChange_one]
      map_mul' := by
        intro a b
        rw [map_mul, map_mul]
        rw [show ((ρ (ι a) * ρ (ι b)) : V ≃ₗ[F] V).toLinearMap
              = (ρ (ι a)).toLinearMap * (ρ (ι b)).toLinearMap from rfl]
        rw [LinearMap.baseChange_mul] }
  have ρW_apply : ∀ w : W, ρW w = (ρ (ι w)).toLinearMap.baseChange K := fun _ => rfl
  -- the intertwining operator is the base change of `ρ g`
  refine ⟨ρW, (ρ g).baseChange F K V V, ?_, ?_, ?_⟩
  · -- faithfulness of `ρW`
    intro a b hab
    have h1 : (ρ (ι a)).toLinearMap = (ρ (ι b)).toLinearMap := by
      ext v
      have h := congrArg (fun f : Module.End K (TensorProduct F K V) =>
        f (TensorProduct.mk F K V (1 : K) v)) hab
      rw [ρW_apply, ρW_apply, TensorProduct.mk_apply, LinearMap.baseChange_tmul,
        LinearMap.baseChange_tmul] at h
      exact tensorProduct_mk_one_injective (by simpa only [TensorProduct.mk_apply] using h)
    exact hι (hfaith (LinearEquiv.toLinearMap_injective h1))
  · -- the intertwining relation
    intro w
    rw [LinearEquiv.coe_baseChange, ρW_apply, ρW_apply]
    simp only [← LinearMap.baseChange_mul]
    congr 1
    have hgg : g * ι w = ι (σ w) * g := by
      rw [hconj w]; group
    calc (ρ g).toLinearMap * (ρ (ι w)).toLinearMap
        = ((ρ g) * (ρ (ι w)) : V ≃ₗ[F] V).toLinearMap := rfl
      _ = (ρ (g * ι w)).toLinearMap := by rw [map_mul]
      _ = (ρ (ι (σ w) * g)).toLinearMap := by rw [hgg]
      _ = ((ρ (ι (σ w))) * (ρ g) : V ≃ₗ[F] V).toLinearMap := by rw [map_mul]
      _ = (ρ (ι (σ w))).toLinearMap * (ρ g).toLinearMap := rfl
  · -- the dimension
    exact Module.finrank_baseChange

end Work.ThmF.ChV12
