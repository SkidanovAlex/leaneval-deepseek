import Mathlib

namespace Work.RPCore.Chain

noncomputable section

/-- A symmetric bilinear form on a finite-dimensional real inner product space whose
`v`-radical is trivial is represented by a self-adjoint, injective continuous linear
operator. -/
theorem selfAdjointRep {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    (β : E → E → ℝ)
    (hadd₁ : ∀ v v' w, β (v + v') w = β v w + β v' w)
    (hsmul₁ : ∀ (c : ℝ) v w, β (c • v) w = c * β v w)
    (hadd₂ : ∀ v w w', β v (w + w') = β v w + β v w')
    (hsmul₂ : ∀ (c : ℝ) v w, β v (c • w) = c * β v w)
    (hsymm : ∀ v w, β v w = β w v)
    (hnondeg : ∀ v, (∀ w, β v w = 0) → v = 0) :
    ∃ A : E →L[ℝ] E, (∀ v w, inner ℝ (A v) w = inner ℝ v (A w)) ∧ Function.Injective A ∧
      ∀ v w, inner ℝ (A v) w = β v w := by
  -- Package the bilinear form as a linear map into the dual of `E`.
  let B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ β hadd₁ (fun c v w => by rw [hsmul₁, smul_eq_mul]) hadd₂
      (fun c v w => by rw [hsmul₂, smul_eq_mul])
  have hB : ∀ v w, B v w = β v w := fun v w => rfl
  -- Each functional `w ↦ β v w` is continuous (finite dimension) and is the image of a
  -- unique vector under the Riesz representation map `InnerProductSpace.toDual`.
  let A_lin : E →ₗ[ℝ] E :=
    ((InnerProductSpace.toDual ℝ E).symm.toLinearEquiv.toLinearMap).comp
      ((LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := E) (F' := ℝ)).toLinearMap.comp B)
  have hAval : ∀ v, A_lin v = (InnerProductSpace.toDual ℝ E).symm (B v).toContinuousLinearMap :=
    fun v => rfl
  let A : E →L[ℝ] E := LinearMap.toContinuousLinearMap A_lin
  have hA : ∀ v, A v = A_lin v := fun v => rfl
  -- The defining representation property of `A`.
  have hrep : ∀ v w, inner ℝ (A v) w = β v w := by
    intro v w
    rw [hA v, hAval v, InnerProductSpace.toDual_symm_apply, LinearMap.coe_toContinuousLinearMap',
      hB]
  refine ⟨A, ?_, ?_, hrep⟩
  · -- Self-adjointness follows from symmetry of the form and of the inner product.
    intro v w
    rw [hrep v w, ← real_inner_comm v (A w), hrep w v, hsymm v w]
  · -- Injectivity from the triviality of the `v`-radical.
    intro x y hxy
    have hz : A (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have h0 : x - y = 0 := by
      apply hnondeg
      intro w
      rw [← hrep (x - y) w, hz, inner_zero_left]
    exact sub_eq_zero.mp h0

end

end Work.RPCore.Chain
