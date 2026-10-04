import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.Evol

theorem Q_pack
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Q : V → V → F)
    (hQlin1 : ∀ (r s : ℝ) (v₁ v₂ : V) (w : V), Q (r • v₁ + s • v₂) w = r • Q v₁ w + s • Q v₂ w)
    (hQlin2 : ∀ (r s : ℝ) (v : V) (w₁ w₂ : V), Q v (r • w₁ + s • w₂) = r • Q v w₁ + s • Q v w₂) :
    ∃ P : V →L[ℝ] (V →L[ℝ] F), ∀ v w : V, P v w = Q v w := by
  -- Extract additivity / homogeneity of `Q` in each slot from the two hypotheses.
  have hadd1 : ∀ (v₁ v₂ : V) (w : V), Q (v₁ + v₂) w = Q v₁ w + Q v₂ w :=
    fun v₁ v₂ w => by simpa using hQlin1 1 1 v₁ v₂ w
  have hsmul1 : ∀ (c : ℝ) (v : V) (w : V), Q (c • v) w = c • Q v w :=
    fun c v w => by simpa using hQlin1 c 0 v 0 w
  have hadd2 : ∀ (v : V) (w₁ w₂ : V), Q v (w₁ + w₂) = Q v w₁ + Q v w₂ :=
    fun v w₁ w₂ => by simpa using hQlin2 1 1 v w₁ w₂
  have hsmul2 : ∀ (c : ℝ) (v w : V), Q v (c • w) = c • Q v w :=
    fun c v w => by simpa using hQlin2 c 0 v w 0
  -- `Q` as a bilinear map.
  let B : V →ₗ[ℝ] V →ₗ[ℝ] F := LinearMap.mk₂ ℝ Q hadd1 hsmul1 hadd2 hsmul2
  have hB : ∀ v w, B v w = Q v w := fun v w => LinearMap.mk₂_apply ℝ Q v w
  -- Upgrade to continuous linear maps: `V` is finite-dimensional.
  let φ : (V →ₗ[ℝ] F) →ₗ[ℝ] (V →L[ℝ] F) := (LinearMap.toContinuousLinearMap (𝕜 := ℝ)).toLinearMap
  have hφ : ∀ f : V →ₗ[ℝ] F, (φ f : V → F) = f := fun f => LinearMap.coe_toContinuousLinearMap' f
  let L : V →ₗ[ℝ] (V →L[ℝ] F) := φ.comp B
  refine ⟨LinearMap.toContinuousLinearMap L, ?_⟩
  intro v w
  simp only [LinearMap.coe_toContinuousLinearMap', L, LinearMap.comp_apply, φ, hφ, hB]

end Work.Diff.Evol
