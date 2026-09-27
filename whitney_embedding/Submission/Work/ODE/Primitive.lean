import Mathlib

set_option autoImplicit false

/-!
# The primitive (Volterra) operator on paths on `[0,δ]`
-/

open scoped Topology NNReal
open Set Function Pointwise

namespace Work.ODE

section Primitive

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The integrand of the primitive operator is continuous. -/
lemma continuous_primIntegrand {δ : ℝ} (hδ : 0 ≤ δ) (u : C(Set.Icc 0 δ, E)) :
    Continuous fun s : ℝ => u (Set.projIcc 0 δ hδ s) :=
  u.continuous.comp (continuous_projIcc (a := 0) (b := δ) (h := hδ))

lemma continuous_primFun {δ : ℝ} (hδ : 0 ≤ δ) (u : C(Set.Icc 0 δ, E)) :
    Continuous fun t : ℝ => ∫ s in (0 : ℝ)..t, u (Set.projIcc 0 δ hδ s) := by
  have hc : Continuous fun s : ℝ => u (Set.projIcc 0 δ hδ s) := continuous_primIntegrand hδ u
  refine continuous_iff_continuousAt.mpr fun t => ?_
  exact (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt).continuousAt

/-- The primitive operator `u ↦ (t ↦ ∫_0^t u)` as a linear map. -/
noncomputable def primLM (δ : ℝ) (hδ : 0 ≤ δ) : C(Set.Icc 0 δ, E) →ₗ[ℝ] C(Set.Icc 0 δ, E) where
  toFun u := ⟨fun t : Set.Icc 0 δ => ∫ s in (0 : ℝ)..(t : ℝ), u (Set.projIcc 0 δ hδ s),
    (continuous_primFun hδ u).comp continuous_subtype_val⟩
  map_add' u v := by
    ext t
    show (∫ s in (0 : ℝ)..(t : ℝ), (u (Set.projIcc 0 δ hδ s) + v (Set.projIcc 0 δ hδ s)))
      = (∫ s in (0 : ℝ)..(t : ℝ), u (Set.projIcc 0 δ hδ s))
        + (∫ s in (0 : ℝ)..(t : ℝ), v (Set.projIcc 0 δ hδ s))
    rw [intervalIntegral.integral_add]
    · exact (continuous_primIntegrand hδ u).intervalIntegrable _ _
    · exact (continuous_primIntegrand hδ v).intervalIntegrable _ _
  map_smul' c u := by
    ext t
    show (∫ s in (0 : ℝ)..(t : ℝ), c • u (Set.projIcc 0 δ hδ s))
      = c • (∫ s in (0 : ℝ)..(t : ℝ), u (Set.projIcc 0 δ hδ s))
    rw [intervalIntegral.integral_smul]

@[simp]
lemma primLM_apply (δ : ℝ) (hδ : 0 ≤ δ) (u : C(Set.Icc 0 δ, E)) (t : Set.Icc 0 δ) :
    primLM δ hδ u t = ∫ s in (0 : ℝ)..(t : ℝ), u (Set.projIcc 0 δ hδ s) := rfl

lemma norm_primLM_le (δ : ℝ) (hδ : 0 ≤ δ) (u : C(Set.Icc 0 δ, E)) :
    ‖primLM δ hδ u‖ ≤ δ * ‖u‖ := by
  rw [ContinuousMap.norm_le _ (by positivity)]
  intro t
  calc ‖primLM δ hδ u t‖ = ‖∫ s in (0 : ℝ)..(t : ℝ), u (Set.projIcc 0 δ hδ s)‖ := rfl
    _ ≤ ‖u‖ * |(t : ℝ) - 0| := by
        refine intervalIntegral.norm_integral_le_of_norm_le_const (C := ‖u‖) (fun s _ => ?_)
        exact ContinuousMap.norm_coe_le_norm u (Set.projIcc 0 δ hδ s)
    _ = ‖u‖ * |(t : ℝ)| := by rw [sub_zero]
    _ ≤ ‖u‖ * δ := by
        gcongr
        rw [abs_of_nonneg t.2.1]
        exact t.2.2
    _ = δ * ‖u‖ := by ring

/-- The primitive operator as a bounded linear map. -/
noncomputable def primCLM (δ : ℝ) (hδ : 0 ≤ δ) : C(Set.Icc 0 δ, E) →L[ℝ] C(Set.Icc 0 δ, E) :=
  LinearMap.mkContinuous (primLM δ hδ) δ (norm_primLM_le δ hδ)

@[simp]
lemma primCLM_apply (δ : ℝ) (hδ : 0 ≤ δ) (u : C(Set.Icc 0 δ, E)) :
    primCLM δ hδ u = primLM δ hδ u := rfl

lemma norm_primCLM_apply_le (δ : ℝ) (hδ : 0 ≤ δ) (u : C(Set.Icc 0 δ, E)) :
    ‖primCLM δ hδ u‖ ≤ δ * ‖u‖ := by
  show ‖primLM δ hδ u‖ ≤ δ * ‖u‖
  exact norm_primLM_le δ hδ u

/-- Composition bound for the primitive operator. -/
lemma norm_primCLM_comp_le (δ : ℝ) (hδ : 0 ≤ δ) {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (B : F →L[ℝ] C(Set.Icc 0 δ, E)) :
    ‖primCLM δ hδ ∘L B‖ ≤ δ * ‖B‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun u => ?_)
  calc ‖(primCLM δ hδ ∘L B) u‖ = ‖primCLM δ hδ (B u)‖ := rfl
    _ ≤ δ * ‖B u‖ := norm_primCLM_apply_le δ hδ (B u)
    _ ≤ δ * (‖B‖ * ‖u‖) := by
        gcongr
        exact ContinuousLinearMap.le_opNorm B u
    _ = δ * ‖B‖ * ‖u‖ := by ring

end Primitive

end Work.ODE
