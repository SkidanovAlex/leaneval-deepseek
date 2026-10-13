import Mathlib
import Submission.Work.WilE9G.Sard.levelSetChartAnalytic

namespace Work.WilE9G.Sard

/-- For continuous linear maps, the range of `f ∘ g` equals the range of `f` as soon as the
inner map `g` is surjective.  Stated here because the coercion of `ContinuousLinearMap.comp`
to a `LinearMap` is not syntactically `LinearMap.comp`, so `LinearMap.range_comp_of_range_eq_top`
cannot be applied directly to a composite of continuous linear maps. -/
theorem clm_range_comp_eq {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    (f : F →L[𝕜] G) (g : E →L[𝕜] F) (hg : g.range = ⊤) : (f.comp g).range = f.range := by
  rw [show (f.comp g : E →ₗ[𝕜] G) = (f : F →ₗ[𝕜] G).comp (g : E →ₗ[𝕜] F) from rfl,
    LinearMap.range_comp_of_range_eq_top (f := (g : E →ₗ[𝕜] F)) (g := (f : F →ₗ[𝕜] G)) hg]

/-- Transport a level-set chart along a continuous linear equivalence `e` from the model space
of the level set `(fderiv ℝ h z₀).ker` to `Fin r → ℝ`, reindexing the parametrisation `γ`
and the inverse chart `C` correspondingly. -/
theorem levelSetChartTransport {Q j r : ℕ} (h : (Fin Q → ℝ) → (Fin j → ℝ)) (z₀ : Fin Q → ℝ)
    (e : (Fin r → ℝ) ≃L[ℝ] (fderiv ℝ h z₀).ker)
    (C : (Fin Q → ℝ) →L[ℝ] (fderiv ℝ h z₀).ker)
    (γ : (fderiv ℝ h z₀).ker → (Fin Q → ℝ))
    (V : Set (fderiv ℝ h z₀).ker) (U : Set (Fin Q → ℝ))
    (hV : IsOpen V) (hU : IsOpen U) (h0V : (0 : (fderiv ℝ h z₀).ker) ∈ V) (hz₀U : z₀ ∈ U)
    (hγ0 : γ 0 = z₀) (hγan : ∀ t ∈ V, AnalyticAt ℝ γ t)
    (hγU : ∀ t ∈ V, γ t ∈ U) (hγh : ∀ t ∈ V, h (γ t) = h z₀)
    (hχ : ∀ y ∈ U, h y = h z₀ → C (y - z₀) ∈ V ∧ γ (C (y - z₀)) = y)
    (hrange : ∀ t ∈ V, (fderiv ℝ γ t).range = (fderiv ℝ h (γ t)).ker) :
    ∃ (γ' : (Fin r → ℝ) → (Fin Q → ℝ)) (C' : (Fin Q → ℝ) →L[ℝ] (Fin r → ℝ))
      (V' : Set (Fin r → ℝ)) (U' : Set (Fin Q → ℝ)),
      IsOpen V' ∧ IsOpen U' ∧ (0 : Fin r → ℝ) ∈ V' ∧ z₀ ∈ U' ∧ γ' 0 = z₀ ∧ AnalyticAt ℝ γ' 0 ∧
      (∀ t ∈ V', γ' t ∈ U') ∧ (∀ t ∈ V', h (γ' t) = h z₀) ∧
      (∀ y ∈ U', h y = h z₀ → C' (y - z₀) ∈ V' ∧ γ' (C' (y - z₀)) = y) ∧
      (∀ t ∈ V', (fderiv ℝ γ' t).range = (fderiv ℝ h (γ' t)).ker) := by
  refine ⟨γ ∘ ⇑e, (e.symm : (fderiv ℝ h z₀).ker →L[ℝ] (Fin r → ℝ)).comp C,
    ⇑e ⁻¹' V, U, hV.preimage e.continuous, hU, ?_, hz₀U, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show e 0 ∈ V; rw [map_zero]; exact h0V
  · show γ (e 0) = z₀; rw [map_zero, hγ0]
  · exact AnalyticAt.comp (x := 0) (f := (e : (Fin r → ℝ) → (fderiv ℝ h z₀).ker))
      (hγan (e 0) (by show e 0 ∈ V; rw [map_zero]; exact h0V))
      (ContinuousLinearMap.analyticAt (e : (Fin r → ℝ) →L[ℝ] (fderiv ℝ h z₀).ker) 0)
  · intro t ht; exact hγU (e t) ht
  · intro t ht; exact hγh (e t) ht
  · intro y hy hyh
    obtain ⟨hCV, hγy⟩ := hχ y hy hyh
    refine ⟨?_, ?_⟩
    · show e (((e.symm : (fderiv ℝ h z₀).ker →L[ℝ] (Fin r → ℝ)).comp C) (y - z₀)) ∈ V
      have hsymm : ((e.symm : (fderiv ℝ h z₀).ker →L[ℝ] (Fin r → ℝ)).comp C) (y - z₀)
          = e.symm (C (y - z₀)) := rfl
      rw [hsymm, ContinuousLinearEquiv.apply_symm_apply]
      exact hCV
    · show γ (e (((e.symm : (fderiv ℝ h z₀).ker →L[ℝ] (Fin r → ℝ)).comp C) (y - z₀))) = y
      have hsymm : ((e.symm : (fderiv ℝ h z₀).ker →L[ℝ] (Fin r → ℝ)).comp C) (y - z₀)
          = e.symm (C (y - z₀)) := rfl
      rw [hsymm, ContinuousLinearEquiv.apply_symm_apply, hγy]
  · intro t ht
    have hcomp : fderiv ℝ (γ ∘ ⇑e) t =
        (fderiv ℝ γ (e t)).comp (e : (Fin r → ℝ) →L[ℝ] (fderiv ℝ h z₀).ker) := by
      have h1 : fderiv ℝ (γ ∘ ⇑e) t =
          (fderiv ℝ γ (e t)).comp (fderiv ℝ (e : (Fin r → ℝ) → (fderiv ℝ h z₀).ker) t) :=
        fderiv_comp (f := (e : (Fin r → ℝ) → (fderiv ℝ h z₀).ker)) (g := γ) t
          ((hγan (e t) ht).differentiableAt)
          (ContinuousLinearMap.differentiableAt (e : (Fin r → ℝ) →L[ℝ] (fderiv ℝ h z₀).ker))
      rw [h1, ContinuousLinearEquiv.fderiv]
    rw [hcomp]
    have hesurj : (e : (Fin r → ℝ) →L[ℝ] (fderiv ℝ h z₀).ker).range = ⊤ := by
      rw [LinearMap.range_eq_top]
      exact e.surjective
    rw [clm_range_comp_eq (fderiv ℝ γ (e t))
      (e : (Fin r → ℝ) →L[ℝ] (fderiv ℝ h z₀).ker) hesurj]
    exact hrange (e t) ht

end Work.WilE9G.Sard
