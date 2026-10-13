import Mathlib
import Submission.Work.WilE7.DimAPI.exists_coordProj_surj_of_le_finrank

namespace Work.WilE7.CoreStep

/-- Derivative at a point of a linear map composed with an analytic map. -/
theorem fderiv_comp_linearMap_at {K n m : ℕ}
    (L : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (β : (Fin K → ℝ) → (Fin n → ℝ)) (x₀ : Fin K → ℝ) (hβ : AnalyticAt ℝ β x₀) :
    fderiv ℝ (fun x => L (β x)) x₀ = L.toContinuousLinearMap ∘SL fderiv ℝ β x₀ := by
  have hA' : HasFDerivAt β (fderiv ℝ β x₀) x₀ := hβ.differentiableAt.hasFDerivAt
  have h2 : HasFDerivAt (fun y => L y) L.toContinuousLinearMap (β x₀) := by
    simpa [LinearMap.coe_toContinuousLinearMap] using (L.toContinuousLinearMap.hasFDerivAt)
  exact (h2.comp x₀ hA').fderiv

/-- **Submersion reduction of rank.**

An analytic map `β : ℝ^K → ℝⁿ` whose differential at `p` has rank `m` can be replaced,
as far as the fibre `β⁻¹(β p)` is concerned, by a map `g : ℝ^K → ℝ^m` which is a submersion
at `p` (its differential there has range `⊤`) and is constant on the fibre of `β` through `p`.

Concretely, `g = L ∘ β` where `L : ℝⁿ → ℝ^m` is a linear surjection that is surjective on the
range of `fderiv ℝ β p`; such an `L` exists by `exists_coordProj_surj_of_le_finrank`. -/
theorem submersionReductionOfRank {K n m : ℕ}
    (β : (Fin K → ℝ) → (Fin n → ℝ)) (hβ : ∀ x, AnalyticAt ℝ β x) (p : Fin K → ℝ)
    (hrank : Module.finrank ℝ (fderiv ℝ β p).range = m) :
    ∃ g : (Fin K → ℝ) → (Fin m → ℝ),
      (∀ x, AnalyticAt ℝ g x) ∧ (fderiv ℝ g p).range = ⊤ ∧
      (∀ x, β x = β p → g x = g p) := by
  classical
  -- The differential of `β` at `p`, as a linear map.
  set A : (Fin K → ℝ) →ₗ[ℝ] (Fin n → ℝ) := (fderiv ℝ β p).toLinearMap with hA
  have hrankA : Module.finrank ℝ A.range = m := hrank
  -- A coordinate projection surjective on the range of `A`.
  obtain ⟨e, he⟩ := Work.WilE7.DimAPI.exists_coordProj_surj_of_le_finrank
      (M := K) (n := n) (m := m) A (le_of_eq hrankA.symm)
  -- The corresponding linear map `L y = y ∘ e : ℝⁿ → ℝ^m`.
  set L : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ) :=
    LinearMap.pi (fun j : Fin m => (LinearMap.proj (e j) : (Fin n → ℝ) →ₗ[ℝ] ℝ)) with hL
  have hL_apply : ∀ v : Fin n → ℝ, L v = v ∘ e := by
    intro v; funext j; simp [hL, LinearMap.pi_apply, LinearMap.proj_apply]
  -- `L` is surjective on the range of `A`, hence `L ∘ A` is onto.
  have hsurj : Function.Surjective ⇑(L.comp A) := by
    have hfun : ⇑(L.comp A) = (fun v : Fin K → ℝ => (A v) ∘ e) := by
      funext v; rw [LinearMap.comp_apply]; exact hL_apply (A v)
    rw [hfun]; exact he
  have hcoe : ⇑(L.toContinuousLinearMap ∘SL fderiv ℝ β p) = ⇑(L.comp A) := by
    ext v; simp [hA]
  have hrange : (fderiv ℝ (fun x => L (β x)) p).range = ⊤ := by
    rw [fderiv_comp_linearMap_at L β p (hβ p)]
    exact LinearMap.range_eq_top.mpr (hcoe.symm ▸ hsurj)
  refine ⟨fun x => L (β x), ?_, hrange, ?_⟩
  · -- analyticity of the composite `L ∘ β`
    intro x
    have h1 : AnalyticAt ℝ (fun y => L y) (β x) := by
      simpa [LinearMap.coe_toContinuousLinearMap] using
        (L.toContinuousLinearMap.analyticAt (β x))
    exact h1.comp (hβ x)
  · -- constancy on the fibre of `β` through `p`
    intro x hx
    exact congrArg L hx

end Work.WilE7.CoreStep
