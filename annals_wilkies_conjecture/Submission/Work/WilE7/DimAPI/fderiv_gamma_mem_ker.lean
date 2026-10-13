import Mathlib

namespace Work.WilE7.DimAPI

theorem fderiv_gamma_mem_ker {n k : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : (Fin n → ℝ) → (Fin k → ℝ)} {p : Fin n → ℝ} (hg : AnalyticAt ℝ g p)
    {γ : E → (Fin n → ℝ)} (hγ0 : γ 0 = p) (hγan : AnalyticAt ℝ γ 0)
    (hlevel : ∀ᶠ s in nhds (0 : E), g (γ s) = g p) :
    ∀ v, (fderiv ℝ γ 0) v ∈ (fderiv ℝ g p).ker := by
  intro v
  have hg' : DifferentiableAt ℝ g (γ 0) := hγ0.symm ▸ hg.differentiableAt
  have hγ' : DifferentiableAt ℝ γ 0 := hγan.differentiableAt
  -- Chain rule: the derivative of `g ∘ γ` at `0` is the composite of the derivatives.
  have hcomp : fderiv ℝ (fun s : E => g (γ s)) 0 = (fderiv ℝ g p).comp (fderiv ℝ γ 0) := by
    have h := fderiv_comp (f := γ) (g := g) (x := (0:E)) hg' hγ'
    rwa [hγ0] at h
  -- `g ∘ γ` is eventually constant, hence has zero derivative at `0`.
  have hconst : Filter.EventuallyEq (nhds 0) (fun s : E => g (γ s)) (fun _ => g p) := hlevel
  have hzero : fderiv ℝ (fun s : E => g (γ s)) 0 = 0 := by
    rw [hconst.fderiv_eq]
    exact fderiv_const_apply (𝕜 := ℝ) (g p)
  have hcomp0 : (fderiv ℝ g p).comp (fderiv ℝ γ 0) = 0 := by
    rw [← hcomp, hzero]
  rw [LinearMap.mem_ker]
  have hf := DFunLike.congr_fun hcomp0 v
  simpa [ContinuousLinearMap.comp_apply] using hf

end Work.WilE7.DimAPI
