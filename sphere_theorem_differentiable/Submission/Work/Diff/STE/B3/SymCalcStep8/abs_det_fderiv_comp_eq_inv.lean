import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3.SymCalcStep8

/-- The determinant (on continuous linear endomorphisms of `ι → ℝ`) is multiplicative. -/
private lemma clm_det_comp {ι : Type*} [Fintype ι] (f g : (ι → ℝ) →L[ℝ] (ι → ℝ)) :
    (f.comp g).det = f.det * g.det := by
  simp only [ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp]

/-- The determinant of the identity (on continuous linear endomorphisms of `ι → ℝ`) is `1`. -/
private lemma clm_det_id {ι : Type*} [Fintype ι] :
    (ContinuousLinearMap.id ℝ (ι → ℝ)).det = 1 := by
  simp only [ContinuousLinearMap.det, ContinuousLinearMap.coe_id, LinearMap.det_id]

theorem abs_det_fderiv_comp_eq_inv {ι : Type*} [Fintype ι] [DecidableEq ι]
    (τ σ : (ι → ℝ) → (ι → ℝ)) (hτ : ContDiff ℝ (⊤ : ℕ∞) τ) (hσ : ContDiff ℝ (⊤ : ℕ∞) σ)
    (U : Set (ι → ℝ)) (hU : IsOpen U) (hστ : ∀ z ∈ U, σ (τ z) = z)
    (x : ι → ℝ) (hx : x ∈ τ '' U) :
    |(fderiv ℝ σ x).det| = (|(fderiv ℝ τ (σ x)).det|)⁻¹ := by
  obtain ⟨z, hzU, rfl⟩ := hx
  -- `σ` is a left inverse of `τ` on the open set `U`, so `σ (τ z) = z`.
  have hzσ : σ (τ z) = z := hστ z hzU
  rw [hzσ]
  have hdiffτ : DifferentiableAt ℝ τ z := (hτ.differentiable (by simp)).differentiableAt
  have hdiffσ : DifferentiableAt ℝ σ (τ z) := (hσ.differentiable (by simp)).differentiableAt
  -- `σ ∘ τ` agrees with the identity near `z` (since `U` is a neighbourhood of `z`).
  have hev : (σ ∘ τ) =ᶠ[nhds z] id := by
    filter_upwards [hU.mem_nhds hzU] with y hy
    exact hστ y hy
  -- Chain rule at `z`, together with `fderiv (σ ∘ τ) z = 1`.
  have hcomp : (fderiv ℝ σ (τ z)).comp (fderiv ℝ τ z) = ContinuousLinearMap.id ℝ (ι → ℝ) := by
    rw [← fderiv_comp z hdiffσ hdiffτ, hev.fderiv_eq, fderiv_id]
  -- Hence the product of the determinants is `1`.
  have h1 : (fderiv ℝ σ (τ z)).det * (fderiv ℝ τ z).det = 1 := by
    have hc := congr_arg ContinuousLinearMap.det hcomp
    rwa [clm_det_comp, clm_det_id] at hc
  have hinv : (fderiv ℝ σ (τ z)).det = ((fderiv ℝ τ z).det)⁻¹ :=
    eq_inv_of_mul_eq_one_left h1
  calc |(fderiv ℝ σ (τ z)).det| = |((fderiv ℝ τ z).det)⁻¹| := by rw [hinv]
    _ = (|(fderiv ℝ τ z).det|)⁻¹ := abs_inv _

end Work.Diff.STE.B3.SymCalcStep8
