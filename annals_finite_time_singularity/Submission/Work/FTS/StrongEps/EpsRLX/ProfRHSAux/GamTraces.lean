import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.dthU_Gam

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsRLX.ProfRHSAux

open scoped Real Topology
open Filter

/-- The base `θ ↦ sin θ · cos²θ` of `Γ(θ) = (sin θ · cos²θ)^{α/3}` is continuous. -/
private theorem continuous_sin_mul_cos_sq :
    Continuous fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2 :=
  Real.continuous_sin.mul (Real.continuous_cos.pow 2)

/-- `q(θ) = cos 2θ - 1/3` is continuous. -/
private theorem continuous_qfun : Continuous Work.Spaces.qfun := by
  show Continuous fun θ : ℝ => Real.cos (2 * θ) - 1 / 3
  exact (Real.continuous_cos.comp (continuous_const.mul continuous_id)).sub continuous_const

/-- `D_θ Γ = sin(2θ)·Γ'(θ) = α·q(θ)·Γ(θ)` on the open quadrant.  This is the exact
shape in which the angular derivative of `Γ` is needed for the trace statements. -/
private theorem sin_two_mul_deriv_Gam {α θ : ℝ} (hα : 0 < α)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Real.sin (2 * θ) * deriv (Work.Spaces.Gam α) θ
      = α * Work.Spaces.qfun θ * Work.Spaces.Gam α θ := by
  have h := Work.Spaces.dthU_Gam α θ hα hθ
  simpa only [Work.Spaces.dthU_apply] using h

theorem GamTraces {α : ℝ} (hα : 0 < α) :
    Filter.Tendsto (fun θ : ℝ => Work.Spaces.Gam α θ) (𝓝[>] 0) (𝓝 0) ∧
    Filter.Tendsto (fun θ : ℝ => Work.Spaces.Gam α θ) (𝓝[<] (Real.pi / 2)) (𝓝 0) ∧
    Filter.Tendsto (fun θ : ℝ => Real.sin (2 * θ) * deriv (Work.Spaces.Gam α) θ)
      (𝓝[>] 0) (𝓝 0) ∧
    Filter.Tendsto (fun θ : ℝ => Real.sin (2 * θ) * deriv (Work.Spaces.Gam α) θ)
      (𝓝[<] (Real.pi / 2)) (𝓝 0) := by
  have hα3 : 0 < α / 3 := by positivity
  have hrpow : Continuous fun x : ℝ => x ^ (α / 3) :=
    Real.continuous_rpow_const (q := α / 3) (le_of_lt hα3)
  have hrpow0 : (0 : ℝ) ^ (α / 3) = 0 := Real.zero_rpow (ne_of_gt hα3)
  -- ## the two limits of `Γ` itself
  have hGam0 : Filter.Tendsto (fun θ : ℝ => Work.Spaces.Gam α θ) (𝓝[>] 0) (𝓝 0) := by
    change Filter.Tendsto (fun θ : ℝ => (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3))
      (𝓝[>] 0) (𝓝 0)
    have hbase : Filter.Tendsto (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2)
        (𝓝[>] 0) (𝓝 0) := by
      simpa using (continuous_sin_mul_cos_sq.tendsto 0).mono_left nhdsWithin_le_nhds
    have h := (hrpow.tendsto 0).comp hbase
    simp only [hrpow0] at h
    exact h
  have hGampi : Filter.Tendsto (fun θ : ℝ => Work.Spaces.Gam α θ)
      (𝓝[<] (Real.pi / 2)) (𝓝 0) := by
    change Filter.Tendsto (fun θ : ℝ => (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3))
      (𝓝[<] (Real.pi / 2)) (𝓝 0)
    have hbase : Filter.Tendsto (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2)
        (𝓝[<] (Real.pi / 2)) (𝓝 0) := by
      simpa using
        (continuous_sin_mul_cos_sq.tendsto (Real.pi / 2)).mono_left nhdsWithin_le_nhds
    have h := (hrpow.tendsto 0).comp hbase
    simp only [hrpow0] at h
    exact h
  -- ## the two limits of `sin(2θ)·Γ'(θ) = α·q(θ)·Γ(θ)`
  have hprod0 : Filter.Tendsto (fun θ : ℝ => α * Work.Spaces.qfun θ * Work.Spaces.Gam α θ)
      (𝓝[>] 0) (𝓝 0) := by
    have hq : Filter.Tendsto (fun θ : ℝ => α * Work.Spaces.qfun θ)
        (𝓝[>] 0) (𝓝 (α * Work.Spaces.qfun 0)) :=
      ((continuous_const.mul continuous_qfun).tendsto 0).mono_left nhdsWithin_le_nhds
    have h := hq.mul hGam0
    simpa using h
  have hprodpi : Filter.Tendsto (fun θ : ℝ => α * Work.Spaces.qfun θ * Work.Spaces.Gam α θ)
      (𝓝[<] (Real.pi / 2)) (𝓝 0) := by
    have hq : Filter.Tendsto (fun θ : ℝ => α * Work.Spaces.qfun θ)
        (𝓝[<] (Real.pi / 2)) (𝓝 (α * Work.Spaces.qfun (Real.pi / 2))) :=
      ((continuous_const.mul continuous_qfun).tendsto _).mono_left nhdsWithin_le_nhds
    have h := hq.mul hGampi
    simpa using h
  have hev0 : (fun θ : ℝ => Real.sin (2 * θ) * deriv (Work.Spaces.Gam α) θ)
      =ᶠ[𝓝[>] 0] (fun θ : ℝ => α * Work.Spaces.qfun θ * Work.Spaces.Gam α θ) := by
    show ∀ᶠ θ in 𝓝[>] 0, Real.sin (2 * θ) * deriv (Work.Spaces.Gam α) θ
      = α * Work.Spaces.qfun θ * Work.Spaces.Gam α θ
    rw [eventually_nhdsWithin_iff]
    filter_upwards [isOpen_Iio.mem_nhds
      (show (0 : ℝ) < Real.pi / 2 by linarith [Real.pi_pos])] with θ hθ hmem
    exact sin_two_mul_deriv_Gam hα ⟨hmem, hθ⟩
  have hevpi : (fun θ : ℝ => Real.sin (2 * θ) * deriv (Work.Spaces.Gam α) θ)
      =ᶠ[𝓝[<] (Real.pi / 2)] (fun θ : ℝ => α * Work.Spaces.qfun θ * Work.Spaces.Gam α θ) := by
    show ∀ᶠ θ in 𝓝[<] (Real.pi / 2), Real.sin (2 * θ) * deriv (Work.Spaces.Gam α) θ
      = α * Work.Spaces.qfun θ * Work.Spaces.Gam α θ
    rw [eventually_nhdsWithin_iff]
    filter_upwards [isOpen_Ioi.mem_nhds
      (show (0 : ℝ) < Real.pi / 2 by linarith [Real.pi_pos])] with θ hθ hmem
    exact sin_two_mul_deriv_Gam hα ⟨hθ, hmem⟩
  exact ⟨hGam0, hGampi, Filter.Tendsto.congr' hev0.symm hprod0,
    Filter.Tendsto.congr' hevpi.symm hprodpi⟩

end Work.FTS.StrongEps.EpsRLX.ProfRHSAux
