/-
Copyright: work module for the Elgindi finite-time singularity project.

# Local integrability of the square root of the `D`-functional

`Work.FTS.StrongEps.EpsLocalPStar.SqrtDLocInt`.

For `α ∈ (0,1]`, `f` of class `ℋ¹` (`Work.Spaces.HkMem α 1 f`) and `0 < a`, the
`u ↦ √(D α f u)` is `∫⁻`-locally finite on `[a,b]`, where

  `D α f u = ∫ σ in Iθ, sin(2σ)^{2-γ} · (∂_θ f u σ)²`,  `γ = gam α = 1 + α/10`.

The proof is the pointwise reduction to the `(D_θ)`-slot of the `ℋ¹`-integrand:

  `sin(2σ)^{2-γ} (∂_θ f u σ)² = (D_θ f u σ)² sin(2σ)^{-γ} / w(u)²`
  `  ≤ (D_θ f u σ · Wt α u σ)² = (mixed 0 1 f u σ · Wt α u σ)² ≤ HkIntegrand α 1 f u σ`

(the middle inequality is the elementary `w(u) ≥ 1` for `u > 0`, together with
`sin(2σ)^{2-γ} = sin(2σ)² · sin(2σ)^{-γ}`, which holds because `sin(2σ) ≥ 0` on `Iθ`
and `γ ∉ {0,2}`).  Integrating in `σ` and using `HkMem α 1 f` gives
`D α f u ≤ F(u) := ∫ σ in Iθ, HkIntegrand α 1 f u σ` for every `u > 0`; since
`√x ≤ x + 1`, the integrand is dominated by `ofReal (F u + 1)`, and `F + 1` is
integrable on the compact interval `[a,b] ⊆ (0,∞)`, whence
`IntegrableOn.setLIntegral_lt_top`.

This is exactly the hypothesis `hD` of `EpsLocalPStar/LamLocInt.lean`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkSq_terms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsLocalPStar

set_option autoImplicit false

/-- `sin(2σ) ≥ 0` on the angular interval `Iθ = [0,π/2]`. -/
theorem SqrtD_sin_two_nonneg {σ : ℝ} (hσ : σ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * σ) :=
  Real.sin_nonneg_of_mem_Icc ⟨by linarith [hσ.1], by linarith [hσ.2, Real.pi_pos]⟩

/-- The radial weight is bounded below by `1` on the half-line: `1 ≤ w(u)²` for `u > 0`. -/
theorem SqrtD_one_le_w_sq {u : ℝ} (hu : 0 < u) : 1 ≤ (Work.Spaces.w u) ^ 2 := by
  have h1 : 1 ≤ Work.Spaces.w u := by
    rw [Work.Spaces.w, le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg u]
  exact one_le_pow₀ h1

/-- **The pointwise reduction to the `D_θ`-slot of the `ℋ¹`-integrand.**  For `u > 0` and
`σ ∈ Iθ`, the integrand of `D α f u` is dominated by the `(i,j) = (1,0)` summand of
`HkIntegrand α 1 f u ·`. -/
theorem SqrtD_integrand_le_HkIntegrand {α : ℝ} (hα : α ∈ Set.Ioc 0 1) {f : ℝ → ℝ → ℝ}
    {u σ : ℝ} (hu : 0 < u) (hσ : σ ∈ Work.Spaces.Iθ) :
    (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α) * (Work.Spaces.pth f u σ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 1 f u σ := by
  have hγ0 : Work.Spaces.gam α ≠ 0 := by
    have := Work.Spaces.one_lt_gam hα.1; linarith
  have hγ2 : Work.Spaces.gam α ≠ 2 := by
    intro h; linarith [Work.Spaces.gam_sub_one α, hα.2, h]
  have hs : 0 ≤ Real.sin (2 * σ) := SqrtD_sin_two_nonneg hσ
  have hw : 1 ≤ (Work.Spaces.w u) ^ 2 := SqrtD_one_le_w_sq hu
  -- `sin(2σ)^{2-γ} = sin(2σ)² · sin(2σ)^{-γ}`
  have h1 : (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)
      = (Real.sin (2 * σ)) ^ 2 * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) := by
    have h : (2 : ℝ) + (-(Work.Spaces.gam α)) ≠ 0 := by
      intro hh; exact hγ2 (by linarith)
    calc (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)
        = (Real.sin (2 * σ)) ^ ((2 : ℝ) + (-(Work.Spaces.gam α))) := rfl
      _ = (Real.sin (2 * σ)) ^ (2 : ℝ) * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) :=
            Real.rpow_add' hs h
      _ = (Real.sin (2 * σ)) ^ 2 * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) := by
            rw [Real.rpow_two]
  -- `sin(2σ)^{-γ} = (sin(2σ)^{-γ/2})²`
  have h2 : (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
      = ((Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2 := by
    have h : (-(Work.Spaces.gam α / 2)) + (-(Work.Spaces.gam α / 2)) ≠ 0 := by
      intro hh; exact hγ0 (by linarith)
    calc (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
        = (Real.sin (2 * σ)) ^ ((-(Work.Spaces.gam α / 2)) + (-(Work.Spaces.gam α / 2))) := by
            ring_nf
      _ = (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α / 2))
            * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α / 2)) := Real.rpow_add' hs h
      _ = ((Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2 := by ring
  -- expansion of the `HkIntegrand`-summand as `sin(2σ)^{2-γ}(∂_θf)² · w(u)²`
  have hsq : (Work.Spaces.mixed 0 1 f u σ * Work.Spaces.Wt α u σ) ^ 2
      = (Real.sin (2 * σ)) ^ 2 * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.pth f u σ) ^ 2 * (Work.Spaces.w u) ^ 2 := by
    rw [h2]
    simp only [Work.Spaces.mixed, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_succ,
      Work.Spaces.DthIter_zero, Work.Spaces.Dth, Work.Spaces.Wt, Work.Spaces.wTheta]
    ring
  refine le_trans ?_ (Work.Spaces.sq_le_HkIntegrand_mixed α 1 f u σ 1 0 le_rfl (by norm_num))
  calc (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α) * (Work.Spaces.pth f u σ) ^ 2
      = (Real.sin (2 * σ)) ^ 2 * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.pth f u σ) ^ 2 := by rw [h1]
    _ ≤ (Real.sin (2 * σ)) ^ 2 * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.pth f u σ) ^ 2 * (Work.Spaces.w u) ^ 2 :=
        le_mul_of_one_le_right
          (mul_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs _)) (sq_nonneg _)) hw
    _ = (Work.Spaces.mixed 0 1 f u σ * Work.Spaces.Wt α u σ) ^ 2 := hsq.symm

theorem SqrtDLocInt {α : ℝ} (hα : α ∈ Set.Ioc 0 1) {f : ℝ → ℝ → ℝ}
    (hm : Work.Spaces.HkMem α 1 f) {a b : ℝ} (ha : 0 < a) :
    ∫⁻ u in Set.Icc a b, ENNReal.ofReal (Real.sqrt (∫ σ in Work.Spaces.Iθ,
        (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α) * (Work.Spaces.pth f u σ) ^ 2)) < ⊤ := by
  -- Step 1: the `σ`-integral of the integrand is dominated by `F(u) = ∫ HkIntegrand α 1 f u`.
  have hDle : ∀ u ∈ Set.Ioi (0 : ℝ),
      (∫ σ in Work.Spaces.Iθ,
          (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α) * (Work.Spaces.pth f u σ) ^ 2)
        ≤ ∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 f u σ := by
    intro u hu
    have hu0 : 0 < u := Set.mem_Ioi.mp hu
    refine MeasureTheory.integral_mono_of_nonneg ?_ (hm.1 u (le_of_lt hu0)) ?_
    · exact MeasureTheory.ae_restrict_of_forall_mem
        (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)
        (fun σ hσ => mul_nonneg (Real.rpow_nonneg (SqrtD_sin_two_nonneg hσ) _) (sq_nonneg _))
    · exact MeasureTheory.ae_restrict_of_forall_mem
        (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)
        (fun σ hσ => SqrtD_integrand_le_HkIntegrand hα hu0 hσ)
  -- Step 2: `u ↦ F(u) + 1` is integrable on the compact interval `[a,b] ⊆ (0,∞)`.
  have hsub : Set.Icc a b ⊆ Work.Spaces.Iz := fun u hu => le_of_lt (lt_of_lt_of_le ha hu.1)
  have hFint : MeasureTheory.IntegrableOn
      (fun u => ∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 f u σ) (Set.Icc a b) :=
    hm.2.mono_set hsub
  have hvol : MeasureTheory.volume (Set.Icc a b) < ⊤ := by
    rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top
  have h1int : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Icc a b) :=
    MeasureTheory.integrableOn_const (ne_of_lt hvol)
  have hH : MeasureTheory.IntegrableOn
      (fun u => (∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 f u σ) + 1)
      (Set.Icc a b) :=
    hFint.add h1int
  -- Step 3: pointwise `√(D α f u) ≤ F(u) + 1` on `[a,b]`, hence the lintegral bound.
  refine lt_of_le_of_lt ?_ hH.setLIntegral_lt_top
  refine MeasureTheory.lintegral_mono_ae ?_
  refine MeasureTheory.ae_restrict_of_forall_mem
    (show MeasurableSet (Set.Icc a b) from measurableSet_Icc) (fun u hu => ?_)
  have hu0 : 0 < u := lt_of_lt_of_le ha hu.1
  have hFnn : 0 ≤ ∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 f u σ :=
    integral_nonneg (fun σ => Work.Spaces.HkIntegrand_nonneg α 1 f u σ)
  have hle : Real.sqrt (∫ σ in Work.Spaces.Iθ,
        (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α) * (Work.Spaces.pth f u σ) ^ 2)
      ≤ (∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 f u σ) + 1 := by
    rw [Real.sqrt_le_left (by linarith)]
    have h1 := hDle u (Set.mem_Ioi.mpr hu0)
    nlinarith [sq_nonneg ((∫ σ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 1 f u σ) + 1 / 2)]
  exact ENNReal.ofReal_le_ofReal hle

end Work.FTS.StrongEps.EpsLocalPStar
