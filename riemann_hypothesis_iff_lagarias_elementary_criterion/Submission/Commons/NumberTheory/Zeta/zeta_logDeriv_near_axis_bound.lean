import Mathlib
import Submission.Commons.NumberTheory.Zeta.zeta_zeroFree_near_axis

open Complex Filter Metric Set
open scoped Real Topology BigOperators

noncomputable section

namespace Commons.NumberTheory.Zeta

/-- `ζ₁ = (s−1)·ζ` in logarithmic-derivative form (for `s ≠ 1` with `ζ s ≠ 0`). -/
private lemma zeta1_logDeriv_eq_aux (s : ℂ) (hs1 : s ≠ 1) (hζs : riemannZeta s ≠ 0) :
    logDeriv riemannZeta₁ s = deriv riemannZeta s / riemannZeta s + (s - 1)⁻¹ := by
  have hEq : riemannZeta₁ =ᶠ[𝓝 s] (fun z => (z - 1) * riemannZeta z) := by
    filter_upwards [eventually_ne_nhds hs1] with z hzne
    have hz := riemannZeta_eq_inv_sub_mul hzne
    calc
      riemannZeta₁ z = (z - 1) * ((z - 1)⁻¹ * riemannZeta₁ z) := by
        rw [← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr hzne)]
        simp
      _ = (z - 1) * riemannZeta z := by rw [hz]
  have hcong := logDeriv_congr_nhds hEq
  have hval : logDeriv riemannZeta₁ s = logDeriv (fun z => (z - 1) * riemannZeta z) s :=
    hcong.self_of_nhds
  rw [hval]
  have hmul := logDeriv_mul (x := s) (f := fun z => z - 1) (g := riemannZeta)
      (sub_ne_zero.mpr hs1) hζs (by fun_prop) (differentiableAt_riemannZeta hs1)
  simp only [Pi.mul_def] at hmul
  rw [hmul]
  have hld_id : logDeriv (fun z : ℂ => z - 1) s = (s - 1)⁻¹ := by
    rw [logDeriv_apply]
    have hd : deriv (fun z : ℂ => z - 1) s = 1 := by
      simp
    rw [hd]
    simp
  rw [hld_id, logDeriv_apply]
  ring

theorem zeta_logDeriv_near_axis_bound :
    ∃ C₂ δ₂ : ℝ, 0 < C₂ ∧ 0 < δ₂ ∧
      ∀ (t σ : ℝ), |t| ≤ 2 → σ ≠ 1 → (1 - δ₂) ≤ σ → σ ≤ 2 →
        ‖(deriv riemannZeta (((σ : ℂ) + Complex.I * (t : ℂ)))) /
            riemannZeta (((σ : ℂ) + Complex.I * (t : ℂ)))‖ ≤
          C₂ + 1 / ‖(((σ : ℂ) + Complex.I * (t : ℂ))) - 1‖ := by
  -- ζ is zero-free on a fixed rectangle around the real axis (Mathlib + commons).
  obtain ⟨ε₀, hε₀pos, hε₀⟩ := zeta_zeroFree_near_axis
  -- Take the strip width `δ₂` at most `ε₀` and at most `1`.
  let δ₂ : ℝ := min ε₀ 1
  have hδ₂pos : 0 < δ₂ := lt_min hε₀pos one_pos
  have hδ₂le : δ₂ ≤ ε₀ := min_le_left _ _
  -- The near-axis rectangle and the parametrising map `(σ,t) ↦ σ + i t`.
  let F : ℝ × ℝ → ℂ := fun p => (p.1 : ℂ) + Complex.I * (p.2 : ℂ)
  have hFcont : Continuous F := by fun_prop
  let P : Set (ℝ × ℝ) := Set.Icc (1 - δ₂) 2 ×ˢ Set.Icc (-2 : ℝ) 2
  have hPcompact : IsCompact P := isCompact_Icc.prod isCompact_Icc
  -- The entire completion `ζ₁ = (s-1)·ζ` has no zero in the rectangle.
  have hne : ∀ p ∈ P, riemannZeta₁ (F p) ≠ 0 := by
    intro p hp hz
    by_cases h1 : F p = 1
    · rw [h1, riemannZeta₁_one] at hz
      exact one_ne_zero hz
    · have ht4 : |p.2| ≤ 4 := by
        rw [abs_le]
        exact ⟨by linarith [hp.2.1], by linarith [hp.2.2]⟩
      have h1lo : 1 - ε₀ ≤ p.1 := by linarith [hp.1.1, hδ₂le]
      have h1hi : p.1 ≤ 2 := hp.1.2
      have hζ0 : riemannZeta (F p) = 0 := by
        rw [riemannZeta_eq_inv_sub_mul h1, hz, mul_zero]
      have hz0 : riemannZeta ((p.1 : ℂ) + Complex.I * (p.2 : ℂ)) = 0 := by
        simpa [F] using hζ0
      exact (hε₀ p.2 p.1 ht4 h1lo h1hi) hz0
  -- Continuity of `p ↦ ζ₁'/ζ₁ (F p)` on the compact rectangle.
  have hcont : ContinuousOn (fun p : ℝ × ℝ => logDeriv riemannZeta₁ (F p)) P := by
    have hnum : ContinuousOn (fun p : ℝ × ℝ => deriv riemannZeta₁ (F p)) P :=
      (differentiable_riemannZeta₁.deriv.continuous.comp hFcont).continuousOn
    have hden : ContinuousOn (fun p : ℝ × ℝ => riemannZeta₁ (F p)) P :=
      (differentiable_riemannZeta₁.continuous.comp hFcont).continuousOn
    have hdiv : ContinuousOn (fun p : ℝ × ℝ => deriv riemannZeta₁ (F p) / riemannZeta₁ (F p)) P :=
      hnum.div hden (fun p hp => hne p hp)
    simpa only [logDeriv_apply] using hdiv
  obtain ⟨C, hC⟩ := hPcompact.exists_bound_of_continuousOn hcont
  refine ⟨max C 1, δ₂, lt_of_lt_of_le zero_lt_one (le_max_right C 1), hδ₂pos, ?_⟩
  intro t σ ht hσ hlo hhi
  set s : ℂ := (σ : ℂ) + Complex.I * (t : ℂ) with hs_def
  have hsr : s.re = σ := by rw [hs_def]; simp
  have hs_ne : s ≠ 1 := by
    intro h
    have h1 : s.re = 1 := by rw [h]; simp
    rw [hsr] at h1
    exact hσ h1
  have hp : (σ, t) ∈ P := ⟨⟨hlo, hhi⟩, abs_le.mp ht⟩
  have hζ1 : riemannZeta₁ s ≠ 0 := by
    have h := hne (σ, t) hp
    simpa [F, hs_def] using h
  have hζs : riemannZeta s ≠ 0 := by
    rw [riemannZeta_eq_inv_sub_mul hs_ne]
    exact mul_ne_zero (inv_ne_zero (sub_ne_zero.mpr hs_ne)) hζ1
  have hbnd : ‖logDeriv riemannZeta₁ s‖ ≤ C := by
    have h := hC (σ, t) hp
    simpa [F, hs_def] using h
  have hid := zeta1_logDeriv_eq_aux s hs_ne hζs
  have hnorm : ‖deriv riemannZeta s / riemannZeta s‖ ≤
      ‖logDeriv riemannZeta₁ s‖ + ‖(s - 1)⁻¹‖ := by
    have heq : deriv riemannZeta s / riemannZeta s = logDeriv riemannZeta₁ s - (s - 1)⁻¹ := by
      rw [hid]; ring
    rw [heq]
    exact norm_sub_le _ _
  calc
    ‖deriv riemannZeta s / riemannZeta s‖ ≤ ‖logDeriv riemannZeta₁ s‖ + ‖(s - 1)⁻¹‖ := hnorm
    _ = ‖logDeriv riemannZeta₁ s‖ + 1 / ‖s - 1‖ := by rw [norm_inv, one_div]
    _ ≤ C + 1 / ‖s - 1‖ := by linarith [hbnd]
    _ ≤ max C 1 + 1 / ‖s - 1‖ := by linarith [le_max_left C 1]

end Commons.NumberTheory.Zeta
