import Mathlib
import Submission.Commons.NumberTheory.Zeta.zeta_logDeriv_near_axis_bound
import Submission.Commons.NumberTheory.Zeta.zeta_zeroFree_near_axis

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open Complex Filter Metric Set
open scoped Real Topology BigOperators

noncomputable section

namespace Work.BMF.liouville

/-- **Logarithmic derivative of `ζ₁ = (s−1)·ζ`, with the pole subtracted.**

For `s ≠ 1` with `ζ s ≠ 0` one has `logDeriv ζ₁ s = ζ'(s)/ζ(s) + (s−1)⁻¹`, equivalently
`ζ'(s)/ζ(s) = (ζ₁)'(s)/ζ₁(s) − (s−1)⁻¹`.  This is the public form of the identity used
inside `Commons.NumberTheory.Zeta.zeta_logDeriv_near_axis_bound`. -/
theorem logDeriv_riemannZeta₁_eq (s : ℂ) (hs1 : s ≠ 1) (hζs : riemannZeta s ≠ 0) :
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
  erw [hmul]
  have hld_id : logDeriv (fun z : ℂ => z - 1) s = (s - 1)⁻¹ := by
    rw [logDeriv_apply]
    have hd : deriv (fun z : ℂ => z - 1) s = 1 := by simp
    rw [hd]
    simp
  rw [hld_id, logDeriv_apply]
  ring

/-- The near-axis log-derivative bound (and matching zero-free statement) extended from
`|t| ≤ 2` to `|t| ≤ 4`.  Available inputs in this workspace (import them directly):
`Submission.Commons.NumberTheory.Zeta.zeta_logDeriv_near_axis_bound` gives
`∃ C₂ δ₂, 0 < C₂ ∧ 0 < δ₂ ∧ ∀ t σ, |t| ≤ 2 → σ ≠ 1 → 1-δ₂ ≤ σ → σ ≤ 2 → ‖ζ'/ζ(σ+it)‖ ≤ C₂ + 1/‖σ+it-1‖`,
and `Submission.Commons.NumberTheory.Zeta.zeta_zeroFree_near_axis` gives
`∃ ε₀ > 0, ∀ t σ, |t| ≤ 4 → 1-ε₀ ≤ σ → σ ≤ 2 → ζ(σ+it) ≠ 0`.  On the compact set
`{1-δ ≤ σ ≤ 2, 2 ≤ |t| ≤ 4}` the function `ζ'/ζ` is continuous (no zeros there by the
zero-free input) hence bounded by some `C` (e.g. `IsCompact.exists_bound_of_continuousOn`);
there `1/‖s-1‖ > 0`, so taking `C₅ := max C₂ C` and `δ₅ := min δ₂ ε₀` gives the claim.
(The near-axis bound's conclusion uses `Complex.I * t` while this statement uses `t * Complex.I`;
these are the same complex number.) -/
theorem zeta_logDeriv_near_four :
    ∃ C₅ δ₅ : ℝ, 0 < C₅ ∧ 0 < δ₅ ∧
      (∀ (t σ : ℝ), |t| ≤ 4 → σ ≠ 1 → (1 - δ₅) ≤ σ → σ ≤ 2 →
        ‖deriv riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) /
            riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          C₅ + 1 / ‖((σ : ℂ) + (t : ℂ) * Complex.I) - 1‖) ∧
      (∀ (t σ : ℝ), |t| ≤ 4 → (1 - δ₅) ≤ σ → σ ≤ 2 →
        riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0) := by
  obtain ⟨C₂, δ₂, hC₂pos, hδ₂pos, hC₂⟩ :=
    Commons.NumberTheory.Zeta.zeta_logDeriv_near_axis_bound
  obtain ⟨ε₀, hε₀pos, hε₀⟩ := Commons.NumberTheory.Zeta.zeta_zeroFree_near_axis
  -- width of the strip: at most the already known zero-free width and the near-axis width
  let δ₅ : ℝ := min δ₂ ε₀
  have hδ₅pos : 0 < δ₅ := lt_min hδ₂pos hε₀pos
  have hδ₅le₂ : δ₅ ≤ δ₂ := min_le_left _ _
  have hδ₅leε : δ₅ ≤ ε₀ := min_le_right _ _
  -- the compact parameter region covering the range `2 ≤ |t| ≤ 4`
  let K : Set (ℝ × ℝ) :=
    Set.Icc (1 - δ₅) 2 ×ˢ (Set.Icc (-4 : ℝ) (-2) ∪ Set.Icc (2 : ℝ) 4)
  have hKcompact : IsCompact K := isCompact_Icc.prod (isCompact_Icc.union isCompact_Icc)
  have hFcont : Continuous (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I) := by fun_prop
  -- points of `K` have `2 ≤ |Im| ≤ 4`
  have hKabs : ∀ p ∈ K, 2 ≤ |p.2| ∧ |p.2| ≤ 4 := by
    intro p hp
    rcases hp.2 with h | h
    · obtain ⟨h1, h2⟩ := h
      constructor
      · rw [abs_of_nonpos (by linarith)]; linarith
      · rw [abs_of_nonpos (by linarith)]; linarith
    · obtain ⟨h1, h2⟩ := h
      constructor
      · rw [abs_of_nonneg (by linarith)]; linarith
      · rw [abs_of_nonneg (by linarith)]; linarith
  -- `ζ₁` has no zero on `K`, since `ζ₁ = (s-1)·ζ` there and `ζ` is zero-free there
  have hne : ∀ p ∈ K, riemannZeta₁ ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I) ≠ 0 := by
    intro p hp hz
    have hplo : 1 - δ₅ ≤ p.1 := hp.1.1
    have hphi : p.1 ≤ 2 := hp.1.2
    have h2 : 2 ≤ |p.2| := (hKabs p hp).1
    have h4 : |p.2| ≤ 4 := (hKabs p hp).2
    have hsne : ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I) ≠ 1 := by
      intro hcon
      have him : (((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)).im = 0 := by rw [hcon]; simp
      have hz2 : p.2 = 0 := by simpa using him
      rw [hz2, abs_zero] at h2
      linarith
    have hz0 : riemannZeta ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I) = 0 := by
      rw [riemannZeta_eq_inv_sub_mul hsne, hz, mul_zero]
    have h1 : 1 - ε₀ ≤ p.1 := by linarith
    exact (hε₀ p.2 p.1 h4 h1 hphi) (by simpa only [mul_comm (p.2 : ℂ) Complex.I] using hz0)
  -- `logDeriv ζ₁` is continuous on the compact set `K`, hence bounded there
  have hcont : ContinuousOn
      (fun p : ℝ × ℝ => logDeriv riemannZeta₁ ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)) K := by
    have hnum : ContinuousOn
        (fun p : ℝ × ℝ => deriv riemannZeta₁ ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)) K :=
      (differentiable_riemannZeta₁.deriv.continuous.comp hFcont).continuousOn
    have hden : ContinuousOn
        (fun p : ℝ × ℝ => riemannZeta₁ ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)) K :=
      (differentiable_riemannZeta₁.continuous.comp hFcont).continuousOn
    have hfun : (fun p : ℝ × ℝ => logDeriv riemannZeta₁ ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I))
        = (fun p : ℝ × ℝ => deriv riemannZeta₁ ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)) /
          (fun p : ℝ × ℝ => riemannZeta₁ ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)) := by
      funext p
      rw [Pi.div_apply, logDeriv_apply]
    rw [hfun]
    exact hnum.div hden (fun p hp => hne p hp)
  obtain ⟨C, hC⟩ := hKcompact.exists_bound_of_continuousOn hcont
  refine ⟨max C₂ (max C 1), δ₅, ?_, hδ₅pos, ?_, ?_⟩
  · exact lt_of_lt_of_le hC₂pos (le_max_left C₂ (max C 1))
  · -- log-derivative bound
    intro t σ ht hσ hlo hhi
    have hlo₂ : 1 - δ₂ ≤ σ := by linarith
    by_cases ht2 : |t| ≤ 2
    · -- near the axis: use the given bound for `|t| ≤ 2`
      have h := hC₂ t σ ht2 hσ hlo₂ hhi
      rw [mul_comm (t : ℂ) Complex.I]
      linarith [h, le_max_left C₂ (max C 1), le_max_right C₂ (max C 1)]
    · -- away from the axis: use the compactness bound
      have ht2' : 2 < |t| := lt_of_not_ge ht2
      have habs2 : 2 ≤ |t| := le_of_lt ht2'
      have htcases : t ∈ Set.Icc (-4 : ℝ) (-2) ∪ Set.Icc (2 : ℝ) 4 := by
        rcases le_total 0 t with h | h
        · refine Or.inr ⟨?_, ?_⟩
          · rwa [abs_of_nonneg h] at habs2
          · rw [abs_le] at ht; exact ht.2
        · refine Or.inl ⟨?_, ?_⟩
          · have h2 := ht; rw [abs_le] at h2; linarith [h2.1]
          · have h2 := habs2; rw [abs_of_nonpos h] at h2; linarith
      have hp : (σ, t) ∈ K := ⟨⟨hlo, hhi⟩, htcases⟩
      have hbnd : ‖logDeriv riemannZeta₁ ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C := by
        simpa using hC (σ, t) hp
      have hsne : ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 1 := by
        intro hcon
        have him : (((σ : ℂ) + (t : ℂ) * Complex.I)).im = 0 := by rw [hcon]; simp
        have ht0 : t = 0 := by simpa using him
        rw [ht0, abs_zero] at ht2'
        linarith
      have hz : riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
        have h1 : riemannZeta₁ ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
          simpa using hne (σ, t) hp
        rw [riemannZeta_eq_inv_sub_mul hsne]
        exact mul_ne_zero (inv_ne_zero (sub_ne_zero.mpr hsne)) h1
      -- translate the `ζ₁` bound into a bound for `ζ'/ζ`
      have hid := logDeriv_riemannZeta₁_eq _ hsne hz
      have heq : deriv riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) /
            riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)
          = logDeriv riemannZeta₁ ((σ : ℂ) + (t : ℂ) * Complex.I)
            - (((σ : ℂ) + (t : ℂ) * Complex.I) - 1)⁻¹ := by
        rw [hid]; ring
      have hle : C ≤ max C₂ (max C 1) :=
        le_trans (le_max_left C 1) (le_max_right C₂ (max C 1))
      calc
        ‖deriv riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) /
            riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖
            = ‖logDeriv riemannZeta₁ ((σ : ℂ) + (t : ℂ) * Complex.I)
                - (((σ : ℂ) + (t : ℂ) * Complex.I) - 1)⁻¹‖ := by rw [heq]
        _ ≤ ‖logDeriv riemannZeta₁ ((σ : ℂ) + (t : ℂ) * Complex.I)‖
              + ‖(((σ : ℂ) + (t : ℂ) * Complex.I) - 1)⁻¹‖ := norm_sub_le _ _
        _ = ‖logDeriv riemannZeta₁ ((σ : ℂ) + (t : ℂ) * Complex.I)‖
              + 1 / ‖((σ : ℂ) + (t : ℂ) * Complex.I) - 1‖ := by rw [norm_inv, one_div]
        _ ≤ C + 1 / ‖((σ : ℂ) + (t : ℂ) * Complex.I) - 1‖ := by linarith
        _ ≤ max C₂ (max C 1) + 1 / ‖((σ : ℂ) + (t : ℂ) * Complex.I) - 1‖ := by linarith
  · -- zero-free statement in the strip
    intro t σ ht hlo hhi
    have h1 : 1 - ε₀ ≤ σ := by linarith
    simpa only [mul_comm (t : ℂ) Complex.I] using hε₀ t σ ht h1 hhi

end Work.BMF.liouville
