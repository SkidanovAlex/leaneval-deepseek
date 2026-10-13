/-
# `Work.FTS_RegExport.RXR7.Support.hasFDerivWithinAt_of_ftc`

The joint Fréchet derivative of a function given by a fundamental-theorem-of-calculus
representation in its last variable.

If, on the set `A ×ˢ B ×ˢ Icc 0 S`,

* `h z' θ' τ = h₀ z' θ' + ∫ s in 0..τ, κ z' θ' s` (the FTC representation), and
* `h₀` has derivative `L₀` at `(z,θ)`, and
* the uncurried `κ` is continuous on `A ×ˢ B ×ˢ Icc 0 S`,

then the uncurried `h` is differentiable within `A ×ˢ B ×ˢ Icc 0 S` at `(z,θ,0)`, with
derivative `L₀` on the `(z,θ)`-directions and the scalar `κ z θ 0` on the `τ`-direction.

The `(z,θ)`-part is the chain rule for `h₀` composed with the linear projection
`p ↦ (p.1, p.2.1)`; the `τ`-part is the parametric fundamental theorem of calculus at the
degenerate interval `[0,0]`, proved below as
`hasFDerivWithinAt_intervalIntegral_of_continuousOn` by an `ε`-`δ` estimate: for `p` close
to `(z,θ,0)`, the whole slice `s ↦ κ p.1 p.2.1 s`, `s ∈ [0, p.2.2]`, is within `ε` of
`κ z θ 0`, so

`|∫ s in 0..p.2.2, κ p.1 p.2.1 s − p.2.2 • κ z θ 0| ≤ ε * p.2.2 ≤ ε * ‖p − (z,θ,0)‖`.
-/
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXR7.Support

open Set Filter MeasureTheory
open scoped Topology

/-- The parametric fundamental theorem of calculus at a degenerate interval: if the
uncurried `κ` is continuous on `A ×ˢ B ×ˢ Icc 0 S`, then
`p ↦ ∫ s in 0..p.2.2, κ p.1 p.2.1 s` has derivative `κ z θ 0` in the `τ`-direction at
`(z,θ,0)`, within `A ×ˢ B ×ˢ Icc 0 S`. -/
theorem hasFDerivWithinAt_intervalIntegral_of_continuousOn {A B : Set ℝ} {S : ℝ} (hS0 : 0 ≤ S)
    {κ : ℝ → ℝ → ℝ → ℝ} {z θ : ℝ} (hz : z ∈ A) (hθ : θ ∈ B)
    (hκ : ContinuousOn (fun p : ℝ × ℝ × ℝ => κ p.1 p.2.1 p.2.2) (A ×ˢ B ×ˢ Set.Icc (0:ℝ) S)) :
    HasFDerivWithinAt (fun p : ℝ × ℝ × ℝ => ∫ s in (0:ℝ)..p.2.2, κ p.1 p.2.1 s)
      ((κ z θ 0) • ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))))
      (A ×ˢ B ×ˢ Set.Icc (0:ℝ) S) (z, θ, 0) := by
  set s : Set (ℝ × ℝ × ℝ) := A ×ˢ B ×ˢ Set.Icc (0:ℝ) S with hs
  rw [hasFDerivWithinAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  have hp0 : (z, θ, 0) ∈ s := by
    rw [hs]; simp only [Set.mem_prod, Set.mem_Icc]
    exact ⟨hz, hθ, le_rfl, hS0⟩
  obtain ⟨δ, hδpos, hδ⟩ := (Metric.continuousWithinAt_iff.mp (hκ.continuousWithinAt hp0)) c hc
  have hmem : Metric.ball (z, θ, 0) (δ / 2) ∩ s ∈ 𝓝[s] (z, θ, 0) := by
    change _ ∈ _root_.nhds (z,θ,0) ⊓ Filter.principal s
    exact Filter.mem_inf_iff.mpr ⟨_, Metric.ball_mem_nhds (z,θ,0) (by linarith), _,
      Filter.mem_principal_self _, rfl⟩
  refine Filter.mem_of_superset hmem ?_
  intro p hp
  rw [Set.mem_inter_iff, Metric.mem_ball] at hp
  obtain ⟨hdp, hps⟩ := hp
  obtain ⟨hzp, hθp, hτp⟩ : p.1 ∈ A ∧ p.2.1 ∈ B ∧ p.2.2 ∈ Set.Icc (0:ℝ) S := by
    rw [hs] at hps; simpa only [Set.mem_prod] using hps
  have hτ0 : 0 ≤ p.2.2 := hτp.1
  have hτS : p.2.2 ≤ S := hτp.2
  have hmaps : Set.MapsTo (fun x : ℝ => ((p.1, p.2.1, x) : ℝ × ℝ × ℝ))
      (Set.uIcc 0 p.2.2) s := by
    intro x hx
    rw [Set.uIcc_of_le hτ0, Set.mem_Icc] at hx
    rw [hs]
    simp only [Set.mem_prod, Set.mem_Icc]
    exact ⟨hzp, hθp, hx.1, le_trans hx.2 hτS⟩
  have hcontSlice : ContinuousOn (fun x : ℝ => κ p.1 p.2.1 x) (Set.uIcc 0 p.2.2) := by
    have hh := hκ.comp
      ((continuous_const.prodMk (continuous_const.prodMk continuous_id)).continuousOn) hmaps
    simpa [Function.comp_def] using hh
  have hint : IntervalIntegrable (fun x : ℝ => κ p.1 p.2.1 x) volume 0 p.2.2 :=
    hcontSlice.intervalIntegrable
  show ‖(∫ s in (0:ℝ)..p.2.2, κ p.1 p.2.1 s) - (∫ s in (0:ℝ)..(0:ℝ), κ z θ s) -
      ((κ z θ 0) • ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))))
        (p - (z, θ, 0))‖ ≤ c * ‖p - (z, θ, 0)‖
  have hL : ((κ z θ 0) • ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))))
      (p - (z, θ, 0)) = (κ z θ 0) * p.2.2 := by
    rw [smul_apply]
    have hc2 : ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))
        (p - (z, θ, 0)) = p.2.2 := by
      rw [ContinuousLinearMap.comp_apply]
      simp
    rw [hc2, smul_eq_mul]
  have hbound : ∀ x ∈ Set.uIoc (0:ℝ) p.2.2, ‖κ p.1 p.2.1 x - κ z θ 0‖ ≤ c := by
    intro x hx
    rw [Set.uIoc_of_le hτ0, Set.mem_Ioc] at hx
    obtain ⟨hx0, hxτ⟩ := hx
    have hxmem : ((p.1, p.2.1, x) : ℝ × ℝ × ℝ) ∈ s := by
      rw [hs]; simp only [Set.mem_prod, Set.mem_Icc]
      exact ⟨hzp, hθp, le_of_lt hx0, le_trans hxτ hτS⟩
    have hdistle : dist ((p.1, p.2.1, x) : ℝ × ℝ × ℝ) (z, θ, 0) ≤ dist p (z, θ, 0) := by
      rw [dist_eq_norm, dist_eq_norm]
      simp only [Prod.norm_def, Prod.fst_sub, Prod.snd_sub, sub_zero, Real.norm_eq_abs]
      refine max_le_max le_rfl (max_le_max le_rfl ?_)
      rw [abs_of_pos hx0, abs_of_nonneg hτ0]
      exact hxτ
    have hlt : dist (κ p.1 p.2.1 x) (κ z θ 0) < c := by
      have hh := hδ hxmem (lt_of_le_of_lt hdistle (lt_of_lt_of_le hdp (by linarith)))
      simpa using hh
    rw [dist_eq_norm] at hlt
    exact le_of_lt hlt
  have heq : ((∫ s in (0:ℝ)..p.2.2, κ p.1 p.2.1 s) - (∫ s in (0:ℝ)..(0:ℝ), κ z θ s))
      - ((κ z θ 0) • ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))))
        (p - (z, θ, 0))
      = ∫ x in (0:ℝ)..p.2.2, (κ p.1 p.2.1 x - κ z θ 0) := by
    rw [hL]
    have hdeg : (∫ s in (0:ℝ)..(0:ℝ), κ z θ s) = 0 := by
      simp [intervalIntegral.integral_same]
    rw [hdeg, sub_zero]
    rw [intervalIntegral.integral_sub hint intervalIntegrable_const, intervalIntegral.integral_const]
    simp only [sub_zero, smul_eq_mul]
    ring
  have hple : p.2.2 ≤ ‖p - (z, θ, 0)‖ := by
    have h1 : ‖(p - (z, θ, 0)).2.2‖ ≤ ‖p - (z, θ, 0)‖ :=
      le_trans (norm_snd_le _) (norm_snd_le _)
    have h2 : (p - (z, θ, 0)).2.2 = p.2.2 := by simp
    rw [h2, Real.norm_of_nonneg hτ0] at h1
    exact h1
  rw [heq]
  calc ‖∫ x in (0:ℝ)..p.2.2, (κ p.1 p.2.1 x - κ z θ 0)‖
      ≤ c * |p.2.2 - 0| := intervalIntegral.norm_integral_le_of_norm_le_const hbound
    _ = c * p.2.2 := by rw [sub_zero, abs_of_nonneg hτ0]
    _ ≤ c * ‖p - (z, θ, 0)‖ := mul_le_mul_of_nonneg_left hple hc.le

theorem hasFDerivWithinAt_of_ftc {A B : Set ℝ} {S : ℝ} (hS0 : 0 ≤ S)
    {h : ℝ → ℝ → ℝ → ℝ} {h₀ : ℝ → ℝ → ℝ} {κ : ℝ → ℝ → ℝ → ℝ}
    {z θ : ℝ} (hz : z ∈ A) (hθ : θ ∈ B) {L₀ : (ℝ × ℝ) →L[ℝ] ℝ}
    (hderiv₀ : HasFDerivAt (fun q : ℝ × ℝ => h₀ q.1 q.2) L₀ (z, θ))
    (hftc : ∀ z' ∈ A, ∀ θ' ∈ B, ∀ τ ∈ Set.Icc (0:ℝ) S,
      h z' θ' τ - h₀ z' θ' = ∫ s in (0:ℝ)..τ, κ z' θ' s)
    (hκ : ContinuousOn (fun p : ℝ × ℝ × ℝ => κ p.1 p.2.1 p.2.2) (A ×ˢ B ×ˢ Set.Icc (0:ℝ) S)) :
    HasFDerivWithinAt (fun p : ℝ × ℝ × ℝ => h p.1 p.2.1 p.2.2)
      (L₀.comp ((ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).prod
          ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))))
        + (κ z θ 0) • ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp
            (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))))
      (A ×ˢ B ×ˢ Set.Icc (0:ℝ) S) (z, θ, 0) := by
  have hp0 : (z, θ, 0) ∈ A ×ˢ B ×ˢ Set.Icc (0:ℝ) S := by
    simp only [Set.mem_prod, Set.mem_Icc]
    exact ⟨hz, hθ, le_rfl, hS0⟩
  -- the `(z,θ)`-part: `h₀` composed with the linear projection `p ↦ (p.1, p.2.1)`
  have h1 : HasFDerivWithinAt (fun p : ℝ × ℝ × ℝ => h₀ p.1 p.2.1)
      (L₀.comp ((ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).prod
          ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))))
      (A ×ˢ B ×ˢ Set.Icc (0:ℝ) S) (z, θ, 0) := by
    have hh := hderiv₀.comp_hasFDerivWithinAt (z, θ, 0)
      ((ContinuousLinearMap.hasFDerivAt ((ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).prod
          ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))))).hasFDerivWithinAt
            (s := A ×ˢ B ×ˢ Set.Icc (0:ℝ) S))
    simpa [Function.comp_def] using hh
  -- the `τ`-part: the parametric FTC at the degenerate interval
  have h2 := hasFDerivWithinAt_intervalIntegral_of_continuousOn hS0 hz hθ hκ
  have hsum := h1.add h2
  -- replace `h₀ + ∫` by `h` on the whole set
  have hEqOn : Set.EqOn (fun p : ℝ × ℝ × ℝ => h p.1 p.2.1 p.2.2)
      (fun p : ℝ × ℝ × ℝ => h₀ p.1 p.2.1 + ∫ s in (0:ℝ)..p.2.2, κ p.1 p.2.1 s)
      (A ×ˢ B ×ˢ Set.Icc (0:ℝ) S) := by
    intro p hp
    obtain ⟨hzp, hθp, hτp⟩ : p.1 ∈ A ∧ p.2.1 ∈ B ∧ p.2.2 ∈ Set.Icc (0:ℝ) S := by
      simpa only [Set.mem_prod] using hp
    have hh := hftc p.1 hzp p.2.1 hθp p.2.2 hτp
    linarith [hh]
  exact hsum.congr hEqOn (hEqOn hp0)

end Work.FTS_RegExport.RXR7.Support
