import Mathlib

namespace Work.Potential

open scoped Interval Topology
open MeasureTheory

/-- Differentiation under the integral sign for the Fourier-type strip integral
`s ↦ ∫ θ in 0..2π, f (s + θ i) * exp (-(k θ) i)`, where `f` is `C²` (in the real sense) on the
open strip `δ₁ < re w < δ₂` containing `s₀`. -/
theorem strip_integral_hasDerivAt
    {f : ℂ → ℂ} {δ₁ δ₂ : ℝ} {k : ℤ} {s₀ : ℝ} (h₁ : δ₁ < s₀) (h₂ : s₀ < δ₂)
    (hf : ∀ w : ℂ, δ₁ < w.re → w.re < δ₂ → ContDiffAt ℝ 2 f w) :
    HasDerivAt
      (fun s : ℝ => ∫ θ in (0 : ℝ)..(2 * Real.pi),
        f ((s : ℂ) + (θ : ℂ) * Complex.I) * Complex.exp (-(((k : ℝ) * θ : ℂ) * Complex.I)))
      (∫ θ in (0 : ℝ)..(2 * Real.pi),
        (fderiv ℝ f ((s₀ : ℂ) + (θ : ℂ) * Complex.I) 1) *
          Complex.exp (-(((k : ℝ) * θ : ℂ) * Complex.I))) s₀ := by
  -- a small symmetric interval around `s₀` on which the strip condition holds
  obtain ⟨ε, hε_pos, hε₁, hε₂⟩ : ∃ ε : ℝ, 0 < ε ∧ δ₁ < s₀ - ε ∧ s₀ + ε < δ₂ := by
    refine ⟨min ((s₀ - δ₁) / 2) ((δ₂ - s₀) / 2), lt_min (by linarith) (by linarith), ?_, ?_⟩
    · have := min_le_left ((s₀ - δ₁) / 2) ((δ₂ - s₀) / 2); linarith
    · have := min_le_right ((s₀ - δ₁) / 2) ((δ₂ - s₀) / 2); linarith
  have hS_ev : ∀ᶠ x in 𝓝 s₀, x ∈ Set.Ioo (s₀ - ε) (s₀ + ε) :=
    isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩
  have hS_nhds : Set.Ioo (s₀ - ε) (s₀ + ε) ∈ 𝓝 s₀ := hS_ev
  have hS_strip : ∀ x ∈ Set.Ioo (s₀ - ε) (s₀ + ε), δ₁ < x ∧ x < δ₂ := by
    intro x hx
    exact ⟨by linarith [hx.1, hε₁], by linarith [hx.2, hε₂]⟩
  -- the compact box on which the derivative of `f` is bounded
  have hK_compact : IsCompact ((fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I) ''
      (Set.Icc (s₀ - ε) (s₀ + ε) ×ˢ Set.Icc 0 (2 * Real.pi))) := by
    exact (isCompact_Icc.prod isCompact_Icc).image (by fun_prop)
  have hK_strip : ∀ w ∈ ((fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I) ''
      (Set.Icc (s₀ - ε) (s₀ + ε) ×ˢ Set.Icc 0 (2 * Real.pi))), δ₁ < w.re ∧ w.re < δ₂ := by
    intro w hw
    obtain ⟨⟨x, θ⟩, ⟨hxI, hθI⟩, rfl⟩ := hw
    have hwre : ((x : ℂ) + (θ : ℂ) * Complex.I).re = x := by simp
    exact ⟨by rw [hwre]; linarith [hxI.1, hε₁], by rw [hwre]; linarith [hxI.2, hε₂]⟩
  have hK_fderiv_cont : ContinuousOn (fun w : ℂ => fderiv ℝ f w)
      ((fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I) ''
      (Set.Icc (s₀ - ε) (s₀ + ε) ×ˢ Set.Icc 0 (2 * Real.pi))) := by
    intro w hw
    obtain ⟨h1, h2⟩ := hK_strip w hw
    exact ((hf w h1 h2).continuousAt_fderiv (by norm_num)).continuousWithinAt
  obtain ⟨C, hC⟩ := hK_compact.exists_bound_of_continuousOn hK_fderiv_cont
  -- continuity in `θ` of the integrand, for `x` in the strip
  have hcontF : ∀ x : ℝ, δ₁ < x → x < δ₂ → Continuous (fun θ : ℝ =>
      f ((x : ℂ) + (θ : ℂ) * Complex.I) * Complex.exp (-(((k : ℝ) * θ : ℂ) * Complex.I))) := by
    intro x hx1 hx2
    have h1 : Continuous (fun θ : ℝ => f ((x : ℂ) + (θ : ℂ) * Complex.I)) := by
      refine continuous_iff_continuousAt.mpr fun θ => ?_
      have hw : ((x : ℂ) + (θ : ℂ) * Complex.I).re = x := by simp
      exact ((hf _ (by rw [hw]; exact hx1) (by rw [hw]; exact hx2)).continuousAt).comp
        (by fun_prop)
    have h2 : Continuous (fun θ : ℝ => Complex.exp (-(((k : ℝ) * θ : ℂ) * Complex.I))) := by
      fun_prop
    exact h1.mul h2
  have hcontF' : ∀ x : ℝ, δ₁ < x → x < δ₂ → Continuous (fun θ : ℝ =>
      (fderiv ℝ f ((x : ℂ) + (θ : ℂ) * Complex.I) 1) *
        Complex.exp (-(((k : ℝ) * θ : ℂ) * Complex.I))) := by
    intro x hx1 hx2
    have h0 : Continuous (fun θ : ℝ => fderiv ℝ f ((x : ℂ) + (θ : ℂ) * Complex.I)) := by
      refine continuous_iff_continuousAt.mpr fun θ => ?_
      have hw : ((x : ℂ) + (θ : ℂ) * Complex.I).re = x := by simp
      exact ((hf _ (by rw [hw]; exact hx1) (by rw [hw]; exact hx2)).continuousAt_fderiv
        (by norm_num)).comp (by fun_prop)
    have h1 : Continuous (fun θ : ℝ => fderiv ℝ f ((x : ℂ) + (θ : ℂ) * Complex.I) 1) := by
      simpa using h0.clm_apply continuous_const
    have h2 : Continuous (fun θ : ℝ => Complex.exp (-(((k : ℝ) * θ : ℂ) * Complex.I))) := by
      fun_prop
    exact h1.mul h2
  -- the uniform bound on the derivative of the integrand
  have hbound : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ι (0:ℝ) (2 * Real.pi) →
      ∀ x ∈ Set.Ioo (s₀ - ε) (s₀ + ε), ‖(fderiv ℝ f ((x : ℂ) + (t : ℂ) * Complex.I) 1) *
        Complex.exp (-(((k : ℝ) * t : ℂ) * Complex.I))‖ ≤ C := by
    refine Filter.Eventually.of_forall fun t ht x hx => ?_
    have hxI : x ∈ Set.Icc (s₀ - ε) (s₀ + ε) := ⟨le_of_lt hx.1, le_of_lt hx.2⟩
    have htI : t ∈ Set.Icc (0:ℝ) (2 * Real.pi) := by
      rw [Set.uIoc, min_eq_left (by positivity : (0:ℝ) ≤ 2 * Real.pi),
        max_eq_right (by positivity : (0:ℝ) ≤ 2 * Real.pi)] at ht
      exact ⟨le_of_lt ht.1, ht.2⟩
    have hxK : (x : ℂ) + (t : ℂ) * Complex.I ∈
        ((fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I) ''
        (Set.Icc (s₀ - ε) (s₀ + ε) ×ˢ Set.Icc 0 (2 * Real.pi))) :=
      ⟨(x, t), ⟨hxI, htI⟩, rfl⟩
    have hexp : ‖Complex.exp (-(((k : ℝ) * t : ℂ) * Complex.I))‖ = 1 :=
      by simpa using Complex.norm_exp_ofReal_mul_I (-((k : ℝ) * t))
    calc ‖(fderiv ℝ f ((x : ℂ) + (t : ℂ) * Complex.I) 1) *
            Complex.exp (-(((k : ℝ) * t : ℂ) * Complex.I))‖
        = ‖fderiv ℝ f ((x : ℂ) + (t : ℂ) * Complex.I) 1‖ * 1 := by rw [norm_mul, hexp]
      _ = ‖fderiv ℝ f ((x : ℂ) + (t : ℂ) * Complex.I) 1‖ := by rw [mul_one]
      _ ≤ ‖fderiv ℝ f ((x : ℂ) + (t : ℂ) * Complex.I)‖ := by
            simpa using ContinuousLinearMap.le_opNorm
              (fderiv ℝ f ((x : ℂ) + (t : ℂ) * Complex.I)) (1 : ℂ)
      _ ≤ C := hC _ hxK
  -- pointwise differentiability of the integrand in the parameter
  have hdiff : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ι (0:ℝ) (2 * Real.pi) →
      ∀ x ∈ Set.Ioo (s₀ - ε) (s₀ + ε), HasDerivAt (fun u : ℝ =>
          f ((u : ℂ) + (t : ℂ) * Complex.I) *
            Complex.exp (-(((k : ℝ) * t : ℂ) * Complex.I)))
        ((fderiv ℝ f ((x : ℂ) + (t : ℂ) * Complex.I) 1) *
          Complex.exp (-(((k : ℝ) * t : ℂ) * Complex.I))) x := by
    refine Filter.Eventually.of_forall fun t ht x hx => ?_
    have hx1 : δ₁ < x := (hS_strip x hx).1
    have hx2 : x < δ₂ := (hS_strip x hx).2
    have hφ : HasDerivAt (fun u : ℝ => (u : ℂ) + (t : ℂ) * Complex.I) (1 : ℂ) x := by
      simpa using (ContinuousLinearMap.hasDerivAt Complex.ofRealCLM (x := x)).add_const
        ((t : ℂ) * Complex.I)
    have hw1 : δ₁ < ((x : ℂ) + (t : ℂ) * Complex.I).re := by
      rw [show ((x : ℂ) + (t : ℂ) * Complex.I).re = x from by simp]; exact hx1
    have hw2 : ((x : ℂ) + (t : ℂ) * Complex.I).re < δ₂ := by
      rw [show ((x : ℂ) + (t : ℂ) * Complex.I).re = x from by simp]; exact hx2
    have hinner : HasDerivAt (fun u : ℝ => f ((u : ℂ) + (t : ℂ) * Complex.I))
        (fderiv ℝ f ((x : ℂ) + (t : ℂ) * Complex.I) 1) x :=
      ((hf _ hw1 hw2).differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt x hφ
    exact hinner.mul_const _
  obtain ⟨-, hmain⟩ :=
    intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (𝕜 := ℝ) (μ := (volume : Measure ℝ)) (a := (0:ℝ)) (b := 2 * Real.pi) (x₀ := s₀)
      (s := Set.Ioo (s₀ - ε) (s₀ + ε))
      (F := fun s θ => f ((s : ℂ) + (θ : ℂ) * Complex.I) *
        Complex.exp (-(((k : ℝ) * θ : ℂ) * Complex.I)))
      (F' := fun s θ => (fderiv ℝ f ((s : ℂ) + (θ : ℂ) * Complex.I) 1) *
        Complex.exp (-(((k : ℝ) * θ : ℂ) * Complex.I)))
      (bound := fun _ => C)
      hS_nhds
      (hS_ev.mono fun x hx =>
        (hcontF x (hS_strip x hx).1 (hS_strip x hx).2).aestronglyMeasurable)
      ((hcontF s₀ h₁ h₂).continuousOn.mono (Set.subset_univ _)).intervalIntegrable
      ((hcontF' s₀ h₁ h₂).aestronglyMeasurable)
      hbound intervalIntegrable_const hdiff
  exact hmain

end Work.Potential
