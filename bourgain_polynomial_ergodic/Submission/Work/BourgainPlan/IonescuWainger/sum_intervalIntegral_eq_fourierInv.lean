import Mathlib

/-!
# A finite sum of interval integrals as one inverse Fourier transform

For a function `m : ℝ → ℂ` which is integrable and vanishes outside `[-1/2, 1/2]`, a finite set `s`
of integers, coefficients `a : ℤ → ℂ` and an integer `n`, the sum over `k ∈ s` of the integral of
`m ξ · e^{2πi(n-k)ξ}` over `(-1/2, 1/2]`, weighted by `a k`, is the inverse Fourier transform at `n`
of the band-limited function `ξ ↦ m ξ · Σ_{k ∈ s} a k e^{-2πikξ}`.

This is the "sampling / major arc" bookkeeping step: the discrete Fourier expansion
`Σ_k a k e^{-2πikξ}` multiplies the band-limited multiplier `m` inside the frequency integral, and
the sum over `k` interchanges with the integral.

The mathematical content is the elementary computation
`e^{2πi n ξ} · e^{-2πi k ξ} = e^{2πi (n-k) ξ}` together with `Finset.sum`/`integral` exchange and the
a.e. vanishing of `m` off `(-1/2, 1/2]`.
-/

namespace Work.BourgainPlan.IonescuWainger

open MeasureTheory Finset

/-- The complement of `Ioc c d` inside `Icc c d` is at most the single point `c`. -/
private lemma Icc_diff_Ioc_subset (c d : ℝ) : Set.Icc c d \ Set.Ioc c d ⊆ {c} := by
  intro x hx
  rw [Set.mem_sdiff, Set.mem_Icc, Set.mem_Ioc] at hx
  simp only [Set.mem_singleton_iff]
  rcases hx with ⟨⟨h1, h2⟩, h3⟩
  by_contra hne
  exact h3 ⟨lt_of_le_of_ne h1 (Ne.symm hne), h2⟩

/-- `‖e^{2πi l t}‖ = 1` for `t : ℝ`, `l : ℤ`. -/
private lemma norm_exp_two_pi_I (t : ℝ) (l : ℤ) :
    ‖Complex.exp (2 * ↑Real.pi * Complex.I * (l : ℂ) * (t : ℂ))‖ = 1 := by
  have h : 2 * ↑Real.pi * Complex.I * (l : ℂ) * (t : ℂ)
      = ((2 * Real.pi * (l:ℝ) * t : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

theorem sum_intervalIntegral_eq_fourierInv (m : ℝ → ℂ) (hmi : MeasureTheory.Integrable m)
    (hmsupp : ∀ ξ : ℝ, ξ ∉ Set.Icc (-(1/2):ℝ) (1/2) → m ξ = 0)
    (s : Finset ℤ) (a : ℤ → ℂ) (n : ℤ) :
    Finset.sum s (fun k => (∫ ξ in Set.Ioc (-(1/2):ℝ) (1/2),
        m ξ * Complex.exp (2 * Real.pi * Complex.I * ((n - k : ℤ) : ℂ) * (ξ : ℂ))) * a k)
      = FourierTransformInv.fourierInv
          (fun ξ : ℝ => m ξ * (Finset.sum s (fun k =>
            a k * Complex.exp (-(2 * Real.pi * Complex.I * (k : ℂ) * (ξ : ℂ)))))) (n : ℝ) := by
  rw [Real.fourierInv_eq']
  -- `m` vanishes a.e. off `(-1/2, 1/2]`
  have hsupp : ∀ᵐ v ∂(volume : Measure ℝ), v ∉ Set.Ioc (-(1/2):ℝ) (1/2) → m v = 0 := by
    rw [MeasureTheory.ae_iff]
    refine MeasureTheory.measure_mono_null ?_ (MeasureTheory.measure_singleton ((-(1/2) : ℝ)))
    intro v hv
    have h1 : v ∉ Set.Ioc (-(1/2):ℝ) (1/2) := (Classical.not_imp.mp hv).1
    have h2 : m v ≠ 0 := (Classical.not_imp.mp hv).2
    have hIcc : v ∈ Set.Icc (-(1/2):ℝ) (1/2) := by
      by_contra hc
      exact h2 (hmsupp v hc)
    exact Icc_diff_Ioc_subset _ _ ⟨hIcc, h1⟩
  -- hence the whole integrand vanishes a.e. off `(-1/2, 1/2]`
  have hvan : ∀ᵐ v ∂(volume : Measure ℝ), v ∉ Set.Ioc (-(1/2):ℝ) (1/2) →
      Complex.exp (↑(2 * Real.pi * inner ℝ v (n:ℝ)) * Complex.I) •
        (m v * ∑ k ∈ s, a k * Complex.exp (-(2 * ↑Real.pi * Complex.I * ↑k * ↑v))) = 0 := by
    filter_upwards [hsupp] with v hv hvI
    rw [hv hvI]
    simp
  rw [← MeasureTheory.setIntegral_eq_integral_of_ae_compl_eq_zero hvan]
  -- pointwise identity of the integrands on `(-1/2, 1/2]`
  have hpt : ∀ ξ : ℝ,
      Complex.exp (↑(2 * Real.pi * inner ℝ ξ (n:ℝ)) * Complex.I) •
        (m ξ * ∑ k ∈ s, a k * Complex.exp (-(2 * ↑Real.pi * Complex.I * ↑k * ↑ξ)))
      = ∑ k ∈ s, a k * (m ξ * Complex.exp (2 * ↑Real.pi * Complex.I * ((n - k : ℤ) : ℂ) * ↑ξ)) := by
    intro ξ
    rw [smul_eq_mul, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    have hexp : Complex.exp (↑(2 * Real.pi * inner ℝ ξ (n:ℝ)) * Complex.I)
        * Complex.exp (-(2 * ↑Real.pi * Complex.I * ↑k * ↑ξ))
        = Complex.exp (2 * ↑Real.pi * Complex.I * ((n - k : ℤ) : ℂ) * ↑ξ) := by
      rw [← Complex.exp_add]
      congr 1
      simp only [Real.inner_apply]
      push_cast
      ring
    rw [← hexp]
    ring
  have hint : ∀ k ∈ s, Integrable (fun ξ : ℝ => a k * (m ξ * Complex.exp (2 * ↑Real.pi * Complex.I * ((n - k : ℤ) : ℂ) * ↑ξ))) (volume.restrict (Set.Ioc (-(1/2):ℝ) (1/2))) := by
    intro k _
    refine MeasureTheory.Integrable.const_mul ?_ (a k)
    refine (hmi.restrict).mul_bdd (c := 1) ?_ ?_
    · exact (Complex.continuous_exp.comp (by continuity)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun ξ => le_of_eq (norm_exp_two_pi_I ξ (n - k)))
  have hmain : (∫ ξ in Set.Ioc (-(1/2):ℝ) (1/2),
      Complex.exp (↑(2 * Real.pi * inner ℝ ξ (n:ℝ)) * Complex.I) •
        (m ξ * ∑ k ∈ s, a k * Complex.exp (-(2 * ↑Real.pi * Complex.I * ↑k * ↑ξ))))
      = Finset.sum s (fun k => (∫ ξ in Set.Ioc (-(1/2):ℝ) (1/2),
          m ξ * Complex.exp (2 * Real.pi * Complex.I * ((n - k : ℤ) : ℂ) * (ξ : ℂ))) * a k) := by
    rw [MeasureTheory.integral_congr_ae (μ := volume.restrict (Set.Ioc (-(1/2):ℝ) (1/2))) (Filter.Eventually.of_forall hpt)]
    rw [MeasureTheory.integral_finsetSum s hint]
    apply Finset.sum_congr rfl
    intro k _
    rw [MeasureTheory.integral_const_mul]
    exact mul_comm _ _
  rw [hmain]

end Work.BourgainPlan.IonescuWainger
