import Mathlib

namespace Work.GM.Affine

open MeasureTheory
open scoped FourierTransform

/-- Complex conjugation sends the Fourier character `e(t) = e^{2πit}` to `e(-t)`. -/
lemma star_fourierChar (t : ℝ) :
    star ((Real.fourierChar t : Circle) : ℂ) = ((Real.fourierChar (-t) : Circle) : ℂ) := by
  rw [Real.fourierChar_apply, Real.fourierChar_apply, ← starRingEnd_apply, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

theorem weighted_plancherel_of_char {g : ℝ → ℂ} (hg : Continuous g) (hcs : HasCompactSupport g)
    {θ K : ℝ → ℝ} (hθint : MeasureTheory.Integrable θ) (hθbdd : ∃ M : ℝ, ∀ ξ, ‖θ ξ‖ ≤ M)
    (hchar : ∀ s : ℝ, ∫ ξ : ℝ, ((θ ξ : ℝ) : ℂ) * (Real.fourierChar (s * ξ) : ℂ) = ((K s : ℝ) : ℂ)) :
    (∫ ξ : ℝ, ((θ ξ * ‖FourierTransform.fourier g ξ‖ ^ 2 : ℝ) : ℂ))
      = ∫ z : ℝ, star (g z) * ∫ u : ℝ, ((K (z - u) : ℝ) : ℂ) * g u := by
  have _hM : ∃ M : ℝ, ∀ ξ, ‖θ ξ‖ ≤ M := hθbdd
  set h : ℝ → ℂ := fun ξ => ((θ ξ : ℝ) : ℂ) with hh
  set Kc : ℝ → ℂ := fun x => ((K x : ℝ) : ℂ) with hKc
  set A : ℝ → ℝ → ℂ := fun ξ u => Real.fourierChar (-(u * ξ)) • g u with hA
  set B : ℝ → ℝ → ℂ := fun ξ z => Real.fourierChar (z * ξ) • star (g z) with hB
  have hgn : Integrable (fun z : ℝ => ‖g z‖) volume :=
    hg.norm.integrable_of_hasCompactSupport hcs.norm
  have hθn : Integrable (fun ξ : ℝ => ‖θ ξ‖) volume := hθint.norm
  -- `𝓕g ξ` and its conjugate as integrals
  have hF : ∀ ξ : ℝ, FourierTransform.fourier g ξ = ∫ u, A ξ u := by
    intro ξ
    rw [Real.fourier_real_eq, hA]
  have hFs : ∀ ξ : ℝ, star (FourierTransform.fourier g ξ) = ∫ z, B ξ z := by
    intro ξ
    have hconj : star (∫ u, A ξ u) = ∫ u, star (A ξ u) := by
      have h := integral_conj (μ := volume) (f := A ξ)
      simp only [starRingEnd_apply] at h
      exact h.symm
    rw [hF ξ, hconj]
    apply integral_congr_ae
    filter_upwards with z
    simp only [hA, hB, Circle.smul_def, smul_eq_mul, star_mul, star_fourierChar, neg_neg]
    ring
  -- measurability and boundedness of `K`, via its definition as a Fourier transform
  have hΦcont : Continuous
      (fun s : ℝ => ∫ ξ : ℝ, ((θ ξ : ℝ) : ℂ) * ((Real.fourierChar (s * ξ) : Circle) : ℂ)) := by
    have hfC : Integrable (fun ξ : ℝ => ((θ ξ : ℝ) : ℂ)) volume := hθint.ofReal
    have hcont : Continuous (FourierTransform.fourier (fun ξ : ℝ => ((θ ξ : ℝ) : ℂ))) :=
      VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
        (innerSL ℝ).continuous₂ hfC
    have heq : (fun s : ℝ => ∫ ξ : ℝ, ((θ ξ : ℝ) : ℂ) *
          ((Real.fourierChar (s * ξ) : Circle) : ℂ))
        = fun s : ℝ => FourierTransform.fourier (fun ξ : ℝ => ((θ ξ : ℝ) : ℂ)) (-s) := by
      funext s
      rw [Real.fourier_real_eq]
      apply integral_congr_ae
      filter_upwards with v
      simp only [Circle.smul_def, smul_eq_mul]
      rw [show -(v * -s) = s * v by ring]
      ring
    rw [heq]
    exact hcont.comp continuous_neg
  have hKmeas : Measurable K := by
    have heq : K = fun s : ℝ =>
        (∫ ξ : ℝ, ((θ ξ : ℝ) : ℂ) * ((Real.fourierChar (s * ξ) : Circle) : ℂ)).re := by
      funext s
      have h := congrArg Complex.re (hchar s)
      simpa using h.symm
    rw [heq]
    exact Complex.continuous_re.measurable.comp hΦcont.measurable
  have hKbd : ∀ s : ℝ, ‖K s‖ ≤ ∫ ξ : ℝ, ‖θ ξ‖ := by
    intro s
    have hnorm := norm_integral_le_integral_norm
      (fun ξ : ℝ => ((θ ξ : ℝ) : ℂ) * ((Real.fourierChar (s * ξ) : Circle) : ℂ)) (μ := volume)
    rw [hchar s] at hnorm
    have h1 : ‖((K s : ℝ) : ℂ)‖ = ‖K s‖ := by simp
    have h2 : ∫ ξ : ℝ, ‖((θ ξ : ℝ) : ℂ) * ((Real.fourierChar (s * ξ) : Circle) : ℂ)‖
        = ∫ ξ : ℝ, ‖θ ξ‖ := by
      apply integral_congr_ae
      filter_upwards with ξ
      rw [norm_mul, Circle.norm_coe, mul_one]
      simp
    rw [h1, h2] at hnorm
    exact hnorm
  -- Step 1: unfold the squared norm into `𝓕g ξ * star (𝓕g ξ)`
  have hstep1 : (∫ ξ : ℝ, ((θ ξ * ‖FourierTransform.fourier g ξ‖ ^ 2 : ℝ) : ℂ))
      = ∫ ξ : ℝ, h ξ * (FourierTransform.fourier g ξ * star (FourierTransform.fourier g ξ)) := by
    apply integral_congr_ae
    filter_upwards with ξ
    simp only [hh]
    rw [Complex.ofReal_mul]
    congr 1
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, starRingEnd_apply]
  -- Step 2: replace the two Fourier transforms by their integral representations
  have hstep2 : (∫ ξ : ℝ, h ξ * (FourierTransform.fourier g ξ * star (FourierTransform.fourier g ξ)))
      = ∫ ξ : ℝ, h ξ * ((∫ z, B ξ z) * (∫ u, A ξ u)) := by
    apply integral_congr_ae
    filter_upwards with ξ
    rw [hFs ξ, hF ξ]
    ring
  -- Step 3: combine the two integrals into a product integral
  have hstep3 : (∫ ξ : ℝ, h ξ * ((∫ z, B ξ z) * (∫ u, A ξ u)))
      = ∫ ξ : ℝ, ∫ q : ℝ × ℝ, h ξ * (B ξ q.1 * A ξ q.2) := by
    apply integral_congr_ae
    filter_upwards with ξ
    rw [← MeasureTheory.integral_prod_mul (B ξ) (A ξ), ← MeasureTheory.integral_const_mul,
      MeasureTheory.Measure.volume_eq_prod]
  -- Step 4: swap the order of integration
  have hunf : Function.uncurry (fun ξ (q : ℝ × ℝ) => h ξ * (B ξ q.1 * A ξ q.2))
      = fun p : ℝ × (ℝ × ℝ) => ((θ p.1 : ℝ) : ℂ) *
          (((Real.fourierChar (p.2.1 * p.1) : Circle) : ℂ) * star (g p.2.1) *
            (((Real.fourierChar (-(p.2.2 * p.1)) : Circle) : ℂ) * g p.2.2)) := by
    funext p
    simp only [Function.uncurry, hh, hA, hB, Circle.smul_def, smul_eq_mul]
  have hd1 : Integrable (fun ξ : ℝ => ‖θ ξ‖) volume := hθn
  have hd2 : Integrable (fun q : ℝ × ℝ => ‖g q.1‖ * ‖g q.2‖) (volume.prod volume) :=
    Integrable.mul_prod hgn hgn
  have hd : Integrable (fun p : ℝ × (ℝ × ℝ) =>
      ‖θ p.1‖ * (‖g p.2.1‖ * ‖g p.2.2‖))
      (volume.prod (volume.prod volume)) :=
    Integrable.mul_prod hd1 hd2
  have hcont : AEStronglyMeasurable (fun p : ℝ × (ℝ × ℝ) =>
      ((θ p.1 : ℝ) : ℂ) *
          (((Real.fourierChar (p.2.1 * p.1) : Circle) : ℂ) * star (g p.2.1) *
            (((Real.fourierChar (-(p.2.2 * p.1)) : Circle) : ℂ) * g p.2.2)))
      (volume.prod (volume.prod volume)) := by
    have hθae : AEStronglyMeasurable (fun ξ : ℝ => ((θ ξ : ℝ) : ℂ)) volume :=
      (Complex.continuous_ofReal.measurable.comp_aemeasurable
        hθint.aestronglyMeasurable.aemeasurable).aestronglyMeasurable
    have h1 : AEStronglyMeasurable (fun p : ℝ × (ℝ × ℝ) => ((θ p.1 : ℝ) : ℂ))
        (volume.prod (volume.prod volume)) := hθae.comp_fst
    have h2 : Continuous (fun p : ℝ × (ℝ × ℝ) =>
        (((Real.fourierChar (p.2.1 * p.1) : Circle) : ℂ) * star (g p.2.1) *
          (((Real.fourierChar (-(p.2.2 * p.1)) : Circle) : ℂ) * g p.2.2))) := by
      fun_prop
    exact h1.mul h2.aestronglyMeasurable
  have hInt : Integrable (Function.uncurry (fun ξ (q : ℝ × ℝ) => h ξ * (B ξ q.1 * A ξ q.2)))
      (volume.prod (volume.prod volume)) := by
    refine Integrable.mono' hd ?_ ?_
    · rw [hunf]; exact hcont
    · filter_upwards with p
      rw [hunf]
      simp only [norm_mul, norm_star, Circle.norm_coe, one_mul]
      rw [show ‖((θ p.1 : ℝ) : ℂ)‖ = ‖θ p.1‖ by simp]
  have hswap : (∫ ξ : ℝ, ∫ q : ℝ × ℝ, h ξ * (B ξ q.1 * A ξ q.2))
      = ∫ q : ℝ × ℝ, ∫ ξ : ℝ, h ξ * (B ξ q.1 * A ξ q.2) :=
    integral_integral_swap hInt
  -- Step 5: evaluate the inner `ξ`-integral
  have hcharCombine : ∀ z u ξ : ℝ,
      (Real.fourierChar (z * ξ) : ℂ) * ((Real.fourierChar (-(u * ξ)) : Circle) : ℂ)
        = (Real.fourierChar ((z - u) * ξ) : ℂ) := by
    intro z u ξ
    rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul]
    congr 1
    congr 1
    ring
  have hinner : ∀ q : ℝ × ℝ, ∫ ξ, h ξ * (B ξ q.1 * A ξ q.2)
      = Kc (q.1 - q.2) * (star (g q.1) * g q.2) := by
    intro q
    have hpw : ∀ ξ : ℝ, h ξ * (B ξ q.1 * A ξ q.2)
        = (h ξ * (Real.fourierChar ((q.1 - q.2) * ξ) : ℂ)) * (star (g q.1) * g q.2) := by
      intro ξ
      simp only [hA, hB, Circle.smul_def, smul_eq_mul]
      calc h ξ * ((Real.fourierChar (q.1 * ξ) : ℂ) * star (g q.1) *
              (((Real.fourierChar (-(q.2 * ξ)) : Circle) : ℂ) * g q.2))
          = (h ξ * ((Real.fourierChar (q.1 * ξ) : ℂ) *
              ((Real.fourierChar (-(q.2 * ξ)) : Circle) : ℂ))) * (star (g q.1) * g q.2) := by
            ring
        _ = (h ξ * (Real.fourierChar ((q.1 - q.2) * ξ) : ℂ)) * (star (g q.1) * g q.2) := by
            rw [hcharCombine q.1 q.2 ξ]
    simp_rw [hpw]
    rw [MeasureTheory.integral_mul_const]
    simp only [hh]
    rw [hchar (q.1 - q.2), hKc]
  have hcongr : (∫ q : ℝ × ℝ, ∫ ξ, h ξ * (B ξ q.1 * A ξ q.2))
      = ∫ q : ℝ × ℝ, Kc (q.1 - q.2) * (star (g q.1) * g q.2) := by
    apply integral_congr_ae
    filter_upwards with q
    exact hinner q
  -- Step 6: undo the product measure and factor out `star (g z)`
  have hd2' : Integrable (fun q : ℝ × ℝ => (∫ ξ : ℝ, ‖θ ξ‖) * ‖g q.1‖ * ‖g q.2‖)
      (volume.prod volume) :=
    Integrable.mul_prod (hgn.const_mul _) hgn
  have hKint : Integrable (fun q : ℝ × ℝ => Kc (q.1 - q.2) * (star (g q.1) * g q.2))
      (volume.prod volume) := by
    refine Integrable.mono' hd2' ?_ ?_
    · have hmeas : Measurable (fun q : ℝ × ℝ => Kc (q.1 - q.2)) := by
        have h1 : Measurable (fun q : ℝ × ℝ => K (q.1 - q.2)) :=
          hKmeas.comp (continuous_fst.sub continuous_snd).measurable
        have h2 : Measurable (fun q : ℝ × ℝ => ((K (q.1 - q.2) : ℝ) : ℂ)) :=
          Complex.continuous_ofReal.measurable.comp h1
        simpa only [hKc] using h2
      exact hmeas.aestronglyMeasurable.mul
        ((by fun_prop : Continuous (fun q : ℝ × ℝ => star (g q.1) * g q.2)).aestronglyMeasurable)
    · filter_upwards with q
      calc ‖Kc (q.1 - q.2) * (star (g q.1) * g q.2)‖
          = ‖K (q.1 - q.2)‖ * (‖g q.1‖ * ‖g q.2‖) := by
            simp only [hKc, norm_mul, norm_star]
            rw [show ‖((K (q.1 - q.2) : ℝ) : ℂ)‖ = ‖K (q.1 - q.2)‖ by simp]
        _ ≤ (∫ ξ : ℝ, ‖θ ξ‖) * (‖g q.1‖ * ‖g q.2‖) :=
            mul_le_mul_of_nonneg_right (hKbd (q.1 - q.2)) (by positivity)
        _ = (∫ ξ : ℝ, ‖θ ξ‖) * ‖g q.1‖ * ‖g q.2‖ := by ring
  have hlast : (∫ q : ℝ × ℝ, Kc (q.1 - q.2) * (star (g q.1) * g q.2))
      = ∫ z, star (g z) * ∫ u, Kc (z - u) * g u := by
    rw [MeasureTheory.Measure.volume_eq_prod, MeasureTheory.integral_prod _ hKint]
    apply integral_congr_ae
    filter_upwards with z
    have hsw : ∀ u : ℝ, Kc (z - u) * (star (g z) * g u) = star (g z) * (Kc (z - u) * g u) := by
      intro u; ring
    simp_rw [hsw]
    rw [MeasureTheory.integral_const_mul]
  calc (∫ ξ : ℝ, ((θ ξ * ‖FourierTransform.fourier g ξ‖ ^ 2 : ℝ) : ℂ))
      = ∫ ξ : ℝ, h ξ * (FourierTransform.fourier g ξ * star (FourierTransform.fourier g ξ)) :=
        hstep1
    _ = ∫ ξ : ℝ, h ξ * ((∫ z, B ξ z) * (∫ u, A ξ u)) := hstep2
    _ = ∫ ξ : ℝ, ∫ q : ℝ × ℝ, h ξ * (B ξ q.1 * A ξ q.2) := hstep3
    _ = ∫ q : ℝ × ℝ, ∫ ξ : ℝ, h ξ * (B ξ q.1 * A ξ q.2) := hswap
    _ = ∫ q : ℝ × ℝ, Kc (q.1 - q.2) * (star (g q.1) * g q.2) := hcongr
    _ = ∫ z : ℝ, star (g z) * ∫ u : ℝ, Kc (z - u) * g u := hlast
    _ = ∫ z : ℝ, star (g z) * ∫ u : ℝ, ((K (z - u) : ℝ) : ℂ) * g u := by simp only [hKc]

end Work.GM.Affine
