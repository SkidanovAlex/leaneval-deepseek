import Mathlib
import Submission.Commons.Analysis.Measure.integral_strip_eq_iterated
import Submission.Commons.Analysis.Measure.lintegral_strip_eq_iterated
import Submission.Commons.Analysis.Fourier.FT_strip_integral_eq
import Submission.Commons.Analysis.Fourier.lintegral_FT_slice_eq
import Submission.Commons.Analysis.Fourier.LogvinenkoSereda.bandlimited_entire_extension_cube
import Submission.Commons.Analysis.Complex.differentiable_eq_zero_of_ae_eq_zero_on_real
import Submission.Commons.Analysis.Fourier.fourierInv_toLp_ae_eq_fourierInv

namespace Commons.Analysis.Fourier

open MeasureTheory Metric FourierTransform
open scoped ENNReal

variable {d : ℕ}

/-! ### Helper lemmas (development) -/

/-- `closedBall 0 σ` sits inside the band cube. -/
private lemma closedBall_subset_bandCube {σ : ℝ} :
    Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) σ ⊆ LogvinenkoSereda.bandCube d σ := by
  intro ξ hξ
  rw [Metric.mem_closedBall, dist_zero_right] at hξ
  intro i
  have h := PiLp.norm_apply_le ξ i
  simpa [Real.norm_eq_abs] using h.trans hξ

/-- Integral over `EuclideanSpace ℝ (Fin d)` versus `Fin d → ℝ`. -/
private lemma lintegral_euclidean_eq_pi {φ : (Fin d → ℝ) → ENNReal} (hφ : Measurable φ) :
    ∫⁻ x : EuclideanSpace ℝ (Fin d), φ (fun i => x i) = ∫⁻ x : Fin d → ℝ, φ x :=
  (PiLp.volume_preserving_ofLp (Fin d)).lintegral_comp hφ

/-- Uniqueness of the entire extension. -/
private lemma entire_eq_FT {σ : ℝ} (hσ : 0 ≤ σ)
    {H : EuclideanSpace ℝ (Fin d) → ℂ}
    (hHmem : MemLp H 2 (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (hHsupp : ∀ᵐ a ∂(volume : Measure (EuclideanSpace ℝ (Fin d))),
      a ∉ LogvinenkoSereda.bandCube d σ → H a = 0)
    {F : (Fin d → ℂ) → ℂ} (hF : Differentiable ℂ F)
    (hFae : (fun x : EuclideanSpace ℝ (Fin d) => F (fun i => (x i : ℂ)))
      =ᵐ[volume] (fun x : EuclideanSpace ℝ (Fin d) => 𝓕⁻ (hHmem.toLp H) x)) :
    F = LogvinenkoSereda.FT d H := by
  have hH1 : MemLp H 1 (volume : Measure (EuclideanSpace ℝ (Fin d))) :=
    LogvinenkoSereda.memLp_one_of_memLp_two_of_ae_support_cube d σ hHmem hHsupp
  have hHint : Integrable H := memLp_one_iff_integrable.mp hH1
  have hGdiff : Differentiable ℂ (LogvinenkoSereda.FT d H) :=
    LogvinenkoSereda.differentiable_FT H hσ hHint hHsupp
  have hGae : (fun x : EuclideanSpace ℝ (Fin d) =>
        LogvinenkoSereda.FT d H (fun i => (x i : ℂ)))
      =ᵐ[volume] (fun x : EuclideanSpace ℝ (Fin d) => 𝓕⁻ (hHmem.toLp H) x) := by
    have hpt : ∀ x : EuclideanSpace ℝ (Fin d),
        LogvinenkoSereda.FT d H (fun i => (x i : ℂ)) = 𝓕⁻ H x := by
      intro x
      rw [LogvinenkoSereda.FT, Real.fourierInv_eq']
      apply integral_congr_ae
      filter_upwards with a
      rw [LogvinenkoSereda.phase_iota_eq, smul_eq_mul, mul_comm]
    have h1 : (fun x : EuclideanSpace ℝ (Fin d) =>
          LogvinenkoSereda.FT d H (fun i => (x i : ℂ)))
        =ᵐ[volume] (𝓕⁻ H) := Filter.Eventually.of_forall hpt
    have h2 : (𝓕⁻ H) =ᵐ[volume]
        ((𝓕⁻ (hHmem.toLp H) :
          Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))) :
            EuclideanSpace ℝ (Fin d) → ℂ) :=
      (fourierInv_toLp_ae_eq_fourierInv hH1 hHmem).symm
    exact h1.trans h2
  have hdiff : Differentiable ℂ (F - LogvinenkoSereda.FT d H) := hF.sub hGdiff
  have hae : (fun x : EuclideanSpace ℝ (Fin d) =>
        (F - LogvinenkoSereda.FT d H) (fun i => (x i : ℂ)))
      =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin d)))] 0 := by
    filter_upwards [hFae, hGae] with x hx1 hx2
    simp only [Pi.sub_apply, hx1, hx2, sub_self, Pi.zero_apply]
  exact sub_eq_zero.mp
    (Commons.Analysis.Complex.differentiable_eq_zero_of_ae_eq_zero_on_real hdiff hae)

/-- **Strip `lintegral` bound for the entire extension of a band-limited `L²` function.**
This is the `lintegral`-over-the-strip form of
`Commons.Analysis.Fourier.strip_integral_entire_le`: for any entire `F` agreeing a.e. with a
band-limited `L²` function `f` (band radius `σ`), the `lintegral` of `‖F z‖^2` over the
horizontal strip `{|Im z_i| ≤ q}` is at most `(2q)^d ∫ ‖𝓕f(ξ)‖² e^{4πq|ξ|₁}`. -/
theorem strip_lintegral_entire_le {d : ℕ} {σ q : ℝ} (hσ : 0 ≤ σ) (hq : 0 < q)
    {f : EuclideanSpace ℝ (Fin d) → ℂ}
    (hf : MemLp f 2 (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (hsupp : ∀ᵐ ξ ∂(volume : Measure (EuclideanSpace ℝ (Fin d))),
      ξ ∉ Metric.closedBall 0 σ →
      ((𝓕 (hf.toLp f) : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))) :
        EuclideanSpace ℝ (Fin d) → ℂ) ξ = 0)
    {F : (Fin d → ℂ) → ℂ} (hF : Differentiable ℂ F)
    (hFae : (fun x : EuclideanSpace ℝ (Fin d) => F (fun i => (x i : ℂ))) =ᵐ[volume] f) :
    ∫⁻ z in {z : Fin d → ℂ | ∀ i : Fin d, |(z i).im| ≤ q}, ENNReal.ofReal (‖F z‖ ^ 2)
      ≤ ENNReal.ofReal ((2 * q) ^ d * ∫ ξ : EuclideanSpace ℝ (Fin d),
          ‖((𝓕 (hf.toLp f) : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))) :
            EuclideanSpace ℝ (Fin d) → ℂ) ξ‖ ^ 2
            * Real.exp (4 * Real.pi * q * ∑ i, |ξ i|)) := by
  classical
  set H : EuclideanSpace ℝ (Fin d) → ℂ := fun ξ =>
    ((𝓕 (hf.toLp f) : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))) :
      EuclideanSpace ℝ (Fin d) → ℂ) ξ with hHdef
  have hHmem : MemLp H 2 (volume : Measure (EuclideanSpace ℝ (Fin d))) := Lp.memLp _
  have hHsupp : ∀ᵐ a ∂(volume : Measure (EuclideanSpace ℝ (Fin d))),
      a ∉ LogvinenkoSereda.bandCube d σ → H a = 0 := by
    filter_upwards [hsupp] with a ha hna
    exact ha (fun hmem => hna (closedBall_subset_bandCube hmem))
  have hH1 : MemLp H 1 (volume : Measure (EuclideanSpace ℝ (Fin d))) :=
    LogvinenkoSereda.memLp_one_of_memLp_two_of_ae_support_cube d σ hHmem hHsupp
  have hHint : Integrable H := memLp_one_iff_integrable.mp hH1
  have hHae : (fun x : EuclideanSpace ℝ (Fin d) => 𝓕⁻ (hHmem.toLp H) x) =ᵐ[volume] f := by
    have h3 : ((𝓕⁻ (hHmem.toLp H) : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))) :
          EuclideanSpace ℝ (Fin d) → ℂ) =ᵐ[volume]
        ((hf.toLp f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))) :
          EuclideanSpace ℝ (Fin d) → ℂ) := by
      rw [Lp.toLp_coeFn _ (Lp.memLp _), FourierPair.fourierInv_fourier_eq]
    exact h3.trans (MemLp.coeFn_toLp hf)
  have hFG : F = LogvinenkoSereda.FT d H :=
    entire_eq_FT hσ hHmem hHsupp hF (hFae.trans hHae.symm)
  set C : ℝ := ∫ a : EuclideanSpace ℝ (Fin d),
    ‖H a‖ ^ 2 * Real.exp (4 * Real.pi * q * ∑ i, |a i|) with hCdef
  have hmaj_int : Integrable (fun a : EuclideanSpace ℝ (Fin d) =>
      ‖H a‖ ^ 2 * Real.exp (4 * Real.pi * q * ∑ i, |a i|)) := by
    have hsq : Integrable (fun a : EuclideanSpace ℝ (Fin d) => ‖H a‖ ^ 2) :=
      LogvinenkoSereda.integrable_norm_sq hHmem
    have hexp_cont : Continuous (fun a : EuclideanSpace ℝ (Fin d) =>
        Real.exp (4 * Real.pi * q * (∑ i, |a i|))) := by
      apply Real.continuous_exp.comp
      apply continuous_const.mul
      apply continuous_finsetSum
      intro i _
      exact continuous_abs.comp (EuclideanSpace.proj i).continuous
    refine Integrable.mono' (hsq.const_mul (Real.exp (4 * Real.pi * q * ((d:ℝ) * σ))))
      ((hHmem.aestronglyMeasurable.norm.pow 2).mul hexp_cont.aestronglyMeasurable) ?_
    filter_upwards [hHsupp] with a ha
    by_cases hmem : a ∈ LogvinenkoSereda.bandCube d σ
    · have hsum : ∑ i, |a i| ≤ (d:ℝ) * σ := by
        calc ∑ i : Fin d, |a i| ≤ ∑ _ : Fin d, σ :=
              Finset.sum_le_sum (fun i _ => hmem i)
          _ = (d:ℝ) * σ := by rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
      have hexp : Real.exp (4 * Real.pi * q * (∑ i, |a i|))
          ≤ Real.exp (4 * Real.pi * q * ((d:ℝ) * σ)) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsum (by positivity))
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_right hexp (show (0:ℝ) ≤ ‖H a‖ ^ 2 by positivity)]
    · rw [ha hmem]; simp
  have hC_nonneg : 0 ≤ C := by
    rw [hCdef]
    exact integral_nonneg (fun a => by positivity)
  have hBmeas : MeasurableSet (Set.pi Set.univ (fun _ : Fin d => Set.Icc (-q) q)) := by
    show MeasurableSet (Set.pi Set.univ (fun _ : Fin d => Set.Icc (-q) q))
    exact MeasurableSet.univ_pi (fun i => measurableSet_Icc)
  have hvol : (volume : Measure (Fin d → ℝ)) (Set.pi Set.univ (fun _ : Fin d => Set.Icc (-q) q))
      = ENNReal.ofReal ((2 * q) ^ d) := by
    show (volume : Measure (Fin d → ℝ))
        (Set.pi Set.univ (fun _ : Fin d => Set.Icc (-q) q)) = ENNReal.ofReal ((2 * q) ^ d)
    have hone : ∀ i : Fin d, (volume : Measure ℝ) (Set.Icc (-q) q) = ENNReal.ofReal (2 * q) := by
      intro i
      rw [Real.volume_Icc]
      congr 1
      ring
    rw [volume_pi_pi]
    rw [Finset.prod_congr rfl (fun i _ => hone i)]
    rw [Finset.prod_const, Finset.card_fin]
    exact (ENNReal.ofReal_pow (by positivity) d).symm
  have hinner : ∀ᵐ y ∂(volume.restrict (Set.pi Set.univ (fun _ : Fin d => Set.Icc (-q) q))),
      (∫⁻ x : Fin d → ℝ, ENNReal.ofReal
        (‖F (fun i => (x i : ℂ) + (y i : ℂ) * Complex.I)‖ ^ 2)) ≤ ENNReal.ofReal C := by
    filter_upwards [ae_restrict_mem hBmeas] with y hy
    have hhy : ∀ i : Fin d, |y i| ≤ q := fun i => abs_le.mpr (hy i trivial)
    have hΨ : Measurable (fun x : Fin d → ℝ =>
        fun i : Fin d => (x i : ℂ) + (y i : ℂ) * Complex.I) :=
      measurable_pi_iff.mpr (fun i =>
        (Complex.measurable_ofReal.comp (measurable_pi_apply i)).add_const _)
    have hmeasφ : Measurable (fun x : Fin d → ℝ =>
        ENNReal.ofReal (‖F (fun i => (x i : ℂ) + (y i : ℂ) * Complex.I)‖ ^ 2)) :=
      ((hF.continuous.measurable.comp hΨ).norm.pow_const 2).ennreal_ofReal
    have hconv : (∫⁻ x : Fin d → ℝ, ENNReal.ofReal
          (‖F (fun i => (x i : ℂ) + (y i : ℂ) * Complex.I)‖ ^ 2))
        = ∫⁻ a : EuclideanSpace ℝ (Fin d), ENNReal.ofReal
            (‖H a‖ ^ 2 * Real.exp (-(4 * Real.pi) * ∑ i : Fin d, y i * a i)) := by
      have h1 : (∫⁻ x : EuclideanSpace ℝ (Fin d), ENNReal.ofReal
            (‖F (fun i => (x i : ℂ) + (y i : ℂ) * Complex.I)‖ ^ 2))
          = ∫⁻ x : EuclideanSpace ℝ (Fin d),
              (ENNReal.ofReal ‖F (fun i => (x i : ℂ) + (y i : ℂ) * Complex.I)‖) ^ (2:ℕ) :=
        lintegral_congr (fun x => ENNReal.ofReal_pow (norm_nonneg _) 2)
      have h2 : (∫⁻ x : EuclideanSpace ℝ (Fin d),
              (ENNReal.ofReal ‖F (fun i => (x i : ℂ) + (y i : ℂ) * Complex.I)‖) ^ (2:ℕ))
          = ∫⁻ x : EuclideanSpace ℝ (Fin d),
              (ENNReal.ofReal ‖LogvinenkoSereda.FT d H
                (fun i => (x i : ℂ) + (y i : ℂ) * Complex.I)‖) ^ (2:ℕ) := by
        simp only [hFG]
      rw [← lintegral_euclidean_eq_pi (φ := fun x : Fin d → ℝ =>
            ENNReal.ofReal (‖F (fun i => (x i : ℂ) + (y i : ℂ) * Complex.I)‖ ^ 2)) hmeasφ,
        h1, h2, lintegral_FT_slice_eq hHint hHsupp y]
    rw [hconv, hCdef]
    rw [ofReal_integral_eq_lintegral_ofReal hmaj_int
      (Filter.Eventually.of_forall (fun a => by positivity))]
    refine lintegral_mono (fun a => ENNReal.ofReal_le_ofReal ?_)
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
    have hsum : -(∑ i : Fin d, y i * a i) ≤ q * ∑ i : Fin d, |a i| := by
      have h1 : -(∑ i : Fin d, y i * a i) ≤ ∑ i : Fin d, |y i * a i| := by
        have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => neg_le_abs (y i * a i))
        rwa [Finset.sum_neg_distrib] at h
      have h2 : ∑ i : Fin d, |y i * a i| ≤ ∑ i : Fin d, q * |a i| := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hhy i) (abs_nonneg _)
      rw [← Finset.mul_sum] at h2
      exact h1.trans h2
    nlinarith [hsum, Real.pi_pos]
  calc ∫⁻ z in {z : Fin d → ℂ | ∀ i : Fin d, |(z i).im| ≤ q}, ENNReal.ofReal (‖F z‖ ^ 2)
      = ∫⁻ y in Set.pi Set.univ (fun _ : Fin d => Set.Icc (-q) q),
          ∫⁻ x : Fin d → ℝ, ENNReal.ofReal
            (‖F (fun i => (x i : ℂ) + (y i : ℂ) * Complex.I)‖ ^ 2) :=
        Commons.Analysis.Measure.lintegral_strip_eq_iterated
          ((hF.continuous.norm.pow 2).aemeasurable.ennreal_ofReal) (Q := q)
    _ ≤ ∫⁻ y in Set.pi Set.univ (fun _ : Fin d => Set.Icc (-q) q), ENNReal.ofReal C :=
        lintegral_mono_ae hinner
    _ = ENNReal.ofReal C * (volume : Measure (Fin d → ℝ))
          (Set.pi Set.univ (fun _ : Fin d => Set.Icc (-q) q)) := setLIntegral_const _ _
    _ = ENNReal.ofReal C * ENNReal.ofReal ((2 * q) ^ d) := by rw [hvol]
    _ = ENNReal.ofReal (C * (2 * q) ^ d) := (ENNReal.ofReal_mul hC_nonneg).symm
    _ = ENNReal.ofReal ((2 * q) ^ d * C) := by rw [mul_comm]

end Commons.Analysis.Fourier
