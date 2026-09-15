import Mathlib
import Submission.Commons.Analysis.Complex.differentiable_eq_zero_of_ae_eq_zero_on_real
import Submission.Commons.Analysis.Fourier.FT_strip_integral_eq
import Submission.Commons.Analysis.Fourier.LogvinenkoSereda.bandlimited_entire_extension_cube
import Submission.Commons.Analysis.Fourier.fourierInv_toLp_ae_eq_fourierInv

namespace Commons.Analysis.Fourier

open MeasureTheory Metric FourierTransform
open scoped ENNReal

/-- `closedBall 0 σ` sits inside the band cube `{ξ | ∀ i, |ξ i| ≤ σ}`. -/
private lemma strip_closedBall_subset_bandCube {d : ℕ} {σ : ℝ} :
    Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) σ
      ⊆ LogvinenkoSereda.bandCube d σ := by
  intro ξ hξ
  rw [Metric.mem_closedBall, dist_zero_right] at hξ
  intro i
  have h := PiLp.norm_apply_le ξ i
  simpa [Real.norm_eq_abs] using h.trans hξ

/-- **Strip bound for the entire extension of a band-limited `L²` function.**

This is the "complex Plancherel" input of Han–Schlag's §4 localisation argument
(Han–Schlag, *A higher dimensional Bourgain–Dyatlov fractal uncertainty principle*,
arXiv:1805.04994, proof of `prop:loc` / `prop:locdim`):

if `F` is an entire extension of the band-limited `L²` function `f` (band radius `σ`, i.e. the
Fourier transform of `f` vanishes a.e. outside `closedBall 0 σ`), then for every `q > 0`
```
∫_{y ∈ [-q,q]^d} ∫_{x} ‖F (x + i y)‖² ≤ (2q)^d ∫ ‖𝓕 f (ξ)‖² e^{4πq |ξ|₁} dξ .
```
The key ingredient to prove it is the identity, valid for each fixed `y`,
```
∫_x ‖F (x + i y)‖² = ∫_ξ ‖𝓕 f (ξ)‖² e^{-4π (y·ξ)} dξ      (complex Plancherel),
```
which follows from the integral representation `F z = ∫_ξ 𝓕f(ξ) e^{2πi (z·ξ)} dξ`
(legitimate because `𝓕f` is compactly supported, hence in `L¹`) together with Plancherel.
Note that `F` is *any* entire function agreeing a.e. with `f` on `ℝ^d`: two such agree
everywhere by the identity theorem (their difference is entire and its closed zero set has full
measure in `ℝ^d`, hence contains `ℝ^d`, hence is everything). Then `∫_{-q}^{q} e^{-4π y ξ} dy
≤ 2q e^{4πq|ξ|}` and Fubini finish the proof.

Signs of the Fourier convention do not matter here: only `e^{±4π y·ξ}` with `|ξ|₁` bounds are
used. -/
theorem strip_integral_entire_le {d : ℕ} {σ : ℝ} (hσ : 0 ≤ σ)
    {f : EuclideanSpace ℝ (Fin d) → ℂ}
    (hf : MeasureTheory.MemLp f 2 (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))))
    (hsupp : ∀ᵐ ξ ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))),
      ξ ∉ Metric.closedBall 0 σ →
      ((FourierTransform.fourier (hf.toLp f) : MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d)))) : EuclideanSpace ℝ (Fin d) → ℂ) ξ = 0)
    {F : (Fin d → ℂ) → ℂ} (hF : Differentiable ℂ F)
    (hFae : (fun x : EuclideanSpace ℝ (Fin d) => F (fun i => (x i : ℂ))) =ᵐ[MeasureTheory.volume] f)
    {q : ℝ} (hq : 0 < q) :
    (∫ y in Set.pi Set.univ (fun _ : Fin d => Set.Icc (-q) q),
        ∫ x : EuclideanSpace ℝ (Fin d), ‖F (fun i => (x i : ℂ) + (y i : ℂ) * Complex.I)‖ ^ 2)
      ≤ (2 * q) ^ d * ∫ ξ : EuclideanSpace ℝ (Fin d),
          ‖((FourierTransform.fourier (hf.toLp f) : MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d)))) : EuclideanSpace ℝ (Fin d) → ℂ) ξ‖ ^ 2
            * Real.exp (4 * Real.pi * q * ∑ i, |ξ i|) := by
  classical
  let H : EuclideanSpace ℝ (Fin d) → ℂ :=
    ⇑(FourierTransform.fourier (hf.toLp f) :
      MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))))
  have hHmem : MemLp H 2 (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))) :=
    Lp.memLp _
  have hHsupp : ∀ᵐ a ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))),
      a ∉ LogvinenkoSereda.bandCube d σ → H a = 0 := by
    filter_upwards [hsupp] with a ha hna
    exact ha (fun hmem => hna (strip_closedBall_subset_bandCube hmem))
  have hH1 : MemLp H 1 (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))) :=
    LogvinenkoSereda.memLp_one_of_memLp_two_of_ae_support_cube d σ hHmem hHsupp
  have hHint : Integrable H := memLp_one_iff_integrable.mp hH1
  let G : (Fin d → ℂ) → ℂ := LogvinenkoSereda.FT d H
  have hGdiff : Differentiable ℂ G :=
    LogvinenkoSereda.differentiable_FT H hσ hHint hHsupp
  have hGae : (fun x : EuclideanSpace ℝ (Fin d) => G (fun i => (x i : ℂ)))
      =ᵐ[MeasureTheory.volume] f := by
    have hpt : ∀ x : EuclideanSpace ℝ (Fin d), G (fun i => (x i : ℂ)) = 𝓕⁻ H x := by
      intro x
      show LogvinenkoSereda.FT d H (fun i => (x i : ℂ)) = 𝓕⁻ H x
      rw [LogvinenkoSereda.FT, Real.fourierInv_eq']
      apply integral_congr_ae
      filter_upwards with a
      rw [LogvinenkoSereda.phase_iota_eq, smul_eq_mul, mul_comm]
    have h1 : (fun x : EuclideanSpace ℝ (Fin d) => G (fun i => (x i : ℂ)))
        =ᵐ[MeasureTheory.volume] (𝓕⁻ H) := Filter.Eventually.of_forall hpt
    have h2 : (𝓕⁻ H) =ᵐ[MeasureTheory.volume]
        ((𝓕⁻ (hHmem.toLp H) :
          MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d)))) :
            EuclideanSpace ℝ (Fin d) → ℂ) :=
      (fourierInv_toLp_ae_eq_fourierInv hH1 hHmem).symm
    have htoLp : hHmem.toLp H = FourierTransform.fourier (hf.toLp f) :=
      Lp.toLp_coeFn _ (Lp.memLp _)
    have h3 : ((𝓕⁻ (hHmem.toLp H) :
          MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d)))) :
            EuclideanSpace ℝ (Fin d) → ℂ) =ᵐ[MeasureTheory.volume]
        ((hf.toLp f : MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d)))) : EuclideanSpace ℝ (Fin d) → ℂ) := by
      rw [htoLp, fourierInv_fourier_eq]
    exact h1.trans (h2.trans (h3.trans (MemLp.coeFn_toLp hf)))
  have hFG : F = G := by
    have hdiff : Differentiable ℂ (F - G) := hF.sub hGdiff
    have hae : (fun x : EuclideanSpace ℝ (Fin d) => (F - G) (fun i => (x i : ℂ)))
        =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d)))] 0 := by
      filter_upwards [hFae, hGae] with x hx1 hx2
      simp only [Pi.sub_apply, hx1, hx2, sub_self, Pi.zero_apply]
    exact sub_eq_zero.mp
      (Commons.Analysis.Complex.differentiable_eq_zero_of_ae_eq_zero_on_real hdiff hae)
  rw [hFG]
  let box : Set (Fin d → ℝ) := Set.pi Set.univ (fun _ : Fin d => Set.Icc (-q) q)
  have hboxmeas : MeasurableSet box := by
    show MeasurableSet (Set.pi Set.univ (fun _ : Fin d => Set.Icc (-q) q))
    exact MeasurableSet.univ_pi (fun i => measurableSet_Icc)
  have hkey : ∀ y : Fin d → ℝ,
      (∫ x : EuclideanSpace ℝ (Fin d), ‖G (fun i => (x i : ℂ) + (y i : ℂ) * Complex.I)‖ ^ 2)
        = ∫ a : EuclideanSpace ℝ (Fin d),
            ‖H a‖ ^ 2 * Real.exp (-(4 * Real.pi) * (∑ i, y i * a i)) := by
    intro y
    have h := FT_strip_integral_eq (d := d) (σ := σ) hσ hHint hHsupp y
    show (∫ x : EuclideanSpace ℝ (Fin d),
        ‖LogvinenkoSereda.FT d H (fun i => (x i : ℂ) + (y i : ℂ) * Complex.I)‖ ^ 2) = _
    simpa [LogvinenkoSereda.FT, LogvinenkoSereda.phase] using h
  have hexp_cont : Continuous (fun a : EuclideanSpace ℝ (Fin d) =>
      Real.exp (4 * Real.pi * q * (∑ i, |a i|))) := by
    apply Real.continuous_exp.comp
    apply continuous_const.mul
    apply continuous_finsetSum
    intro i _
    exact continuous_abs.comp (EuclideanSpace.proj i).continuous
  have hmaj_int : Integrable (fun a : EuclideanSpace ℝ (Fin d) =>
      ‖H a‖ ^ 2 * Real.exp (4 * Real.pi * q * (∑ i, |a i|))) := by
    have hsq : Integrable (fun a : EuclideanSpace ℝ (Fin d) => ‖H a‖ ^ 2) :=
      LogvinenkoSereda.integrable_norm_sq hHmem
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
      nlinarith [mul_le_mul_of_nonneg_right hexp
        (show (0:ℝ) ≤ ‖H a‖ ^ 2 by positivity)]
    · rw [ha hmem]; simp
  have hbound : ∀ y ∈ box, ‖(∫ x : EuclideanSpace ℝ (Fin d),
      ‖G (fun i => (x i : ℂ) + (y i : ℂ) * Complex.I)‖ ^ 2)‖
      ≤ ∫ a : EuclideanSpace ℝ (Fin d), ‖H a‖ ^ 2 * Real.exp (4 * Real.pi * q * (∑ i, |a i|)) := by
    intro y hy
    rw [hkey y]
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun a => by positivity))]
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall (fun a => by positivity)) hmaj_int ?_
    filter_upwards with a
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    have hS : ∑ i, y i * a i ≤ q * ∑ i, |a i| := by
      have h1 : ∑ i : Fin d, y i * a i ≤ ∑ i : Fin d, |y i| * |a i| :=
        Finset.sum_le_sum (fun i _ => by
          calc y i * a i ≤ |y i * a i| := le_abs_self _
            _ = |y i| * |a i| := abs_mul _ _)
      have h2 : ∑ i : Fin d, |y i| * |a i| ≤ ∑ i : Fin d, q * |a i| :=
        Finset.sum_le_sum (fun i _ =>
          mul_le_mul_of_nonneg_right (abs_le.mpr (hy i trivial)) (abs_nonneg _))
      rw [← Finset.mul_sum] at h2
      exact h1.trans h2
    have hS2 : -(∑ i, y i * a i) ≤ q * ∑ i, |a i| := by
      have h3 : -(∑ i : Fin d, y i * a i) = ∑ i : Fin d, -(y i * a i) := by
        rw [Finset.sum_neg_distrib]
      rw [h3]
      have h1 : ∑ i : Fin d, -(y i * a i) ≤ ∑ i : Fin d, |y i| * |a i| :=
        Finset.sum_le_sum (fun i _ => by
          calc -(y i * a i) ≤ |-(y i * a i)| := le_abs_self _
            _ = |y i| * |a i| := by rw [abs_neg, abs_mul])
      have h2 : ∑ i : Fin d, |y i| * |a i| ≤ ∑ i : Fin d, q * |a i| :=
        Finset.sum_le_sum (fun i _ =>
          mul_le_mul_of_nonneg_right (abs_le.mpr (hy i trivial)) (abs_nonneg _))
      rw [← Finset.mul_sum] at h2
      exact h1.trans h2
    have := mul_le_mul_of_nonneg_left hS2 (by positivity : (0:ℝ) ≤ 4 * Real.pi)
    nlinarith [this]
  have hvol : (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)) box
      = ENNReal.ofReal ((2 * q) ^ d) := by
    show (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ))
        (Set.pi Set.univ (fun _ : Fin d => Set.Icc (-q) q)) = ENNReal.ofReal ((2 * q) ^ d)
    have hone : ∀ i : Fin d, (MeasureTheory.volume : MeasureTheory.Measure ℝ) (Set.Icc (-q) q)
        = ENNReal.ofReal (2 * q) := by
      intro i
      rw [Real.volume_Icc]
      congr 1
      ring
    rw [volume_pi_pi]
    rw [Finset.prod_congr rfl (fun i _ => hone i)]
    rw [Finset.prod_const, Finset.card_fin]
    exact (ENNReal.ofReal_pow (by positivity) d).symm
  have hvoltop : (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)) box < ⊤ := by
    rw [hvol]; exact ENNReal.ofReal_lt_top
  have hreal : ((MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)).real box)
      = (2 * q) ^ d := by
    rw [MeasureTheory.measureReal_def, hvol, ENNReal.toReal_ofReal (by positivity)]
  have hnonneg : 0 ≤ ∫ y in box, (∫ x : EuclideanSpace ℝ (Fin d),
      ‖G (fun i => (x i : ℂ) + (y i : ℂ) * Complex.I)‖ ^ 2) := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [ae_restrict_mem hboxmeas] with y hy
    exact integral_nonneg (fun x => by positivity)
  calc ∫ y in box, (∫ x : EuclideanSpace ℝ (Fin d),
        ‖G (fun i => (x i : ℂ) + (y i : ℂ) * Complex.I)‖ ^ 2)
      = ‖∫ y in box, (∫ x : EuclideanSpace ℝ (Fin d),
        ‖G (fun i => (x i : ℂ) + (y i : ℂ) * Complex.I)‖ ^ 2)‖ :=
        (abs_of_nonneg hnonneg).symm
    _ ≤ (∫ a : EuclideanSpace ℝ (Fin d), ‖H a‖ ^ 2 * Real.exp (4 * Real.pi * q * (∑ i, |a i|)))
          * ((MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℝ)).real box) :=
        norm_setIntegral_le_of_norm_le_const hvoltop hbound
    _ = (2 * q) ^ d * ∫ a : EuclideanSpace ℝ (Fin d),
          ‖H a‖ ^ 2 * Real.exp (4 * Real.pi * q * (∑ i, |a i|)) := by
        rw [hreal]; ring

end Commons.Analysis.Fourier
