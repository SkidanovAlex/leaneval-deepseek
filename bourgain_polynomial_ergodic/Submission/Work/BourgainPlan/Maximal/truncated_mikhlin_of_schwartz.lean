import Mathlib
import Submission.Commons.Analysis.Fourier.fourierInv_mul_fourier_eq_convolution
import Submission.Work.BourgainPlan.Maximal.schwartz_density_L1Lp

/-!
# From the Schwartz bound to the `L¹` bound for a compactly supported symbol

Let `Φ : ℝ → ℂ` be a bounded, measurable symbol supported in `[-R, R]`, so that `Φ ∈ L¹(ℝ)` and the
kernel `K = 𝓕⁻Φ` is a bounded (indeed continuous) function.  We show that if the multiplier operator
with symbol `Φ` is bounded by `E` on `Lᵖ` *on the Schwartz functions*, then the same bound holds for
every integrable `g`:

`∫⁻ ‖𝓕⁻(Φ · 𝓕g)‖^p ≤ E^p ∫⁻ ‖g‖^p`.

The point is that for integrable `f` the multiplier operator is the convolution with `K`,
`𝓕⁻(Φ · 𝓕f) x = ∫ y, K (x - y) * f y`, so approximating `g` by Schwartz functions `Gₙ` both in `L¹`
(the convolution then converges *uniformly*) and in the `Lᵖ` energy, Fatou's lemma gives the claim.
-/

namespace Work.BourgainPlan.Maximal

open MeasureTheory Filter
open scoped ENNReal Topology

noncomputable section

set_option linter.unusedVariables false

/-- If `k` and `u` are almost everywhere strongly measurable, so is the convolution integral
`x ↦ ∫ y, k (x - y) * u y`. -/
private lemma aestronglyMeasurable_convolution_integral {k u : ℝ → ℂ}
    (hk : AEStronglyMeasurable k (volume : Measure ℝ))
    (hu : AEStronglyMeasurable u (volume : Measure ℝ)) :
    AEStronglyMeasurable (fun x : ℝ => ∫ y : ℝ, k (x - y) * u y) (volume : Measure ℝ) := by
  have hjoint : AEStronglyMeasurable (fun z : ℝ × ℝ => k (z.1 - z.2) * u z.2)
      (volume.prod volume) :=
    (hk.comp_quasiMeasurePreserving
      (quasiMeasurePreserving_sub_of_right_invariant volume volume)).mul hu.comp_snd
  simpa using hjoint.integral_prod_right'

/-- **Uniform bound on the difference of two convolution integrals.**  If `‖k‖ ≤ B` pointwise and
`f, h ∈ L¹`, then the convolution integrals with the difference `f - h` differ by at most
`B · ‖f - h‖₁`, uniformly in the point at which the convolutions are evaluated. -/
private lemma norm_convolution_sub_le {k f h : ℝ → ℂ} {B : ℝ}
    (hkB : ∀ t : ℝ, ‖k t‖ ≤ B) (hk : AEStronglyMeasurable k (volume : Measure ℝ))
    (hf : Integrable f) (hh : Integrable h) (x : ℝ) :
    ‖(∫ y : ℝ, k (x - y) * f y) - (∫ y : ℝ, k (x - y) * h y)‖
      ≤ B * ∫ y : ℝ, ‖f y - h y‖ := by
  have hkx : AEStronglyMeasurable (fun y : ℝ => k (x - y)) (volume : Measure ℝ) :=
    hk.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub_left_of_right_invariant volume x)
  have hfi : Integrable (fun y : ℝ => k (x - y) * f y) := by
    refine (hf.norm.const_mul B).mono' (hkx.mul hf.aestronglyMeasurable) ?_
    filter_upwards with y
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hkB (x - y)) (norm_nonneg _)
  have hhi : Integrable (fun y : ℝ => k (x - y) * h y) := by
    refine (hh.norm.const_mul B).mono' (hkx.mul hh.aestronglyMeasurable) ?_
    filter_upwards with y
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hkB (x - y)) (norm_nonneg _)
  have hsub : (∫ y : ℝ, k (x - y) * f y) - (∫ y : ℝ, k (x - y) * h y)
      = ∫ y : ℝ, k (x - y) * (f y - h y) := by
    rw [← integral_sub hfi hhi]
    exact integral_congr_ae (Eventually.of_forall fun y => by ring)
  rw [hsub]
  have hmd : Integrable (fun y : ℝ => k (x - y) * (f y - h y)) := by
    refine ((hf.sub hh).norm.const_mul B).mono'
      (hkx.mul (hf.aestronglyMeasurable.sub hh.aestronglyMeasurable)) ?_
    filter_upwards with y
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hkB (x - y)) (norm_nonneg _)
  calc ‖∫ y : ℝ, k (x - y) * (f y - h y)‖
      ≤ ∫ y : ℝ, ‖k (x - y) * (f y - h y)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y : ℝ, B * ‖f y - h y‖ := by
        refine integral_mono_ae hmd.norm ((hf.sub hh).norm.const_mul B) ?_
        filter_upwards with y
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hkB (x - y)) (norm_nonneg _)
    _ = B * ∫ y : ℝ, ‖f y - h y‖ := integral_const_mul B _

/-- **The truncated Mikhlin bound for integrable functions.**  If the multiplier operator with
symbol `Φ` (bounded by `A`, measurable, supported in `|ξ| ≤ R`) satisfies the `Lᵖ` bound with
constant `E` on Schwartz functions, then it satisfies it on every integrable function `g`.

(`A` and `R` are used only through the integrability of `Φ` and the boundedness of the kernel
`𝓕⁻Φ`.) -/
theorem truncated_mikhlin_of_schwartz (p : ℝ) (hp : 1 < p) {Φ : ℝ → ℂ} {A E R : ℝ}
    (hA : 0 ≤ A) (hE : 0 < E) (hR : 0 ≤ R)
    (hΦbd : ∀ ξ : ℝ, ‖Φ ξ‖ ≤ A) (hΦsupp : ∀ ξ : ℝ, R < |ξ| → Φ ξ = 0)
    (hΦmeas : MeasureTheory.AEStronglyMeasurable Φ (MeasureTheory.volume : MeasureTheory.Measure ℝ))
    (hsch : ∀ G : SchwartzMap ℝ ℂ,
      MeasureTheory.lintegral (MeasureTheory.volume : MeasureTheory.Measure ℝ)
        (fun x : ℝ => ENNReal.rpow (enorm (FourierTransformInv.fourierInv
          (fun ξ : ℝ => Φ ξ * FourierTransform.fourier (G : ℝ → ℂ) ξ) x)) p)
      ≤ ENNReal.ofReal (E ^ p) * MeasureTheory.lintegral (MeasureTheory.volume : MeasureTheory.Measure ℝ)
          (fun x : ℝ => ENNReal.rpow (enorm ((G : ℝ → ℂ) x)) p))
    (g : ℝ → ℂ) (hg : MeasureTheory.Integrable g) :
    MeasureTheory.lintegral (MeasureTheory.volume : MeasureTheory.Measure ℝ)
      (fun x : ℝ => ENNReal.rpow (enorm (FourierTransformInv.fourierInv
        (fun ξ : ℝ => Φ ξ * FourierTransform.fourier g ξ) x)) p)
    ≤ ENNReal.ofReal (E ^ p) * MeasureTheory.lintegral (MeasureTheory.volume : MeasureTheory.Measure ℝ)
        (fun x : ℝ => ENNReal.rpow (enorm (g x)) p) := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  -- ## Step 1: `Φ` is integrable (bounded, measurable, compactly supported)
  have hΦint : Integrable Φ := by
    have hfin : (volume : Measure ℝ) (Set.Icc (-R) R) ≠ ⊤ := by
      rw [Real.volume_Icc]
      exact ENNReal.ofReal_ne_top
    have hdom : Integrable ((Set.Icc (-R) R).indicator (fun _ : ℝ => A)) :=
      (integrableOn_const (C := A) hfin).integrable_indicator measurableSet_Icc
    refine hdom.mono' hΦmeas ?_
    filter_upwards with ξ
    by_cases hξ : ξ ∈ Set.Icc (-R) R
    · rw [Set.indicator_of_mem hξ]
      exact hΦbd ξ
    · have hgt : R < |ξ| := by
        rw [Set.mem_Icc, not_and_or] at hξ
        rcases hξ with h | h
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; linarith
      simp [Set.indicator_of_notMem hξ, hΦsupp ξ hgt]
  -- ## Step 2: the kernel `K = 𝓕⁻Φ` is continuous and bounded by `B = ∫ ‖Φ‖`
  set K : ℝ → ℂ := FourierTransformInv.fourierInv Φ with hKdef
  set B : ℝ := ∫ ξ : ℝ, ‖Φ ξ‖ with hBdef
  have hBnn : 0 ≤ B := by
    rw [hBdef]
    exact integral_nonneg (fun ξ => norm_nonneg _)
  have hKcont : Continuous K := by
    have h1 : K = fun x : ℝ => FourierTransform.fourier Φ (-x) := by
      funext x
      rw [hKdef, Real.fourierInv_eq_fourier_neg]
    rw [h1]
    exact (VectorFourier.fourierIntegral_continuous (μ := (volume : Measure ℝ))
      (L := innerₗ ℝ) Real.continuous_fourierChar continuous_inner hΦint).comp continuous_neg
  have hKbd : ∀ x : ℝ, ‖K x‖ ≤ B := by
    intro x
    have h1 : K x = FourierTransform.fourier Φ (-x) := by
      rw [hKdef, Real.fourierInv_eq_fourier_neg]
    rw [h1, hBdef]
    exact VectorFourier.norm_fourierIntegral_le_integral_norm (μ := (volume : Measure ℝ))
      (L := innerₗ ℝ) Real.fourierChar (Φ : ℝ → ℂ) (-x)
  -- ## Step 3: for integrable `f` the multiplier operator is the convolution with `K`
  have hident : ∀ (f : ℝ → ℂ), Integrable f → ∀ x : ℝ,
      FourierTransformInv.fourierInv (fun ξ : ℝ => Φ ξ * FourierTransform.fourier f ξ) x
        = ∫ y : ℝ, K (x - y) * f y := by
    intro f hf x
    rw [Commons.Analysis.Fourier.fourierInv_mul_fourier_eq_convolution hΦint hf x, hKdef]
    exact integral_congr_ae (Eventually.of_forall fun y => mul_comm _ _)
  -- ## Step 4: the target integrand, the kernel applied to `g`
  set Fg : ℝ → ℝ≥0∞ := fun x => ENNReal.rpow (enorm (∫ y : ℝ, K (x - y) * g y)) p with hFgdef
  have hgoal : MeasureTheory.lintegral (MeasureTheory.volume : MeasureTheory.Measure ℝ)
        (fun x : ℝ => ENNReal.rpow (enorm (FourierTransformInv.fourierInv
          (fun ξ : ℝ => Φ ξ * FourierTransform.fourier g ξ) x)) p)
      = ∫⁻ x : ℝ, Fg x := by
    refine lintegral_congr (fun x => ?_)
    rw [hFgdef, hident g hg x]
  rw [hgoal]
  -- ## Step 5: if `g ∉ Lᵖ` the right hand side is infinite
  rcases eq_or_ne (∫⁻ x : ℝ, ENNReal.rpow (enorm (g x)) p) ⊤ with htop | hfin
  · have hne : ENNReal.ofReal (E ^ p) ≠ 0 :=
      ENNReal.ofReal_ne_zero_iff.mpr (Real.rpow_pos_of_pos hE p)
    rw [htop, ENNReal.mul_top hne]
    exact le_top
  -- ## Step 6: `g ∈ Lᵖ`, approximate it by Schwartz functions
  have hgp : MemLp g (ENNReal.ofReal p) (volume : Measure ℝ) := by
    rw [memLp_iff, lt_top_iff_ne_top,
      eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_ne_zero_iff.mpr hp0)
        ENNReal.ofReal_ne_top hg.aestronglyMeasurable, ENNReal.toReal_ofReal hp0.le]
    exact ENNReal.rpow_ne_top_of_nonneg (by positivity) hfin
  obtain ⟨G, hG1, -, hG3⟩ := schwartz_density_L1Lp p hp g hg hgp
  -- the integrand of the `n`-th approximation
  set F : ℕ → ℝ → ℝ≥0∞ :=
    fun n x => ENNReal.rpow (enorm (∫ y : ℝ, K (x - y) * (G n : ℝ → ℂ) y)) p with hFdef
  have hFaesm : ∀ n : ℕ, AEMeasurable (F n) (volume : Measure ℝ) := by
    intro n
    have h : AEStronglyMeasurable
        (fun x : ℝ => ∫ y : ℝ, K (x - y) * (G n : ℝ → ℂ) y) (volume : Measure ℝ) :=
      aestronglyMeasurable_convolution_integral hKcont.aestronglyMeasurable
        (G n).continuous.aestronglyMeasurable
    exact (h.aemeasurable.enorm).pow_const p
  -- ## Step 7: pointwise convergence of the approximating integrands
  have hpt : ∀ x : ℝ, Tendsto (fun n : ℕ => F n x) atTop (𝓝 (Fg x)) := by
    intro x
    have hle : ∀ n : ℕ,
        ‖(∫ y : ℝ, K (x - y) * (G n : ℝ → ℂ) y) - (∫ y : ℝ, K (x - y) * g y)‖
          ≤ B * ∫ y : ℝ, ‖(G n : ℝ → ℂ) y - g y‖ :=
      fun n => norm_convolution_sub_le hKbd hKcont.aestronglyMeasurable
        (G n).integrable hg x
    have h1 : Tendsto (fun n : ℕ => ‖(∫ y : ℝ, K (x - y) * (G n : ℝ → ℂ) y)
          - (∫ y : ℝ, K (x - y) * g y)‖) atTop (𝓝 0) := by
      refine squeeze_zero (fun n => norm_nonneg _) hle ?_
      simpa using hG1.const_mul B
    have h2 : Tendsto (fun n : ℕ => ∫ y : ℝ, K (x - y) * (G n : ℝ → ℂ) y)
        atTop (𝓝 (∫ y : ℝ, K (x - y) * g y)) :=
      tendsto_iff_norm_sub_tendsto_zero.mpr h1
    have h4 : Tendsto (fun n : ℕ => ‖∫ y : ℝ, K (x - y) * (G n : ℝ → ℂ) y‖ₑ)
        atTop (𝓝 ‖∫ y : ℝ, K (x - y) * g y‖ₑ) := by
      have h5 : Tendsto (fun n : ℕ => ENNReal.ofReal ‖∫ y : ℝ, K (x - y) * (G n : ℝ → ℂ) y‖)
          atTop (𝓝 (ENNReal.ofReal ‖∫ y : ℝ, K (x - y) * g y‖)) :=
        (ENNReal.continuous_ofReal.tendsto _).comp h2.norm
      simpa only [ofReal_norm] using h5
    have h6 := h4.ennrpow_const p
    simpa only [hFdef, hFgdef, ENNReal.rpow_eq_pow] using h6
  -- ## Step 8: Fatou
  have hFatou : ∫⁻ x : ℝ, liminf (fun n : ℕ => F n x) atTop ≤
      liminf (fun n : ℕ => ∫⁻ x : ℝ, F n x) atTop :=
    lintegral_liminf_le' (fun n => hFaesm n)
  -- ## Step 9: the Schwartz bound for each approximation
  have hbound : ∀ n : ℕ, ∫⁻ x : ℝ, F n x ≤
      ENNReal.ofReal (E ^ p) * ∫⁻ x : ℝ, ENNReal.rpow (enorm ((G n : ℝ → ℂ) x)) p := by
    intro n
    have h := hsch (G n)
    calc ∫⁻ x : ℝ, F n x
        = ∫⁻ x : ℝ, ENNReal.rpow (enorm (FourierTransformInv.fourierInv
            (fun ξ : ℝ => Φ ξ * FourierTransform.fourier ((G n) : ℝ → ℂ) ξ) x)) p := by
          refine lintegral_congr (fun x => ?_)
          simp only [hFdef]
          rw [hident ((G n) : ℝ → ℂ) (G n).integrable x]
      _ ≤ _ := h
  -- ## Step 10: pass to the limit
  have hliminfR : liminf (fun n : ℕ => ENNReal.ofReal (E ^ p) *
        ∫⁻ x : ℝ, ENNReal.rpow (enorm ((G n : ℝ → ℂ) x)) p) atTop
      = ENNReal.ofReal (E ^ p) * ∫⁻ x : ℝ, ENNReal.rpow (enorm (g x)) p :=
    (ENNReal.Tendsto.const_mul hG3 (Or.inr ENNReal.ofReal_ne_top)).liminf_eq
  calc ∫⁻ x : ℝ, Fg x
      = ∫⁻ x : ℝ, liminf (fun n : ℕ => F n x) atTop := by
        refine lintegral_congr (fun x => ?_)
        exact ((hpt x).liminf_eq).symm
    _ ≤ liminf (fun n : ℕ => ∫⁻ x : ℝ, F n x) atTop := hFatou
    _ ≤ liminf (fun n : ℕ => ENNReal.ofReal (E ^ p) *
          ∫⁻ x : ℝ, ENNReal.rpow (enorm ((G n : ℝ → ℂ) x)) p) atTop := by
        refine Filter.liminf_le_liminf (Eventually.of_forall hbound) ?_ ?_
        · exact isBoundedUnder_of ⟨⊥, fun n => bot_le⟩
        · exact IsBoundedUnder.isCoboundedUnder_flip (r := fun x1 x2 : ℝ≥0∞ => x1 ≤ x2)
            (isBoundedUnder_of ⟨⊤, fun n => le_top⟩)
    _ = ENNReal.ofReal (E ^ p) * ∫⁻ x : ℝ, ENNReal.rpow (enorm (g x)) p := hliminfR

end

end Work.BourgainPlan.Maximal
