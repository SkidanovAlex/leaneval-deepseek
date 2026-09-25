import Mathlib
import Submission.Commons.Analysis.Fourier.mikhlin_multiplier_lp
import Submission.Commons.Analysis.Fourier.fourierInv_mul_fourier_eq_convolution
import Submission.Commons.Analysis.Convolution.eLpNorm_convolution_le_complex
import Submission.Work.BourgainPlan.Maximal.aeIntegrableMulSubOfMemLp
import Submission.Work.BourgainPlan.Maximal.convolutionEqMultiplierSchwartz

namespace Work.BourgainPlan.Maximal

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

open MeasureTheory Filter
open scoped ENNReal Topology

noncomputable section

/-- **`AEStronglyMeasurable` of the convolution integral.**  If `k` and `u` are almost everywhere
strongly measurable, so is `x ↦ ∫ y, k (x - y) * u y`. -/
private lemma aestronglyMeasurable_convolution {k u : ℝ → ℂ}
    (hk : AEStronglyMeasurable k (volume : Measure ℝ))
    (hu : AEStronglyMeasurable u (volume : Measure ℝ)) :
    AEStronglyMeasurable (fun x : ℝ => ∫ y : ℝ, k (x - y) * u y) (volume : Measure ℝ) := by
  have hjoint : AEStronglyMeasurable (fun z : ℝ × ℝ => k (z.1 - z.2) * u z.2)
      (volume.prod volume) :=
    (hk.comp_quasiMeasurePreserving
      (quasiMeasurePreserving_sub_of_right_invariant volume volume)).mul (hu.comp_snd)
  simpa using hjoint.integral_prod_right'

/-- **Extension of an `L^p` convolution bound from Schwartz functions to all of `L^p`.**

If `κ ∈ L¹(ℝ,ℂ)` and the convolution with `κ` is bounded on the Schwartz functions with constant
`C` (i.e. `‖κ * G‖_p ≤ C ‖G‖_p` for every Schwartz `G`), then the *pointwise* convolution
`x ↦ ∫ y, κ (x - y) * f y` is bounded by `C` on all of `L^p(ℝ,ℂ)`.

The proof uses two facts.  First, `SchwartzMap.denseRange_toLpCLM` gives Schwartz functions `Gₙ → f`
in `L^p`.  Second, the two integrals `∫ y, κ (x - y) * f y` and `∫ y, κ (x - y) * Gₙ y` converge
absolutely for almost every `x` (this is `aeIntegrableMulSubOfMemLp`), so that almost everywhere
the convolution integral is additive and the `L^p` triangle inequality applies.  Then Young's
inequality bounds the difference term by `‖κ‖₁ ‖f - Gₙ‖_p → 0` and the result follows by taking
limits. -/
theorem eLpNorm_convolution_le_of_schwartz {p : ℝ} (hp : 1 < p) {κ : ℝ → ℂ}
    (hκ : MemLp κ 1 (volume : Measure ℝ)) {C : ℝ} (hC : 0 ≤ C)
    (hS : ∀ G : SchwartzMap ℝ ℂ, eLpNorm (fun x : ℝ => ∫ y : ℝ, κ (x - y) * (G : ℝ → ℂ) y)
        (ENNReal.ofReal p) (volume : Measure ℝ)
      ≤ ENNReal.ofReal C * eLpNorm (G : ℝ → ℂ) (ENNReal.ofReal p) (volume : Measure ℝ))
    {f : ℝ → ℂ} (hf : MemLp f (ENNReal.ofReal p) (volume : Measure ℝ)) :
    eLpNorm (fun x : ℝ => ∫ y : ℝ, κ (x - y) * f y) (ENNReal.ofReal p) (volume : Measure ℝ)
      ≤ ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal p) (volume : Measure ℝ) := by
  have hpf1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.mpr hp.le
  haveI : Fact (1 ≤ ENNReal.ofReal p) := ⟨hpf1⟩
  have htop : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  -- Schwartz functions are dense in `L^p`
  have hdense : DenseRange (SchwartzMap.toLpCLM ℝ ℂ (ENNReal.ofReal p) (volume : Measure ℝ)) :=
    SchwartzMap.denseRange_toLpCLM htop
  choose G hG using fun n : ℕ =>
    Metric.denseRange_iff.mp hdense (MemLp.toLp f hf) (1 / ((n:ℝ) + 1)) (by positivity)
  have hfin : ∀ n : ℕ,
      eLpNorm (fun x : ℝ => f x - (G n : ℝ → ℂ) x) (ENNReal.ofReal p) (volume : Measure ℝ) < ⊤ := by
    intro n
    exact lt_of_le_of_lt
      (eLpNorm_sub_le hpf1)
      (ENNReal.add_lt_top.mpr ⟨hf.eLpNorm_lt_top,
        ((G n).memLp (ENNReal.ofReal p) volume).eLpNorm_lt_top⟩)
  -- the distance bound, converted to a bound on `eLpNorm (f - Gₙ)`
  have hdist : ∀ n : ℕ,
      (eLpNorm (fun x : ℝ => f x - (G n : ℝ → ℂ) x) (ENNReal.ofReal p) (volume : Measure ℝ)).toReal
        < 1 / ((n:ℝ) + 1) := by
    intro n
    have h := hG n
    rw [Lp.dist_def, SchwartzMap.toLpCLM_apply] at h
    have hcoe : (↑↑(MemLp.toLp f hf) - ↑↑((G n).toLp (ENNReal.ofReal p) volume) : ℝ → ℂ)
        =ᵐ[volume] (fun x : ℝ => f x - (G n : ℝ → ℂ) x) := by
      filter_upwards [hf.coeFn_toLp, (G n).coeFn_toLp (ENNReal.ofReal p) volume] with x h2 h3
      rw [Pi.sub_apply, h2, h3]
    rwa [eLpNorm_congr_ae hcoe] at h
  have h3 : Tendsto (fun n : ℕ =>
      eLpNorm (fun x : ℝ => f x - (G n : ℝ → ℂ) x) (ENNReal.ofReal p) (volume : Measure ℝ))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ =>
        (eLpNorm (fun x : ℝ => f x - (G n : ℝ → ℂ) x) (ENNReal.ofReal p)
          (volume : Measure ℝ)).toReal) atTop (𝓝 0) :=
      squeeze_zero (fun n => ENNReal.toReal_nonneg) (fun n => le_of_lt (hdist n))
        tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 : Tendsto (fun n : ℕ => ENNReal.ofReal
        ((eLpNorm (fun x : ℝ => f x - (G n : ℝ → ℂ) x) (ENNReal.ofReal p)
          (volume : Measure ℝ)).toReal)) atTop (𝓝 0) := by
      have hh := (ENNReal.continuous_ofReal.tendsto (0:ℝ)).comp h1
      simpa only [Function.comp_def, ENNReal.ofReal_zero] using hh
    refine h2.congr' (Eventually.of_forall (fun n => ?_))
    rw [ENNReal.ofReal_toReal (ne_of_lt (hfin n))]
  -- almost everywhere, the convolution integral with `f` splits as `Gₙ` plus the remainder
  have hsplit : ∀ n : ℕ, (fun x : ℝ => ∫ y : ℝ, κ (x - y) * f y) =ᵐ[volume]
      (fun x : ℝ => (∫ y : ℝ, κ (x - y) * (G n : ℝ → ℂ) y)
        + (∫ y : ℝ, κ (x - y) * (f y - (G n : ℝ → ℂ) y))) := by
    intro n
    have hA := aeIntegrableMulSubOfMemLp hp.le hκ hf
    have hB := aeIntegrableMulSubOfMemLp hp.le hκ ((G n).memLp (ENNReal.ofReal p) volume)
    filter_upwards [hA, hB] with x hxA hxB
    have hsub : (∫ y : ℝ, κ (x - y) * (f y - (G n : ℝ → ℂ) y))
        = (∫ y : ℝ, κ (x - y) * f y) - (∫ y : ℝ, κ (x - y) * (G n : ℝ → ℂ) y) := by
      rw [show (fun y : ℝ => κ (x - y) * (f y - (G n : ℝ → ℂ) y))
          = (fun y : ℝ => κ (x - y) * f y - κ (x - y) * (G n : ℝ → ℂ) y) from by
        funext y; ring]
      exact integral_sub hxA hxB
    rw [hsub]; ring
  have hchain : ∀ n : ℕ,
      eLpNorm (fun x : ℝ => ∫ y : ℝ, κ (x - y) * f y) (ENNReal.ofReal p) (volume : Measure ℝ)
      ≤ ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal p) (volume : Measure ℝ)
        + (ENNReal.ofReal C + eLpNorm κ 1 (volume : Measure ℝ))
          * eLpNorm (fun x : ℝ => f x - (G n : ℝ → ℂ) x) (ENNReal.ofReal p)
            (volume : Measure ℝ) := by
    intro n
    have hGn_aesm : AEStronglyMeasurable
        (fun x : ℝ => ∫ y : ℝ, κ (x - y) * (G n : ℝ → ℂ) y) (volume : Measure ℝ) :=
      aestronglyMeasurable_convolution hκ.aestronglyMeasurable
        ((G n).continuous.aestronglyMeasurable)
    have hHn_aesm : AEStronglyMeasurable
        (fun x : ℝ => ∫ y : ℝ, κ (x - y) * (f y - (G n : ℝ → ℂ) y)) (volume : Measure ℝ) :=
      aestronglyMeasurable_convolution hκ.aestronglyMeasurable
        (hf.aestronglyMeasurable.sub ((G n).continuous.aestronglyMeasurable))
    calc eLpNorm (fun x : ℝ => ∫ y : ℝ, κ (x - y) * f y) (ENNReal.ofReal p) (volume : Measure ℝ)
        = eLpNorm (fun x : ℝ => (∫ y : ℝ, κ (x - y) * (G n : ℝ → ℂ) y)
            + (∫ y : ℝ, κ (x - y) * (f y - (G n : ℝ → ℂ) y))) (ENNReal.ofReal p)
            (volume : Measure ℝ) :=
          eLpNorm_congr_ae (hsplit n)
      _ ≤ eLpNorm (fun x : ℝ => ∫ y : ℝ, κ (x - y) * (G n : ℝ → ℂ) y) (ENNReal.ofReal p)
              (volume : Measure ℝ)
            + eLpNorm (fun x : ℝ => ∫ y : ℝ, κ (x - y) * (f y - (G n : ℝ → ℂ) y))
              (ENNReal.ofReal p) (volume : Measure ℝ) :=
          eLpNorm_add_le hpf1
      _ ≤ ENNReal.ofReal C * eLpNorm (G n : ℝ → ℂ) (ENNReal.ofReal p) (volume : Measure ℝ)
            + eLpNorm κ 1 (volume : Measure ℝ)
              * eLpNorm (fun x : ℝ => f x - (G n : ℝ → ℂ) x) (ENNReal.ofReal p)
                (volume : Measure ℝ) :=
          add_le_add (hS (G n))
            (Commons.Analysis.Convolution.eLpNorm_convolution_le_complex κ
              (fun x => f x - (G n : ℝ → ℂ) x) p hp.le hκ
              (hf.sub ((G n).memLp (ENNReal.ofReal p) volume)))
      _ ≤ ENNReal.ofReal C * (eLpNorm f (ENNReal.ofReal p) (volume : Measure ℝ)
              + eLpNorm (fun x : ℝ => f x - (G n : ℝ → ℂ) x) (ENNReal.ofReal p)
                (volume : Measure ℝ))
            + eLpNorm κ 1 (volume : Measure ℝ)
              * eLpNorm (fun x : ℝ => f x - (G n : ℝ → ℂ) x) (ENNReal.ofReal p)
                (volume : Measure ℝ) := by
          gcongr
          calc eLpNorm (G n : ℝ → ℂ) (ENNReal.ofReal p) (volume : Measure ℝ)
              = eLpNorm (f - (fun x : ℝ => f x - (G n : ℝ → ℂ) x)) (ENNReal.ofReal p)
                  (volume : Measure ℝ) :=
                eLpNorm_congr_ae (Eventually.of_forall (fun x => by simp))
            _ ≤ _ := eLpNorm_sub_le hpf1
      _ = ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal p) (volume : Measure ℝ)
            + (ENNReal.ofReal C + eLpNorm κ 1 (volume : Measure ℝ))
              * eLpNorm (fun x : ℝ => f x - (G n : ℝ → ℂ) x) (ENNReal.ofReal p)
                (volume : Measure ℝ) := by
          rw [mul_add, add_mul]; ac_rfl
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal p)
        (volume : Measure ℝ)
        + (ENNReal.ofReal C + eLpNorm κ 1 (volume : Measure ℝ))
          * eLpNorm (fun x : ℝ => f x - (G n : ℝ → ℂ) x) (ENNReal.ofReal p)
            (volume : Measure ℝ))
      atTop (𝓝 (ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal p) (volume : Measure ℝ))) := by
    have hc : (ENNReal.ofReal C + eLpNorm κ 1 (volume : Measure ℝ)) ≠ ⊤ :=
      ne_of_lt (ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top, hκ.eLpNorm_lt_top⟩)
    have hmul := ENNReal.Tendsto.const_mul
      (a := ENNReal.ofReal C + eLpNorm κ 1 (volume : Measure ℝ)) h3 (Or.inr hc)
    have hcst : Tendsto (fun _ : ℕ => ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal p)
        (volume : Measure ℝ))
        atTop (𝓝 (ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal p) (volume : Measure ℝ))) :=
      tendsto_const_nhds
    simpa using hcst.add hmul
  exact ge_of_tendsto hlim (Eventually.of_forall hchain)

/-- **Mikhlin's multiplier bound on `L^p`, in convolution form.**

Let `Θ : ℝ → ℂ` be a Mikhlin symbol with constant `A` (the three bounds `‖Θ‖ ≤ A`,
`|ξ| * ‖deriv Θ ξ‖ ≤ A`, `|ξ|^2 * ‖iteratedDeriv 2 Θ ξ‖ ≤ A`, with `Θ` of class `C²`), and assume
moreover that `Θ` and `κ := 𝓕⁻Θ` are both integrable. Then the convolution with `κ` is bounded on
`L^p(ℝ)` with norm `≤ C_p * A`, for every `1 < p < ∞` and every `f ∈ L^p(ℝ)`.

The point of the *convolution* form (rather than the multiplier form of
`Commons.Analysis.Fourier.mikhlin_multiplier_lp`, which is stated for Schwartz test functions) is
that the operator is defined on all of `L^p` by the explicit integral `∫ y, κ (x-y) * f y`, so it
can be applied to an arbitrary `f ∈ L^p` — which is what the randomisation argument for the annulus
square function needs.

Suggested proof route (the modules below are all in this workspace, under
`Submission/Commons/Analysis/`):
* import `Submission.Commons.Analysis.Fourier.mikhlin_multiplier_lp` (proved),
  `Submission.Commons.Analysis.Fourier.fourierInv_mul_fourier_eq_convolution` (proved) and
  `Submission.Commons.Analysis.Convolution.eLpNorm_convolution_le_complex` (proved);
* apply `mikhlin_multiplier_lp p hp` to a Schwartz `G : SchwartzMap ℝ ℂ` and identify its expression
  `∫ ξ, (Θ ξ * Complex.exp (2πi·x·ξ)) • 𝓕G ξ` with `∫ y, 𝓕⁻Θ (x-y) * G y` — this is
  `Commons.Analysis.Fourier.fourierInv_mul_fourier_eq_convolution (m := Θ) (f := G)` combined with
  `Real.fourierInv_eq'` (which exhibits `𝓕⁻(Θ · 𝓕G) x` as exactly that integral);
* extend from Schwartz `G` to `f ∈ L^p`: by `SchwartzMap.denseRange_toLpCLM` (for `p ≠ ⊤`) pick
  Schwartz `Gₙ → f` in `L^p`; by Young's inequality
  (`Commons.Analysis.Convolution.eLpNorm_convolution_le_complex`, with the `Integrable (𝓕⁻Θ)`
  hypothesis, giving `eLpNorm (fun x => ∫ y, 𝓕⁻Θ (x-y) * f y) p ≤ eLpNorm (𝓕⁻Θ) 1 * eLpNorm f p`)
  the values converge, so
  `eLpNorm (κ ⋆ f) p ≤ ofReal (C*A) * eLpNorm Gₙ p + ‖κ‖₁ * eLpNorm (f - Gₙ) p` and the limit gives
  the claim.  (The a.e.-representative bookkeeping can be avoided by an `ε`/`toReal` argument or by
  passing to `Lp` elements; `eLpNorm` of the pointwise convolution integral is what is needed.) -/
theorem mikhlinConvolutionLp (p : ℝ) (hp : 1 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Θ : ℝ → ℂ) (A : ℝ), 0 ≤ A →
      MeasureTheory.Integrable Θ (MeasureTheory.volume : MeasureTheory.Measure ℝ) →
      ContDiff ℝ 2 Θ →
      (∀ ξ : ℝ, ‖Θ ξ‖ ≤ A) →
      (∀ ξ : ℝ, |ξ| * ‖deriv Θ ξ‖ ≤ A) →
      (∀ ξ : ℝ, |ξ| ^ 2 * ‖iteratedDeriv 2 Θ ξ‖ ≤ A) →
      MeasureTheory.Integrable (FourierTransformInv.fourierInv Θ)
        (MeasureTheory.volume : MeasureTheory.Measure ℝ) →
      ∀ f : ℝ → ℂ, MeasureTheory.MemLp f (ENNReal.ofReal p) (MeasureTheory.volume : MeasureTheory.Measure ℝ) →
        MeasureTheory.eLpNorm (fun x : ℝ => ∫ y : ℝ,
            FourierTransformInv.fourierInv Θ (x - y) * f y)
          (ENNReal.ofReal p) (MeasureTheory.volume : MeasureTheory.Measure ℝ)
        ≤ ENNReal.ofReal (C * A) *
            MeasureTheory.eLpNorm f (ENNReal.ofReal p) (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
  obtain ⟨C, hCpos, hC⟩ := Commons.Analysis.Fourier.mikhlin_multiplier_lp p hp
  refine ⟨C, hCpos, fun Θ A hA hΘint hΘC2 hb hb1 hb2 hκint f hf => ?_⟩
  refine eLpNorm_convolution_le_of_schwartz hp (memLp_one_iff_integrable.mpr hκint)
    (mul_nonneg hCpos.le hA) ?_ hf
  intro G
  rw [convolutionEqMultiplierSchwartz Θ hΘint G]
  exact hC Θ A hA hΘC2 hb hb1 hb2 G

end

end Work.BourgainPlan.Maximal
