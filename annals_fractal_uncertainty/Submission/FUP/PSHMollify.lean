import Submission.FUP.DbarDbarPos
import Submission.FUP.PSHAPI
import Submission.FUP.BMReduction
import Submission.Commons.MeasureTheory.Integral.convolution_ge_of_subMeanValue
import Submission.Commons.MeasureTheory.Integral.tendsto_convolution_le
import Submission.Commons.MeasureTheory.Integral.exists_approximate_identity_complex
import Submission.Commons.MeasureTheory.Integral.contDiff_integral_kernel_mul_complex
import Submission.Commons.Analysis.Complex.psh_smooth_plane_laplacian_nonneg
import Submission.Commons.MeasureTheory.Integral.exists_product_approximate_identity_complex
import Mathlib.MeasureTheory.Integral.Prod

open FractalUncertainty MeasureTheory FourierTransform Metric Filter
open scoped ENNReal BigOperators Topology

set_option autoImplicit false
variable {d : ℕ}
local notation "ℂᵈ" => (Fin d → ℂ)

namespace Submission.FUP

/-- The circle parametrisation used in `SubMeanValue`, as a function of `(θ, v)`. -/
noncomputable def circDir (θ : ℝ) (v : ℂᵈ) : ℂᵈ := fun j => Complex.exp (θ * Complex.I) * v j

@[simp] lemma circDir_apply (θ : ℝ) (v : ℂᵈ) (j : Fin d) :
    circDir θ v j = Complex.exp (θ * Complex.I) * v j := rfl

lemma circDir_eq_smul (θ : ℝ) (v : ℂᵈ) : circDir θ v = Complex.exp (θ * Complex.I) • v := rfl

lemma norm_circDir (θ : ℝ) (v : ℂᵈ) : ‖circDir θ v‖ = ‖v‖ := by
  rw [circDir_eq_smul, norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul]

lemma continuous_circDir (v : ℂᵈ) : Continuous (fun θ : ℝ => circDir θ v) := by
  have h : Continuous fun θ : ℝ => Complex.exp (θ * (Complex.I : ℂ)) :=
    Complex.continuous_exp.comp (by fun_prop)
  exact h.smul continuous_const

/-- `SubMeanValue` written with `circDir`. -/
lemma subMeanValue_iff (u : ℂᵈ → ℝ) :
    SubMeanValue u ↔ ∀ z v, u z ≤ (∫ θ in (0 : ℝ)..(2 * Real.pi), u (z + circDir θ v))
      / (2 * Real.pi) := Iff.rfl

section SmvConv

/-- `K` times a function which is bounded on the support of the compactly supported continuous `K`
is integrable. -/
private lemma integrable_kernel_mul_of_bound {K g : ℂᵈ → ℝ} (hKc : Continuous K)
    (hKcs : HasCompactSupport K) (hg : Measurable g) {M : ℝ}
    (hM : ∀ s ∈ tsupport K, |g s| ≤ M) : Integrable (fun s => K s * g s) := by
  have hKint : Integrable (fun s : ℂᵈ => |K s|) := (hKc.integrable_of_hasCompactSupport hKcs).abs
  refine (hKint.const_mul (max M 0)).mono' (hKc.measurable.mul hg).aestronglyMeasurable ?_
  filter_upwards with s
  by_cases hs : K s = 0
  · simp [hs]
  · have hsm : s ∈ tsupport K := subset_tsupport K (Function.mem_support.mpr hs)
    rw [Real.norm_eq_abs, abs_mul, mul_comm (max M 0) (|K s|)]
    exact mul_le_mul_of_nonneg_left (le_trans (hM s hsm) (le_max_left M 0)) (abs_nonneg (K s))

/-- Integrability of the two-variable integrand used in Fubini for the convolution. -/
private lemma integrable_uncurry_kernel {u : ℂᵈ → ℝ} (hum : Measurable u)
    (hb : BoundedOnCompact u)
    {K : ℂᵈ → ℝ} (hKc : Continuous K) (hKcs : HasCompactSupport K) (z v : ℂᵈ) :
    Integrable (Function.uncurry (fun θ s => K s * u (z - s + circDir θ v)))
      ((volume.restrict (Set.uIoc 0 (2 * Real.pi))).prod volume) := by
  obtain ⟨C, hC⟩ := hKcs.isCompact.isBounded.exists_norm_le
  obtain ⟨CK, hCK⟩ := hKcs.isCompact.exists_bound_of_continuousOn hKc.continuousOn
  obtain ⟨M, hM⟩ := hb (‖z‖ + ‖v‖ + max C 0)
  set Cst : ℝ := max CK 0 * max M 0 with hCst
  have hCst0 : 0 ≤ Cst := mul_nonneg (le_max_right _ _) (le_max_right _ _)
  have hbound : ∀ p ∈ Set.uIoc 0 (2 * Real.pi) ×ˢ tsupport K,
      ‖Function.uncurry (fun θ s => K s * u (z - s + circDir θ v)) p‖ ≤ Cst := by
    rintro ⟨θ, s⟩ ⟨hθ, hs⟩
    have hu : ‖u (z - s + circDir θ v)‖ ≤ max M 0 := by
      rw [Real.norm_eq_abs]
      refine le_trans (hM _ ?_) (le_max_left _ _)
      calc ‖z - s + circDir θ v‖ ≤ ‖z - s‖ + ‖circDir θ v‖ := norm_add_le _ _
        _ ≤ (‖z‖ + ‖s‖) + ‖v‖ := by
            rw [norm_circDir]; exact add_le_add (norm_sub_le z s) le_rfl
        _ ≤ ‖z‖ + ‖v‖ + max C 0 := by
            have := hC s hs
            have := le_max_left C 0
            linarith
    rw [Function.uncurry_apply_pair, norm_mul, hCst]
    exact mul_le_mul (le_trans (hCK s hs) (le_max_left _ _)) hu (norm_nonneg _)
      (le_trans (norm_nonneg _) (le_trans (hCK s hs) (le_max_left _ _)))
  have hmeas : AEStronglyMeasurable
      (Function.uncurry (fun θ s => K s * u (z - s + circDir θ v)))
      ((volume.restrict (Set.uIoc 0 (2 * Real.pi))).prod volume) := by
    refine Measurable.aestronglyMeasurable ?_
    change Measurable (fun p : ℝ × ℂᵈ => K p.2 * u (z - p.2 + circDir p.1 v))
    have hcont : Continuous (fun p : ℝ × ℂᵈ => z - p.2 + circDir p.1 v) :=
      (continuous_const.sub continuous_snd).add ((continuous_circDir v).comp continuous_fst)
    exact (hKc.comp continuous_snd).measurable.mul (hum.comp hcont.measurable)
  have h1 : Integrable (fun θ : ℝ =>
      Set.indicator (Set.uIoc 0 (2 * Real.pi)) (fun _ => (1 : ℝ)) θ)
      (volume.restrict (Set.uIoc 0 (2 * Real.pi))) := by
    have hs : volume (Set.uIoc 0 (2 * Real.pi)) ≠ ⊤ := by
      rw [Real.volume_uIoc]; exact ENNReal.ofReal_ne_top
    exact (integrableOn_const (C := (1 : ℝ)) hs).indicator measurableSet_uIoc
  have h2 : Integrable (fun s : ℂᵈ => Set.indicator (tsupport K) (fun _ => (1 : ℝ)) s) volume :=
    (integrableOn_iff_integrable_of_support_subset (s := tsupport K)
      (fun x hx => by
        by_contra hx'
        exact hx (Set.indicator_of_notMem hx' (fun _ : ℂᵈ => (1 : ℝ))))).mp
      ((integrableOn_const (C := (1 : ℝ)) hKcs.isCompact.measure_lt_top.ne).indicator
        hKcs.isClosed.measurableSet)
  have hmajor : Integrable (fun p : ℝ × ℂᵈ => Cst *
      (Set.indicator (Set.uIoc 0 (2 * Real.pi)) (fun _ => (1 : ℝ)) p.1
        * Set.indicator (tsupport K) (fun _ => (1 : ℝ)) p.2))
      ((volume.restrict (Set.uIoc 0 (2 * Real.pi))).prod volume) :=
    (h1.mul_prod h2).const_mul Cst
  refine hmajor.mono' hmeas ?_
  have hae : ∀ᵐ p : ℝ × ℂᵈ ∂((volume.restrict (Set.uIoc 0 (2 * Real.pi))).prod volume),
      p.1 ∈ Set.uIoc 0 (2 * Real.pi) := by
    have hprod : (volume.restrict (Set.uIoc 0 (2 * Real.pi))).prod (volume : Measure ℂᵈ)
        = (volume.prod volume).restrict (Set.uIoc 0 (2 * Real.pi) ×ˢ Set.univ) := by
      rw [← Measure.prod_restrict (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℂᵈ))
        (s := Set.uIoc 0 (2 * Real.pi)) (t := Set.univ), Measure.restrict_univ]
    rw [hprod]
    exact (ae_restrict_mem (measurableSet_uIoc.prod MeasurableSet.univ)).mono fun p hp => hp.1
  filter_upwards [hae] with p hp
  by_cases hK : p.2 ∈ tsupport K
  · have h := hbound p ⟨hp, hK⟩
    rw [hCst] at h ⊢
    rw [Set.indicator_of_mem hp, Set.indicator_of_mem hK, mul_one, mul_one]
    exact h
  · have hzero : Function.uncurry (fun θ s => K s * u (z - s + circDir θ v)) p = 0 := by
      rw [Function.uncurry_apply_pair, image_eq_zero_of_notMem_tsupport hK, zero_mul]
    rw [hzero, norm_zero]
    simp only [Set.indicator_of_notMem hK, mul_zero, le_refl]

/-- **The circle sub-mean-value property is preserved by convolution with a nonnegative kernel.** -/
theorem subMeanValue_convolution {u : ℂᵈ → ℝ} (hsmv : SubMeanValue u)
    (hum : Measurable u) (hb : BoundedOnCompact u)
    {K : ℂᵈ → ℝ} (hKnn : ∀ s, 0 ≤ K s) (hKc : Continuous K) (hKcs : HasCompactSupport K) :
    SubMeanValue (fun z => ∫ s, K s * u (z - s)) := by
  rw [subMeanValue_iff] at hsmv ⊢
  intro z v
  have hint := integrable_uncurry_kernel hum hb hKc hKcs z v
  have hzw : ∀ (θ : ℝ) (s : ℂᵈ), z + circDir θ v - s = (z - s) + circDir θ v := by
    intro θ s; abel
  simp_rw [hzw]
  rw [intervalIntegral_integral_swap hint]
  have hstep : ∀ s : ℂᵈ, (∫ θ in (0 : ℝ)..(2 * Real.pi), K s * u (z - s + circDir θ v))
      = K s * (∫ θ in (0 : ℝ)..(2 * Real.pi), u (z - s + circDir θ v)) := by
    intro s
    rw [intervalIntegral.integral_const_mul]
  simp_rw [hstep]
  have hpoint : ∀ s : ℂᵈ, K s * (2 * Real.pi * u (z - s))
      ≤ K s * (∫ θ in (0 : ℝ)..(2 * Real.pi), u (z - s + circDir θ v)) := by
    intro s
    refine mul_le_mul_of_nonneg_left ?_ (hKnn s)
    have h := hsmv (z - s) v
    have hπ : (0:ℝ) < 2 * Real.pi := by positivity
    rw [le_div_iff₀ hπ] at h
    calc 2 * Real.pi * u (z - s) = u (z - s) * (2 * Real.pi) := by ring
      _ ≤ ∫ θ in (0 : ℝ)..(2 * Real.pi), u (z - s + circDir θ v) := h
  have hInt1 : Integrable (fun s : ℂᵈ => K s *
      (∫ θ in (0 : ℝ)..(2 * Real.pi), u (z - s + circDir θ v))) := by
    have h := hint.integral_prod_right
    refine h.congr (Filter.Eventually.of_forall fun s => ?_)
    have hπ : (0:ℝ) ≤ 2 * Real.pi := by positivity
    show (∫ θ, Function.uncurry (fun θ s => K s * u (z - s + circDir θ v)) (θ, s)
        ∂(volume.restrict (Set.uIoc 0 (2 * Real.pi))))
      = K s * (∫ θ in (0 : ℝ)..(2 * Real.pi), u (z - s + circDir θ v))
    rw [← intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le hπ,
      Set.uIoc_of_le hπ]
    rfl
  have hInt2 : Integrable (fun s : ℂᵈ => K s * (2 * Real.pi * u (z - s))) := by
    obtain ⟨C, hC⟩ := hKcs.isCompact.isBounded.exists_norm_le
    obtain ⟨Mu, hMu⟩ := hb (‖z‖ + max C 0)
    refine integrable_kernel_mul_of_bound hKc hKcs
      (measurable_const.mul (hum.comp (by fun_prop : Measurable fun s : ℂᵈ => z - s)))
      (M := 2 * Real.pi * max Mu 0) ?_
    intro s hs
    rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
    refine mul_le_mul_of_nonneg_left ?_ (le_of_lt (by positivity : (0:ℝ) < 2 * Real.pi))
    refine le_trans (hMu _ ?_) (le_max_left _ _)
    calc ‖z - s‖ ≤ ‖z‖ + ‖s‖ := norm_sub_le z s
      _ ≤ ‖z‖ + max C 0 := by
          have h1 := hC s hs
          have h2 := le_max_left C 0
          linarith
  have hmono := integral_mono hInt2 hInt1 hpoint
  have hsplit : (∫ s, K s * (2 * Real.pi * u (z - s)))
      = 2 * Real.pi * ∫ s, K s * u (z - s) := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun s => by ring)
  rw [hsplit] at hmono
  have hπ : (0:ℝ) < 2 * Real.pi := by positivity
  rw [le_div_iff₀ hπ]
  linarith

end SmvConv

section Main

/-- The mollification `∫ s, K s * u (z - s)` of `u` by the kernel `K`. -/
noncomputable def mollify (K u : ℂᵈ → ℝ) (z : ℂᵈ) : ℝ := ∫ s, K s * u (z - s)

lemma mollify_apply (K u : ℂᵈ → ℝ) (z : ℂᵈ) : mollify K u z = ∫ s, K s * u (z - s) := rfl

lemma mollify_eq_fun (K u : ℂᵈ → ℝ) : mollify K u = fun z => ∫ s, K s * u (z - s) := rfl

lemma subMeanValue_mollify {u : ℂᵈ → ℝ} (hsmv : SubMeanValue u) (hum : Measurable u)
    (hb : BoundedOnCompact u) {K : ℂᵈ → ℝ} (hKnn : ∀ s, 0 ≤ K s) (hKc : Continuous K)
    (hKcs : HasCompactSupport K) : SubMeanValue (mollify K u) :=
  subMeanValue_convolution hsmv hum hb hKnn hKc hKcs

lemma mollify_ge_of_product {u : ℂᵈ → ℝ} (hsmv : SubMeanValue u) (hum : Measurable u)
    (hb : BoundedOnCompact u) {k : ℂ → ℝ} (hknn : ∀ s, 0 ≤ k s) (hkc : Continuous k)
    (hkcs : HasCompactSupport k) (hkrad : ∀ s c : ℂ, ‖c‖ = 1 → k (c * s) = k s)
    (hkmass : ∫ s : ℂ, k s = 1) (z : ℂᵈ) :
    u z ≤ mollify (fun s : ℂᵈ => ∏ j, k (s j)) u z := by
  rw [mollify_apply]
  exact Commons.MeasureTheory.Integral.convolution_ge_of_subMeanValue
    (d := d) hknn hkc hkcs hkrad hkmass hsmv hum hb z

/-- **A plurisubharmonic function satisfies `∂∂̄u ≥ 0` in the distributional sense.**

The proof smooths `u` by convolution with the product approximate identity `K n` of
`exists_product_approximate_identity_complex`: the smoothing `U n = mollify (K n) u` is smooth,
still satisfies the circle sub-mean-value property (`subMeanValue_convolution`), dominates `u`
(`convolution_ge_of_subMeanValue`) and converges to `u` pointwise (`tendsto_convolution_le`).
Hence `DbarDbarPos (U n) 0` by `psh_smooth_plane_laplacian_nonneg` and `dbarDbarPos_of_hessian`,
and the limit is taken with dominated convergence. -/
theorem isPSH_dbarDbarPos {u : ℂᵈ → ℝ} (hpsh : IsPSH u) (hb : BoundedOnCompact u)
    (hm : Measurable u) : DbarDbarPos u (fun _ => 0) := by
  obtain ⟨k, K, hknn, hkmass, hkc, hkcs, hkrad, hksupp, hKdef, hKnn, hKmass, hKsmooth,
    hKcs, hKsupp⟩ :=
    Commons.MeasureTheory.Integral.exists_product_approximate_identity_complex d
  have hUeq : ∀ (n : ℕ) (z : ℂᵈ), mollify (K n) u z = ∫ s, K n s * u (z - s) := fun n z =>
    mollify_apply (K n) u z
  have hKprod : ∀ (n : ℕ), K n = fun s : ℂᵈ => ∏ j, k n (s j) := by
    intro n; funext s; exact hKdef n s
  have hsmv : ∀ n, SubMeanValue (mollify (K n) u) := fun n =>
    subMeanValue_mollify hpsh.2 hm hb (hKnn n) (hKsmooth n).continuous (hKcs n)
  have hge : ∀ n z, u z ≤ mollify (K n) u z := by
    intro n z
    rw [hKprod n]
    exact mollify_ge_of_product hpsh.2 hm hb (hknn n) (hkc n) (hkcs n) (hkrad n) (hkmass n) z
  have hCinf : ∀ n, ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (mollify (K n) u) := by
    intro n
    have h : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (fun z : ℂᵈ => ∫ s, K n s * u (z - s)) :=
      Commons.MeasureTheory.Integral.contDiff_infty_integral_kernel_mul_complex
        (hKsmooth n) (hKcs n) hm hb
    simpa only [mollify_eq_fun] using h
  have h3top : ((3 : ENat) : WithTop ENat) ≤ ((⊤ : ENat) : WithTop ENat) :=
    WithTop.coe_le_coe.mpr (le_top : (3 : ENat) ≤ ⊤)
  have h2top : ((2 : ENat) : WithTop ENat) ≤ ((⊤ : ENat) : WithTop ENat) :=
    WithTop.coe_le_coe.mpr (le_top : (2 : ENat) ≤ ⊤)
  have hC3 : ∀ n, ContDiff ℝ 3 (mollify (K n) u) := fun n => (hCinf n).of_le h3top
  have hC2 : ∀ n, ContDiff ℝ 2 (mollify (K n) u) := fun n => (hCinf n).of_le h2top
  have hkey : ∀ (n : ℕ) (z : ℂᵈ) (Mu : ℝ),
      (∀ w : ℂᵈ, ‖w‖ ≤ ‖z‖ + 1 → |u w| ≤ Mu) → 0 ≤ Mu →
      |mollify (K n) u z| ≤ Mu := by
    intro n z Mu hMu hMu0
    have hsupp1 : ∀ s ∈ tsupport (K n), ‖s‖ ≤ 1 := by
      intro s hs
      have h1 : s ∈ Metric.closedBall (0 : ℂᵈ) (1 / (↑n + 1)) :=
        closure_minimal (hKsupp n) Metric.isClosed_closedBall hs
      rw [Metric.mem_closedBall, dist_zero_right] at h1
      have h2 : (1 : ℝ) / (↑n + 1) ≤ 1 := by
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < (↑n : ℝ) + 1)]
        have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
      linarith
    have hnorm : ∀ s ∈ tsupport (K n), |u (z - s)| ≤ Mu := by
      intro s hs
      refine hMu _ ?_
      calc ‖z - s‖ ≤ ‖z‖ + ‖s‖ := norm_sub_le z s
        _ ≤ ‖z‖ + 1 := by linarith [hsupp1 s hs]
    have hnorm' : ∀ s ∈ tsupport (K n), |(|u (z - s)|)| ≤ Mu := by
      intro s hs
      rw [abs_of_nonneg (abs_nonneg _)]
      exact hnorm s hs
    have hg1 : Measurable (fun s : ℂᵈ => |u (z - s)|) :=
      (hm.comp (by fun_prop : Measurable fun s : ℂᵈ => z - s)).norm
    have hint1 : Integrable (fun s : ℂᵈ => K n s * |u (z - s)|) :=
      integrable_kernel_mul_of_bound (hKsmooth n).continuous (hKcs n) hg1 hnorm'
    have hint2 : Integrable (fun s : ℂᵈ => K n s * Mu) :=
      ((hKsmooth n).continuous.integrable_of_hasCompactSupport (hKcs n)).mul_const _
    have h1 : |mollify (K n) u z| ≤ ∫ s, K n s * |u (z - s)| := by
      rw [mollify_apply]
      calc |∫ s, K n s * u (z - s)| ≤ ∫ s, |K n s * u (z - s)| := abs_integral_le_integral_abs
        _ = ∫ s, K n s * |u (z - s)| := by
            refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
            show |K n s * u (z - s)| = K n s * |u (z - s)|
            rw [abs_mul, abs_of_nonneg (hKnn n s)]
    have h2 : ∫ s, K n s * |u (z - s)| ≤ Mu := by
      have h3 : ∫ s, K n s * |u (z - s)| ≤ ∫ s, K n s * Mu :=
        integral_mono hint1 hint2 (fun s => by
          by_cases hs : s ∈ tsupport (K n)
          · exact mul_le_mul_of_nonneg_left (hnorm s hs) (hKnn n s)
          · rw [image_eq_zero_of_notMem_tsupport hs, zero_mul, zero_mul])
      rw [integral_mul_const, hKmass n, one_mul] at h3
      exact h3
    linarith
  have hbdd : ∀ n, BoundedOnCompact (mollify (K n) u) := by
    intro n R
    obtain ⟨M', hM'⟩ := hb (max R 0 + 1)
    refine ⟨max M' 0, fun z hz => ?_⟩
    refine hkey n z (max M' 0) (fun w hw => ?_) (le_max_right M' 0)
    refine le_trans (hM' w ?_) (le_max_left M' 0)
    have hzR : ‖z‖ ≤ max R 0 := le_trans hz (le_max_left R 0)
    linarith
  have hdbar : ∀ n, DbarDbarPos (mollify (K n) u) (fun _ => 0) := by
    intro n
    refine dbarDbarPos_of_hessian (hC2 n) measurable_const
      (fun R => ⟨0, fun z _ => by simp⟩) (hbdd n) ?_
    intro z w
    have h := Commons.Analysis.Complex.psh_smooth_plane_laplacian_nonneg
      (mollify (K n) u) (hC3 n) (hsmv n) z w
    simpa using h
  have hlim : ∀ z, Tendsto (fun n => mollify (K n) u z) atTop (nhds (u z)) := by
    intro z
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hε2 : (0:ℝ) < ε / 2 := by linarith
    have hup : ∀ᶠ n : ℕ in atTop, mollify (K n) u z ≤ u z + ε / 2 := by
      simpa only [mollify_apply] using
        Commons.MeasureTheory.Integral.tendsto_convolution_le hpsh.1 hb hKnn hKmass hKsupp
          z (ε / 2) hε2
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hup
    refine ⟨N, fun n hn => ?_⟩
    have hn' := hN n hn
    rw [Real.dist_eq, abs_sub_lt_iff]
    exact ⟨by have := hge n z; linarith, by have := hge n z; linarith⟩
  intro α hα hsα
  refine ⟨?_, ?_, ?_⟩
  · simp only [zero_mul]; exact integrable_zero _ _ _
  · exact integrable_mul_of_boundedOnCompact hm hb (continuous_dbarDbarTest hα)
      (hasCompactSupport_dbarDbarTest hsα)
  · simp only [zero_mul, integral_zero]
    set ψ : ℂᵈ → ℝ := dbarDbarTest α with hψ
    have hψc : Continuous ψ := continuous_dbarDbarTest hα
    have hψcs : HasCompactSupport ψ := hasCompactSupport_dbarDbarTest hsα
    obtain ⟨R, hRpos, hR⟩ := hψcs.isBounded.exists_pos_norm_le
    obtain ⟨Mu, hMu⟩ := hb (R + 1)
    set M : ℝ := max Mu 0 with hMdef
    have hM0 : 0 ≤ M := by rw [hMdef]; exact le_max_right _ _
    have hub : ∀ (n : ℕ) (z : ℂᵈ), ‖z‖ ≤ R → |mollify (K n) u z| ≤ M := by
      intro n z hz
      refine hkey n z M (fun w hw => ?_) hM0
      refine le_trans (hMu w ?_) (le_max_left Mu 0)
      have hzR : ‖z‖ ≤ max R 0 := le_trans hz (le_max_left R 0)
      have hzR' : ‖z‖ ≤ R := hz
      linarith
    have hmaj : Integrable (fun z : ℂᵈ => M * ‖ψ z‖) :=
      (hψc.norm.integrable_of_hasCompactSupport hψcs.norm).const_mul M
    have hconv : Tendsto (fun n => ∫ z, mollify (K n) u z * ψ z) atTop
        (nhds (∫ z, u z * ψ z)) := by
      refine tendsto_integral_of_dominated_convergence (fun z : ℂᵈ => M * ‖ψ z‖)
        (fun n => ((hC3 n).continuous.aestronglyMeasurable).mul hψc.aestronglyMeasurable)
        hmaj (fun n => ?_)
        (Filter.Eventually.of_forall fun z =>
          (hlim z).mul (tendsto_const_nhds (x := ψ z)))
      filter_upwards with z
      by_cases hz : z ∈ tsupport ψ
      · rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hub n z (hR z hz)) (abs_nonneg _)
      · rw [image_eq_zero_of_notMem_tsupport hz, mul_zero]
        simp
    have hnn : ∀ n, (0:ℝ) ≤ ∫ z, mollify (K n) u z * ψ z := fun n => by
      have h := (hdbar n α hα hsα).2.2
      simp only [zero_mul, integral_zero] at h
      exact h
    have hle : (0:ℝ) ≤ ∫ z, u z * ψ z :=
      le_of_tendsto_of_tendsto tendsto_const_nhds hconv (Filter.Eventually.of_forall hnn)
    exact hle

end Main

end Submission.FUP
