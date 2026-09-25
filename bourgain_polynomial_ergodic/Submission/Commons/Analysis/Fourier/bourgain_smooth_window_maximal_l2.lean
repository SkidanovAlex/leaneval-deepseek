import Mathlib
import Submission.Commons.Analysis.ContDiff.exists_smooth_cutoff_infty
import Submission.Commons.Analysis.ENNReal.add_rpow_two_le_two_mul
import Submission.Commons.Analysis.Fourier.aestronglyMeasurable_conv
import Submission.Commons.Analysis.Fourier.bandSum_windowed
import Submission.Commons.Analysis.Fourier.boundary_layer_l2
import Submission.Commons.Analysis.Fourier.bourgain_entropy_integral_l2_fixed
import Submission.Commons.Analysis.Fourier.chain_exp_sum_le_entropy
import Submission.Commons.Analysis.Fourier.convolution_kernel_fubini
import Submission.Commons.Analysis.Fourier.dilation_variation_scalar_l2
import Submission.Commons.Analysis.Fourier.entropy_integral_le_of_sup_bound
import Submission.Commons.Analysis.Fourier.exists_dyadic_chain_decomposition
import Submission.Commons.Analysis.Fourier.l2_multiplier_sum_square_function
import Submission.Commons.Analysis.Fourier.lintegral_iSup_band_sum_dilation_le
import Submission.Commons.Analysis.Fourier.lintegral_iSup_pi_window_le
import Submission.Commons.Analysis.Fourier.lintegral_sq_sum_le_of_class_bounds
import Submission.Commons.Analysis.Fourier.lintegral_translate_sub_sq_le_of_fourier_support
import Submission.Commons.Analysis.Fourier.max_finset_exponential_sum_l2
import Submission.Commons.Analysis.Fourier.maximal_dilation_convolution_l2
import Submission.Commons.Analysis.Fourier.nested_scales_maximal_l2_real
import Submission.Commons.Analysis.Fourier.net_selfmap_of_cover
import Submission.Commons.Analysis.Fourier.separated_exponentials_near_orthogonal
import Submission.Commons.Analysis.Fourier.separated_maximal_of_smooth_window
import Submission.Commons.Analysis.Metric.coveringNumber_le_of_variation
import Submission.Commons.Analysis.Metric.coveringNumber_ne_top_of_isBounded

set_option maxHeartbeats 8000000

open _root_.MeasureTheory Finset
open scoped BigOperators _root_.ENNReal FourierTransform

set_option maxHeartbeats 800000

namespace Commons.Analysis.Fourier

noncomputable section

/-- The `k`-th band symbol `1_{[λ-h,λ+h]}·φ((·-λ)/h)` as a complex-valued function. -/
def bandSym (φ : ℝ → ℝ) (lamk h : ℝ) : ℝ → ℂ :=
  (Set.Icc (lamk - h) (lamk + h)).indicator fun θ => (φ ((θ - lamk) / h) : ℂ)

lemma bandSym_apply (φ : ℝ → ℝ) (lamk h θ : ℝ) :
    bandSym φ lamk h θ =
      if θ ∈ Set.Icc (lamk - h) (lamk + h) then (φ ((θ - lamk) / h) : ℂ) else 0 :=
  Set.indicator_apply _ _ _

lemma bandSym_measurable {φ : ℝ → ℝ} (hφ : ∀ n : ℕ, ContDiff ℝ n φ) (lamk h : ℝ) :
    Measurable (bandSym φ lamk h) := by
  refine Measurable.indicator ?_ measurableSet_Icc
  exact Complex.measurable_ofReal.comp ((hφ 1).continuous.measurable.comp (by fun_prop))

lemma bandSym_bound {φ : ℝ → ℝ} (hbd : ∀ x : ℝ, |φ x| ≤ 2) (lamk h θ : ℝ) :
    ‖bandSym φ lamk h θ‖ ≤ 2 := by
  rw [bandSym_apply]
  split
  · rw [Complex.norm_real, Real.norm_eq_abs]; exact hbd _
  · simp

/-- The total band symbol `∑_k bandSym φ (λ_k) h`. -/
def bandSumSym {K : ℕ} (φ : ℝ → ℝ) (lam : Fin K → ℝ) (h : ℝ) : ℝ → ℂ :=
  fun θ => ∑ k : Fin K, bandSym φ (lam k) h θ

lemma bandSumSym_measurable {K : ℕ} {φ : ℝ → ℝ} (hφ : ∀ n : ℕ, ContDiff ℝ n φ)
    (lam : Fin K → ℝ) (h : ℝ) : Measurable (bandSumSym φ lam h) :=
  Finset.measurable_sum _ (fun k _ => bandSym_measurable hφ _ _)

lemma bandSumSym_bound {K : ℕ} {φ : ℝ → ℝ} (hbd : ∀ x : ℝ, |φ x| ≤ 2)
    (lam : Fin K → ℝ) (h θ : ℝ) : ‖bandSumSym φ lam h θ‖ ≤ 2 * K := by
  calc ‖bandSumSym φ lam h θ‖ ≤ ∑ k : Fin K, ‖bandSym φ (lam k) h θ‖ := norm_sum_le _ _
    _ ≤ ∑ _k : Fin K, (2:ℝ) := Finset.sum_le_sum (fun k _ => bandSym_bound hbd _ _ _)
    _ = 2 * K := by simp [mul_comm]

/-- A nonnegative bound for the `λ_k`. -/
lemma exists_abs_bound {K : ℕ} (lam : Fin K → ℝ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ k : Fin K, |lam k| ≤ M := by
  rcases Nat.eq_zero_or_pos K with hK | hK
  · subst hK
    exact ⟨0, le_refl 0, fun k => absurd k.isLt (Nat.not_lt_zero k.val)⟩
  · haveI : Nonempty (Fin K) := ⟨⟨0, hK⟩⟩
    obtain ⟨k0, -, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin K))
      (fun k => |lam k|) Finset.univ_nonempty
    exact ⟨|lam k0|, abs_nonneg _, fun k => hmax k (Finset.mem_univ k)⟩

lemma bandSumSym_support_measure_ne_top {K : ℕ} {φ : ℝ → ℝ} (lam : Fin K → ℝ) (h : ℝ) :
    (volume : Measure ℝ) (Function.support (bandSumSym φ lam h)) ≠ ∞ := by
  obtain ⟨M, hMnn, hM⟩ := exists_abs_bound lam
  have hsub : Function.support (bandSumSym φ lam h) ⊆ Set.Icc (-(M + |h|)) (M + |h|) := by
    intro θ hθ
    by_contra hcon
    apply hθ
    rw [bandSumSym]
    refine Finset.sum_eq_zero (fun k _ => ?_)
    rw [bandSym_apply, if_neg]
    intro hmem
    simp only [Set.mem_Icc, not_and_or, not_le] at hcon hmem
    have hkle := abs_le.mp (hM k)
    rcases hcon with hc | hc
    · have h3 : lam k < -M := by linarith [hmem.1, hc, le_abs_self h]
      have : M < |lam k| := by
        rw [abs_of_neg (by linarith)]
        linarith
      linarith [hkle.2]
    · have h3 : M < lam k := by linarith [hmem.2, hc, le_abs_self h]
      have : M < |lam k| := by
        rw [abs_of_pos (by linarith)]
        linarith
      linarith [hkle.1]
  refine ne_top_of_le_ne_top ?_ (measure_mono hsub)
  rw [Real.volume_Icc]
  exact ENNReal.ofReal_ne_top

lemma bandSumSym_memLp_one {K : ℕ} {φ : ℝ → ℝ} (hφ : ∀ n : ℕ, ContDiff ℝ n φ)
    (hbd : ∀ x : ℝ, |φ x| ≤ 2) (lam : Fin K → ℝ) (h : ℝ) :
    MemLp (bandSumSym φ lam h) 1 (volume : Measure ℝ) :=
  (memLp_top_of_bound (bandSumSym_measurable hφ lam h).aestronglyMeasurable _
      (Filter.Eventually.of_forall (fun θ => bandSumSym_bound hbd lam h θ))
    ).mono_exponent_of_measure_support_ne_top
      (s := Function.support (bandSumSym φ lam h)) (fun _ hx => Function.notMem_support.mp hx)
      (bandSumSym_support_measure_ne_top lam h) le_top

lemma bandSumSym_memLp_two {K : ℕ} {φ : ℝ → ℝ} (hφ : ∀ n : ℕ, ContDiff ℝ n φ)
    (hbd : ∀ x : ℝ, |φ x| ≤ 2) (lam : Fin K → ℝ) (h : ℝ) :
    MemLp (bandSumSym φ lam h) 2 (volume : Measure ℝ) :=
  (memLp_top_of_bound (bandSumSym_measurable hφ lam h).aestronglyMeasurable _
      (Filter.Eventually.of_forall (fun θ => bandSumSym_bound hbd lam h θ))
    ).mono_exponent_of_measure_support_ne_top
      (s := Function.support (bandSumSym φ lam h)) (fun _ hx => Function.notMem_support.mp hx)
      (bandSumSym_support_measure_ne_top lam h) le_top

lemma bandSumSym_memLp_top {K : ℕ} {φ : ℝ → ℝ} (hφ : ∀ n : ℕ, ContDiff ℝ n φ)
    (hbd : ∀ x : ℝ, |φ x| ≤ 2) (lam : Fin K → ℝ) (h : ℝ) :
    MemLp (bandSumSym φ lam h) ⊤ (volume : Measure ℝ) :=
  memLp_top_of_bound (bandSumSym_measurable hφ lam h).aestronglyMeasurable _
    (Filter.Eventually.of_forall (fun θ => bandSumSym_bound hbd lam h θ))

/-- **Identification of the smooth band sum with a single Fourier multiplier.**
For `f ∈ L¹ ∩ L²`, the target's double integral is the single multiplier
`ξ ↦ (∑_k φ(-(2πξ+λ_k)/h))` applied to `𝓕 f`, times `2π`. -/
theorem bandSum_eq_single_multiplier {K : ℕ} (lam : Fin K → ℝ) (φ : ℝ → ℝ)
    (hφ : ∀ n : ℕ, ContDiff ℝ n φ) (hbd : ∀ x : ℝ, |φ x| ≤ 2)
    (hsupp : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    {h : ℝ} (hh : 0 < h) {f : ℝ → ℂ} (hf1 : MemLp f 1 (volume : Measure ℝ))
    (hf2 : MemLp f 2 (volume : Measure ℝ)) (x : ℝ) :
    (∫ y, f y * (∑ k : Fin K, ∫ θ in (lam k - h)..(lam k + h),
        (φ ((θ - lam k) / h) : ℂ) *
          Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ)))))
      = 2 * Real.pi * FourierTransformInv.fourierInv
          (fun ξ : ℝ => (∑ k : Fin K, (φ (-((2 * Real.pi * ξ + lam k) / h)) : ℂ)) *
            FourierTransform.fourier f ξ) x := by

  have hcont : Continuous φ := (hφ 1).continuous
  have hsym : ∀ ξ : ℝ, bandSumSym φ lam h (-(2 * Real.pi) * ξ)
      = ∑ k : Fin K, (φ (-((2 * Real.pi * ξ + lam k) / h)) : ℂ) := by
    intro ξ
    rw [bandSumSym]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [bandSym_apply]
    by_cases hmem : -(2 * Real.pi) * ξ ∈ Set.Icc (lam k - h) (lam k + h)
    · rw [if_pos hmem]
      congr 1
      field_simp
      ring
    · rw [if_neg hmem]
      symm
      rw [Complex.ofReal_eq_zero]
      apply hsupp
      have hnot : ¬ ((-(2 * Real.pi) * ξ) ∈ Set.Icc (lam k - h) (lam k + h)) := hmem
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hnot
      have key : (1:ℝ) ≤ |(-((2 * Real.pi * ξ + lam k) / h))| := by
        rw [abs_neg, abs_div, abs_of_pos hh, le_div_iff₀ hh, one_mul]
        rcases hnot with h1 | h1
        · rw [abs_of_pos (by linarith)]; linarith
        · rw [abs_of_neg (by linarith)]; linarith
      exact key
  have hstep : ∀ y : ℝ,
      (∫ θ, bandSumSym φ lam h θ * Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ))))
      = ∑ k : Fin K, ∫ θ in (lam k - h)..(lam k + h),
          (φ ((θ - lam k) / h) : ℂ) * Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ))) := by
    intro y
    simp only [bandSumSym, Finset.sum_mul]
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [intervalIntegral.integral_of_le (by linarith : lam k - h ≤ lam k + h),
        ← MeasureTheory.integral_indicator measurableSet_Ioc]
      apply integral_congr_ae
      filter_upwards with θ
      rw [bandSym_apply, Set.indicator_apply]
      by_cases hθ : θ ∈ Set.Icc (lam k - h) (lam k + h)
      · by_cases hθ' : θ ∈ Set.Ioc (lam k - h) (lam k + h)
        · simp [hθ, hθ']
        · have hθe : θ = lam k - h := by
            simp only [Set.mem_Ioc, not_and_or, not_lt, not_le] at hθ'
            rcases hθ' with hc | hc
            · linarith [hθ.1, hc]
            · exfalso; linarith [hθ.2, hc]
          rw [if_pos hθ, if_neg hθ', hθe]
          have h1 : (lam k - h - lam k) / h = -1 := by
            field_simp
            ring
          rw [h1, hsupp (-1) (by norm_num : (1:ℝ) ≤ |(-1:ℝ)|)]
          simp
      · rw [if_neg hθ]
        by_cases hθ' : θ ∈ Set.Ioc (lam k - h) (lam k + h)
        · exact absurd (Set.Ioc_subset_Icc_self hθ') hθ
        · simp [hθ']
    · intro k _
      have hm : MeasurableSet (Set.Icc (lam k - h) (lam k + h)) := measurableSet_Icc
      have hint : IntegrableOn (fun θ : ℝ => (φ ((θ - lam k) / h) : ℂ) *
          Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ))))
          (Set.Icc (lam k - h) (lam k + h)) volume :=
        ContinuousOn.integrableOn_compact isCompact_Icc
          ((Continuous.mul (Complex.continuous_ofReal.comp (hcont.comp (by fun_prop)))
            (Complex.continuous_exp.comp (by fun_prop))).continuousOn)
      have hI : Integrable ((Set.Icc (lam k - h) (lam k + h)).indicator
          (fun θ : ℝ => (φ ((θ - lam k) / h) : ℂ) *
            Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ))))) volume :=
        hint.integrable_indicator hm
      have hfun : (fun θ : ℝ => bandSym φ (lam k) h θ *
            Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ))))
          = (Set.Icc (lam k - h) (lam k + h)).indicator (fun θ : ℝ =>
              (φ ((θ - lam k) / h) : ℂ) *
                Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ)))) := by
        funext θ
        rw [bandSym_apply, Set.indicator_apply]
        by_cases hθ : θ ∈ Set.Icc (lam k - h) (lam k + h) <;> simp [hθ]
      rw [hfun]
      exact hI
  have hLHS : (∫ y, f y * (∑ k : Fin K, ∫ θ in (lam k - h)..(lam k + h),
        (φ ((θ - lam k) / h) : ℂ) *
          Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ)))))
      = ∫ y, f y * (∫ θ, bandSumSym φ lam h θ *
          Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ)))) := by
    apply integral_congr_ae
    filter_upwards with y
    rw [hstep y]
  rw [hLHS, convolution_kernel_fubini (bandSumSym φ lam h) f (bandSumSym_measurable hφ lam h)
      (bandSumSym_memLp_one hφ hbd lam h) (bandSumSym_memLp_two hφ hbd lam h)
      (bandSumSym_memLp_top hφ hbd lam h) hf1 hf2 x]
  have hfun : (fun ξ : ℝ => bandSumSym φ lam h (-(2 * Real.pi) * ξ) *
      FourierTransform.fourier f ξ)
      = (fun ξ : ℝ => (∑ k : Fin K, (φ (-((2 * Real.pi * ξ + lam k) / h)) : ℂ)) *
          FourierTransform.fourier f ξ) := by
    funext ξ
    rw [hsym]
  rw [hfun]

end

end Commons.Analysis.Fourier


/-!
# The `ℓ²`-vector form of Bourgain's entropy integral (Lemma 3.33)

The published `Commons.Analysis.Fourier.bourgain_entropy_integral_l2_fixed` measures the metric
entropy of the windowed curve `t ↦ ((f k * Ψ_t)(x))_k` in the **supremum** norm on `Fin K → ℂ`.
The chain estimate `Commons.Analysis.Fourier.chain_exp_sum_le_entropy` however controls nets with
**`ℓ²`** radii, and the `ℓ²`-covering number is larger than the sup one.  This file proves the
`ℓ²` form: the curve is regarded as a map into `EuclideanSpace ℂ (Fin K)` and the entropy integral
is controlled by `‖Ψ‖_∞` and `log²(K+2)`, with the vector-valued variation bound obtained from the
scalar variation bound by Minkowski's inequality.
-/

namespace Commons.Analysis.Fourier

open _root_.MeasureTheory _root_.Metric
open scoped _root_.ENNReal _root_.Topology BigOperators

noncomputable section

variable {K : ℕ}

/-- The windowed dilation curve, as a map into the Euclidean space `EuclideanSpace ℂ (Fin K)`. -/
noncomputable def winCurveL2 (Ψ : SchwartzMap ℝ ℂ) (f : Fin K → ℝ → ℂ) (x : ℝ) :
    {t : ℝ // 0 < t} → EuclideanSpace ℂ (Fin K) :=
  fun t => WithLp.toLp 2 (fun k : Fin K =>
    ∫ y : ℝ, f k y * ((t : ℝ)⁻¹ • (Ψ : ℝ → ℂ) ((x - y) / (t : ℝ))))

@[simp] lemma winCurveL2_apply (Ψ : SchwartzMap ℝ ℂ) (f : Fin K → ℝ → ℂ) (x : ℝ)
    (t : {t : ℝ // 0 < t}) (k : Fin K) :
    winCurveL2 Ψ f x t k = ∫ y : ℝ, f k y * ((t : ℝ)⁻¹ • (Ψ : ℝ → ℂ) ((x - y) / (t : ℝ))) :=
  rfl

/-- The logarithmic reparametrisation of `winCurveL2`. -/
noncomputable def winCurveRL2 (Ψ : SchwartzMap ℝ ℂ) (f : Fin K → ℝ → ℂ) (x : ℝ) :
    ℝ → EuclideanSpace ℂ (Fin K) :=
  fun u => winCurveL2 Ψ f x ⟨Real.exp u, Real.exp_pos u⟩

/-- The `ℓ²`-valued `s`-variation of the curve `winCurveL2` over the scales `t > 0`. -/
noncomputable def winVarVecL2 (Ψ : SchwartzMap ℝ ℂ) (f : Fin K → ℝ → ℂ) (x : ℝ) (s : ℝ) : ℝ≥0∞ :=
  ⨆ (J : ℕ) (u : Fin (J + 1) → {t : ℝ // 0 < t}),
    ⨆ (_ : StrictMono (fun j => (u j : ℝ))),
      ENNReal.ofReal ((∑ j : Fin J,
        ‖winCurveL2 Ψ f x (u (Fin.castSucc j)) - winCurveL2 Ψ f x (u (Fin.succ j))‖ ^ s)
          ^ ((1:ℝ)/s))

/-- The entropy-number integrand of the `ℓ²`-valued curve. -/
noncomputable def winML2 (Ψ : SchwartzMap ℝ ℂ) (f : Fin K → ℝ → ℂ) (x : ℝ) (l : ℝ) : ENNReal :=
  (((Metric.coveringNumber l.toNNReal (Set.range (winCurveL2 Ψ f x)) : ℕ∞) : ENNReal) - 1)

/-- The `ℝ≥0∞`-valued supremum of the `ℓ²`-valued curve. -/
noncomputable def winFL2 (Ψ : SchwartzMap ℝ ℂ) (f : Fin K → ℝ → ℂ) (x : ℝ) : ENNReal :=
  ⨆ (t : {t : ℝ // 0 < t}), ‖winCurveL2 Ψ f x t‖ₑ

/-- The range of the logarithmically reparametrised curve is the range of the curve. -/
lemma range_winCurveRL2 (Ψ : SchwartzMap ℝ ℂ) (f : Fin K → ℝ → ℂ) (x : ℝ) :
    Set.range (winCurveRL2 Ψ f x) = Set.range (winCurveL2 Ψ f x) := by
  have h1 : Set.range (winCurveRL2 Ψ f x)
      = Set.range (winCurveL2 Ψ f x ∘ fun u : ℝ =>
          (⟨Real.exp u, Real.exp_pos u⟩ : {t : ℝ // 0 < t})) := rfl
  have h2 : Set.range (fun u : ℝ => (⟨Real.exp u, Real.exp_pos u⟩ : {t : ℝ // 0 < t}))
      = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro t
    exact ⟨Real.log t.1, Subtype.ext (Real.exp_log t.2)⟩
  rw [h1, Set.range_comp, h2, Set.image_univ]

/-- The tuple sums of the logarithmically reparametrised curve are bounded by `winVarVecL2`. -/
lemma winVarVecL2_tuple_bound (Ψ : SchwartzMap ℝ ℂ) (f : Fin K → ℝ → ℂ) (x : ℝ) {s : ℝ}
    (J : ℕ) (u : Fin (J + 1) → ℝ) (hu : StrictMono u) :
    ENNReal.ofReal ((∑ j : Fin J, dist (winCurveRL2 Ψ f x (u (Fin.castSucc j)))
        (winCurveRL2 Ψ f x (u (Fin.succ j))) ^ s) ^ ((1:ℝ)/s)) ≤ winVarVecL2 Ψ f x s := by
  simp only [winCurveRL2, winVarVecL2, dist_eq_norm]
  refine le_iSup_of_le J (le_iSup_of_le (fun j => (⟨Real.exp (u j), Real.exp_pos _⟩ :
    {t : ℝ // 0 < t})) ?_)
  refine le_iSup_of_le ?_ le_rfl
  intro i j hij
  show (Real.exp (u i) : ℝ) < Real.exp (u j)
  exact Real.exp_lt_exp.mpr (hu hij)

/-- In the Euclidean space the `enorm` of a vector is the `ℓ²` combination of the coordinates. -/
lemma enorm_eq_sqrt_sum_L2 (v : EuclideanSpace ℂ (Fin K)) :
    ‖v‖ₑ = (∑ k : Fin K, ‖v k‖ₑ ^ (2:ℝ)) ^ ((1:ℝ)/2) := by
  have h1 : (∑ k : Fin K, ‖v k‖ₑ ^ (2:ℝ))
      = ENNReal.ofReal (∑ k : Fin K, ‖v k‖ ^ 2) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => sq_nonneg _)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [enorm_eq_ofReal_norm',
      show ENNReal.ofReal ‖v k‖ ^ (2:ℝ) = ENNReal.ofReal (‖v k‖ ^ 2) by
        rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast,
          ENNReal.ofReal_pow (norm_nonneg _)]]
  rw [h1, enorm_eq_ofReal_norm', EuclideanSpace.norm_eq, Real.sqrt_eq_rpow,
    ENNReal.ofReal_rpow_of_nonneg (Finset.sum_nonneg fun k _ => sq_nonneg _)
      (by norm_num : (0:ℝ) ≤ 1/2)]

end

namespace MinkowskiInterlude

/-! ### Minkowski's inequality for finite sums -/

/-- **Minkowski's inequality for finite sums.**  For `2 < s` and nonnegative `b`, the `ℓ^s(ℓ²)`
norm is bounded by the `ℓ²(ℓ^s)` norm:
`(∑_j (∑_k b j k²)^{s/2})^{1/s} ≤ (∑_k (∑_j b j k^s)^{2/s})^{1/2}`. -/
theorem minkowski_sum {ι κ : Type*} [Fintype ι] [Fintype κ] (b : ι → κ → ℝ)
    (hb : ∀ j k, 0 ≤ b j k) {s : ℝ} (hs : 2 < s) :
    (∑ j, (∑ k, b j k ^ (2:ℝ)) ^ (s / 2)) ^ (1 / s)
      ≤ (∑ k, (∑ j, b j k ^ s) ^ (2 / s)) ^ ((1:ℝ) / 2) := by
  have hs0 : 0 < s := by linarith
  set A : ι → ℝ := fun j => (∑ k, b j k ^ (2:ℝ)) ^ ((1:ℝ)/2) with hA
  have hsum : ∀ j, 0 ≤ ∑ k, b j k ^ (2:ℝ) := fun j =>
    Finset.sum_nonneg (fun k _ => Real.rpow_nonneg (hb j k) 2)
  have hAnn : ∀ j, 0 ≤ A j := fun j => by
    rw [hA]; beta_reduce
    exact Real.rpow_nonneg (hsum j) ((1:ℝ)/2)
  have hAsq : ∀ j, (A j) ^ (2:ℝ) = ∑ k, b j k ^ (2:ℝ) := fun j => by
    rw [hA]; beta_reduce
    rw [← Real.rpow_mul (hsum j), show ((1:ℝ)/2) * 2 = 1 by norm_num, Real.rpow_one]
  have hAs : ∀ j, (A j) ^ s = (∑ k, b j k ^ (2:ℝ)) ^ (s / 2) := fun j => by
    rw [hA]; beta_reduce
    rw [← Real.rpow_mul (hsum j)]
    congr 1
    ring
  have hAsplit : ∀ j, (A j) ^ s = (A j) ^ (s - 2) * (A j) ^ (2:ℝ) := fun j => by
    rw [← Real.rpow_add' (hAnn j) (by linarith : (s - 2) + 2 ≠ 0)]
    congr 1
    ring
  -- Hölder step
  have hpq : Real.HolderConjugate (s / (s - 2)) (s / 2) :=
    ⟨by field_simp; ring, by positivity, by positivity⟩
  have hholder : ∀ k, ∑ j, (A j) ^ (s - 2) * (b j k) ^ (2:ℝ)
      ≤ (∑ j, (A j) ^ s) ^ ((s-2)/s) * (∑ j, (b j k) ^ s) ^ (2/s) := by
    intro k
    have h := Real.inner_le_Lp_mul_Lq_of_nonneg Finset.univ hpq
      (f := fun j => (A j) ^ (s - 2)) (g := fun j => (b j k) ^ (2:ℝ))
      (fun j _ => Real.rpow_nonneg (hAnn j) _) (fun j _ => Real.rpow_nonneg (hb j k) 2)
    have h1 : ∀ j, ((A j) ^ (s - 2)) ^ (s / (s - 2)) = (A j) ^ s := by
      intro j
      rw [← Real.rpow_mul (hAnn j)]
      congr 1
      have hne : s - 2 ≠ 0 := by linarith
      field_simp
    have h2 : ∀ j, ((b j k) ^ (2:ℝ)) ^ (s / 2) = (b j k) ^ s := by
      intro j
      rw [← Real.rpow_mul (hb j k)]
      ring_nf
    rw [Finset.sum_congr rfl (fun j _ => h1 j), Finset.sum_congr rfl (fun j _ => h2 j)] at h
    have e1 : (1 / (s / (s - 2))) = (s - 2) / s := by
      field_simp
    have e2 : (1 / (s / 2)) = 2 / s := by
      field_simp
    rw [e1, e2] at h
    exact h
  have hB : ∑ j, (A j) ^ s
      ≤ (∑ j, (A j) ^ s) ^ ((s-2)/s) * ∑ k, (∑ j, (b j k) ^ s) ^ (2/s) := by
    calc ∑ j, (A j) ^ s = ∑ j, (A j) ^ (s - 2) * (A j) ^ (2:ℝ) :=
          Finset.sum_congr rfl fun j _ => hAsplit j
      _ = ∑ j, (A j) ^ (s - 2) * ∑ k, (b j k) ^ (2:ℝ) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hAsq j]
      _ = ∑ j, ∑ k, (A j) ^ (s - 2) * (b j k) ^ (2:ℝ) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.mul_sum]
      _ = ∑ k, ∑ j, (A j) ^ (s - 2) * (b j k) ^ (2:ℝ) := Finset.sum_comm
      _ ≤ ∑ k, (∑ j, (A j) ^ s) ^ ((s-2)/s) * (∑ j, (b j k) ^ s) ^ (2/s) :=
          Finset.sum_le_sum fun k _ => hholder k
      _ = (∑ j, (A j) ^ s) ^ ((s-2)/s) * ∑ k, (∑ j, (b j k) ^ s) ^ (2/s) := by
          rw [Finset.mul_sum]
  set B : ℝ := ∑ j, (A j) ^ s with hBdef
  set C : ℝ := ∑ k, (∑ j, (b j k) ^ s) ^ (2/s) with hCdef
  have hBnn : 0 ≤ B := Finset.sum_nonneg fun j _ => Real.rpow_nonneg (hAnn j) _
  have hCnn : 0 ≤ C := Finset.sum_nonneg fun k _ =>
    Real.rpow_nonneg (Finset.sum_nonneg fun j _ => Real.rpow_nonneg (hb j k) s) _
  have hBC : B ≤ B ^ ((s-2)/s) * C := hB
  have hLHS : (∑ j, (∑ k, b j k ^ (2:ℝ)) ^ (s / 2)) = B := by
    rw [hBdef]
    exact Finset.sum_congr rfl fun j _ => (hAs j).symm
  rw [hLHS]
  rcases eq_or_lt_of_le hBnn with hB0 | hBpos
  · rw [← hB0, Real.zero_rpow (by positivity : (1/s : ℝ) ≠ 0)]
    exact Real.rpow_nonneg hCnn _
  · have hexp : 2/s + (s-2)/s = (1:ℝ) := by
      have hsne : s ≠ 0 := hs0.ne'
      field_simp
      ring
    have hBeq : B = B ^ (2/s) * B ^ ((s-2)/s) := by
      have h1 : B ^ (2/s) * B ^ ((s-2)/s) = B ^ (2/s + (s-2)/s) :=
        (Real.rpow_add' hBpos.le (by rw [hexp]; norm_num)).symm
      rw [h1, hexp, Real.rpow_one]
    have hdiv : B ^ (2/s) ≤ C := by
      have hpos : 0 < B ^ ((s-2)/s) := Real.rpow_pos_of_pos hBpos _
      have h2 : B ^ (2/s) * B ^ ((s-2)/s) ≤ C * B ^ ((s-2)/s) := by
        rw [← hBeq]
        exact hBC.trans (le_of_eq (mul_comm _ _))
      exact le_of_mul_le_mul_right h2 hpos
    calc B ^ (1 / s) = (B ^ (2 / s)) ^ ((1:ℝ) / 2) := by
          rw [← Real.rpow_mul hBnn]
          congr 1
          field_simp
      _ ≤ C ^ ((1:ℝ) / 2) := Real.rpow_le_rpow (Real.rpow_nonneg hBnn _) hdiv (by norm_num)

end MinkowskiInterlude

open MinkowskiInterlude

variable {K : ℕ}

/-- The coordinates of `winCurveL2` are the scalar windowed convolutions. -/
lemma winCurveL2_sub_apply (Ψ : SchwartzMap ℝ ℂ) (f : Fin K → ℝ → ℂ) (x : ℝ)
    (t t' : {t : ℝ // 0 < t}) (k : Fin K) :
    (winCurveL2 Ψ f x t - winCurveL2 Ψ f x t') k
      = winOp Ψ (f k) x (t : ℝ) - winOp Ψ (f k) x (t' : ℝ) := rfl

/-- Squares of `ofReal`s. -/
lemma ofReal_rpow_two_eq {x : ℝ} (hx : 0 ≤ x) :
    ENNReal.ofReal (x ^ (2:ℝ)) = ENNReal.ofReal x ^ (2:ℝ) :=
  (ENNReal.ofReal_rpow_of_nonneg hx (by norm_num : (0:ℝ) ≤ 2)).symm

/-- **The `ℓ²`-valued variation is dominated by the `ℓ²` sum of the scalar variations**
(Minkowski's inequality, with `p = 2 ≤ q = s`). -/
lemma winVarVecL2_sq_le_sum (Ψ : SchwartzMap ℝ ℂ) (f : Fin K → ℝ → ℂ) (x : ℝ) {s : ℝ}
    (hs : 2 < s) :
    winVarVecL2 Ψ f x s ^ (2:ℝ) ≤ ∑ k : Fin K, winVar Ψ (f k) x s ^ (2:ℝ) := by
  have hs0 : 0 < s := by linarith
  set V : ℝ≥0∞ := (∑ k : Fin K, winVar Ψ (f k) x s ^ (2:ℝ)) ^ ((1:ℝ)/2) with hV
  have hstep : ∀ (J : ℕ) (u : Fin (J+1) → {t : ℝ // 0 < t})
      (hu : StrictMono (fun j => (u j : ℝ))),
      ENNReal.ofReal ((∑ j : Fin J, ‖winCurveL2 Ψ f x (u (Fin.castSucc j))
        - winCurveL2 Ψ f x (u (Fin.succ j))‖ ^ s) ^ ((1:ℝ)/s)) ≤ V := by
    intro J u hu
    set D : Fin J → Fin K → ℝ := fun j k =>
      ‖(winCurveL2 Ψ f x (u (Fin.castSucc j)) - winCurveL2 Ψ f x (u (Fin.succ j))) k‖ with hD
    have hDnn : ∀ j k, 0 ≤ D j k := fun j k => norm_nonneg _
    have hDk : ∀ (j : Fin J) (k : Fin K), D j k
        = ‖winOp Ψ (f k) x (u (Fin.castSucc j) : ℝ) - winOp Ψ (f k) x (u (Fin.succ j) : ℝ)‖ := by
      intro j k
      rw [hD]
      exact congrArg norm (winCurveL2_sub_apply Ψ f x (u (Fin.castSucc j)) (u (Fin.succ j)) k)
    -- replace the vector norms by the `ℓ²` sums of the coordinates
    have hnorm : ∀ j : Fin J, ‖winCurveL2 Ψ f x (u (Fin.castSucc j))
        - winCurveL2 Ψ f x (u (Fin.succ j))‖
        = (∑ k : Fin K, D j k ^ (2:ℝ)) ^ ((1:ℝ)/2) := by
      intro j
      rw [EuclideanSpace.norm_eq, Real.sqrt_eq_rpow]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hD, Real.rpow_two]
    have hsum_eq : (∑ j : Fin J, ‖winCurveL2 Ψ f x (u (Fin.castSucc j))
          - winCurveL2 Ψ f x (u (Fin.succ j))‖ ^ s)
        = ∑ j : Fin J, (∑ k : Fin K, D j k ^ (2:ℝ)) ^ (s/2) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hnorm j, ← Real.rpow_mul (Finset.sum_nonneg fun k _ =>
        Real.rpow_nonneg (hDnn j k) 2)]
      congr 1
      ring
    -- Minkowski
    have hmink := minkowski_sum (ι := Fin J) (κ := Fin K) D hDnn (s := s) hs
    -- the scalar chain values are bounded by the scalar variations
    have hWk : ∀ k : Fin K,
        ENNReal.ofReal ((∑ j : Fin J, D j k ^ s) ^ ((1:ℝ)/s)) ≤ winVar Ψ (f k) x s := by
      intro k
      refine le_iSup_of_le J (le_iSup_of_le u (le_iSup_of_le hu ?_))
      have h1 : (∑ j : Fin J, D j k ^ s)
          = ∑ j : Fin J, ‖winOp Ψ (f k) x (u (Fin.castSucc j) : ℝ)
              - winOp Ψ (f k) x (u (Fin.succ j) : ℝ)‖ ^ s := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hDk j k]
      rw [h1]
    -- the algebraic conversion
    have hconv : ENNReal.ofReal ((∑ k : Fin K, (∑ j : Fin J, D j k ^ s) ^ ((2:ℝ)/s)) ^ ((1:ℝ)/2))
        = (∑ k : Fin K, (ENNReal.ofReal ((∑ j : Fin J, D j k ^ s) ^ ((1:ℝ)/s))) ^ (2:ℝ))
            ^ ((1:ℝ)/2) := by
      have hz : ∀ k : Fin K, 0 ≤ ∑ j : Fin J, D j k ^ s := fun k =>
        Finset.sum_nonneg fun j _ => Real.rpow_nonneg (hDnn j k) s
      rw [← ENNReal.ofReal_rpow_of_nonneg (Finset.sum_nonneg fun k _ =>
        Real.rpow_nonneg (hz k) _) (by norm_num : (0:ℝ) ≤ (1:ℝ)/2)]
      congr 1
      rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => Real.rpow_nonneg (hz k) _)]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [show (2:ℝ)/s = ((1:ℝ)/s) * 2 by field_simp, Real.rpow_mul (hz k)]
      rw [ofReal_rpow_two_eq (Real.rpow_nonneg (hz k) _)]
    have hmink' : (∑ j : Fin J, (∑ k : Fin K, D j k ^ (2:ℝ)) ^ (s / 2)) ^ ((1:ℝ)/s)
        ≤ (∑ k : Fin K, (∑ j : Fin J, D j k ^ s) ^ ((2:ℝ)/s)) ^ ((1:ℝ)/2) := by
      have h := hmink
      rwa [show (2:ℝ)/s = 2/s by ring] at h
    calc ENNReal.ofReal ((∑ j : Fin J, ‖winCurveL2 Ψ f x (u (Fin.castSucc j))
            - winCurveL2 Ψ f x (u (Fin.succ j))‖ ^ s) ^ ((1:ℝ)/s))
        = ENNReal.ofReal ((∑ j : Fin J, (∑ k : Fin K, D j k ^ (2:ℝ)) ^ (s/2))
            ^ ((1:ℝ)/s)) := by rw [hsum_eq]
      _ ≤ ENNReal.ofReal ((∑ k : Fin K, (∑ j : Fin J, D j k ^ s) ^ ((2:ℝ)/s))
            ^ ((1:ℝ)/2)) := ENNReal.ofReal_le_ofReal hmink'
      _ = (∑ k : Fin K, (ENNReal.ofReal ((∑ j : Fin J, D j k ^ s) ^ ((1:ℝ)/s))) ^ (2:ℝ))
            ^ ((1:ℝ)/2) := hconv
      _ ≤ V := by
          rw [hV]
          refine ENNReal.rpow_le_rpow ?_ (by norm_num)
          exact Finset.sum_le_sum fun k _ =>
            ENNReal.rpow_le_rpow (hWk k) (by norm_num)
  have hsup : winVarVecL2 Ψ f x s ≤ V :=
    iSup_le fun J => iSup_le fun u => iSup_le fun hu => hstep J u hu
  calc winVarVecL2 Ψ f x s ^ (2:ℝ) ≤ V ^ (2:ℝ) := ENNReal.rpow_le_rpow hsup (by norm_num)
    _ = ∑ k : Fin K, winVar Ψ (f k) x s ^ (2:ℝ) := by
        rw [hV, ← ENNReal.rpow_mul]
        rw [show ((1:ℝ)/2) * 2 = 1 by norm_num, ENNReal.rpow_one]


/-! ### The pointwise entropy-versus-variation bound in the `ℓ²` metric -/

/-- **The pointwise entropy-versus-variation bound** (Bourgain's Lemma 3.30, `ℓ²` form). -/
lemma winML2_mul_rpow_le (Ψ : SchwartzMap ℝ ℂ) (f : Fin K → ℝ → ℂ) (x : ℝ) {s : ℝ} (hs : 1 ≤ s)
    (hΛ : winVarVecL2 Ψ f x s < ⊤) {R : ℝ} (hR0 : 0 ≤ R)
    (hR : ∀ t : {t : ℝ // 0 < t}, ‖winCurveL2 Ψ f x t‖ ≤ R) :
    ∀ l : ℝ, 0 < l → ENNReal.ofReal l * (winML2 Ψ f x l) ^ ((1:ℝ)/s)
      ≤ ENNReal.ofReal ((2:ℝ) ^ ((1:ℝ)/s) * ((winVarVecL2 Ψ f x s).toReal + 2 * R)) := by
  intro l hl
  rcases le_total l (2 * R) with h | h
  · have hfin : Metric.coveringNumber l.toNNReal (Set.range (winCurveRL2 Ψ f x)) ≠ ⊤ := by
      refine Commons.Analysis.Metric.coveringNumber_ne_top_of_isBounded ?_ ?_
      · rw [isBounded_iff_subset_closedBall (0 : EuclideanSpace ℂ (Fin K))]
        refine ⟨R, ?_⟩
        rintro y ⟨u, rfl⟩
        rw [mem_closedBall, dist_zero_right]
        exact hR ⟨Real.exp u, Real.exp_pos u⟩
      · exact Real.toNNReal_pos.mpr hl
    · have hVreal : ∀ (J : ℕ) (u : Fin (J + 1) → ℝ), StrictMono u →
          (∑ j : Fin J, dist (winCurveRL2 Ψ f x (u (Fin.castSucc j)))
              (winCurveRL2 Ψ f x (u (Fin.succ j))) ^ s) ^ ((1:ℝ)/s)
            ≤ (winVarVecL2 Ψ f x s).toReal := by
        intro J u hu
        have h1 := winVarVecL2_tuple_bound Ψ f x (s := s) J u hu
        have h2 := ENNReal.toReal_mono hΛ.ne h1
        rwa [ENNReal.toReal_ofReal (Real.rpow_nonneg
          (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg dist_nonneg _) _)] at h2
      have hkey := Metric.coveringNumber_le_of_variation (winCurveRL2 Ψ f x) s hs
        ((winVarVecL2 Ψ f x s).toReal) hVreal hl hfin
      have hM : winML2 Ψ f x l = (((Metric.coveringNumber l.toNNReal
            (Set.range (winCurveRL2 Ψ f x)) : ℕ∞) : ENNReal) - 1) := by
        rw [winML2, range_winCurveRL2]
      rw [hM]
      refine le_trans hkey ?_
      refine ENNReal.ofReal_le_ofReal ?_
      have h3 : (0:ℝ) < (2:ℝ) ^ ((1:ℝ)/s) := Real.rpow_pos_of_pos (by norm_num) _
      nlinarith [h, h3, (winVarVecL2 Ψ f x s).toReal_nonneg]
  · have hzero : winML2 Ψ f x l = 0 := by
      rw [winML2, tsub_eq_zero_iff_le]
      have hcov : Metric.coveringNumber l.toNNReal (Set.range (winCurveL2 Ψ f x)) ≤ 1 := by
        refine Metric.coveringNumber_le_one_of_ediam_le ?_
        rw [ediam_le_iff]
        rintro p ⟨tp, rfl⟩ q ⟨tq, rfl⟩
        have hp : ‖winCurveL2 Ψ f x tp‖ₑ ≤ ENNReal.ofReal R := by
          rw [enorm_eq_ofReal_norm']; exact ENNReal.ofReal_le_ofReal (hR tp)
        have hq : ‖winCurveL2 Ψ f x tq‖ₑ ≤ ENNReal.ofReal R := by
          rw [enorm_eq_ofReal_norm']; exact ENNReal.ofReal_le_ofReal (hR tq)
        have h2R : (2:ℝ) * R = R + R := two_mul R
        rw [edist_eq_enorm_sub]
        calc ‖winCurveL2 Ψ f x tp - winCurveL2 Ψ f x tq‖ₑ
            = ‖winCurveL2 Ψ f x tp + (- winCurveL2 Ψ f x tq)‖ₑ := by rw [sub_eq_add_neg]
          _ ≤ ‖winCurveL2 Ψ f x tp‖ₑ + ‖- winCurveL2 Ψ f x tq‖ₑ := enorm_add_le _ _
          _ = ‖winCurveL2 Ψ f x tp‖ₑ + ‖winCurveL2 Ψ f x tq‖ₑ := by rw [enorm_neg]
          _ ≤ ENNReal.ofReal (2 * R) := by
              rw [h2R, ENNReal.ofReal_add hR0 hR0]; exact add_le_add hp hq
          _ ≤ ENNReal.ofReal l := by
              rw [ENNReal.ofReal_le_ofReal_iff (by positivity)]
              exact h
          _ = (l.toNNReal : ℝ≥0∞) := by
              rw [ENNReal.ofReal_eq_coe_nnreal hl.le, Real.toNNReal_of_nonneg hl.le]
      exact_mod_cast hcov
    rw [hzero, ENNReal.zero_rpow_of_pos (by positivity : (0:ℝ) < 1/s), mul_zero]
    exact bot_le

theorem bourgain_entropy_integral_l2_l2vec (Ψ : SchwartzMap ℝ ℂ) (M : ℝ)
    (hM : ∀ x : ℝ, ‖(Ψ : ℝ → ℂ) x‖ ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : ℕ) (f : Fin K → ℝ → ℂ),
      (∀ k : Fin K, MemLp (f k) 2 (volume : Measure ℝ)) →
      (∀ k : Fin K, MemLp (f k) ⊤ (volume : Measure ℝ)) →
      ∫⁻ x : ℝ, (∫⁻ r in Set.Ioi (0:ℝ),
          min (((Metric.coveringNumber r.toNNReal (Set.range (winCurveL2 Ψ f x)) : ℝ≥0∞) - 1)
              ^ (1/2:ℝ)) (ENNReal.ofReal (Real.sqrt K))) ^ (2:ℝ)
        ≤ ENNReal.ofReal ((C * (Real.log ((K:ℝ)+2))^2)^2) *
            ∫⁻ x : ℝ, ENNReal.ofReal (∑ k : Fin K, ‖f k x‖^2) := by
  obtain ⟨Cvs, hCvspos, hCvs⟩ := dilation_variation_scalar_l2 Ψ
  obtain ⟨C₁, hC₁pos, hC₁⟩ := maximal_dilation_convolution_enorm_le_hlMax Ψ
  obtain ⟨C₀, hC₀pos, hC₀⟩ := Commons.Analysis.Maximal.real_maximal_strong_type 2 (by norm_num)
  set C : ℝ := Real.sqrt (10 ^ 30 * (Cvs ^ 2 + (C₀ ^ 2 * C₁ ^ 2) ^ 2 + C₁ ^ 2 + 1))
    with hCdef
  have hCpos : 0 < C := by rw [hCdef]; positivity
  have hCsq : C ^ 2 = 10 ^ 30 * (Cvs ^ 2 + (C₀ ^ 2 * C₁ ^ 2) ^ 2 + C₁ ^ 2 + 1) := by
    rw [hCdef, Real.sq_sqrt (by positivity)]
  refine ⟨C, hCpos, ?_⟩
  intro K f hf2 hfinf
  set A : ENNReal := ∫⁻ x : ℝ, ENNReal.ofReal (∑ k : Fin K, ‖f k x‖ ^ 2) with hAdef
  set L : ℝ := max 1 (Real.log ((K:ℝ) + 2)) with hLdef
  set s : ℝ := 2 + 1/L with hsdef
  have hL1 : 1 ≤ L := le_max_left _ _
  have hLpos : 0 < L := lt_of_lt_of_le one_pos hL1
  have hs2 : 2 < s := by
    rw [hsdef]; exact lt_add_of_pos_right _ (one_div_pos.mpr hLpos)
  have hs3 : s ≤ 3 := by
    rw [hsdef, show (2:ℝ) + 1/L ≤ 3 ↔ 1/L ≤ 1 by constructor <;> intro h <;> linarith]
    rw [div_le_one hLpos]; exact hL1
  have hs1 : 1 ≤ s := by linarith
  have hsne : s - 2 = 1/L := by rw [hsdef]; ring
  have hKpow : (K:ℝ) ^ ((1:ℝ)/2 - 1/s) ≤ 2 := by
    rw [hsdef, hLdef]
    exact rpow_half_sub_inv_le_two K
  -- the measurable majorant of the sup of the curve
  set hh : ℝ → ENNReal := fun x => (∑ k : Fin K,
      (ENNReal.ofReal C₁ * Commons.Analysis.Maximal.hlMax (fun y : ℝ => ‖f k y‖ₑ) x) ^ (2:ℝ))
      ^ ((1:ℝ)/2) with hhdef
  have hFle : ∀ x, winFL2 Ψ f x ≤ hh x := by
    intro x
    have h1 : winFL2 Ψ f x ≤ (⨆ (t : {t : ℝ // 0 < t}),
        (∑ k : Fin K, ‖winCurveL2 Ψ f x t k‖ₑ ^ (2:ℝ)) ^ ((1:ℝ)/2)) :=
      iSup_le fun t => (enorm_eq_sqrt_sum_L2 (winCurveL2 Ψ f x t)).le.trans
        (le_iSup (fun t : {t : ℝ // 0 < t} =>
          (∑ k : Fin K, ‖winCurveL2 Ψ f x t k‖ₑ ^ (2:ℝ)) ^ ((1:ℝ)/2)) t)
    refine h1.trans ?_
    rw [hhdef]
    refine iSup_le fun t => ?_
    refine ENNReal.rpow_le_rpow (Finset.sum_le_sum fun k _ => ?_) (by norm_num)
    exact ENNReal.rpow_le_rpow ((le_iSup (fun t : {t : ℝ // 0 < t} =>
      ‖winCurveL2 Ψ f x t k‖ₑ) t).trans (hC₁ (f k) (hf2 k) x)) (by norm_num)
  have hhmeas : Measurable hh := by
    rw [hhdef]
    exact (ENNReal.continuous_rpow_const.measurable).comp
      (Finset.measurable_sum _ fun k _ =>
        (measurable_const.mul (Commons.Analysis.Maximal.measurable_hlMax _)).pow_const 2)
  have hb : ∀ k : Fin K, AEMeasurable
      (fun x => (ENNReal.ofReal C₁ * Commons.Analysis.Maximal.hlMax (fun y : ℝ => ‖f k y‖ₑ) x) ^ (2:ℝ))
      volume := fun k => ((measurable_const.mul
        (Commons.Analysis.Maximal.measurable_hlMax _)).pow_const 2).aemeasurable
  have hAfin : A < ⊤ := by
    rw [hAdef]
    have hcongr : (fun x : ℝ => ENNReal.ofReal (∑ k : Fin K, ‖f k x‖ ^ 2))
        = fun x => ∑ k : Fin K, ENNReal.ofReal (‖f k x‖ ^ 2) := by
      funext x
      exact ENNReal.ofReal_sum_of_nonneg (fun k _ => sq_nonneg _)
    rw [hcongr, lintegral_finsetSum' (Finset.univ)
      (f := fun k : Fin K => fun x : ℝ => ENNReal.ofReal (‖f k x‖ ^ 2))
      (fun k _ => ((hf2 k).aemeasurable.norm.pow_const 2).ennreal_ofReal)]
    refine ENNReal.sum_lt_top.mpr fun k _ => ?_
    have h1 : Integrable (fun x : ℝ => ‖f k x‖ ^ 2) volume := by
      have := (hf2 k).integrable_norm_rpow (p := 2) (by norm_num) (by norm_num)
      simpa using this
    have h2 := h1.lintegral_lt_top
    simpa only [enorm_eq_ofReal_norm'] using h2
  have hhfin : ∫⁻ x, hh x ^ (2:ℝ) ≤ ENNReal.ofReal (C₀ ^ 2 * C₁ ^ 2) * A := by
    have hpow : ∀ x : ℝ, hh x ^ (2:ℝ)
        = ∑ k : Fin K, (ENNReal.ofReal C₁ * Commons.Analysis.Maximal.hlMax (fun y : ℝ => ‖f k y‖ₑ) x) ^ (2:ℝ) := by
      intro x
      rw [hhdef, ← ENNReal.rpow_mul, show ((1:ℝ)/2) * 2 = 1 by norm_num, ENNReal.rpow_one]
    have hstep : ∀ k : Fin K, ∫⁻ x, (ENNReal.ofReal C₁ *
          Commons.Analysis.Maximal.hlMax (fun y : ℝ => ‖f k y‖ₑ) x) ^ (2:ℝ)
        ≤ ENNReal.ofReal (C₀ ^ 2 * C₁ ^ 2) * ∫⁻ x, ENNReal.ofReal (‖f k x‖ ^ 2) := by
      intro k
      have hfac : (fun x : ℝ => (ENNReal.ofReal C₁ *
            Commons.Analysis.Maximal.hlMax (fun y : ℝ => ‖f k y‖ₑ) x) ^ (2:ℝ))
          = fun x => (ENNReal.ofReal C₁) ^ (2:ℝ) *
              (Commons.Analysis.Maximal.hlMax (fun y : ℝ => ‖f k y‖ₑ) x) ^ (2:ℝ) := by
        funext x; rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
      rw [hfac, lintegral_const_mul'' _
        (((Commons.Analysis.Maximal.measurable_hlMax _).pow_const 2).aemeasurable)]
      rw [show (ENNReal.ofReal C₁) ^ (2:ℝ) = ENNReal.ofReal (C₁ ^ 2) by
        rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast,
          ENNReal.ofReal_pow hC₁pos.le]]
      have h32 : ∫⁻ x : ℝ, (Commons.Analysis.Maximal.hlMax (fun y : ℝ => ‖f k y‖ₑ) x) ^ (2:ℝ)
          ≤ ENNReal.ofReal (C₀ ^ 2) * ∫⁻ x : ℝ, ENNReal.ofReal (‖f k x‖ ^ 2) := by
        have h := hC₀ (fun y : ℝ => ‖f k y‖)
        have h1 : (fun y : ℝ => ‖(fun y : ℝ => ‖f k y‖) y‖ₑ) = fun y => ‖f k y‖ₑ := by
          funext y; exact enorm_norm_eq_enorm (f k y)
        rw [h1] at h
        have h2 : (fun x : ℝ => ‖‖f k x‖‖ₑ ^ (2:ℝ)) = fun x => ENNReal.ofReal (‖f k x‖ ^ 2) := by
          funext x
          rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast, enorm_norm_eq_enorm,
            enorm_eq_ofReal_norm', ENNReal.ofReal_pow (norm_nonneg _)]
        rw [h2] at h
        have hC : (C₀ : ℝ) ^ (2:ℝ) = C₀ ^ 2 := by
          rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
        rw [hC] at h
        simpa only [Commons.Analysis.Maximal.hlMax] using h
      calc ENNReal.ofReal (C₁ ^ 2) * ∫⁻ x, (Commons.Analysis.Maximal.hlMax (fun y : ℝ => ‖f k y‖ₑ) x) ^ (2:ℝ)
          ≤ ENNReal.ofReal (C₁ ^ 2) * (ENNReal.ofReal (C₀ ^ 2) * ∫⁻ x, ENNReal.ofReal (‖f k x‖ ^ 2)) :=
            mul_le_mul_of_nonneg_left h32 bot_le
        _ = ENNReal.ofReal (C₀ ^ 2 * C₁ ^ 2) * ∫⁻ x, ENNReal.ofReal (‖f k x‖ ^ 2) := by
            rw [ENNReal.ofReal_mul (sq_nonneg C₀)]
            ring
    calc ∫⁻ x, hh x ^ (2:ℝ)
        = ∑ k : Fin K, ∫⁻ x, (ENNReal.ofReal C₁ *
            Commons.Analysis.Maximal.hlMax (fun y : ℝ => ‖f k y‖ₑ) x) ^ (2:ℝ) := by
          rw [lintegral_congr fun x => hpow x, lintegral_finsetSum' Finset.univ (fun k _ => hb k)]
      _ ≤ ∑ k : Fin K, ENNReal.ofReal (C₀ ^ 2 * C₁ ^ 2) * ∫⁻ x, ENNReal.ofReal (‖f k x‖ ^ 2) :=
          Finset.sum_le_sum fun k _ => hstep k
      _ = ENNReal.ofReal (C₀ ^ 2 * C₁ ^ 2) * A := by
          rw [← Finset.mul_sum, hAdef]
          congr 1
          rw [← lintegral_finsetSum' Finset.univ
            (f := fun k : Fin K => fun x : ℝ => ENNReal.ofReal (‖f k x‖ ^ 2))
            (fun k _ => ((hf2 k).aemeasurable.norm.pow_const 2).ennreal_ofReal)]
          exact lintegral_congr fun x =>
            (ENNReal.ofReal_sum_of_nonneg (fun k _ => sq_nonneg _)).symm
  have hhh2 : ∀ᵐ x ∂(volume : Measure ℝ), hh x ^ (2:ℝ) < ⊤ :=
    ae_lt_top (hhmeas.pow_const 2) (by
      refine ne_of_lt (lt_of_le_of_lt hhfin ?_)
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hAfin)
  have hhh : ∀ᵐ x ∂(volume : Measure ℝ), hh x < ⊤ := by
    filter_upwards [hhh2] with x hx
    by_contra h
    rw [not_lt] at h
    rw [top_le_iff.mp h, ENNReal.top_rpow_of_pos (by norm_num : (0:ℝ) < 2)] at hx
    exact lt_irrefl _ hx
  have hVtop : ∀ᵐ x ∂(volume : Measure ℝ), winVarVecL2 Ψ f x s < ⊤ := by
    have hmeas : ∀ k : Fin K, AEMeasurable (fun x : ℝ => winVar Ψ (f k) x s ^ (2:ℝ)) volume :=
      fun k => (dilation_variation_aemeasurable Ψ s (f k) (hf2 k).aemeasurable (hf2 k)).pow_const 2
    have hsumfin : ∫⁻ x, ∑ k : Fin K, winVar Ψ (f k) x s ^ (2:ℝ) < ⊤ := by
      rw [lintegral_finsetSum' Finset.univ (fun k _ => hmeas k)]
      refine ENNReal.sum_lt_top.mpr fun k _ => ?_
      refine lt_of_le_of_lt (hCvs s hs2 hs3 (f k) (hf2 k) (hfinf k)) ?_
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (by
        have h1 : Integrable (fun x : ℝ => ‖f k x‖ ^ 2) volume := by
          have := (hf2 k).integrable_norm_rpow (p := 2) (by norm_num) (by norm_num)
          simpa using this
        have h2 := h1.lintegral_lt_top
        simpa only [enorm_eq_ofReal_norm'] using h2)
    have hmeas2 : AEMeasurable (fun x : ℝ => ∑ k : Fin K, winVar Ψ (f k) x s ^ (2:ℝ)) volume := by
      have hsa : (∑ k : Fin K, (fun x : ℝ => winVar Ψ (f k) x s ^ (2:ℝ)))
          = fun x : ℝ => ∑ k : Fin K, winVar Ψ (f k) x s ^ (2:ℝ) := by
        funext x; exact Finset.sum_apply x Finset.univ _
      rw [← hsa]
      exact Finset.aemeasurable_sum Finset.univ
        (f := fun k : Fin K => fun x : ℝ => winVar Ψ (f k) x s ^ (2:ℝ)) (fun k _ => hmeas k)
    have htop := ae_lt_top' hmeas2 hsumfin.ne
    filter_upwards [htop] with x hx
    have h3 : winVarVecL2 Ψ f x s ^ (2:ℝ) < ⊤ :=
      lt_of_le_of_lt (winVarVecL2_sq_le_sum Ψ f x hs2) hx
    by_contra h
    rw [not_lt] at h
    rw [top_le_iff.mp h, ENNReal.top_rpow_of_pos (by norm_num : (0:ℝ) < 2)] at h3
    exact lt_irrefl _ h3
  -- the pointwise entropy bound
  set Gc : ℝ → ℝ := fun x => (2:ℝ) ^ ((1:ℝ)/s)
    * ((winVarVecL2 Ψ f x s).toReal + 2 * (hh x).toReal) with hGcdef
  set Lc : ℝ := (1 + 2/(s - 2)) * (K:ℝ) ^ ((1:ℝ)/2 - 1/s) with hLcdef
  have hsL0 : 1 / (s - 2) = L := by rw [hsne, one_div_one_div]
  have hLcpos : 0 ≤ Lc := by
    rw [hLcdef]
    have h2 : (0:ℝ) ≤ 1 + 2/(s-2) := by
      rw [show (2:ℝ)/(s-2) = 2*(1/(s-2)) by ring, hsL0]
      linarith [hL1]
    exact mul_nonneg h2 (Real.rpow_nonneg (by positivity) _)
  have hGcpos : ∀ x, 0 ≤ Gc x := by
    intro x
    rw [hGcdef]
    refine mul_nonneg (Real.rpow_pos_of_pos (by norm_num) _).le ?_
    have h1 := (winVarVecL2 Ψ f x s).toReal_nonneg
    have h2 := (hh x).toReal_nonneg
    linarith
  have hpw : ∀ᵐ x ∂(volume : Measure ℝ),
      (∫⁻ r in Set.Ioi (0:ℝ), min (ENNReal.ofReal (Real.sqrt K)) (winML2 Ψ f x r ^ ((1:ℝ)/2)))
        ≤ ENNReal.ofReal (Lc * Gc x) := by
    filter_upwards [hVtop, hhh] with x hxV hxH
    have hR : ∀ t : {t : ℝ // 0 < t}, ‖winCurveL2 Ψ f x t‖ ≤ (hh x).toReal := by
      intro t
      have h1 : ‖winCurveL2 Ψ f x t‖ₑ ≤ hh x :=
        (le_iSup (fun t : {t : ℝ // 0 < t} => ‖winCurveL2 Ψ f x t‖ₑ) t).trans (hFle x)
      rw [enorm_eq_ofReal_norm'] at h1
      have h2 := ENNReal.toReal_mono hxH.ne h1
      rwa [ENNReal.toReal_ofReal (norm_nonneg _)] at h2
    have this := entropy_integral_le_of_sup_bound (M := fun r => winML2 Ψ f x r) (K := (K:ℝ))
      (r := s) (G := Gc x) (by positivity) hs2 (by positivity : (0:ℝ) ≤ Gc x)
      (winML2_mul_rpow_le Ψ f x hs1 hxV ENNReal.toReal_nonneg hR)
    simpa only [hLcdef] using this
  -- the two integral bounds
  have hVsum : ∀ᵐ x ∂(volume : Measure ℝ),
      ENNReal.ofReal ((winVarVecL2 Ψ f x s).toReal ^ 2)
        ≤ ∑ k : Fin K, winVar Ψ (f k) x s ^ (2:ℝ) := by
    filter_upwards [hVtop] with x hxV
    have h1 : winVarVecL2 Ψ f x s ^ (2:ℝ) ≤ ∑ k : Fin K, winVar Ψ (f k) x s ^ (2:ℝ) :=
      winVarVecL2_sq_le_sum Ψ f x hs2
    have h2 : ENNReal.ofReal ((winVarVecL2 Ψ f x s).toReal ^ 2)
        = (ENNReal.ofReal (winVarVecL2 Ψ f x s).toReal) ^ (2:ℝ) := by
      rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast,
        ENNReal.ofReal_pow ENNReal.toReal_nonneg]
    rw [h2, ENNReal.ofReal_toReal hxV.ne]
    exact h1
  have hVint : ∫⁻ x, ∑ k : Fin K, winVar Ψ (f k) x s ^ (2:ℝ)
      ≤ ENNReal.ofReal ((Cvs / (s - 2)) ^ 2) * A := by
    have hmeas : ∀ k : Fin K, AEMeasurable (fun x : ℝ => winVar Ψ (f k) x s ^ (2:ℝ)) volume :=
      fun k => (dilation_variation_aemeasurable Ψ s (f k) (hf2 k).aemeasurable (hf2 k)).pow_const 2
    have hsplit : ∫⁻ x, ∑ k : Fin K, winVar Ψ (f k) x s ^ (2:ℝ)
        = ∑ k : Fin K, ∫⁻ x, winVar Ψ (f k) x s ^ (2:ℝ) := by
      simpa only [Finset.sum_apply] using lintegral_finsetSum' Finset.univ
        (f := fun k : Fin K => fun x : ℝ => winVar Ψ (f k) x s ^ (2:ℝ)) (fun k _ => hmeas k)
    have hAeq : A = ∑ k : Fin K, ∫⁻ x : ℝ, ENNReal.ofReal (‖f k x‖ ^ 2) := by
      rw [hAdef]
      rw [lintegral_congr fun x => ENNReal.ofReal_sum_of_nonneg (fun k _ => sq_nonneg _)]
      simpa only [Finset.sum_apply] using lintegral_finsetSum' Finset.univ
        (f := fun k : Fin K => fun x : ℝ => ENNReal.ofReal (‖f k x‖ ^ 2))
        (fun k _ => ((hf2 k).aemeasurable.norm.pow_const 2).ennreal_ofReal)
    rw [hsplit, hAeq, Finset.mul_sum]
    exact Finset.sum_le_sum fun k _ => hCvs s hs2 hs3 (f k) (hf2 k) (hfinf k)
  have hRint : ∫⁻ x, ENNReal.ofReal ((hh x).toReal ^ 2) ≤ ENNReal.ofReal (C₀ ^ 2 * C₁ ^ 2) * A := by
    refine le_trans (lintegral_mono fun x => ?_) hhfin
    have h1 : ENNReal.ofReal ((hh x).toReal ^ 2)
        = (ENNReal.ofReal (hh x).toReal) ^ (2:ℝ) := by
      rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast,
        ENNReal.ofReal_pow ENNReal.toReal_nonneg]
    rw [h1]
    exact ENNReal.rpow_le_rpow ENNReal.ofReal_toReal_le (by norm_num)
  -- final assembly
  have hsL : 1 / (s - 2) = L := by rw [hsne, one_div_one_div]
  have hLle : L ≤ 200 * Real.log ((K:ℝ)+2) := by rw [hLdef]; exact max_one_log_le K
  have hRmeas : AEMeasurable (fun x : ℝ => ENNReal.ofReal ((hh x).toReal ^ 2)) volume :=
    (((hhmeas.ennreal_toReal).pow_const 2).ennreal_ofReal).aemeasurable
  have hsumMeas : AEMeasurable (fun x : ℝ => ∑ k : Fin K, winVar Ψ (f k) x s ^ (2:ℝ)) volume := by
    have hsa : (∑ k : Fin K, (fun x : ℝ => winVar Ψ (f k) x s ^ (2:ℝ)))
        = fun x : ℝ => ∑ k : Fin K, winVar Ψ (f k) x s ^ (2:ℝ) := by
      funext x; exact Finset.sum_apply x Finset.univ _
    rw [← hsa]
    exact Finset.aemeasurable_sum Finset.univ
      (f := fun k : Fin K => fun x : ℝ => winVar Ψ (f k) x s ^ (2:ℝ)) (fun k _ =>
        (dilation_variation_aemeasurable Ψ s (f k) (hf2 k).aemeasurable (hf2 k)).pow_const 2)

  have hIntMeas : AEMeasurable (fun x : ℝ => 2 * (∑ k : Fin K, winVar Ψ (f k) x s ^ (2:ℝ))
      + 8 * ENNReal.ofReal ((hh x).toReal ^ 2)) volume :=
    (hsumMeas.const_mul 2).add (hRmeas.const_mul 8)
  have hG2 : ∀ᵐ x ∂(volume : Measure ℝ), ENNReal.ofReal (Gc x ^ 2)
      ≤ ENNReal.ofReal 2 * (2 * (∑ k : Fin K, winVar Ψ (f k) x s ^ (2:ℝ))
          + 8 * ENNReal.ofReal ((hh x).toReal ^ 2)) := by
    filter_upwards [hVsum, hVtop] with x hx hxV
    have hreal : ENNReal.ofReal (Gc x ^ 2)
        ≤ ENNReal.ofReal 2 * (2 * ENNReal.ofReal ((winVarVecL2 Ψ f x s).toReal ^ 2)
            + 8 * ENNReal.ofReal ((hh x).toReal ^ 2)) := by
      rw [hGcdef]
      have hexp2 : ((2:ℝ) ^ ((1:ℝ)/s)) ^ 2 ≤ 2 := by
        have h1 : (2:ℝ) ^ ((1:ℝ)/s) ≤ Real.sqrt 2 := by
          rw [Real.sqrt_eq_rpow]
          refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
          rw [div_le_iff₀ (by linarith : (0:ℝ) < s)]
          linarith
        calc ((2:ℝ) ^ ((1:ℝ)/s)) ^ 2 ≤ (Real.sqrt 2) ^ 2 :=
              pow_le_pow_left₀ (Real.rpow_nonneg (by norm_num) _) h1 2
          _ = 2 := Real.sq_sqrt (by norm_num)
      have hquad : ((winVarVecL2 Ψ f x s).toReal + 2 * (hh x).toReal) ^ 2
          ≤ 2 * ((winVarVecL2 Ψ f x s).toReal) ^ 2 + 8 * ((hh x).toReal) ^ 2 := by
        nlinarith [sq_nonneg ((winVarVecL2 Ψ f x s).toReal - 2 * (hh x).toReal)]
      have hAnn : (0:ℝ) ≤ ((2:ℝ) ^ ((1:ℝ)/s)) ^ 2 := by positivity
      calc ENNReal.ofReal (((2:ℝ) ^ ((1:ℝ)/s) * ((winVarVecL2 Ψ f x s).toReal + 2 * (hh x).toReal)) ^ 2)
          = ENNReal.ofReal (((2:ℝ) ^ ((1:ℝ)/s)) ^ 2
              * ((winVarVecL2 Ψ f x s).toReal + 2 * (hh x).toReal) ^ 2) := by
            rw [mul_pow]
        _ ≤ ENNReal.ofReal (2 * (2 * ((winVarVecL2 Ψ f x s).toReal) ^ 2 + 8 * ((hh x).toReal) ^ 2)) := by
            refine ENNReal.ofReal_le_ofReal ?_
            exact mul_le_mul hexp2 hquad (by positivity) (by norm_num)
        _ = ENNReal.ofReal 2 * (2 * ENNReal.ofReal ((winVarVecL2 Ψ f x s).toReal ^ 2)
              + 8 * ENNReal.ofReal ((hh x).toReal ^ 2)) := by
            rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
              ENNReal.ofReal_add (by positivity) (by positivity),
              ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
              ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 8)]
            norm_num
    refine hreal.trans ?_
    refine mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left ?_ (by norm_num)) le_rfl) bot_le
    exact hx
  rw [show (fun x : ℝ => (∫⁻ r in Set.Ioi (0:ℝ),
        min (((Metric.coveringNumber r.toNNReal (Set.range (winCurveL2 Ψ f x)) : ℝ≥0∞) - 1)
          ^ (1/2:ℝ)) (ENNReal.ofReal (Real.sqrt K))) ^ (2:ℝ))
      = fun x : ℝ => (∫⁻ r in Set.Ioi (0:ℝ),
          min (ENNReal.ofReal (Real.sqrt K)) (winML2 Ψ f x r ^ ((1:ℝ)/2))) ^ (2:ℝ) from by
    funext x
    congr 1
    refine lintegral_congr fun r => ?_
    exact min_comm _ _]
  -- the numerical collapse of the constants
  have hfinal_cmp : ENNReal.ofReal (Lc^2) * ENNReal.ofReal (2:ℝ)
      * (2 * ENNReal.ofReal ((Cvs/(s-2))^2) + 8 * ENNReal.ofReal (C₀^2*C₁^2))
      ≤ ENNReal.ofReal ((C * (Real.log ((K:ℝ)+2))^2)^2) := by
    have hEq : ENNReal.ofReal (Lc^2) * ENNReal.ofReal (2:ℝ)
        * (2 * ENNReal.ofReal ((Cvs/(s-2))^2) + 8 * ENNReal.ofReal (C₀^2*C₁^2))
        = ENNReal.ofReal (Lc^2 * 2 * (2*(Cvs/(s-2))^2 + 8*(C₀^2*C₁^2))) := by
      rw [show (2:ℝ≥0∞) = ENNReal.ofReal (2:ℝ) by simp]
      rw [show (8:ℝ≥0∞) = ENNReal.ofReal (8:ℝ) by simp]
      rw [← ENNReal.ofReal_mul (sq_nonneg Lc),
          ← ENNReal.ofReal_mul (show (0:ℝ) ≤ 2 by norm_num),
          ← ENNReal.ofReal_mul (show (0:ℝ) ≤ 8 by norm_num),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
    have hReal : Lc^2 * 2 * (2*(Cvs/(s-2))^2 + 8*(C₀^2*C₁^2))
        ≤ (C * (Real.log ((K:ℝ)+2))^2)^2 := by
      have hb := final_const_bound K (s := s) (L := L) (A := Cvs) (B := C₀^2*C₁^2)
        hL1 hsne hLle hKpow (le_of_lt hCvspos) (by positivity)
      have hLc2 : Lc^2 = ((1 + 2/(s-2)) * (K:ℝ)^((1:ℝ)/2-1/s))^2 := by rw [hLcdef]
      have hCsq' : (C * (Real.log ((K:ℝ)+2))^2)^2
          = 10^30 * (Cvs^2 + (C₀^2*C₁^2)^2 + C₁^2 + 1)
              * (Real.log ((K:ℝ)+2))^4 := by
        rw [mul_pow, hCsq]
        ring
      rw [hLc2, hCsq']
      refine hb.trans ?_
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith [sq_nonneg C₁]
    exact hEq.le.trans (ENNReal.ofReal_le_ofReal hReal)
  -- the chain of integral estimates
  have h1 : ∫⁻ x, (∫⁻ r in Set.Ioi (0:ℝ), min (ENNReal.ofReal (Real.sqrt K))
        (winML2 Ψ f x r ^ ((1:ℝ)/2))) ^ (2:ℝ)
      ≤ ∫⁻ x, (ENNReal.ofReal (Lc * Gc x)) ^ (2:ℝ) := by
    refine lintegral_mono_ae ?_
    filter_upwards [hpw] with x hx
    exact ENNReal.rpow_le_rpow hx (by norm_num)
  have h2 : ∫⁻ x, (ENNReal.ofReal (Lc * Gc x)) ^ (2:ℝ)
      = ENNReal.ofReal (Lc^2) * ∫⁻ x, ENNReal.ofReal ((Gc x)^2) := by
    have hp : ∀ x : ℝ, (ENNReal.ofReal (Lc * Gc x)) ^ (2:ℝ)
        = ENNReal.ofReal (Lc^2) * ENNReal.ofReal ((Gc x)^2) := by
      intro x
      calc (ENNReal.ofReal (Lc * Gc x)) ^ (2:ℝ)
          = ENNReal.ofReal ((Lc * Gc x) ^ (2:ℝ)) :=
            ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hLcpos (hGcpos x))
              (by norm_num : (0:ℝ) ≤ 2)
        _ = ENNReal.ofReal ((Lc * Gc x) ^ 2) := by rw [Real.rpow_two]
        _ = ENNReal.ofReal (Lc^2 * (Gc x)^2) := by rw [mul_pow]
        _ = ENNReal.ofReal (Lc^2) * ENNReal.ofReal ((Gc x)^2) :=
            ENNReal.ofReal_mul (sq_nonneg Lc)
    rw [lintegral_congr hp, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have h3 : ∫⁻ x, ENNReal.ofReal ((Gc x)^2)
      ≤ ENNReal.ofReal (2:ℝ) * (2 * (∫⁻ x, ∑ k : Fin K, winVar Ψ (f k) x s ^ (2:ℝ))
          + 8 * (∫⁻ x, ENNReal.ofReal ((hh x).toReal ^ 2))) := by
    calc ∫⁻ x, ENNReal.ofReal ((Gc x)^2)
        ≤ ∫⁻ x, ENNReal.ofReal (2:ℝ) * (2 * (∑ k : Fin K, winVar Ψ (f k) x s ^ (2:ℝ))
            + 8 * ENNReal.ofReal ((hh x).toReal ^ 2)) := by
          refine lintegral_mono_ae ?_
          filter_upwards [hG2] with x hx
          exact hx
      _ = ENNReal.ofReal (2:ℝ) * ∫⁻ x, (2 * (∑ k : Fin K, winVar Ψ (f k) x s ^ (2:ℝ))
            + 8 * ENNReal.ofReal ((hh x).toReal ^ 2)) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal (2:ℝ) * (2 * (∫⁻ x, ∑ k : Fin K, winVar Ψ (f k) x s ^ (2:ℝ))
            + 8 * (∫⁻ x, ENNReal.ofReal ((hh x).toReal ^ 2))) := by
          congr 1
          rw [lintegral_add_left' (hsumMeas.const_mul 2),
            lintegral_const_mul' (2:ℝ≥0∞) _ (by norm_num : (2:ℝ≥0∞) ≠ ⊤),
            lintegral_const_mul' (8:ℝ≥0∞) _ (by norm_num : (8:ℝ≥0∞) ≠ ⊤)]
  have h4 : ENNReal.ofReal (2:ℝ) * (2 * (∫⁻ x, ∑ k : Fin K, winVar Ψ (f k) x s ^ (2:ℝ))
          + 8 * (∫⁻ x, ENNReal.ofReal ((hh x).toReal ^ 2)))
      ≤ ENNReal.ofReal (2:ℝ) * (2 * (ENNReal.ofReal ((Cvs / (s-2))^2) * A)
          + 8 * (ENNReal.ofReal (C₀^2 * C₁^2) * A)) := by
    refine mul_le_mul_of_nonneg_left ?_ bot_le
    refine add_le_add (mul_le_mul_of_nonneg_left hVint (by norm_num))
      (mul_le_mul_of_nonneg_left hRint (by norm_num))
  have h5 : ENNReal.ofReal (Lc^2) * (ENNReal.ofReal (2:ℝ)
        * (2 * (ENNReal.ofReal ((Cvs / (s-2))^2) * A)
          + 8 * (ENNReal.ofReal (C₀^2 * C₁^2) * A)))
      ≤ ENNReal.ofReal ((C * (Real.log ((K:ℝ)+2))^2)^2) * A := by
    rw [show ENNReal.ofReal (Lc^2) * (ENNReal.ofReal (2:ℝ)
          * (2 * (ENNReal.ofReal ((Cvs / (s-2))^2) * A)
            + 8 * (ENNReal.ofReal (C₀^2 * C₁^2) * A)))
        = (ENNReal.ofReal (Lc^2) * ENNReal.ofReal (2:ℝ)
            * (2 * ENNReal.ofReal ((Cvs/(s-2))^2) + 8 * ENNReal.ofReal (C₀^2*C₁^2))) * A
        from by ring]
    exact mul_le_mul_of_nonneg_right hfinal_cmp bot_le
  refine h1.trans ?_
  rw [h2]
  exact (mul_le_mul_of_nonneg_left (h3.trans h4) bot_le).trans h5

end Commons.Analysis.Fourier


/-!
# The band-operator framework for the smooth-window maximal estimate

Definitions and elementary estimates for the fixed-window maximal estimate of Bourgain's
Lemma 4.13: the dyadic band operator `bandOpD`, its energy `bandSq`, its maximal function
`bandMax`, and the translation operators.
-/

namespace Commons.Analysis.Fourier

open _root_.MeasureTheory Finset Function Filter
open scoped _root_.ENNReal _root_.Topology BigOperators FourierTransform

noncomputable section

variable {K : ℕ}

/-! ### Dilated Schwartz windows -/

/-- The affine map `u ↦ (x - u)/t`. -/
noncomputable def dilFun (x t : ℝ) : ℝ → ℝ := fun u => (x - u)/t

lemma dilFun_temp (x t : ℝ) : (dilFun x t).HasTemperateGrowth := by
  unfold dilFun
  exact ((HasTemperateGrowth.const x).sub HasTemperateGrowth.id').mul
    (HasTemperateGrowth.const _)

lemma dilFun_anti (x t : ℝ) (ht : t ≠ 0) :
    AntilipschitzWith (Real.toNNReal |t|) (dilFun x t) := by
  refine AntilipschitzWith.of_le_mul_dist fun u v => ?_
  have htv : (↑(Real.toNNReal |t|) : ℝ) = |t| := Real.coe_toNNReal _ (abs_nonneg t)
  have hd : dilFun x t u - dilFun x t v = -((u - v)/t) := by unfold dilFun; ring
  have hmain : |t| * |dilFun x t u - dilFun x t v| = |u - v| := by
    rw [hd, abs_neg, abs_div, div_eq_mul_inv]
    calc |t| * (|u - v| * |t|⁻¹) = |u - v| * (|t| * |t|⁻¹) := by ring
      _ = |u - v| * 1 := by rw [mul_inv_cancel₀ (abs_ne_zero.mpr ht)]
      _ = |u - v| := mul_one _
  rw [Real.dist_eq, Real.dist_eq, htv, hmain]

/-- The dilated window `u ↦ Ψ((x-u)/t)` as a Schwartz map. -/
noncomputable def winDil (Ψ : SchwartzMap ℝ ℂ) (x t : ℝ) (ht : t ≠ 0) : SchwartzMap ℝ ℂ :=
  SchwartzMap.compCLMOfAntilipschitz (𝕜 := ℝ) (F := ℂ) (dilFun_temp x t) (dilFun_anti x t ht) Ψ

lemma winDil_apply (Ψ : SchwartzMap ℝ ℂ) (x t : ℝ) (ht : t ≠ 0) (u : ℝ) :
    winDil Ψ x t ht u = Ψ ((x - u)/t) := rfl

lemma memLp_winDil (Ψ : SchwartzMap ℝ ℂ) (x t : ℝ) (ht : t ≠ 0) :
    MemLp (fun u : ℝ => Ψ ((x - u)/t)) 2 (volume : Measure ℝ) := by
  change MemLp (⇑(winDil Ψ x t ht)) 2 (volume : Measure ℝ)
  exact (winDil Ψ x t ht).memLp 2 (volume : Measure ℝ)

/-! ### The dyadic scale, the window `winK`, and the curve -/

/-- The scale `t_j = 2^{j+1} = 1/h_j`. -/
noncomputable def scaleTj (j : ℕ) : ℝ := (2:ℝ)^(j+1)

lemma scaleTj_pos (j : ℕ) : 0 < scaleTj j := by
  unfold scaleTj
  positivity

lemma scaleTj_eq_inv (j : ℕ) : ((2:ℝ)^(-(j:ℝ)-1)) = (scaleTj j)⁻¹ := by
  unfold scaleTj
  rw [show (-(j:ℝ)-1) = -((j:ℝ)+1) by ring, Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),
    ← Real.rpow_natCast]
  congr 1
  push_cast
  ring

/-- The dyadic-scale window `h_j Ψ(h_j ·)`, `h_j = 2^{-(j+1)}`. -/
noncomputable def winK (Ψ : SchwartzMap ℝ ℂ) (j : ℕ) : ℝ → ℂ :=
  fun u => (((2:ℝ)^(-(j:ℝ)-1) : ℝ) : ℂ) * (Ψ ((2:ℝ)^(-(j:ℝ)-1) * u))

lemma winK_eq_smul (Ψ : SchwartzMap ℝ ℂ) (j : ℕ) (u : ℝ) :
    winK Ψ j u = (((scaleTj j : ℝ)⁻¹ : ℝ) : ℂ) * (Ψ (u / scaleTj j)) := by
  unfold winK
  rw [scaleTj_eq_inv]
  congr 1
  rw [div_eq_mul_inv]
  ring

lemma memLp_winK (Ψ : SchwartzMap ℝ ℂ) (j : ℕ) (z : ℝ) :
    MemLp (fun u : ℝ => winK Ψ j (z - u)) 2 (volume : Measure ℝ) := by
  have h := memLp_winDil Ψ z (scaleTj j) (scaleTj_pos j).ne'
  have h2 : MemLp (fun u : ℝ => (((scaleTj j : ℝ)⁻¹ : ℝ) : ℂ) * Ψ ((z - u) / scaleTj j)) 2
      (volume : Measure ℝ) := h.const_mul _
  refine MemLp.ae_eq ?_ h2
  exact Filter.Eventually.of_forall fun u => (winK_eq_smul Ψ j (z - u)).symm

lemma integrable_mul_winK (Ψ : SchwartzMap ℝ ℂ) (j : ℕ) {g : ℝ → ℂ}
    (hg : MemLp g 2 (volume : Measure ℝ)) (x : ℝ) :
    Integrable (fun u : ℝ => g u * winK Ψ j (x - u)) (volume : Measure ℝ) :=
  hg.integrable_mul (memLp_winK Ψ j x)

/-- The windowed convolution (curve point) of `H k` at scale `j`, evaluated at `z`. -/
noncomputable def curvePt (Ψ : SchwartzMap ℝ ℂ) (H : Fin K → ℝ → ℂ) (j : ℕ) (z : ℝ)
    (k : Fin K) : ℂ :=
  ∫ u : ℝ, H k u * winK Ψ j (z - u)

/-- The curve point with its phase `e^{-I λ_k z}`. -/
noncomputable def curvePtPh (Ψ : SchwartzMap ℝ ℂ) (lam : Fin K → ℝ) (H : Fin K → ℝ → ℂ)
    (j : ℕ) (z : ℝ) (k : Fin K) : ℂ :=
  Complex.exp (-(Complex.I * (lam k : ℂ) * (z : ℂ))) * curvePt Ψ H j z k

/-- The dyadic band operator: `Σ_k e^{-I λ_k x} (H_k * winK_j)(x)`. -/
noncomputable def bandOpD (Ψ : SchwartzMap ℝ ℂ) (lam : Fin K → ℝ) (H : Fin K → ℝ → ℂ)
    (j : ℕ) (x : ℝ) : ℂ :=
  ∑ k : Fin K, curvePtPh Ψ lam H j x k

/-- The `ℓ²` energy of the tuple `H`. -/
noncomputable def bandSq (H : Fin K → ℝ → ℂ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (∑ k : Fin K, ‖H k x‖ ^ 2)

/-- The maximal function of the band operator over the dyadic scales. -/
noncomputable def bandMax (Ψ : SchwartzMap ℝ ℂ) (lam : Fin K → ℝ) (H : Fin K → ℝ → ℂ) : ℝ≥0∞ :=
  ∫⁻ x, (⨆ j : ℕ, ‖bandOpD Ψ lam H j x‖ₑ) ^ (2:ℝ)

/-- The translate `T_y H`. -/
noncomputable def transH (H : Fin K → ℝ → ℂ) (y : ℝ) : Fin K → ℝ → ℂ :=
  fun k x => H k (x + y)

/-- The difference `H - T_y H`. -/
noncomputable def shiftH (H : Fin K → ℝ → ℂ) (y : ℝ) : Fin K → ℝ → ℂ :=
  fun k x => H k x - H k (x + y)

/-! ### Elementary algebra of the band operator -/

lemma curvePt_add (Ψ : SchwartzMap ℝ ℂ) (H G : Fin K → ℝ → ℂ) (j : ℕ) (z : ℝ) (k : Fin K)
    (hH : MemLp (H k) 2 (volume : Measure ℝ)) (hG : MemLp (G k) 2 (volume : Measure ℝ)) :
    curvePt Ψ (fun k' x => H k' x + G k' x) j z k = curvePt Ψ H j z k + curvePt Ψ G j z k := by
  unfold curvePt
  rw [← integral_add (integrable_mul_winK Ψ j hH z) (integrable_mul_winK Ψ j hG z)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  ring

lemma curvePt_sub (Ψ : SchwartzMap ℝ ℂ) (H G : Fin K → ℝ → ℂ) (j : ℕ) (z : ℝ) (k : Fin K)
    (hH : MemLp (H k) 2 (volume : Measure ℝ)) (hG : MemLp (G k) 2 (volume : Measure ℝ)) :
    curvePt Ψ (fun k' x => H k' x - G k' x) j z k = curvePt Ψ H j z k - curvePt Ψ G j z k := by
  unfold curvePt
  rw [← integral_sub (integrable_mul_winK Ψ j hH z) (integrable_mul_winK Ψ j hG z)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  ring

lemma bandOp_add (Ψ : SchwartzMap ℝ ℂ) (lam : Fin K → ℝ) (H G : Fin K → ℝ → ℂ) (j : ℕ)
    (x : ℝ) (hH : ∀ k, MemLp (H k) 2 (volume : Measure ℝ))
    (hG : ∀ k, MemLp (G k) 2 (volume : Measure ℝ)) :
    bandOpD Ψ lam (fun k z => H k z + G k z) j x
      = bandOpD Ψ lam H j x + bandOpD Ψ lam G j x := by
  unfold bandOpD curvePtPh
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [curvePt_add Ψ H G j x k (hH k) (hG k)]
  ring

lemma bandOp_sub (Ψ : SchwartzMap ℝ ℂ) (lam : Fin K → ℝ) (H G : Fin K → ℝ → ℂ) (j : ℕ)
    (x : ℝ) (hH : ∀ k, MemLp (H k) 2 (volume : Measure ℝ))
    (hG : ∀ k, MemLp (G k) 2 (volume : Measure ℝ)) :
    bandOpD Ψ lam (fun k z => H k z - G k z) j x
      = bandOpD Ψ lam H j x - bandOpD Ψ lam G j x := by
  unfold bandOpD curvePtPh
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [curvePt_sub Ψ H G j x k (hH k) (hG k)]
  ring

/-! ### Measurability -/

lemma aemeasurable_curvePt (Ψ : SchwartzMap ℝ ℂ) {H : ℝ → ℂ} (hH : MemLp H 2 (volume : Measure ℝ))
    (j : ℕ) : AEMeasurable (fun z : ℝ => ∫ u : ℝ, H u * winK Ψ j (z - u)) volume := by
  have hk : Measurable (winK Ψ j) := by unfold winK; fun_prop
  exact (SepWin.aestronglyMeasurable_conv hH hk).aemeasurable

lemma aemeasurable_curvePtPh (Ψ : SchwartzMap ℝ ℂ) (lam : Fin K → ℝ) (H : Fin K → ℝ → ℂ)
    {j : ℕ} {k : Fin K} (hH : MemLp (H k) 2 (volume : Measure ℝ)) :
    AEMeasurable (fun z : ℝ => curvePtPh Ψ lam H j z k) volume := by
  have h1 : Continuous fun z : ℝ => Complex.exp (-(Complex.I * (lam k : ℂ) * (z : ℂ))) := by
    fun_prop
  exact (h1.measurable.aemeasurable.mul (aemeasurable_curvePt Ψ hH j))

lemma aemeasurable_bandOp (Ψ : SchwartzMap ℝ ℂ) (lam : Fin K → ℝ) (H : Fin K → ℝ → ℂ)
    (hH : ∀ k, MemLp (H k) 2 (volume : Measure ℝ)) (j : ℕ) :
    AEMeasurable (fun x : ℝ => bandOpD Ψ lam H j x) volume := by
  have hsum : (fun x : ℝ => bandOpD Ψ lam H j x)
      = ∑ k : Fin K, fun x : ℝ => curvePtPh Ψ lam H j x k := by
    funext x
    simp only [bandOpD, Finset.sum_apply]
  rw [hsum]
  exact Finset.aemeasurable_sum Finset.univ (fun k _ => aemeasurable_curvePtPh Ψ lam H (hH k))

lemma aemeasurable_iSup_bandOp (Ψ : SchwartzMap ℝ ℂ) (lam : Fin K → ℝ) (H : Fin K → ℝ → ℂ)
    (hH : ∀ k, MemLp (H k) 2 (volume : Measure ℝ)) :
    AEMeasurable (fun x : ℝ => (⨆ j : ℕ, ‖bandOpD Ψ lam H j x‖ₑ) ^ (2:ℝ)) volume := by
  refine AEMeasurable.pow_const ?_ 2
  refine AEMeasurable.iSup (fun j => ?_)
  exact ((aemeasurable_bandOp Ψ lam H hH j).enorm)

/-! ### The triangle inequality for the maximal function -/

lemma bandMax_add_le (Ψ : SchwartzMap ℝ ℂ) (lam : Fin K → ℝ) (H G : Fin K → ℝ → ℂ)
    (hH : ∀ k, MemLp (H k) 2 (volume : Measure ℝ))
    (hG : ∀ k, MemLp (G k) 2 (volume : Measure ℝ)) :
    bandMax Ψ lam (fun k z => H k z + G k z)
      ≤ 2 * bandMax Ψ lam H + 2 * bandMax Ψ lam G := by
  have hpt : ∀ x : ℝ, (⨆ j : ℕ, ‖bandOpD Ψ lam (fun k z => H k z + G k z) j x‖ₑ) ^ (2:ℝ)
      ≤ 2 * ((⨆ j : ℕ, ‖bandOpD Ψ lam H j x‖ₑ) ^ (2:ℝ))
        + 2 * ((⨆ j : ℕ, ‖bandOpD Ψ lam G j x‖ₑ) ^ (2:ℝ)) := by
    intro x
    have h1 : (⨆ j : ℕ, ‖bandOpD Ψ lam (fun k z => H k z + G k z) j x‖ₑ)
        ≤ (⨆ j : ℕ, ‖bandOpD Ψ lam H j x‖ₑ) + (⨆ j : ℕ, ‖bandOpD Ψ lam G j x‖ₑ) := by
      refine iSup_le fun j => ?_
      rw [bandOp_add Ψ lam H G j x hH hG]
      exact (enorm_add_le _ _).trans (add_le_add
        (le_iSup (fun j => ‖bandOpD Ψ lam H j x‖ₑ) j)
        (le_iSup (fun j => ‖bandOpD Ψ lam G j x‖ₑ) j))
    calc (⨆ j : ℕ, ‖bandOpD Ψ lam (fun k z => H k z + G k z) j x‖ₑ) ^ (2:ℝ)
        ≤ ((⨆ j : ℕ, ‖bandOpD Ψ lam H j x‖ₑ) + (⨆ j : ℕ, ‖bandOpD Ψ lam G j x‖ₑ)) ^ (2:ℝ) :=
          ENNReal.rpow_le_rpow h1 (by norm_num)
      _ ≤ 2 * ((⨆ j : ℕ, ‖bandOpD Ψ lam H j x‖ₑ) ^ (2:ℝ))
          + 2 * ((⨆ j : ℕ, ‖bandOpD Ψ lam G j x‖ₑ) ^ (2:ℝ)) :=
          Commons.Analysis.ENNReal.add_rpow_two_le_two_mul _ _
  calc bandMax Ψ lam (fun k z => H k z + G k z)
      ≤ ∫⁻ x, (2 * ((⨆ j : ℕ, ‖bandOpD Ψ lam H j x‖ₑ) ^ (2:ℝ))
          + 2 * ((⨆ j : ℕ, ‖bandOpD Ψ lam G j x‖ₑ) ^ (2:ℝ))) := lintegral_mono hpt
    _ = 2 * bandMax Ψ lam H + 2 * bandMax Ψ lam G := by
        rw [lintegral_add_left' ((aemeasurable_iSup_bandOp Ψ lam H hH).const_mul 2),
            lintegral_const_mul'' 2 (aemeasurable_iSup_bandOp Ψ lam H hH),
            lintegral_const_mul'' 2 (aemeasurable_iSup_bandOp Ψ lam G hG)]
        rfl

/-! ### The `u`-averaging identities -/

lemma curvePt_translate (Ψ : SchwartzMap ℝ ℂ) (H : Fin K → ℝ → ℂ) (j : ℕ) (z y : ℝ)
    (k : Fin K) (hH : MemLp (H k) 2 (volume : Measure ℝ)) :
    curvePt Ψ (transH H y) j z k = curvePt Ψ H j (z + y) k := by
  have hF : (fun u : ℝ => H k (u + y) * winK Ψ j (z - u))
      = fun u : ℝ => (fun t : ℝ => H k t * winK Ψ j (z + y - t)) (u + y) := by
    funext u
    simp only []
    congr 2
    ring
  unfold curvePt
  simp only [transH]
  rw [hF]
  have key : (∫ u : ℝ, (fun t : ℝ => H k t * winK Ψ j (z + y - t)) (u + y))
      = ∫ u : ℝ, (fun t : ℝ => H k t * winK Ψ j (z + y - t)) u :=
    integral_add_right_eq_self (μ := volume) (f := fun t : ℝ => H k t * winK Ψ j (z + y - t)) y
  rw [key]

lemma bandOpD_translate (Ψ : SchwartzMap ℝ ℂ) (lam : Fin K → ℝ) (H : Fin K → ℝ → ℂ)
    (j : ℕ) (x y : ℝ) (hH : ∀ k, MemLp (H k) 2 (volume : Measure ℝ)) :
    bandOpD Ψ lam (transH H y) j x
      = ∑ k : Fin K, Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))
          * curvePtPh Ψ lam H j (x + y) k := by
  unfold bandOpD
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold curvePtPh
  rw [curvePt_translate Ψ H j x y k (hH k)]
  rw [show -(Complex.I * (lam k : ℂ) * (x : ℂ))
        = Complex.I * (lam k : ℂ) * (y : ℂ)
          + (-(Complex.I * (lam k : ℂ) * ((x + y : ℝ) : ℂ))) by push_cast; ring,
    Complex.exp_add]
  ring

/-- **The `u`-averaging identity** (Krause's reduction): the maximal function of the translate
`T_y H` is the maximal exponential sum with the curve-point coefficients. -/
lemma bandMax_translate (Ψ : SchwartzMap ℝ ℂ) (lam : Fin K → ℝ) (H : Fin K → ℝ → ℂ)
    (hH : ∀ k, MemLp (H k) 2 (volume : Measure ℝ)) (y : ℝ) :
    bandMax Ψ lam (transH H y)
      = ∫⁻ z : ℝ, (⨆ j : ℕ, ‖∑ k : Fin K, Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))
          * curvePtPh Ψ lam H j z k‖ₑ) ^ (2:ℝ) := by
  have hpt : ∀ x : ℝ, (⨆ j : ℕ, ‖bandOpD Ψ lam (transH H y) j x‖ₑ)
      = (⨆ j : ℕ, ‖∑ k : Fin K, Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))
          * curvePtPh Ψ lam H j (x + y) k‖ₑ) := by
    intro x
    refine iSup_congr fun j => ?_
    rw [bandOpD_translate Ψ lam H j x y hH]
  unfold bandMax
  rw [lintegral_congr fun x => congrArg (fun t : ℝ≥0∞ => t ^ (2:ℝ)) (hpt x)]
  exact lintegral_add_right_eq_self (fun z : ℝ => (⨆ j : ℕ, ‖∑ k : Fin K,
      Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ)) * curvePtPh Ψ lam H j z k‖ₑ) ^ (2:ℝ)) y

/-! ### The band-limited contraction -/

/-- **The band-limited contraction.**  If every `H k` is band-limited to `[-a,a]`, then the
`ℓ²` energy of `H - T_y H` is at most `(2πa|y|)²` times that of `H`. -/
lemma bandSq_translate_sub_le (H : Fin K → ℝ → ℂ) {a y : ℝ} (ha : 0 ≤ a)
    (hH1 : ∀ k, Integrable (H k)) (hH2 : ∀ k, MemLp (H k) 2 (volume : Measure ℝ))
    (hsup : ∀ k (ξ : ℝ), a < |ξ| → 𝓕 (H k) ξ = 0) :
    bandSq (shiftH H y) ≤ ENNReal.ofReal ((2 * Real.pi * a * |y|) ^ 2) * bandSq H := by
  have hmeas : ∀ k : Fin K, AEMeasurable (fun x : ℝ => ‖shiftH H y k x‖ₑ ^ (2:ℝ)) volume := by
    intro k
    have h2 : AEMeasurable (fun x : ℝ => H k (x + y)) volume :=
      ((hH2 k).comp_measurePreserving (measurePreserving_add_right volume y)).aemeasurable
    have h3 : AEMeasurable (fun x : ℝ => shiftH H y k x) volume := (hH2 k).aemeasurable.sub h2
    exact h3.enorm.pow_const 2
  have hpt : ∀ x : ℝ, ENNReal.ofReal (∑ k : Fin K, ‖shiftH H y k x‖ ^ 2)
      = ∑ k : Fin K, ‖shiftH H y k x‖ₑ ^ (2:ℝ) := by
    intro x
    rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => sq_nonneg _)]
    exact Finset.sum_congr rfl fun k _ => by
      rw [enorm_eq_ofReal_norm',
        show ENNReal.ofReal ‖shiftH H y k x‖ ^ (2:ℝ) = ENNReal.ofReal (‖shiftH H y k x‖ ^ 2) by
          rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast,
            ← ENNReal.ofReal_pow (norm_nonneg _) 2]]
  have hterm : ∀ k : Fin K, ∫⁻ x, ‖shiftH H y k x‖ₑ ^ (2:ℝ)
      ≤ ENNReal.ofReal ((2 * Real.pi * a * |y|) ^ 2) * ∫⁻ x, ‖H k x‖ₑ ^ (2:ℝ) := by
    intro k
    have hcon := lintegral_translate_sub_sq_le_of_fourier_support (G := H k) (a := a) (y := y)
      (hH1 k) (hH2 k) ha (hsup k)
    rw [show (fun x : ℝ => ‖shiftH H y k x‖ₑ ^ (2:ℝ))
        = fun x : ℝ => ‖H k (x + y) - H k x‖ₑ ^ (2:ℝ) from by
      funext x
      simp only [shiftH, Pi.sub_apply]
      rw [show ‖H k x - H k (x + y)‖ₑ = ‖H k (x + y) - H k x‖ₑ from by
        rw [← edist_eq_enorm_sub, edist_comm, edist_eq_enorm_sub]]]
    exact hcon
  have hSqH : bandSq H = ∑ k : Fin K, ∫⁻ x, ‖H k x‖ₑ ^ (2:ℝ) := by
    unfold bandSq
    rw [lintegral_congr (fun x => ?_), lintegral_finsetSum' Finset.univ
      (fun k _ => ((hH2 k).aemeasurable.enorm.pow_const (2:ℝ)))]
    rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => sq_nonneg _)]
    exact Finset.sum_congr rfl fun k _ => by
      rw [enorm_eq_ofReal_norm', show ENNReal.ofReal ‖H k x‖ ^ (2:ℝ)
        = ENNReal.ofReal (‖H k x‖ ^ 2) by
          rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast,
            ← ENNReal.ofReal_pow (norm_nonneg _) 2]]
  calc bandSq (shiftH H y)
      = ∑ k : Fin K, ∫⁻ x, ‖shiftH H y k x‖ₑ ^ (2:ℝ) := by
        unfold bandSq
        rw [lintegral_congr hpt, lintegral_finsetSum' Finset.univ (fun k _ => hmeas k)]
    _ ≤ ∑ k : Fin K, ENNReal.ofReal ((2 * Real.pi * a * |y|) ^ 2) * ∫⁻ x, ‖H k x‖ₑ ^ (2:ℝ) :=
        Finset.sum_le_sum fun k _ => hterm k
    _ = ENNReal.ofReal ((2 * Real.pi * a * |y|) ^ 2) * bandSq H := by
        rw [hSqH, Finset.mul_sum]

/-! ### The a priori bound -/

/-- The band sum in the form of the published dilation bound. -/
noncomputable def bandSumC (Ψ : SchwartzMap ℝ ℂ) (lam : Fin K → ℝ) (H : Fin K → ℝ → ℂ)
    (t : {t : ℝ // 0 < t}) (x : ℝ) : ℂ :=
  ∑ k : Fin K, Complex.exp (-(Complex.I * (lam k : ℂ) * (x : ℂ))) *
    (∫ y : ℝ, H k y * (((t : ℝ))⁻¹ • (Ψ : ℝ → ℂ) ((x - y) / ((t : ℝ)))))

lemma bandOpD_eq_bandSumC (Ψ : SchwartzMap ℝ ℂ) (lam : Fin K → ℝ) (H : Fin K → ℝ → ℂ)
    (j : ℕ) (x : ℝ) :
    bandOpD Ψ lam H j x = bandSumC Ψ lam H ⟨scaleTj j, scaleTj_pos j⟩ x := by
  unfold bandOpD bandSumC curvePtPh curvePt
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only []
  rw [winK_eq_smul]
  simp only [Complex.real_smul]

/-- The maximal function is dominated by the continuous-scale supremum. -/
lemma bandMax_le_continuum (Ψ : SchwartzMap ℝ ℂ) (lam : Fin K → ℝ) (H : Fin K → ℝ → ℂ) :
    bandMax Ψ lam H ≤ ∫⁻ x, (⨆ (t : {t : ℝ // 0 < t}), ‖bandSumC Ψ lam H t x‖ₑ) ^ (2:ℝ) := by
  refine lintegral_mono fun x => ENNReal.rpow_le_rpow ?_ (by norm_num)
  refine iSup_le fun j => ?_
  rw [bandOpD_eq_bandSumC Ψ lam H j x]
  exact le_iSup (fun t : {t : ℝ // 0 < t} => ‖bandSumC Ψ lam H t x‖ₑ) ⟨scaleTj j, scaleTj_pos j⟩

/-- **The a priori bound.**  From the published band-sum dilation bound, the maximal function of
the band operator is bounded by a constant times the `ℓ²` energy. -/
lemma bandMax_apriori (Ψ : SchwartzMap ℝ ℂ) (lam : Fin K → ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (H : Fin K → ℝ → ℂ), (∀ k, MemLp (H k) 2 (volume : Measure ℝ)) →
      bandMax Ψ lam H ≤ ENNReal.ofReal (C * (K:ℝ)) * bandSq H := by
  obtain ⟨C, hCpos, hC⟩ := lintegral_iSup_band_sum_dilation_le K lam Ψ
  exact ⟨C, hCpos, fun H hH => (bandMax_le_continuum Ψ lam H).trans (hC H hH)⟩

/-! ### The abstract bootstrap -/

/-- **Bourgain's bootstrap (abstract form).**  Assume for a fixed shift `y`:
* admissibility is preserved by the shift `H ↦ H - T_y H`,
* the one-step inequality `bandMax H ≤ A·bandSq H + bandMax (H - T_yH)`,
* the contraction `bandSq (H - T_yH) ≤ θ²·bandSq H`,
* the a priori bound `bandMax H ≤ CK·bandSq H`.
Then `bandMax H ≤ (A/(1-θ²))·bandSq H` whenever `2θ² < 1`. -/
theorem bandMax_le_of_oneStep (Ψ : SchwartzMap ℝ ℂ) (lam : Fin K → ℝ) (y : ℝ) {A θ CK : ℝ}
    (hA : 0 ≤ A) (hApos : 0 < A) (hθ0 : 0 ≤ θ) (hθ : 2 * θ ^ 2 < 1) (hCK : 0 ≤ CK)
    (Adm : (Fin K → ℝ → ℂ) → Prop)
    (hpres : ∀ H, Adm H → Adm (shiftH H y))
    (hone : ∀ H, Adm H →
      bandMax Ψ lam H ≤ ENNReal.ofReal A * bandSq H + bandMax Ψ lam (shiftH H y))
    (hcon : ∀ H, Adm H → bandSq (shiftH H y) ≤ ENNReal.ofReal (θ ^ 2) * bandSq H)
    (hap : ∀ H, Adm H → bandMax Ψ lam H ≤ ENNReal.ofReal CK * bandSq H)
    (H : Fin K → ℝ → ℂ) (hH : Adm H) :
    bandMax Ψ lam H ≤ ENNReal.ofReal (A / (1 - θ ^ 2)) * bandSq H := by
  set Hn : ℕ → Fin K → ℝ → ℂ := fun n => Nat.rec H (fun n G => shiftH G y) n with hHn
  have hHn_succ : ∀ n, Hn (n+1) = shiftH (Hn n) y := fun n => rfl
  have hAdm : ∀ n, Adm (Hn n) := by
    intro n
    induction n with
    | zero => exact hH
    | succ n ih => rw [hHn_succ n]; exact hpres (Hn n) ih
  have hrec : ∀ n, bandMax Ψ lam (Hn n) ≤
      ENNReal.ofReal A * bandSq (Hn n) + bandMax Ψ lam (Hn (n+1)) := by
    intro n
    have := hone (Hn n) (hAdm n)
    rw [← hHn_succ n] at this
    exact this
  have hsq : ∀ n, bandSq (Hn (n+1)) ≤ ENNReal.ofReal (θ ^ 2) * bandSq (Hn n) := by
    intro n
    have := hcon (Hn n) (hAdm n)
    rw [← hHn_succ n] at this
    exact this
  have hsq_pow : ∀ n, bandSq (Hn n) ≤ (ENNReal.ofReal (θ ^ 2)) ^ n * bandSq H := by
    intro n
    induction n with
    | zero => simp [hHn]
    | succ n ih =>
        calc bandSq (Hn (n+1)) ≤ ENNReal.ofReal (θ^2) * bandSq (Hn n) := hsq n
          _ ≤ ENNReal.ofReal (θ^2) * ((ENNReal.ofReal (θ^2)) ^ n * bandSq H) :=
              mul_le_mul_of_nonneg_left ih (bot_le)
          _ = (ENNReal.ofReal (θ^2)) ^ (n+1) * bandSq H := by ring
  have htot : ∀ n, bandMax Ψ lam H
      ≤ (∑ i ∈ Finset.range n, ENNReal.ofReal A * (ENNReal.ofReal (θ^2)) ^ i) * bandSq H
        + bandMax Ψ lam (Hn n) := by
    intro n
    induction n with
    | zero => simp [hHn]
    | succ n ih =>
        calc bandMax Ψ lam H
            ≤ (∑ i ∈ Finset.range n, ENNReal.ofReal A * (ENNReal.ofReal (θ^2)) ^ i) * bandSq H
              + bandMax Ψ lam (Hn n) := ih
          _ ≤ (∑ i ∈ Finset.range n, ENNReal.ofReal A * (ENNReal.ofReal (θ^2)) ^ i) * bandSq H
              + (ENNReal.ofReal A * bandSq (Hn n) + bandMax Ψ lam (Hn (n+1))) :=
              add_le_add (le_refl _) (hrec n)
          _ ≤ (∑ i ∈ Finset.range n, ENNReal.ofReal A * (ENNReal.ofReal (θ^2)) ^ i) * bandSq H
              + (ENNReal.ofReal A * ((ENNReal.ofReal (θ^2)) ^ n * bandSq H)
                + bandMax Ψ lam (Hn (n+1))) := by
              refine add_le_add (le_refl _) (add_le_add ?_ (le_refl _))
              exact mul_le_mul_of_nonneg_left (hsq_pow n) (bot_le)
          _ = (∑ i ∈ Finset.range (n+1), ENNReal.ofReal A * (ENNReal.ofReal (θ^2)) ^ i) * bandSq H
              + bandMax Ψ lam (Hn (n+1)) := by
              rw [Finset.sum_range_succ]; ring
  have htail : ∀ n, bandMax Ψ lam (Hn n) ≤ ENNReal.ofReal CK * (ENNReal.ofReal (θ^2)) ^ n
      * bandSq H := by
    intro n
    calc bandMax Ψ lam (Hn n) ≤ ENNReal.ofReal CK * bandSq (Hn n) := hap (Hn n) (hAdm n)
      _ ≤ ENNReal.ofReal CK * ((ENNReal.ofReal (θ^2)) ^ n * bandSq H) :=
          mul_le_mul_of_nonneg_left (hsq_pow n) (bot_le)
      _ = ENNReal.ofReal CK * (ENNReal.ofReal (θ^2)) ^ n * bandSq H := by ring
  have hfin : bandMax Ψ lam H ≤ ⨅ n, ((∑ i ∈ Finset.range n,
      ENNReal.ofReal A * (ENNReal.ofReal (θ^2)) ^ i) + ENNReal.ofReal CK * (ENNReal.ofReal (θ^2)) ^ n)
      * bandSq H := by
    refine le_iInf (fun n => ?_)
    calc bandMax Ψ lam H
        ≤ (∑ i ∈ Finset.range n, ENNReal.ofReal A * (ENNReal.ofReal (θ^2)) ^ i) * bandSq H
          + bandMax Ψ lam (Hn n) := htot n
      _ ≤ (∑ i ∈ Finset.range n, ENNReal.ofReal A * (ENNReal.ofReal (θ^2)) ^ i) * bandSq H
          + ENNReal.ofReal CK * (ENNReal.ofReal (θ^2)) ^ n * bandSq H := add_le_add (le_refl _) (htail n)
      _ = ((∑ i ∈ Finset.range n, ENNReal.ofReal A * (ENNReal.ofReal (θ^2)) ^ i)
            + ENNReal.ofReal CK * (ENNReal.ofReal (θ^2)) ^ n) * bandSq H := by ring
  have hcast1 : ∀ n, (∑ i ∈ Finset.range n, ENNReal.ofReal A * (ENNReal.ofReal (θ^2)) ^ i)
      = ENNReal.ofReal (A * (∑ i ∈ Finset.range n, (θ^2) ^ i)) := by
    intro n
    have hterm : ∀ i, ENNReal.ofReal A * (ENNReal.ofReal (θ^2)) ^ i
        = ENNReal.ofReal (A * (θ^2)^i) := by
      intro i
      rw [ENNReal.ofReal_mul hA, ENNReal.ofReal_pow (sq_nonneg θ)]
    rw [Finset.sum_congr rfl (fun i _ => hterm i),
      ← ENNReal.ofReal_sum_of_nonneg
        (fun i _ => mul_nonneg hA (pow_nonneg (sq_nonneg θ) i))]
    conv_rhs => rw [Finset.mul_sum]
  have hcast2 : ∀ n, ENNReal.ofReal CK * (ENNReal.ofReal (θ^2)) ^ n
      = ENNReal.ofReal (CK * (θ^2) ^ n) := by
    intro n
    rw [ENNReal.ofReal_mul hCK, ENNReal.ofReal_pow (sq_nonneg θ)]
  have hcast : ∀ n, ((∑ i ∈ Finset.range n, ENNReal.ofReal A * (ENNReal.ofReal (θ^2)) ^ i)
      + ENNReal.ofReal CK * (ENNReal.ofReal (θ^2)) ^ n)
      = ENNReal.ofReal (A * (∑ i ∈ Finset.range n, (θ^2) ^ i) + CK * (θ^2) ^ n) := by
    intro n
    rw [hcast1 n, hcast2 n, ← ENNReal.ofReal_add
      (mul_nonneg hA (Finset.sum_nonneg fun i _ => pow_nonneg (sq_nonneg θ) i))
      (mul_nonneg hCK (pow_nonneg (sq_nonneg θ) _))]
  have hgeo : ∀ n, (∑ i ∈ Finset.range n, (θ^2)^i) ≤ (1 - θ^2)⁻¹ := by
    intro n
    have hden : 0 < 1 - θ^2 := by nlinarith
    rw [inv_eq_one_div, le_div_iff₀ hden]
    have hgm := geom_sum_mul (θ^2) n
    have h1 : (∑ i ∈ Finset.range n, (θ^2)^i) * (1 - θ^2) = 1 - (θ^2)^n := by
      have := geom_sum_mul (θ^2) n
      rw [show (1:ℝ) - θ^2 = -((θ^2) - 1) by ring, mul_neg, this]
      ring
    rw [h1]
    have : (0:ℝ) ≤ (θ^2)^n := pow_nonneg (sq_nonneg θ) n
    linarith
  have hlim : (⨅ n, ((∑ i ∈ Finset.range n, ENNReal.ofReal A * (ENNReal.ofReal (θ^2)) ^ i)
      + ENNReal.ofReal CK * (ENNReal.ofReal (θ^2)) ^ n)) ≤ ENNReal.ofReal (A / (1 - θ^2)) := by
    refine ENNReal.le_of_forall_pos_le_add (fun ε hε _ => ?_)
    have hlt : (θ^2) < 1 := by nlinarith
    obtain ⟨n, hn⟩ : ∃ n : ℕ, CK * (θ^2)^n ≤ (ε : ℝ) := by
      rcases eq_or_lt_of_le hCK with h0 | hpos
      · refine ⟨0, ?_⟩
        rw [← h0]; simp
      · have hε' : (0:ℝ) < (ε:ℝ) := by exact_mod_cast hε
        obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (by positivity : (0:ℝ) < (ε:ℝ)/CK) hlt
        refine ⟨n, le_of_lt ?_⟩
        calc CK * (θ^2)^n < CK * ((ε:ℝ)/CK) := mul_lt_mul_of_pos_left hn hpos
          _ = (ε:ℝ) := by field_simp
    calc (⨅ n, ((∑ i ∈ Finset.range n, ENNReal.ofReal A * (ENNReal.ofReal (θ^2)) ^ i)
            + ENNReal.ofReal CK * (ENNReal.ofReal (θ^2)) ^ n))
        ≤ ((∑ i ∈ Finset.range n, ENNReal.ofReal A * (ENNReal.ofReal (θ^2)) ^ i)
            + ENNReal.ofReal CK * (ENNReal.ofReal (θ^2)) ^ n) := iInf_le _ n
      _ = ENNReal.ofReal (A * (∑ i ∈ Finset.range n, (θ^2) ^ i) + CK * (θ^2) ^ n) := hcast n
      _ ≤ ENNReal.ofReal (A * (1 - θ^2)⁻¹ + (ε : ℝ)) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have hge := hgeo n
          have hA1 : A * (∑ i ∈ Finset.range n, (θ^2)^i) ≤ A * (1 - θ^2)⁻¹ :=
            mul_le_mul_of_nonneg_left hge hA
          linarith [hn]
      _ = ENNReal.ofReal (A * (1 - θ^2)⁻¹) + ENNReal.ofReal ((ε : ℝ)) :=
          ENNReal.ofReal_add (by positivity) (by positivity)
      _ = ENNReal.ofReal (A / (1 - θ^2)) + (ε : ENNReal) := by
          rw [ENNReal.ofReal_coe_nnreal]
          congr 1
  have hX1 : ∀ n : ℕ, ENNReal.ofReal A ≤ (∑ i ∈ Finset.range (n+1),
      ENNReal.ofReal A * (ENNReal.ofReal (θ^2)) ^ i)
      + ENNReal.ofReal CK * (ENNReal.ofReal (θ^2)) ^ (n+1) := by
    intro n
    have h1 : ENNReal.ofReal A ≤ ∑ i ∈ Finset.range (n+1),
        ENNReal.ofReal A * (ENNReal.ofReal (θ^2)) ^ i := by
      have := Finset.single_le_sum
        (f := fun i => ENNReal.ofReal A * (ENNReal.ofReal (θ^2)) ^ i)
        (fun i _ => bot_le) (Finset.mem_range.mpr (Nat.succ_pos n))
      simpa using this
    exact le_add_right h1
  have hLpos : 0 < ⨅ n, ((∑ i ∈ Finset.range (n+1), ENNReal.ofReal A * (ENNReal.ofReal (θ^2)) ^ i)
      + ENNReal.ofReal CK * (ENNReal.ofReal (θ^2)) ^ (n+1)) :=
    lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hApos) (le_iInf fun n => hX1 n)
  have hLtop : (⨅ n, ((∑ i ∈ Finset.range (n+1), ENNReal.ofReal A * (ENNReal.ofReal (θ^2)) ^ i)
      + ENNReal.ofReal CK * (ENNReal.ofReal (θ^2)) ^ (n+1))) ≠ ⊤ := by
    refine ne_of_lt (lt_of_le_of_lt (iInf_le _ 0) ?_)
    rw [hcast (0+1)]
    simp only [Nat.zero_add]
    exact ENNReal.ofReal_lt_top
  have hfin : bandMax Ψ lam H ≤ ⨅ n, ((∑ i ∈ Finset.range (n+1),
      ENNReal.ofReal A * (ENNReal.ofReal (θ^2)) ^ i)
      + ENNReal.ofReal CK * (ENNReal.ofReal (θ^2)) ^ (n+1)) * bandSq H := by
    refine le_iInf fun n => ?_
    calc bandMax Ψ lam H
        ≤ (∑ i ∈ Finset.range (n+1), ENNReal.ofReal A * (ENNReal.ofReal (θ^2)) ^ i) * bandSq H
          + bandMax Ψ lam (Hn (n+1)) := htot (n+1)
      _ ≤ (∑ i ∈ Finset.range (n+1), ENNReal.ofReal A * (ENNReal.ofReal (θ^2)) ^ i) * bandSq H
          + ENNReal.ofReal CK * (ENNReal.ofReal (θ^2)) ^ (n+1) * bandSq H :=
          add_le_add (le_refl _) (htail (n+1))
      _ = ((∑ i ∈ Finset.range (n+1), ENNReal.ofReal A * (ENNReal.ofReal (θ^2)) ^ i)
            + ENNReal.ofReal CK * (ENNReal.ofReal (θ^2)) ^ (n+1)) * bandSq H := by ring
  have hkey : ∀ ε : NNReal, 0 < ε → ∃ n : ℕ, ((∑ i ∈ Finset.range (n+1),
      ENNReal.ofReal A * (ENNReal.ofReal (θ^2)) ^ i)
      + ENNReal.ofReal CK * (ENNReal.ofReal (θ^2)) ^ (n+1))
      ≤ ENNReal.ofReal (A / (1 - θ^2)) + (ε : ENNReal) := by
    intro ε hε
    have hlt : (θ^2) < 1 := by nlinarith
    have hε' : (0:ℝ) < (ε:ℝ) := by exact_mod_cast hε
    obtain ⟨n, hn⟩ : ∃ n : ℕ, CK * (θ^2)^(n+1) ≤ (ε : ℝ) := by
      rcases eq_or_lt_of_le hCK with h0 | hpos
      · refine ⟨0, ?_⟩
        rw [← h0, zero_mul]
        exact hε'.le
      · obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (by positivity : (0:ℝ) < (ε:ℝ)/CK) hlt
        refine ⟨m, le_of_lt ?_⟩
        calc CK * (θ^2)^(m+1) = (CK * (θ^2)^m) * (θ^2) := by ring
          _ ≤ (CK * (θ^2)^m) * 1 :=
              mul_le_mul_of_nonneg_left hlt.le (by positivity)
          _ = CK * (θ^2)^m := by ring
          _ < CK * ((ε:ℝ)/CK) := mul_lt_mul_of_pos_left hm hpos
          _ = (ε:ℝ) := by field_simp
    refine ⟨n, ?_⟩
    calc ((∑ i ∈ Finset.range (n+1), ENNReal.ofReal A * (ENNReal.ofReal (θ^2)) ^ i)
          + ENNReal.ofReal CK * (ENNReal.ofReal (θ^2)) ^ (n+1))
        = ENNReal.ofReal (A * (∑ i ∈ Finset.range (n+1), (θ^2) ^ i) + CK * (θ^2) ^ (n+1)) :=
          hcast (n+1)
      _ ≤ ENNReal.ofReal (A * (1 - θ^2)⁻¹ + (ε : ℝ)) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have hge := hgeo (n+1)
          have hA1 : A * (∑ i ∈ Finset.range (n+1), (θ^2)^i) ≤ A * (1 - θ^2)⁻¹ :=
            mul_le_mul_of_nonneg_left hge hA
          linarith [hn]
      _ = ENNReal.ofReal (A * (1 - θ^2)⁻¹) + ENNReal.ofReal ((ε : ℝ)) :=
          ENNReal.ofReal_add (by positivity) (by positivity)
      _ = ENNReal.ofReal (A / (1 - θ^2)) + (ε : ENNReal) := by
          rw [ENNReal.ofReal_coe_nnreal]
          congr 1
  have hlimShift : (⨅ n, ((∑ i ∈ Finset.range (n+1),
      ENNReal.ofReal A * (ENNReal.ofReal (θ^2)) ^ i)
      + ENNReal.ofReal CK * (ENNReal.ofReal (θ^2)) ^ (n+1))) ≤ ENNReal.ofReal (A / (1 - θ^2)) := by
    refine ENNReal.le_of_forall_pos_le_add (fun ε hε _ => ?_)
    obtain ⟨n, hn⟩ := hkey ε hε
    exact (iInf_le _ n).trans hn
  calc bandMax Ψ lam H
      ≤ ⨅ n, ((∑ i ∈ Finset.range (n+1), ENNReal.ofReal A * (ENNReal.ofReal (θ^2)) ^ i)
          + ENNReal.ofReal CK * (ENNReal.ofReal (θ^2)) ^ (n+1)) * bandSq H := hfin
    _ = (⨅ n, ((∑ i ∈ Finset.range (n+1), ENNReal.ofReal A * (ENNReal.ofReal (θ^2)) ^ i)
          + ENNReal.ofReal CK * (ENNReal.ofReal (θ^2)) ^ (n+1))) * bandSq H :=
        (ENNReal.iInf_mul (f := fun n => (∑ i ∈ Finset.range (n+1),
            ENNReal.ofReal A * (ENNReal.ofReal (θ^2)) ^ i)
            + ENNReal.ofReal CK * (ENNReal.ofReal (θ^2)) ^ (n+1))
          (a := bandSq H) (fun _ h0 => absurd h0 hLpos.ne')).symm
    _ ≤ ENNReal.ofReal (A / (1 - θ^2)) * bandSq H :=
        mul_le_mul_of_nonneg_right hlimShift bot_le

end

end Commons.Analysis.Fourier


/-!
# The entropy step of Bourgain's Lemma 4.13

The `u`-averaging identity `bandMax_translate` turns the maximal function of a translate into a
maximal exponential sum with the curve coefficients.  This file develops the chaining argument
which bounds it: the net construction (`exists_net_selfmap_l2`), the per-`z` chain bound, and the
comparison of the resulting dyadic sum with the entropy integral (`winML2`), which is bounded by
`bourgain_entropy_integral_l2_l2vec`.
-/

namespace Commons.Analysis.Fourier

open _root_.MeasureTheory Finset Function Filter
open scoped _root_.ENNReal _root_.Topology BigOperators

noncomputable section

variable {K : ℕ}

/-! ### The entropy chain on an arbitrary unit interval -/

/-- `∫⁻ y in (0,1], F (y + c) = ∫⁻ y in (c, c+1], F y`. -/
private lemma lintegral_Ioc_add_right (F : ℝ → ℝ≥0∞) (c : ℝ) :
    ∫⁻ y in Set.Ioc (0:ℝ) 1, F (y + c) = ∫⁻ y in Set.Ioc c (c + 1), F y := by
  rw [← MeasureTheory.lintegral_indicator measurableSet_Ioc,
      ← MeasureTheory.lintegral_indicator measurableSet_Ioc]
  have h1 : ∀ y, Set.indicator (Set.Ioc (0:ℝ) 1) (fun z => F (z + c)) y
      = Set.indicator (Set.Ioc c (c + 1)) F (y + c) := by
    intro y
    rw [Set.indicator_apply, Set.indicator_apply]
    by_cases h : y ∈ Set.Ioc (0:ℝ) 1
    · rw [if_pos h, if_pos ⟨by linarith [h.1], by linarith [h.2]⟩]
    · rw [if_neg h]
      by_cases h2 : y + c ∈ Set.Ioc c (c + 1)
      · exact absurd ⟨by linarith [h2.1], by linarith [h2.2]⟩ h
      · rw [if_neg h2]
  calc ∫⁻ y, Set.indicator (Set.Ioc (0:ℝ) 1) (fun z => F (z + c)) y
      = ∫⁻ y, Set.indicator (Set.Ioc c (c + 1)) F (y + c) := by simp only [h1]
    _ = ∫⁻ y, Set.indicator (Set.Ioc c (c + 1)) F y :=
        MeasureTheory.lintegral_add_right_eq_self _ c

/-- The character `y ↦ e^{I λ y}` has modulus one. -/
private lemma norm_cexp_lin (lam y : ℝ) :
    ‖Complex.exp (Complex.I * (lam : ℂ) * (y : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  have h : (Complex.I * (lam : ℂ) * (y : ℂ)).re = 0 := by
    rw [Complex.mul_re, Complex.mul_re]; simp
  rw [h, Real.exp_zero]

/-- **The entropy chain on an arbitrary interval of length one.**  The published
`chain_exp_sum_le_entropy` with `(0,1]` replaced by `(c, c+1]`; the bound is covariant under the
per-frequency unimodular rescaling `a i k ↦ a i k · e^{I λ_k c}`. -/
theorem chain_exp_sum_le_entropy_Ioc (K : ℕ) (lam : Fin K → ℝ)
    (hsep : ∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N S : ℕ) (a : Fin (N+1) → Fin K → ℂ)
        (σ : ℕ → Fin (N+1) → Fin (N+1)) (M : ℕ → ℕ) (c : ℝ),
      1 ≤ S →
      (∀ i : Fin (N+1), σ 0 i = σ 0 0) →
      (N+1) ≤ M S →
      (∀ t, t ≤ S → (Finset.univ.image (σ t)).card ≤ M t) →
      (∀ t, t ≤ S → ∀ i : Fin (N+1),
        ∑ k : Fin K, ‖a i k - a (σ t i) k‖ ^ 2 ≤ (2 * (1/2:ℝ)^t)^2) →
      ∫⁻ y in Set.Ioc c (c + 1),
          ENNReal.ofReal (⨆ i : Fin (N+1),
            ‖∑ k : Fin K, a i k * Complex.exp (Complex.I * (lam k:ℂ) * (y:ℂ))‖) ^ 2
        ≤ ENNReal.ofReal ((C * (Real.sqrt (∑ k : Fin K, ‖a (σ 0 0) k‖ ^ 2)
            + ∑ t ∈ Finset.range (S+1),
                (1/2:ℝ)^t * Real.sqrt (min (K:ℝ) ((M t : ℝ) + 1)))) ^ 2) := by
  obtain ⟨C, hCpos, hC⟩ := chain_exp_sum_le_entropy K lam hsep
  refine ⟨C, hCpos, ?_⟩
  intro N S a σ M c hS hconst hNM hcard hnet
  set a' : Fin (N+1) → Fin K → ℂ :=
    fun i k => a i k * Complex.exp (Complex.I * (lam k : ℂ) * (c : ℂ)) with ha'
  have hnet' : ∀ t, t ≤ S → ∀ i : Fin (N+1),
      ∑ k : Fin K, ‖a' i k - a' (σ t i) k‖ ^ 2 ≤ (2 * (1/2:ℝ)^t)^2 := by
    intro t ht i
    have h : ∀ k : Fin K, ‖a' i k - a' (σ t i) k‖ = ‖a i k - a (σ t i) k‖ := by
      intro k
      have he : a' i k - a' (σ t i) k
          = (a i k - a (σ t i) k) * Complex.exp (Complex.I * (lam k:ℂ) * (c:ℂ)) := by
        rw [ha']; ring
      rw [he, norm_mul, norm_cexp_lin (lam k) c, mul_one]
    simpa only [h] using hnet t ht i
  have hmain := hC N S a' σ M hS hconst hNM hcard hnet'
  have hbase : (∑ k : Fin K, ‖a' (σ 0 0) k‖ ^ 2) = ∑ k : Fin K, ‖a (σ 0 0) k‖ ^ 2 := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [ha', norm_mul, norm_cexp_lin (lam k) c, mul_one]
  rw [hbase] at hmain
  have hchar : ∀ (i : Fin (N+1)) (y : ℝ),
      (∑ k : Fin K, a' i k * Complex.exp (Complex.I * (lam k:ℂ) * (y:ℂ)))
        = ∑ k : Fin K, a i k * Complex.exp (Complex.I * (lam k:ℂ) * ((y + c : ℝ):ℂ)) := by
    intro i y
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [ha']
    rw [mul_assoc]
    rw [show Complex.exp (Complex.I * (lam k : ℂ) * (c : ℂ))
            * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))
          = Complex.exp (Complex.I * (lam k : ℂ) * ((y + c : ℝ) : ℂ)) from by
        rw [← Complex.exp_add]; congr 1; push_cast; ring]
  have hshift : ∫⁻ y in Set.Ioc (0:ℝ) 1,
        ENNReal.ofReal (⨆ i : Fin (N+1),
          ‖∑ k : Fin K, a' i k * Complex.exp (Complex.I * (lam k:ℂ) * (y:ℂ))‖) ^ 2
      = ∫⁻ y in Set.Ioc c (c + 1),
        ENNReal.ofReal (⨆ i : Fin (N+1),
          ‖∑ k : Fin K, a i k * Complex.exp (Complex.I * (lam k:ℂ) * (y:ℂ))‖) ^ 2 := by
    rw [← lintegral_Ioc_add_right (fun y => ENNReal.ofReal (⨆ i : Fin (N+1),
      ‖∑ k : Fin K, a i k * Complex.exp (Complex.I * (lam k:ℂ) * (y:ℂ))‖) ^ 2) c]
    refine lintegral_congr (fun y => ?_)
    simp only [hchar]
  rw [hshift] at hmain
  exact hmain

/-! ### Covers from covering numbers -/

/-- A finite cover of cardinality at most the covering number. -/
lemma exists_cover_of_coveringNumber {X : Type*} [PseudoMetricSpace X] (A : Set X) {ε : NNReal}
    (hfin : Metric.coveringNumber ε A ≠ ⊤) :
    ∃ S : Finset X, (∀ x ∈ A, ∃ s ∈ S, dist x s ≤ ε) ∧
      ((S.card : ℕ∞) ≤ Metric.coveringNumber ε A) := by
  have hIsCov := Metric.isCover_minimalCover (A := A) (ε := ε) hfin
  have hfin' : (Metric.minimalCover ε A).Finite := Metric.finite_minimalCover
  refine ⟨hfin'.toFinset, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := hIsCov hx
    refine ⟨y, hfin'.mem_toFinset.mpr hy, ?_⟩
    have hxy' : edist x y ≤ (ε : ℝ≥0∞) := by simpa only [Set.mem_setOf_eq] using hxy
    have h1 : (nndist x y : ℝ≥0∞) ≤ (ε : ℝ≥0∞) := by
      rwa [edist_nndist] at hxy'
    have h2 : nndist x y ≤ ε := ENNReal.coe_le_coe.mp h1
    have h3 : dist x y ≤ (ε : ℝ) := by rw [dist_nndist]; exact_mod_cast h2
    exact h3
  · have h1 : ((hfin'.toFinset.card : ℕ) : ℕ∞) = Metric.coveringNumber ε A := by
      rw [← hfin'.encard_eq_coe_toFinset_card, Metric.encard_minimalCover hfin]
    exact le_of_eq h1

/-! ### The dyadic curve family -/

/-- The family of dyadic curve points, as `ℓ²`-vectors. -/
noncomputable def curveVec (Ψ : SchwartzMap ℝ ℂ) (H : Fin K → ℝ → ℂ) (S : ℕ) (z : ℝ) :
    Fin (S+1) → EuclideanSpace ℂ (Fin K) :=
  fun i => winCurveL2 Ψ H z ⟨scaleTj (i:ℕ), scaleTj_pos (i:ℕ)⟩

lemma curveVec_apply (Ψ : SchwartzMap ℝ ℂ) (H : Fin K → ℝ → ℂ) (S : ℕ) (z : ℝ)
    (i : Fin (S+1)) (k : Fin K) :
    curveVec Ψ H S z i k
      = ∫ y : ℝ, H k y * (((scaleTj (i:ℕ) : ℝ)⁻¹ : ℝ) • (Ψ : ℝ → ℂ) ((z - y) / (scaleTj (i:ℕ) : ℝ))) :=
  rfl

/-- The maximal `ℓ²`-norm of the dyadic curve family. -/
noncomputable def curveRad (Ψ : SchwartzMap ℝ ℂ) (H : Fin K → ℝ → ℂ) (S : ℕ) (z : ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun i : Fin (S+1) => ‖curveVec Ψ H S z i‖

lemma curveRad_nonneg (Ψ : SchwartzMap ℝ ℂ) (H : Fin K → ℝ → ℂ) (S : ℕ) (z : ℝ) :
    0 ≤ curveRad Ψ H S z := by
  unfold curveRad
  exact le_trans (norm_nonneg _) (Finset.le_sup' (f := fun i : Fin (S+1) => ‖curveVec Ψ H S z i‖)
    (Finset.mem_univ 0))


/-! ### Dyadic Riemann sums on a scaled grid -/

/-- **Dyadic sum versus integral on the scaled grid `{c·2^{-ℓ}}`.**  For non-increasing
`f : ℝ → ℝ≥0∞` and `c > 0`, `∑_{ℓ<L} 2^{-ℓ} f (c·2^{-ℓ}) ≤ c⁻¹ · 2∫_{(0,c]} f`. -/


lemma enn_min_rpow_half (a b : ℝ≥0∞) :
    (min a b) ^ ((1:ℝ)/2) = min (a ^ ((1:ℝ)/2)) (b ^ ((1:ℝ)/2)) := by
  refine le_antisymm ?_ ?_
  · exact le_min (ENNReal.rpow_le_rpow (min_le_left _ _) (by norm_num))
      (ENNReal.rpow_le_rpow (min_le_right _ _) (by norm_num))
  · rcases le_total a b with h | h
    · rw [min_eq_left h]; exact min_le_left _ _
    · rw [min_eq_right h]; exact min_le_right _ _

private lemma min_add_le (a x y : ℝ≥0∞) : min a (x + y) ≤ min a x + y := by
  rcases le_total a x with h' | h'
  · calc min a (x + y) ≤ a := min_le_left _ _
      _ = min a x := (min_eq_left h').symm
      _ ≤ min a x + y := le_add_right le_rfl
  · calc min a (x + y) ≤ x + y := min_le_right _ _
      _ = min a x + y := by rw [min_eq_right h']

lemma dyadic_sum_le_lintegral_entropy (E : ℝ → ℝ≥0∞)
    (hanti : ∀ r r' : ℝ, 0 < r → r ≤ r' → E r' ≤ E r)
    (hE1 : ∀ r : ℝ, 0 < r → 1 ≤ E r)
    (K : ℕ) (M : ℕ → ℕ) {c : ℝ} (hc : 0 < c) (L : ℕ)
    (hM : ∀ t : ℕ, (M t : ℝ≥0∞) ≤ E (c * (1/2:ℝ)^t)) :
    ENNReal.ofReal (∑ t ∈ Finset.range L,
        (1/2:ℝ)^t * Real.sqrt (min (K:ℝ) ((M t : ℝ) + 1)))
      ≤ ENNReal.ofReal c⁻¹ * (2 * (∫⁻ r in Set.Ioi (0:ℝ),
          min (ENNReal.ofReal (Real.sqrt (K:ℝ))) ((E r - 1) ^ ((1:ℝ)/2)))) + 4 := by
  set g : ℝ → ℝ≥0∞ := fun r =>
    min (ENNReal.ofReal (Real.sqrt (K:ℝ))) ((E r - 1) ^ ((1:ℝ)/2)) with hg
  have hganti : ∀ r r' : ℝ, 0 < r → r ≤ r' → g r' ≤ g r := by
    intro r r' hr hrr
    refine min_le_min le_rfl ?_
    exact ENNReal.rpow_le_rpow (tsub_le_tsub_right (hanti r r' hr hrr) 1) (by norm_num)
  have hbase : ∀ t : ℕ, ENNReal.ofReal (Real.sqrt (min (K:ℝ) ((M t : ℝ) + 1)))
      = (min (ENNReal.ofReal (K:ℝ)) ((M t : ℝ≥0∞) + 1)) ^ ((1:ℝ)/2) := by
    intro t
    rw [Real.sqrt_eq_rpow,
      ← ENNReal.ofReal_rpow_of_nonneg (le_min (Nat.cast_nonneg K) (by positivity))
        (by norm_num : (0:ℝ) ≤ (1:ℝ)/2),
      ENNReal.ofReal_min, ENNReal.ofReal_add (by positivity) (by norm_num),
      ENNReal.ofReal_natCast, ENNReal.ofReal_one]
    simp only [ENNReal.ofReal_natCast]
  have hK : (ENNReal.ofReal (K:ℝ)) ^ ((1:ℝ)/2) = ENNReal.ofReal (Real.sqrt (K:ℝ)) := by
    rw [Real.sqrt_eq_rpow, ← ENNReal.ofReal_rpow_of_nonneg (Nat.cast_nonneg K)
      (by norm_num : (0:ℝ) ≤ (1:ℝ)/2)]
  have hterm : ∀ t : ℕ, ENNReal.ofReal ((1/2:ℝ)^t * Real.sqrt (min (K:ℝ) ((M t : ℝ) + 1)))
      ≤ ENNReal.ofReal ((1/2:ℝ)^t) * (g (c * (1/2:ℝ)^t) + 2) := by
    intro t
    have hstep : ENNReal.ofReal (Real.sqrt (min (K:ℝ) ((M t : ℝ) + 1)))
        ≤ g (c * (1/2:ℝ)^t) + 2 := by
      rw [hbase, enn_min_rpow_half, hK]
      refine le_trans (min_le_min le_rfl ?_) (min_add_le _ _ 2)
      calc ((M t : ℝ≥0∞) + 1) ^ ((1:ℝ)/2)
          ≤ (E (c * (1/2:ℝ)^t) + 1) ^ ((1:ℝ)/2) :=
            ENNReal.rpow_le_rpow (add_le_add (hM t) le_rfl) (by norm_num)
        _ ≤ ((E (c * (1/2:ℝ)^t) - 1) + 2) ^ ((1:ℝ)/2) := by
            apply ENNReal.rpow_le_rpow _ (by norm_num)
            have h1 : E (c * (1/2:ℝ)^t) ≤ E (c * (1/2:ℝ)^t) - 1 + 1 := by
              rw [tsub_add_cancel_of_le (hE1 _ (by positivity))]
            calc E (c * (1/2:ℝ)^t) + 1
                ≤ (E (c * (1/2:ℝ)^t) - 1 + 1) + 1 := add_le_add h1 le_rfl
              _ = (E (c * (1/2:ℝ)^t) - 1) + 2 := by ring
        _ ≤ (E (c * (1/2:ℝ)^t) - 1) ^ ((1:ℝ)/2) + 2 ^ ((1:ℝ)/2) :=
            ENNReal.rpow_add_le_add_rpow _ _ (by norm_num) (by norm_num)
        _ ≤ (E (c * (1/2:ℝ)^t) - 1) ^ ((1:ℝ)/2) + 2 := by
            refine add_le_add le_rfl ?_
            have h := ENNReal.rpow_le_rpow_of_exponent_le
              (show (1:ℝ≥0∞) ≤ 2 by norm_num) (show ((1:ℝ)/2) ≤ 1 by norm_num)
            simpa using h
    rw [ENNReal.ofReal_mul (by positivity)]
    exact mul_le_mul le_rfl hstep bot_le bot_le
  have hsum : ENNReal.ofReal (∑ t ∈ Finset.range L,
        (1/2:ℝ)^t * Real.sqrt (min (K:ℝ) ((M t : ℝ) + 1)))
      = ∑ t ∈ Finset.range L, ENNReal.ofReal
          ((1/2:ℝ)^t * Real.sqrt (min (K:ℝ) ((M t : ℝ) + 1))) :=
    ENNReal.ofReal_sum_of_nonneg (fun t _ => by positivity)
  rw [hsum]
  have hsplit : ∑ t ∈ Finset.range L, ENNReal.ofReal
        ((1/2:ℝ)^t * Real.sqrt (min (K:ℝ) ((M t : ℝ) + 1)))
      ≤ (∑ t ∈ Finset.range L, ENNReal.ofReal ((1/2:ℝ)^t) * g (c * (1/2:ℝ)^t))
        + ∑ t ∈ Finset.range L, ENNReal.ofReal ((1/2:ℝ)^t) * 2 := by
    calc ∑ t ∈ Finset.range L, ENNReal.ofReal
          ((1/2:ℝ)^t * Real.sqrt (min (K:ℝ) ((M t : ℝ) + 1)))
        ≤ ∑ t ∈ Finset.range L, ENNReal.ofReal ((1/2:ℝ)^t) * (g (c * (1/2:ℝ)^t) + 2) :=
          Finset.sum_le_sum (fun t _ => hterm t)
      _ = (∑ t ∈ Finset.range L, ENNReal.ofReal ((1/2:ℝ)^t) * g (c * (1/2:ℝ)^t))
          + ∑ t ∈ Finset.range L, ENNReal.ofReal ((1/2:ℝ)^t) * 2 := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun t _ => by ring
  have hgeo : ∑ t ∈ Finset.range L, ENNReal.ofReal ((1/2:ℝ)^t) * 2 ≤ 4 := by
    have h1 : ∑ t ∈ Finset.range L, (1/2:ℝ)^t ≤ 2 := by
      have h2 : ∑ t ∈ Finset.range L, (1/2:ℝ)^t = 2 * (1 - (1/2:ℝ)^L) := by
        rw [geom_sum_eq (by norm_num : (1/2:ℝ) ≠ 1)]
        field_simp
        ring
      rw [h2]
      have : (0:ℝ) < (1/2:ℝ)^L := pow_pos (by norm_num : (0:ℝ) < 1/2) _
      linarith
    calc ∑ t ∈ Finset.range L, ENNReal.ofReal ((1/2:ℝ)^t) * 2
        = (∑ t ∈ Finset.range L, ENNReal.ofReal ((1/2:ℝ)^t)) * 2 :=
            (Finset.sum_mul _ _ _).symm
      _ = ENNReal.ofReal (∑ t ∈ Finset.range L, (1/2:ℝ)^t) * 2 := by
          rw [ENNReal.ofReal_sum_of_nonneg (fun t _ => by positivity)]
      _ ≤ ENNReal.ofReal 2 * 2 :=
          mul_le_mul (ENNReal.ofReal_le_ofReal h1) le_rfl bot_le bot_le
      _ = 4 := by norm_num
  have hmain : ∑ t ∈ Finset.range L, ENNReal.ofReal ((1/2:ℝ)^t) * g (c * (1/2:ℝ)^t)
      ≤ ENNReal.ofReal c⁻¹ * (2 * (∫⁻ r in Set.Ioi (0:ℝ), g r)) := by
    let d : ℕ → Set ℝ := fun t => Set.Ioc (c * (1/2:ℝ)^(t+1)) (c * (1/2:ℝ)^t)
    have hclen : ∀ t, ENNReal.ofReal ((1/2:ℝ)^t)
        = ENNReal.ofReal c⁻¹ * (2 * volume (d t)) := by
      intro t
      have hvol : volume (d t) = ENNReal.ofReal (c * (1/2:ℝ)^(t+1)) := by
        rw [Real.volume_Ioc]; congr 1; ring
      rw [hvol, show (2:ℝ≥0∞) = ENNReal.ofReal 2 by simp,
        ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
        ← ENNReal.ofReal_mul (inv_nonneg.mpr hc.le)]
      congr 1
      rw [pow_succ]
      field_simp
    have hcdisj : (Finset.range L : Set ℕ).PairwiseDisjoint d := by
      intro i hi j hj hij
      change Disjoint (d i) (d j)
      rw [Set.disjoint_left]
      intro r hri hrj
      have hri' : r ∈ Set.Ioc (c * (1/2:ℝ)^(i+1)) (c * (1/2:ℝ)^i) := hri
      have hrj' : r ∈ Set.Ioc (c * (1/2:ℝ)^(j+1)) (c * (1/2:ℝ)^j) := hrj
      simp only [Set.mem_Ioc] at hri' hrj'
      rcases lt_or_gt_of_ne hij with h | h
      · have hle : c * (1/2:ℝ)^j ≤ c * (1/2:ℝ)^(i+1) :=
          mul_le_mul_of_nonneg_left
            (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)) hc.le
        linarith [hri'.1, hrj'.2, hle]
      · have hle : c * (1/2:ℝ)^i ≤ c * (1/2:ℝ)^(j+1) :=
          mul_le_mul_of_nonneg_left
            (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)) hc.le
        linarith [hrj'.1, hri'.2, hle]
    have hterm2 : ∀ t, ENNReal.ofReal ((1/2:ℝ)^t) * g (c * (1/2:ℝ)^t)
        ≤ ENNReal.ofReal c⁻¹ * (2 * ∫⁻ r in d t, g r) := by
      intro t
      have hmono : ∫⁻ r in d t, g (c * (1/2:ℝ)^t) ≤ ∫⁻ r in d t, g r := by
        apply setLIntegral_mono' (μ := volume) measurableSet_Ioc
        intro r hr
        have hr' : r ∈ Set.Ioc (c * (1/2:ℝ)^(t+1)) (c * (1/2:ℝ)^t) := hr
        simp only [Set.mem_Ioc] at hr'
        exact hganti r (c * (1/2:ℝ)^t)
          (by linarith [hr'.1, mul_pos hc (pow_pos (by norm_num : (0:ℝ) < 1/2) (t+1))]) hr'.2
      calc ENNReal.ofReal ((1/2:ℝ)^t) * g (c * (1/2:ℝ)^t)
          = ENNReal.ofReal c⁻¹ * (2 * (volume (d t) * g (c * (1/2:ℝ)^t))) := by
            rw [hclen t]; ring_nf
        _ = ENNReal.ofReal c⁻¹ * (2 * ∫⁻ r in d t, g (c * (1/2:ℝ)^t)) := by
            rw [setLIntegral_const (μ := volume) (d t) (g (c * (1/2:ℝ)^t)),
              mul_comm (g (c * (1/2:ℝ)^t)) (volume (d t))]
        _ ≤ ENNReal.ofReal c⁻¹ * (2 * ∫⁻ r in d t, g r) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmono (by norm_num)) bot_le
    calc ∑ t ∈ Finset.range L, ENNReal.ofReal ((1/2:ℝ)^t) * g (c * (1/2:ℝ)^t)
        ≤ ∑ t ∈ Finset.range L, ENNReal.ofReal c⁻¹ * (2 * ∫⁻ r in d t, g r) :=
          Finset.sum_le_sum (fun t _ => hterm2 t)
      _ = ENNReal.ofReal c⁻¹ * (2 * ∑ t ∈ Finset.range L, ∫⁻ r in d t, g r) := by
          rw [Finset.mul_sum, Finset.mul_sum]
      _ = ENNReal.ofReal c⁻¹ * (2 * ∫⁻ r in (⋃ t ∈ Finset.range L, d t), g r) := by
          rw [MeasureTheory.lintegral_biUnion_finset hcdisj (fun t _ => measurableSet_Ioc) g]
      _ ≤ ENNReal.ofReal c⁻¹ * (2 * (∫⁻ r in Set.Ioi (0:ℝ), g r)) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (lintegral_mono_set ?_)
            (by norm_num)) bot_le
          intro r hr
          simp only [Set.mem_iUnion] at hr
          obtain ⟨t, -, ht⟩ := hr
          have ht' : r ∈ Set.Ioc (c * (1/2:ℝ)^(t+1)) (c * (1/2:ℝ)^t) := ht
          simp only [Set.mem_Ioc] at ht'
          show (0:ℝ) < r
          have hpos : (0:ℝ) < (1/2:ℝ)^(t+1) := pow_pos (by norm_num : (0:ℝ) < 1/2) (t+1)
          linarith [ht'.1, mul_pos hc hpos]
  calc ∑ t ∈ Finset.range L, ENNReal.ofReal
        ((1/2:ℝ)^t * Real.sqrt (min (K:ℝ) ((M t : ℝ) + 1)))
      ≤ (∑ t ∈ Finset.range L, ENNReal.ofReal ((1/2:ℝ)^t) * g (c * (1/2:ℝ)^t))
        + ∑ t ∈ Finset.range L, ENNReal.ofReal ((1/2:ℝ)^t) * 2 := hsplit
    _ ≤ ENNReal.ofReal c⁻¹ * (2 * (∫⁻ r in Set.Ioi (0:ℝ), g r)) + 4 := add_le_add hmain hgeo
    _ = ENNReal.ofReal c⁻¹ * (2 * (∫⁻ r in Set.Ioi (0:ℝ),
          min (ENNReal.ofReal (Real.sqrt (K:ℝ))) ((E r - 1) ^ ((1:ℝ)/2)))) + 4 := by rw [hg]




lemma curveVec_eq_curvePt (Ψ : SchwartzMap ℝ ℂ) (H : Fin K → ℝ → ℂ) (S : ℕ) (z : ℝ)
    (i : Fin (S+1)) (k : Fin K) :
    curveVec Ψ H S z i k = curvePt Ψ H (i:ℕ) z k := by
  simp only [curveVec_apply, curvePt, winK_eq_smul, Complex.real_smul]

lemma euclid_norm_sq (Ψ : SchwartzMap ℝ ℂ) (H : Fin K → ℝ → ℂ) (S : ℕ) (z : ℝ)
    (i : Fin (S+1)) :
    ‖curveVec Ψ H S z i‖ ^ 2 = ∑ k : Fin K, ‖curvePt Ψ H (i:ℕ) z k‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun k _ => by positivity)]
  exact Finset.sum_congr rfl fun k _ => by rw [curveVec_eq_curvePt]

/-- Each `ℓ²` norm of the dyadic curve is bounded by `curveRad`. -/
lemma norm_curveVec_le_curveRad (Ψ : SchwartzMap ℝ ℂ) (H : Fin K → ℝ → ℂ) (S : ℕ) (z : ℝ)
    (i : Fin (S+1)) : ‖curveVec Ψ H S z i‖ ≤ curveRad Ψ H S z :=
  Finset.le_sup' (f := fun i : Fin (S+1) => ‖curveVec Ψ H S z i‖) (Finset.mem_univ i)

lemma sum_norm_sq_curvePt_le (Ψ : SchwartzMap ℝ ℂ) (H : Fin K → ℝ → ℂ) (S : ℕ) (z : ℝ)
    (i : Fin (S+1)) :
    ∑ k : Fin K, ‖curvePt Ψ H (i:ℕ) z k‖ ^ 2 ≤ (curveRad Ψ H S z) ^ 2 := by
  rw [← euclid_norm_sq Ψ H S z i]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_curveVec_le_curveRad Ψ H S z i) 2


/-- **Net construction for the entropy chain.**  For the normalised family `a/(2c)` there are
nested nets `σ t` with cardinalities `M t`, the net at level `t` being a covering of the dyadic
curve at radius `c·2^{-t}`. -/
lemma exists_nets (Ψ : SchwartzMap ℝ ℂ) (H : Fin K → ℝ → ℂ) (S : ℕ) (z : ℝ) (c : ℝ)
    (hcpos : 0 < c) (hcb : c = curveRad Ψ H (S+1) z) :
    ∃ (σ : ℕ → Fin (S+2) → Fin (S+2)) (M : ℕ → ℕ),
      (∀ i : Fin (S+2), σ 0 i = σ 0 0) ∧ M 0 = 1 ∧ (M (S+1) = S + 2) ∧
      (∀ t, t ≤ S+1 → (Finset.univ.image (σ t)).card ≤ M t) ∧
      (∀ t, t ≤ S+1 → ∀ i : Fin (S+2), ∑ k : Fin K,
          ‖curvePt Ψ H (i:ℕ) z k - curvePt Ψ H ((σ t i : Fin (S+2)):ℕ) z k‖ ^ 2
            ≤ (4 * c * (1/2:ℝ)^t)^2) ∧
      (∀ t, 0 < t → t < S+1 →
        (M t : ENNReal) ≤ winML2 Ψ H z (c * (1/2:ℝ)^t) + 1) := by
  classical
  have hnet : ∀ t : ℕ, 1 ≤ t → t ≤ S →
      ∃ (τ : Fin (S+2) → Fin (S+2)) (m : ℕ),
        (Finset.univ.image τ).card ≤ m ∧
        (∀ i : Fin (S+2), ∑ k : Fin K,
          ‖curvePt Ψ H (i:ℕ) z k - curvePt Ψ H ((τ i : Fin (S+2)):ℕ) z k‖ ^ 2
            ≤ (4 * c * (1/2:ℝ)^t)^2) ∧
        (m : ENNReal) ≤ winML2 Ψ H z (c * (1/2:ℝ)^t) + 1 := by
    intro t ht1 htS
    have hfin : Metric.coveringNumber ((2 * c * (1/2:ℝ)^t).toNNReal)
        (Set.range (curveVec Ψ H (S+1) z)) ≠ ⊤ := by
      refine ne_of_lt (lt_of_le_of_lt (Metric.coveringNumber_le_encard_self _) ?_)
      rw [Set.Finite.encard_eq_coe_toFinset_card (Set.finite_range _)]
      exact ENat.natCast_lt_top _
    obtain ⟨Sc, hcov, hSc⟩ := exists_cover_of_coveringNumber (Set.range (curveVec Ψ H (S+1) z))
      (ε := (2 * c * (1/2:ℝ)^t).toNNReal) hfin
    have hcov' : ∀ i : Fin (S+2), ∃ s ∈ Sc.image WithLp.ofLp,
        ∑ k : Fin K, ‖curvePt Ψ H (i:ℕ) z k - s k‖ ^ 2 ≤ ((4 * c * (1/2:ℝ)^t) / 2) ^ 2 := by
      intro i
      obtain ⟨s₀, hs₀, hdist⟩ := hcov (curveVec Ψ H (S+1) z i) (Set.mem_range_self i)
      refine ⟨WithLp.ofLp s₀, Finset.mem_image_of_mem _ hs₀, ?_⟩
      have hd : dist (curveVec Ψ H (S+1) z i) s₀ ≤ 2 * c * (1/2:ℝ)^t := by
        have h := hdist
        rwa [Real.coe_toNNReal _ (by positivity)] at h
      have hd2 : Real.sqrt (∑ k : Fin K,
          ‖(curveVec Ψ H (S+1) z i).ofLp k - s₀.ofLp k‖ ^ 2) ≤ 2 * c * (1/2:ℝ)^t := by
        rw [EuclideanSpace.dist_eq] at hd
        simpa only [dist_eq_norm] using hd
      have hsum : ∑ k : Fin K, ‖(curveVec Ψ H (S+1) z i).ofLp k - s₀.ofLp k‖ ^ 2
          ≤ (2 * c * (1/2:ℝ)^t) ^ 2 := (Real.sqrt_le_iff.mp hd2).2
      have h4 : (4 * c * (1/2:ℝ)^t) / 2 = 2 * c * (1/2:ℝ)^t := by ring
      rw [h4]
      calc ∑ k : Fin K, ‖curvePt Ψ H (i:ℕ) z k - s₀.ofLp k‖ ^ 2
          = ∑ k : Fin K, ‖(curveVec Ψ H (S+1) z i).ofLp k - s₀.ofLp k‖ ^ 2 := by
            refine Finset.sum_congr rfl fun k _ => by rw [curveVec_eq_curvePt]
        _ ≤ (2 * c * (1/2:ℝ)^t) ^ 2 := hsum
    obtain ⟨τ, hτcard, hτnet⟩ := net_selfmap_of_cover
      (fun i k => curvePt Ψ H (i:ℕ) z k) (Sc.image WithLp.ofLp)
      (r := 4 * c * (1/2:ℝ)^t) (by
        intro i
        obtain ⟨s, hs, hle⟩ := hcov' i
        exact ⟨s, hs, hle⟩)
    refine ⟨τ, Sc.card, ?_, ?_, ?_⟩
    · calc (Finset.univ.image τ).card ≤ (Sc.image WithLp.ofLp).card := hτcard
        _ ≤ Sc.card := Finset.card_image_le
    · intro i
      exact hτnet i
    · have hcast : ((Sc.card : ℕ∞) : ENNReal) ≤
          ((Metric.coveringNumber ((2 * c * (1/2:ℝ)^t).toNNReal)
            (Set.range (curveVec Ψ H (S+1) z)) : ℕ∞) : ENNReal) := by
        exact_mod_cast hSc
      refine hcast.trans ?_
      have hsub : Set.range (curveVec Ψ H (S+1) z) ⊆ Set.range (winCurveL2 Ψ H z) := by
        rintro x ⟨i, rfl⟩
        exact ⟨⟨scaleTj (i:ℕ), scaleTj_pos (i:ℕ)⟩, rfl⟩
      have hmono := Metric.coveringNumber_subset_le (A := Set.range (curveVec Ψ H (S+1) z))
        (B := Set.range (winCurveL2 Ψ H z)) hsub (ε := (2 * c * (1/2:ℝ)^t).toNNReal)
      have h2to : Real.toNNReal 2 = (2:NNReal) := by
        apply NNReal.coe_injective
        rw [Real.coe_toNNReal 2 (by norm_num), NNReal.coe_ofNat]
      have hhalf : (2 * c * (1/2:ℝ)^t).toNNReal / 2 = (c * (1/2:ℝ)^t).toNNReal := by
        have h2 : (2 * c * (1/2:ℝ)^t).toNNReal = 2 * (c * (1/2:ℝ)^t).toNNReal := by
          rw [show 2 * c * (1/2:ℝ)^t = 2 * (c * (1/2:ℝ)^t) by ring,
            Real.toNNReal_mul (by norm_num : (0:ℝ) ≤ 2), h2to]
        rw [h2, mul_comm 2 ((c * (1/2:ℝ)^t).toNNReal), mul_div_assoc,
          div_self (by norm_num : (2:NNReal) ≠ 0), mul_one]
      rw [hhalf] at hmono
      have hmono' : ((Metric.coveringNumber ((2 * c * (1/2:ℝ)^t).toNNReal)
            (Set.range (curveVec Ψ H (S+1) z)) : ℕ∞) : ENNReal)
          ≤ ((Metric.coveringNumber (c * (1/2:ℝ)^t).toNNReal
              (Set.range (winCurveL2 Ψ H z)) : ℕ∞) : ENNReal) := by
        exact_mod_cast hmono
      refine hmono'.trans ?_
      have hpos : 0 < Metric.coveringNumber (c * (1/2:ℝ)^t).toNNReal
          (Set.range (winCurveL2 Ψ H z)) := by
        rw [Metric.coveringNumber_pos_iff]
        exact ⟨winCurveL2 Ψ H z ⟨scaleTj 0, scaleTj_pos 0⟩, Set.mem_range_self _⟩
      have hone : (1 : ENNReal) ≤
          ((Metric.coveringNumber (c * (1/2:ℝ)^t).toNNReal
            (Set.range (winCurveL2 Ψ H z)) : ℕ∞) : ENNReal) := by
        have h1 : (1:ℕ∞) ≤ Metric.coveringNumber (c * (1/2:ℝ)^t).toNNReal
            (Set.range (winCurveL2 Ψ H z)) :=
          Order.one_le_iff_ne_zero.mpr (ne_of_gt hpos)
        exact_mod_cast h1
      rw [winML2, tsub_add_cancel_of_le hone]
  have hnet' : ∀ t : ℕ, ∃ (τ : Fin (S+2) → Fin (S+2)) (m : ℕ),
      (1 ≤ t ∧ t ≤ S) →
        ((Finset.univ.image τ).card ≤ m ∧
          (∀ i : Fin (S+2), ∑ k : Fin K,
            ‖curvePt Ψ H (i:ℕ) z k - curvePt Ψ H ((τ i : Fin (S+2)):ℕ) z k‖ ^ 2
              ≤ (4 * c * (1/2:ℝ)^t)^2) ∧
          (m : ENNReal) ≤ winML2 Ψ H z (c * (1/2:ℝ)^t) + 1) := by
    intro t
    by_cases h : 1 ≤ t ∧ t ≤ S
    · obtain ⟨τ, m, h1, h2, h3⟩ := hnet t h.1 h.2
      exact ⟨τ, m, fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨id, 1, fun hc => absurd hc h⟩
  choose τ m hτm using hnet'
  let σ : ℕ → Fin (S+2) → Fin (S+2) := fun t => if t = 0 then (fun _ : Fin (S+2) => 0)
    else if t = S+1 then id else τ t
  let M : ℕ → ℕ := fun t => if t = 0 then 1 else if t = S+1 then S+2 else m t
  have hσ0 : σ 0 = fun _ : Fin (S+2) => 0 := by simp [σ]
  have hMS : M (S+1) = S+2 := by simp [M]
  have hσS : σ (S+1) = id := by simp [σ]
  have hσt : ∀ t, t ≠ 0 → t ≠ S+1 → σ t = τ t := by intro t h0 h2; simp [σ, h0, h2]
  have hMt : ∀ t, t ≠ 0 → t ≠ S+1 → M t = m t := by intro t h0 h2; simp [M, h0, h2]
  have hM0 : M 0 = 1 := by simp [M]
  refine ⟨σ, M, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `σ 0` is constant
    intro i
    rw [hσ0]
  · rw [hM0]
  · rw [hMS]
  · -- cardinality bound
    intro t ht
    by_cases h0 : t = 0
    · subst h0
      rw [hσ0, hM0, Finset.card_le_one]
      rintro a ha b hb
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at ha hb
      obtain ⟨a', -, rfl⟩ := ha
      obtain ⟨b', -, rfl⟩ := hb
      rfl
    · by_cases h2 : t = S+1
      · subst h2
        rw [hσS, hMS, Finset.image_id, Finset.card_univ, Fintype.card_fin]
      · rw [hσt t h0 h2, hMt t h0 h2]
        exact (hτm t ⟨by omega, by omega⟩).1
  · -- the net bound
    intro t ht i
    by_cases h0 : t = 0
    · subst h0
      rw [hσ0]
      have hbnd : ∀ (i : Fin (S+2)), ∑ k : Fin K, ‖curvePt Ψ H (i:ℕ) z k‖ ^ 2 ≤ c ^ 2 := by
        intro i
        refine le_trans (sum_norm_sq_curvePt_le Ψ H (S+1) z i) ?_
        rw [hcb]
      have hexp : ∀ k : Fin K,
          ‖curvePt Ψ H (i:ℕ) z k - curvePt Ψ H ((0:Fin (S+2)):ℕ) z k‖ ^ 2
          ≤ 2 * ‖curvePt Ψ H (i:ℕ) z k‖ ^ 2 + 2 * ‖curvePt Ψ H ((0:Fin (S+2)):ℕ) z k‖ ^ 2 := by
        intro k
        have h2 := pow_le_pow_left₀ (norm_nonneg _)
          (norm_sub_le (curvePt Ψ H (i:ℕ) z k) (curvePt Ψ H ((0:Fin (S+2)):ℕ) z k)) 2
        nlinarith [h2, sq_nonneg (‖curvePt Ψ H (i:ℕ) z k‖
          - ‖curvePt Ψ H ((0:Fin (S+2)):ℕ) z k‖)]
      calc ∑ k : Fin K, ‖curvePt Ψ H (i:ℕ) z k - curvePt Ψ H ((0:Fin (S+2)):ℕ) z k‖ ^ 2
          ≤ ∑ k : Fin K, (2 * ‖curvePt Ψ H (i:ℕ) z k‖ ^ 2
              + 2 * ‖curvePt Ψ H ((0:Fin (S+2)):ℕ) z k‖ ^ 2) :=
            Finset.sum_le_sum fun k _ => hexp k
        _ = 2 * ∑ k : Fin K, ‖curvePt Ψ H (i:ℕ) z k‖ ^ 2
              + 2 * ∑ k : Fin K, ‖curvePt Ψ H ((0:Fin (S+2)):ℕ) z k‖ ^ 2 := by
            rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
        _ ≤ 2 * c ^ 2 + 2 * c ^ 2 :=
            add_le_add (mul_le_mul_of_nonneg_left (hbnd i) (by norm_num))
              (mul_le_mul_of_nonneg_left (hbnd 0) (by norm_num))
        _ ≤ (4 * c * (1/2:ℝ)^0) ^ 2 := by
            norm_num
            nlinarith [sq_nonneg c]
    · by_cases h2 : t = S+1
      · subst h2
        rw [hσS]
        have hz : (∑ k : Fin K, ‖curvePt Ψ H (i:ℕ) z k - curvePt Ψ H (↑(id i) : ℕ) z k‖ ^ 2) = 0 := by
          refine Finset.sum_eq_zero fun k _ => ?_
          simp
        rw [hz]
        positivity
      · rw [hσt t h0 h2]
        exact (hτm t ⟨by omega, by omega⟩).2.1 i
  · -- the covering-number bound
    intro t ht1 ht2
    rw [hMt t ht1.ne' (by omega)]
    exact (hτm t ⟨ht1, by omega⟩).2.2


end

end Commons.Analysis.Fourier


open _root_.MeasureTheory Finset
open scoped BigOperators _root_.ENNReal _root_.Topology

namespace Commons.Analysis.Fourier

noncomputable section

variable {K : ℕ}

/-- `1 ≤ a + 1` in `ℝ≥0∞`. -/
private lemma one_le_add_one (a : ENNReal) : 1 ≤ a + 1 := by
  calc (1:ENNReal) = 0 + 1 := by simp
    _ ≤ a + 1 := add_le_add bot_le le_rfl

/-- The last dyadic term of the entropy sum is at most one. -/
private lemma dyadic_tail_le_one (K S : ℕ) :
    (1/2:ℝ)^(S+1) * Real.sqrt (min (K:ℝ) ((S:ℝ) + 3)) ≤ 1 := by
  have h4 : ∀ S : ℕ, S + 3 ≤ 4^(S+1) := by
    intro S
    induction S with
    | zero => norm_num
    | succ k ih =>
        have hstep : k + 1 + 3 ≤ 4 * (k + 3) := by omega
        calc k + 1 + 3 ≤ 4 * (k + 3) := hstep
          _ ≤ 4 * 4^(k+1) := Nat.mul_le_mul_left 4 ih
          _ = 4^(k+2) := by ring
  have hsqrt : Real.sqrt (min (K:ℝ) ((S:ℝ) + 3)) ≤ 2^(S+1) := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have h5 : min (K:ℝ) ((S:ℝ) + 3) ≤ (S:ℝ) + 3 := min_le_right _ _
    have h6 : ((S:ℝ) + 3) ≤ (4:ℝ)^(S+1) := by exact_mod_cast h4 S
    have h7 : ((4:ℝ)^(S+1)) = (2:ℝ)^(S+1) * 2^(S+1) := by
      have : (4:ℝ) = 2 * 2 := by norm_num
      rw [this, mul_pow]
    rw [sq]
    linarith [h5, h6, h7]
  calc (1/2:ℝ)^(S+1) * Real.sqrt (min (K:ℝ) ((S:ℝ) + 3))
      ≤ (1/2:ℝ)^(S+1) * 2^(S+1) := mul_le_mul_of_nonneg_left hsqrt (by positivity)
    _ = 1 := by rw [← mul_pow]; norm_num

/-- The per-`z` chain bound. -/
theorem chain_bound_at_z (Ψ : SchwartzMap ℝ ℂ) (lam : Fin K → ℝ)
    (hsep : ∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|) :
    ∃ C : ℝ, 0 < C ∧ ∀ (H : Fin K → ℝ → ℂ) (S : ℕ) (z : ℝ),
      ∫⁻ y in Set.Ioc (-z) (-z + 1),
        ENNReal.ofReal (⨆ i : Fin (S+2), ‖∑ k : Fin K,
          curvePt Ψ H (i:ℕ) z k * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖) ^ (2:ℝ)
      ≤ ENNReal.ofReal (C ^ 2) *
          (256 * (ENNReal.ofReal (curveRad Ψ H (S+1) z)) ^ (2:ℝ)
           + 16 * (∫⁻ r in Set.Ioi (0:ℝ), min (ENNReal.ofReal (Real.sqrt (K:ℝ)))
                    ((winML2 Ψ H z r) ^ ((1:ℝ)/2))) ^ (2:ℝ)) := by
  obtain ⟨Cch, hCchpos, hCch⟩ := chain_exp_sum_le_entropy_Ioc K lam hsep
  refine ⟨16 * (Cch + 1), by positivity, ?_⟩
  intro H S z
  set I : ENNReal := ∫⁻ r in Set.Ioi (0:ℝ), min (ENNReal.ofReal (Real.sqrt (K:ℝ)))
    ((winML2 Ψ H z r) ^ ((1:ℝ)/2)) with hI
  set c : ℝ := curveRad Ψ H (S+1) z with hc
  have hcle : 0 ≤ c := by rw [hc]; exact curveRad_nonneg Ψ H (S+1) z
  by_cases hc0 : c = 0
  · -- degenerate: all curve points vanish
    have hcurve0 : ∀ i : Fin (S+2), curveVec Ψ H (S+1) z i = 0 := by
      intro i
      have hle : ‖curveVec Ψ H (S+1) z i‖ ≤ 0 := by
        have h := norm_curveVec_le_curveRad Ψ H (S+1) z i
        rw [← hc] at h
        rw [hc0] at h
        exact h
      exact norm_eq_zero.mp (le_antisymm hle (norm_nonneg _))
    have hpt0 : ∀ (i : Fin (S+2)) (k : Fin K), curvePt Ψ H (i:ℕ) z k = 0 := by
      intro i k
      rw [← curveVec_eq_curvePt]
      simp [hcurve0 i]
    have hsup0 : ∀ y : ℝ, (⨆ i : Fin (S+2), ‖∑ k : Fin K,
        curvePt Ψ H (i:ℕ) z k * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖) = 0 := by
      intro y
      rw [show (fun i : Fin (S+2) => ‖∑ k : Fin K,
          curvePt Ψ H (i:ℕ) z k * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖)
          = fun _ => (0:ℝ) from funext fun i => by simp [hpt0 i]]
      simp
    have hLHS0 : ∫⁻ y in Set.Ioc (-z) (-z + 1),
        ENNReal.ofReal (⨆ i : Fin (S+2), ‖∑ k : Fin K,
          curvePt Ψ H (i:ℕ) z k * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖) ^ (2:ℝ)
        = 0 := by
      simp [hsup0]
    rw [hLHS0]
    exact bot_le
  · have hcpos : 0 < c := lt_of_le_of_ne hcle (Ne.symm hc0)
    set κ : ℝ := 2 * c with hκ
    have hκpos : 0 < κ := by rw [hκ]; positivity
    have hκne : (κ:ℂ) ≠ 0 := by
      rw [ne_eq, Complex.ofReal_eq_zero]; exact hκpos.ne'
    -- the normalised family
    set b : Fin (S+2) → Fin K → ℂ := fun i k => ((κ:ℂ))⁻¹ * curvePt Ψ H (i:ℕ) z k with hb
    have hb_eq : ∀ (i : Fin (S+2)) (k : Fin K), curvePt Ψ H (i:ℕ) z k = (κ:ℂ) * b i k := by
      intro i k
      rw [hb, ← mul_assoc, mul_inv_cancel₀ hκne, one_mul]
    -- norm bound for the normalised family
    have hbnorm : ∀ i : Fin (S+2), ∑ k : Fin K, ‖b i k‖ ^ 2 ≤ (1:ℝ) := by
      intro i
      have h1 : ∑ k : Fin K, ‖curvePt Ψ H (i:ℕ) z k‖ ^ 2 ≤ c ^ 2 := by
        refine le_trans (sum_norm_sq_curvePt_le Ψ H (S+1) z i) ?_
        rw [hc]
      have h2 : ∀ k : Fin K,
          ‖b i k‖ ^ 2 = (κ⁻¹) ^ 2 * ‖curvePt Ψ H (i:ℕ) z k‖ ^ 2 := by
        intro k
        rw [hb]
        simp only [norm_mul, norm_inv, Complex.norm_of_nonneg hκpos.le]
        ring
      calc ∑ k : Fin K, ‖b i k‖ ^ 2
          = (κ⁻¹) ^ 2 * ∑ k : Fin K, ‖curvePt Ψ H (i:ℕ) z k‖ ^ 2 := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun k _ => h2 k
        _ ≤ (κ⁻¹) ^ 2 * c ^ 2 := mul_le_mul_of_nonneg_left h1 (by positivity)
        _ ≤ 1 := by
            rw [hκ]
            have hcne : c ≠ 0 := hcpos.ne'
            field_simp
            nlinarith [hcpos]
    -- the nets
    obtain ⟨σ, M, hσ0, hM0, hMS, hcard, hnetUn, hMbound⟩ := exists_nets Ψ H S z c hcpos (by rw [hc])
    -- the normalised net hypothesis
    have hnet : ∀ t, t ≤ S+1 → ∀ i : Fin (S+2),
        ∑ k : Fin K, ‖b i k - b (σ t i) k‖ ^ 2 ≤ (2 * (1/2:ℝ)^t)^2 := by
      intro t ht i
      have h := hnetUn t ht i
      have h3 : ∀ k : Fin K,
          ‖b i k - b (σ t i) k‖ ^ 2 = (κ⁻¹) ^ 2 * ‖curvePt Ψ H (i:ℕ) z k
            - curvePt Ψ H ((σ t i : Fin (S+2)):ℕ) z k‖ ^ 2 := by
        intro k
        rw [hb]
        have hrw : ((κ:ℂ))⁻¹ * curvePt Ψ H (i:ℕ) z k
            - ((κ:ℂ))⁻¹ * curvePt Ψ H ((σ t i : Fin (S+2)):ℕ) z k
            = ((κ:ℂ))⁻¹ * (curvePt Ψ H (i:ℕ) z k
                - curvePt Ψ H ((σ t i : Fin (S+2)):ℕ) z k) := by ring
        rw [hrw, norm_mul, norm_inv, Complex.norm_of_nonneg hκpos.le]
        ring
      calc ∑ k : Fin K, ‖b i k - b (σ t i) k‖ ^ 2
          = (κ⁻¹) ^ 2 * ∑ k : Fin K, ‖curvePt Ψ H (i:ℕ) z k
              - curvePt Ψ H ((σ t i : Fin (S+2)):ℕ) z k‖ ^ 2 := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun k _ => h3 k
        _ ≤ (κ⁻¹) ^ 2 * (4 * c * (1/2:ℝ)^t) ^ 2 := mul_le_mul_of_nonneg_left h (by positivity)
        _ = (2 * (1/2:ℝ)^t) ^ 2 := by
            rw [hκ]
            have hcne : c ≠ 0 := hcpos.ne'
            field_simp
            ring
    -- the chain bound
    have hchain := hCch (S+1) (S+1) b σ M (-z) (by omega) hσ0 (by rw [hMS]) hcard hnet
    -- bounds on the two summands of the chain RHS
    have hbase : Real.sqrt (∑ k : Fin K, ‖b (σ 0 0) k‖ ^ 2) ≤ 1 := by
      rw [Real.sqrt_le_one]
      exact hbnorm (σ 0 0)
    have hdyadic : ∀ r : ℝ, winML2 Ψ H z r + 1 - 1 = winML2 Ψ H z r := by
      intro r
      exact ENNReal.add_sub_cancel_right (by norm_num : (1:ENNReal) ≠ ∞)
    have hsumE : ENNReal.ofReal (∑ t ∈ Finset.range (S+1),
        (1/2:ℝ)^t * Real.sqrt (min (K:ℝ) ((M t : ℝ) + 1)))
        ≤ ENNReal.ofReal c⁻¹ * (2 * I) + 4 := by
      have hanti : ∀ r r' : ℝ, 0 < r → r ≤ r' →
          (fun r => winML2 Ψ H z r + 1) r' ≤ (fun r => winML2 Ψ H z r + 1) r := by
        intro r r' hr hrr
        refine add_le_add ?_ le_rfl
        have h1 : r.toNNReal ≤ r'.toNNReal := Real.toNNReal_mono hrr
        have h2 := Metric.coveringNumber_anti (A := Set.range (winCurveL2 Ψ H z))
          (ε := r.toNNReal) (δ := r'.toNNReal) h1
        have h3 : ((Metric.coveringNumber r'.toNNReal (Set.range (winCurveL2 Ψ H z)) : ℕ∞) : ENNReal)
            ≤ ((Metric.coveringNumber r.toNNReal (Set.range (winCurveL2 Ψ H z)) : ℕ∞) : ENNReal) := by
          exact_mod_cast h2
        unfold winML2
        exact tsub_le_tsub_right h3 1
      have hE1 : ∀ r : ℝ, 0 < r → 1 ≤ (fun r => winML2 Ψ H z r + 1) r :=
        fun r _ => one_le_add_one _
      have hhyp : ∀ t : ℕ, ((if t ≤ S then M t else 1 : ℕ) : ENNReal)
          ≤ (fun r => winML2 Ψ H z r + 1) (c * (1/2:ℝ)^t) := by
        intro t
        show ((if t ≤ S then M t else 1 : ℕ) : ENNReal)
          ≤ winML2 Ψ H z (c * (1/2:ℝ)^t) + 1
        by_cases ht : t ≤ S
        · rw [if_pos ht]
          rcases Nat.eq_zero_or_pos t with h0 | hpos
          · subst h0
            rw [hM0]
            simpa using one_le_add_one (winML2 Ψ H z (c * (1/2:ℝ)^0))
          · exact hMbound t hpos (by omega)
        · rw [if_neg ht]
          simpa using one_le_add_one (winML2 Ψ H z (c * (1/2:ℝ)^t))
      have h := dyadic_sum_le_lintegral_entropy (fun r => winML2 Ψ H z r + 1) hanti hE1 K
        (fun t => if t ≤ S then M t else 1) hcpos (S+1) hhyp
      have hIeq : (∫⁻ r in Set.Ioi (0:ℝ), min (ENNReal.ofReal (Real.sqrt (K:ℝ)))
            ((winML2 Ψ H z r + 1 - 1) ^ ((1:ℝ)/2))) = I := by
        rw [hI]
        exact lintegral_congr fun r => by rw [hdyadic r]
      have hsum_eq : (∑ t ∈ Finset.range (S+1), (1/2:ℝ)^t
            * Real.sqrt (min (K:ℝ) (((if t ≤ S then M t else 1 : ℕ) : ℝ) + 1)))
          = ∑ t ∈ Finset.range (S+1), (1/2:ℝ)^t
            * Real.sqrt (min (K:ℝ) ((M t : ℝ) + 1)) := by
        refine Finset.sum_congr rfl fun t ht => ?_
        rw [if_pos (Nat.lt_succ_iff.mp (Finset.mem_range.mp ht))]
      rw [hsum_eq, hIeq] at h
      exact h
    have htailTerm : ENNReal.ofReal ((1/2:ℝ)^(S+1) * Real.sqrt (min (K:ℝ) ((M (S+1) : ℝ) + 1)))
        ≤ 1 := by
      rw [hMS]
      have : ((S + 2 : ℕ) : ℝ) + 1 = (S:ℝ) + 3 := by push_cast; ring
      rw [this]
      exact ENNReal.ofReal_le_one.mpr (dyadic_tail_le_one K S)
    have hsumTot : ENNReal.ofReal (∑ t ∈ Finset.range (S+2),
        (1/2:ℝ)^t * Real.sqrt (min (K:ℝ) ((M t : ℝ) + 1)))
        ≤ ENNReal.ofReal c⁻¹ * (2 * I) + 5 := by
      rw [Finset.sum_range_succ, ENNReal.ofReal_add (by positivity) (by positivity)]
      refine (add_le_add hsumE htailTerm).trans (le_of_eq ?_)
      ring
    -- the sup comparison: the un-normalised sup is `κ` times the normalised one
    have hsup : ∀ y : ℝ, ENNReal.ofReal (⨆ i : Fin (S+2), ‖∑ k : Fin K,
        curvePt Ψ H (i:ℕ) z k * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖) ^ (2:ℝ)
        ≤ (ENNReal.ofReal κ) ^ 2 * ENNReal.ofReal (⨆ i : Fin (S+2), ‖∑ k : Fin K,
            b i k * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖) ^ (2:ℝ) := by
      intro y
      have h1 : (⨆ i : Fin (S+2), ‖∑ k : Fin K,
            curvePt Ψ H (i:ℕ) z k * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖)
          ≤ κ * (⨆ i : Fin (S+2), ‖∑ k : Fin K,
            b i k * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖) := by
        refine ciSup_le fun i => ?_
        have h2 : (∑ k : Fin K, curvePt Ψ H (i:ℕ) z k
              * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ)))
            = (κ:ℂ) * ∑ k : Fin K, b i k * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ)) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by rw [hb_eq i k]; ring
        rw [h2, norm_mul, Complex.norm_of_nonneg hκpos.le]
        have hbdd : BddAbove (Set.range (fun i : Fin (S+2) => ‖∑ k : Fin K,
            b i k * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖)) :=
          (Set.finite_range _).bddAbove
        exact mul_le_mul_of_nonneg_left (le_ciSup hbdd i) hκpos.le
      calc ENNReal.ofReal (⨆ i : Fin (S+2), ‖∑ k : Fin K,
            curvePt Ψ H (i:ℕ) z k * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖) ^ (2:ℝ)
          ≤ ENNReal.ofReal (κ * (⨆ i : Fin (S+2), ‖∑ k : Fin K,
              b i k * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖)) ^ (2:ℝ) :=
            ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal h1) (by norm_num)
        _ = (ENNReal.ofReal κ) ^ 2 * ENNReal.ofReal (⨆ i : Fin (S+2), ‖∑ k : Fin K,
              b i k * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖) ^ (2:ℝ) := by
            rw [ENNReal.ofReal_mul hκpos.le]
            rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast,
              ENNReal.rpow_natCast]
            ring
    -- integrability of the normalised integrand
    have hmeas : AEMeasurable (fun y : ℝ => ENNReal.ofReal (⨆ i : Fin (S+2), ‖∑ k : Fin K,
        b i k * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖) ^ (2:ℝ))
        (volume.restrict (Set.Ioc (-z) (-z+1))) := by
      refine (AEMeasurable.pow_const ?_ 2).mono_measure Measure.restrict_le_self
      refine ENNReal.continuous_ofReal.measurable.comp_aemeasurable ?_
      refine AEMeasurable.iSup fun i => ?_
      exact (by fun_prop : Continuous (fun y : ℝ => ‖∑ k : Fin K,
        b i k * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖)).aemeasurable
    -- integrate the sup comparison against the constant `(ofReal κ)²`
    have hLHSle : ∫⁻ y in Set.Ioc (-z) (-z + 1),
        ENNReal.ofReal (⨆ i : Fin (S+2), ‖∑ k : Fin K,
          curvePt Ψ H (i:ℕ) z k * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖) ^ (2:ℝ)
        ≤ (ENNReal.ofReal κ) ^ 2 * ∫⁻ y in Set.Ioc (-z) (-z + 1),
            ENNReal.ofReal (⨆ i : Fin (S+2), ‖∑ k : Fin K,
              b i k * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖) ^ (2:ℝ) :=
      calc ∫⁻ y in Set.Ioc (-z) (-z + 1),
            ENNReal.ofReal (⨆ i : Fin (S+2), ‖∑ k : Fin K,
              curvePt Ψ H (i:ℕ) z k * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖) ^ (2:ℝ)
          ≤ ∫⁻ y in Set.Ioc (-z) (-z + 1), (ENNReal.ofReal κ) ^ 2
              * ENNReal.ofReal (⨆ i : Fin (S+2), ‖∑ k : Fin K,
                b i k * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖) ^ (2:ℝ) :=
            lintegral_mono hsup
        _ = (ENNReal.ofReal κ) ^ 2 * ∫⁻ y in Set.Ioc (-z) (-z + 1),
              ENNReal.ofReal (⨆ i : Fin (S+2), ‖∑ k : Fin K,
                b i k * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖) ^ (2:ℝ) :=
            MeasureTheory.lintegral_const_mul'' _ hmeas
    -- the two bounds on the summands of the chain RHS, inside the chain bound
    have hbase' : ENNReal.ofReal (Real.sqrt (∑ k : Fin K, ‖b (σ 0 0) k‖ ^ 2)) ≤ 1 :=
      ENNReal.ofReal_le_one.mpr hbase
    have hSumM : ENNReal.ofReal (∑ t ∈ Finset.range (S+2),
        (1/2:ℝ)^t * Real.sqrt (min (K:ℝ) ((M t : ℝ) + 1)))
        ≤ ENNReal.ofReal c⁻¹ * (2 * I) + 5 := hsumTot
    have hinner : ENNReal.ofReal ((Cch * (Real.sqrt (∑ k : Fin K, ‖b (σ 0 0) k‖ ^ 2)
          + ∑ t ∈ Finset.range (S+2), (1/2:ℝ)^t * Real.sqrt (min (K:ℝ) ((M t : ℝ) + 1)))) ^ 2)
        ≤ (ENNReal.ofReal Cch * (1 + (ENNReal.ofReal c⁻¹ * (2 * I) + 5))) ^ (2:ℝ) := by
      rw [ENNReal.ofReal_pow (mul_nonneg hCchpos.le
          (add_nonneg (Real.sqrt_nonneg _)
            (Finset.sum_nonneg fun t _ => mul_nonneg
              (pow_nonneg (by norm_num : (0:ℝ) ≤ 1/2) t) (Real.sqrt_nonneg _)))),
        show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast]
      refine pow_le_pow_left₀ bot_le ?_ 2
      rw [ENNReal.ofReal_mul hCchpos.le]
      have hfac : ENNReal.ofReal (Real.sqrt (∑ k : Fin K, ‖b (σ 0 0) k‖ ^ 2)
            + ∑ i ∈ Finset.range (S+2), (1/2:ℝ)^i * Real.sqrt (min (K:ℝ) ((M i : ℝ) + 1)))
          ≤ 1 + (ENNReal.ofReal c⁻¹ * (2 * I) + 5) := by
        rw [ENNReal.ofReal_add (Real.sqrt_nonneg _)
          (Finset.sum_nonneg fun t _ => mul_nonneg
            (pow_nonneg (by norm_num : (0:ℝ) ≤ 1/2) t) (Real.sqrt_nonneg _))]
        exact add_le_add hbase' hSumM
      exact mul_le_mul_of_nonneg_left hfac bot_le
    -- **first identity**: `ofReal κ * ofReal c⁻¹ = 2`, since `κ * c⁻¹ = 2`.
    have hκc : ENNReal.ofReal κ * ENNReal.ofReal c⁻¹ = 2 := by
      rw [← ENNReal.ofReal_mul hκpos.le,
        show κ * c⁻¹ = 2 from by rw [hκ]; field_simp]
      norm_num
    -- the squared bound for `ofReal κ · Z`
    have hsq : ((ENNReal.ofReal κ) ^ 2) *
          (ENNReal.ofReal Cch * (1 + (ENNReal.ofReal c⁻¹ * (2 * I) + 5))) ^ (2:ℝ)
        ≤ ENNReal.ofReal ((16 * (Cch + 1)) ^ 2) *
          (256 * (ENNReal.ofReal c) ^ (2:ℝ) + 16 * I ^ (2:ℝ)) := by
      -- Step A: `ofReal κ * Z ≤ 6 * ofReal κ * ofReal Cch + 4 * ofReal Cch * I`
      have hZ : ENNReal.ofReal κ * (ENNReal.ofReal Cch
            * (1 + (ENNReal.ofReal c⁻¹ * (2 * I) + 5)))
          ≤ 6 * (ENNReal.ofReal κ * ENNReal.ofReal Cch) + 4 * ENNReal.ofReal Cch * I := by
        have h2 : (ENNReal.ofReal κ * ENNReal.ofReal Cch * ENNReal.ofReal c⁻¹)
            = 2 * ENNReal.ofReal Cch := by
          rw [mul_assoc, mul_comm (ENNReal.ofReal Cch) (ENNReal.ofReal c⁻¹), ← mul_assoc, hκc]
        have heq : ENNReal.ofReal κ * (ENNReal.ofReal Cch
              * (1 + (ENNReal.ofReal c⁻¹ * (2 * I) + 5)))
            = 6 * (ENNReal.ofReal κ * ENNReal.ofReal Cch) + 4 * ENNReal.ofReal Cch * I := by
          calc ENNReal.ofReal κ * (ENNReal.ofReal Cch
                * (1 + (ENNReal.ofReal c⁻¹ * (2 * I) + 5)))
              = ENNReal.ofReal κ * ENNReal.ofReal Cch
                + (ENNReal.ofReal κ * ENNReal.ofReal Cch * ENNReal.ofReal c⁻¹) * (2 * I)
                + 5 * (ENNReal.ofReal κ * ENNReal.ofReal Cch) := by ring
            _ = 6 * (ENNReal.ofReal κ * ENNReal.ofReal Cch) + 4 * ENNReal.ofReal Cch * I := by
                rw [h2]; ring
        rw [heq]
      -- Step B: `(ofReal κ)² * Z² = (ofReal κ * Z)²`
      have hB : ((ENNReal.ofReal κ) ^ 2) * (ENNReal.ofReal Cch
            * (1 + (ENNReal.ofReal c⁻¹ * (2 * I) + 5))) ^ (2:ℝ)
          = (ENNReal.ofReal κ * (ENNReal.ofReal Cch
              * (1 + (ENNReal.ofReal c⁻¹ * (2 * I) + 5)))) ^ (2:ℝ) := by
        rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num]
        simp only [ENNReal.rpow_natCast]
        rw [mul_pow]
        ring_nf
      -- Step C: the square of the bound
      have hC : (6 * (ENNReal.ofReal κ * ENNReal.ofReal Cch) + 4 * ENNReal.ofReal Cch * I) ^ (2:ℝ)
          ≤ 288 * (ENNReal.ofReal c) ^ (2:ℝ) * (ENNReal.ofReal Cch) ^ (2:ℝ)
            + 32 * (ENNReal.ofReal Cch) ^ (2:ℝ) * I ^ (2:ℝ) := by
        have h2 : (ENNReal.ofReal κ) ^ (2:ℝ) = 4 * (ENNReal.ofReal c) ^ (2:ℝ) := by
          rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num]
          simp only [ENNReal.rpow_natCast]
          rw [← ENNReal.ofReal_pow hκpos.le, ← ENNReal.ofReal_pow hcpos.le, hκ,
            show (2 * c) ^ 2 = 4 * c ^ 2 by ring,
            ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4),
            show ENNReal.ofReal (4:ℝ) = 4 from by norm_num]
        have hA : (6 * (ENNReal.ofReal κ * ENNReal.ofReal Cch)) ^ (2:ℝ)
            = 36 * ((ENNReal.ofReal κ) ^ (2:ℝ) * (ENNReal.ofReal Cch) ^ (2:ℝ)) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (z := (2:ℝ)) (show (0:ℝ) ≤ (2:ℝ) by norm_num),
            ENNReal.mul_rpow_of_nonneg _ _ (z := (2:ℝ)) (show (0:ℝ) ≤ (2:ℝ) by norm_num),
            show (6:ENNReal) ^ (2:ℝ) = 36 from by
              rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast]; norm_num]
        have hB2 : (4 * ENNReal.ofReal Cch * I) ^ (2:ℝ)
            = 16 * ((ENNReal.ofReal Cch) ^ (2:ℝ) * I ^ (2:ℝ)) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (z := (2:ℝ)) (show (0:ℝ) ≤ (2:ℝ) by norm_num),
            ENNReal.mul_rpow_of_nonneg _ _ (z := (2:ℝ)) (show (0:ℝ) ≤ (2:ℝ) by norm_num),
            show (4:ENNReal) ^ (2:ℝ) = 16 from by
              rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast]; norm_num]
          ring_nf
        calc (6 * (ENNReal.ofReal κ * ENNReal.ofReal Cch) + 4 * ENNReal.ofReal Cch * I) ^ (2:ℝ)
            ≤ 2 * (6 * (ENNReal.ofReal κ * ENNReal.ofReal Cch)) ^ (2:ℝ)
              + 2 * (4 * ENNReal.ofReal Cch * I) ^ (2:ℝ) :=
              Commons.Analysis.ENNReal.add_rpow_two_le_two_mul _ _
          _ = 2 * (36 * ((ENNReal.ofReal κ) ^ (2:ℝ) * (ENNReal.ofReal Cch) ^ (2:ℝ)))
              + 2 * (16 * ((ENNReal.ofReal Cch) ^ (2:ℝ) * I ^ (2:ℝ))) := by rw [hA, hB2]
          _ = 288 * (ENNReal.ofReal c) ^ (2:ℝ) * (ENNReal.ofReal Cch) ^ (2:ℝ)
              + 32 * (ENNReal.ofReal Cch) ^ (2:ℝ) * I ^ (2:ℝ) := by
              rw [h2]; ring_nf
      -- Step D: the constant comparison
      have hD : 288 * (ENNReal.ofReal c) ^ (2:ℝ) * (ENNReal.ofReal Cch) ^ (2:ℝ)
            + 32 * (ENNReal.ofReal Cch) ^ (2:ℝ) * I ^ (2:ℝ)
          ≤ ENNReal.ofReal ((16 * (Cch + 1)) ^ 2) *
            (256 * (ENNReal.ofReal c) ^ (2:ℝ) + 16 * I ^ (2:ℝ)) := by
        have h4 : (ENNReal.ofReal Cch) ^ (2:ℝ) ≤ ENNReal.ofReal ((Cch + 1) ^ 2) := by
          rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast,
            ← ENNReal.ofReal_pow hCchpos.le]
          exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hCchpos.le
            (le_trans (le_refl Cch) (le_add_of_nonneg_right (by norm_num : (0:ℝ) ≤ 1))) 2)
        have hC' : ENNReal.ofReal ((16 * (Cch + 1)) ^ 2)
            = 256 * ENNReal.ofReal ((Cch + 1) ^ 2) := by
          rw [show (16 * (Cch + 1)) ^ 2 = 256 * (Cch + 1) ^ 2 by ring,
            ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 256), ENNReal.ofReal_pow (by positivity)]
          norm_num
        rw [hC']
        refine (add_le_add (mul_le_mul le_rfl h4 (bot_le : (0:ENNReal) ≤ _) (bot_le : (0:ENNReal) ≤ _))
          (mul_le_mul (mul_le_mul le_rfl h4 (bot_le : (0:ENNReal) ≤ _) (bot_le : (0:ENNReal) ≤ _)) le_rfl (bot_le : (0:ENNReal) ≤ _) (bot_le : (0:ENNReal) ≤ _))).trans ?_
        rw [mul_add]
        refine add_le_add ?_ ?_
        · calc 288 * (ENNReal.ofReal c) ^ (2:ℝ) * ENNReal.ofReal ((Cch + 1) ^ 2)
              ≤ 65536 * (ENNReal.ofReal c) ^ (2:ℝ) * ENNReal.ofReal ((Cch + 1) ^ 2) :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by norm_num) bot_le) bot_le
            _ = 256 * ENNReal.ofReal ((Cch + 1) ^ 2) * (256 * (ENNReal.ofReal c) ^ (2:ℝ)) := by ring
        · calc 32 * ENNReal.ofReal ((Cch + 1) ^ 2) * I ^ (2:ℝ)
              ≤ 4096 * ENNReal.ofReal ((Cch + 1) ^ 2) * I ^ (2:ℝ) :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by norm_num) bot_le) bot_le
            _ = 256 * ENNReal.ofReal ((Cch + 1) ^ 2) * (16 * I ^ (2:ℝ)) := by ring
      calc ((ENNReal.ofReal κ) ^ 2) * (ENNReal.ofReal Cch
            * (1 + (ENNReal.ofReal c⁻¹ * (2 * I) + 5))) ^ (2:ℝ)
          = (ENNReal.ofReal κ * (ENNReal.ofReal Cch
              * (1 + (ENNReal.ofReal c⁻¹ * (2 * I) + 5)))) ^ (2:ℝ) := hB
        _ ≤ (6 * (ENNReal.ofReal κ * ENNReal.ofReal Cch) + 4 * ENNReal.ofReal Cch * I) ^ (2:ℝ) :=
            ENNReal.rpow_le_rpow hZ (show (0:ℝ) ≤ (2:ℝ) by norm_num)
        _ ≤ 288 * (ENNReal.ofReal c) ^ (2:ℝ) * (ENNReal.ofReal Cch) ^ (2:ℝ)
              + 32 * (ENNReal.ofReal Cch) ^ (2:ℝ) * I ^ (2:ℝ) := hC
        _ ≤ ENNReal.ofReal ((16 * (Cch + 1)) ^ 2) *
              (256 * (ENNReal.ofReal c) ^ (2:ℝ) + 16 * I ^ (2:ℝ)) := hD
    -- The chain bound with the exponent written as an rpow (matching the goal's integrand).
    -- NOTE (hard-won): `simpa only [...] using hchain` CANNOT descend into the integrand's lambda
    -- to change the exponent; restate as an explicit `(∫ …) = (∫ …)` and prove it with
    -- `congr 1`, `funext y`, then the `rpow_natCast` rewrite.  Same for any ℕ-vs-ℝ exponent
    -- mismatch under an integral.
    have hchainR : ∫⁻ y in Set.Ioc (-z) (-z + 1), ENNReal.ofReal (⨆ i : Fin (S+2), ‖∑ k : Fin K,
          b i k * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖) ^ (2:ℝ)
        ≤ ENNReal.ofReal ((Cch * (Real.sqrt (∑ k : Fin K, ‖b (σ 0 0) k‖ ^ 2)
            + ∑ t ∈ Finset.range (S+2), (1/2:ℝ)^t
                * Real.sqrt (min (K:ℝ) ((M t : ℝ) + 1)))) ^ 2) := by
      have h1 : (∫⁻ y in Set.Ioc (-z) (-z + 1), ENNReal.ofReal (⨆ i : Fin (S+2), ‖∑ k : Fin K,
            b i k * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖) ^ (2:ℝ))
          = (∫⁻ y in Set.Ioc (-z) (-z + 1), ENNReal.ofReal (⨆ i : Fin (S+2), ‖∑ k : Fin K,
            b i k * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖) ^ (2:ℕ)) := by
        congr 1
        funext y
        rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast]
      rw [h1]
      exact hchain
    -- final assembly
    calc ∫⁻ y in Set.Ioc (-z) (-z + 1),
          ENNReal.ofReal (⨆ i : Fin (S+2), ‖∑ k : Fin K,
            curvePt Ψ H (i:ℕ) z k * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖) ^ (2:ℝ)
        ≤ (ENNReal.ofReal κ) ^ 2 * ∫⁻ y in Set.Ioc (-z) (-z + 1),
            ENNReal.ofReal (⨆ i : Fin (S+2), ‖∑ k : Fin K,
              b i k * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖) ^ (2:ℝ) := hLHSle
      _ ≤ (ENNReal.ofReal κ) ^ 2 * ENNReal.ofReal ((Cch * (Real.sqrt (∑ k : Fin K,
            ‖b (σ 0 0) k‖ ^ 2) + ∑ t ∈ Finset.range (S+2),
              (1/2:ℝ)^t * Real.sqrt (min (K:ℝ) ((M t : ℝ) + 1)))) ^ 2) :=
           mul_le_mul le_rfl hchainR (bot_le : (0:ENNReal) ≤ _) (bot_le : (0:ENNReal) ≤ _)
      _ ≤ (ENNReal.ofReal κ) ^ 2 * (ENNReal.ofReal Cch
            * (1 + (ENNReal.ofReal c⁻¹ * (2 * I) + 5))) ^ (2:ℝ) :=
          mul_le_mul le_rfl hinner (bot_le : (0:ENNReal) ≤ _) (bot_le : (0:ENNReal) ≤ _)
      _ ≤ ENNReal.ofReal ((16 * (Cch + 1)) ^ 2) *
          (256 * (ENNReal.ofReal c) ^ (2:ℝ) + 16 * I ^ (2:ℝ)) := hsq
      _ = ENNReal.ofReal ((16 * (Cch + 1)) ^ 2) *
          (256 * (ENNReal.ofReal (curveRad Ψ H (S+1) z)) ^ (2:ℝ)
           + 16 * (∫⁻ r in Set.Ioi (0:ℝ), min (ENNReal.ofReal (Real.sqrt (K:ℝ)))
                    ((winML2 Ψ H z r) ^ ((1:ℝ)/2))) ^ (2:ℝ)) := by rw [hc, hI]

end

end Commons.Analysis.Fourier

open scoped _root_.ENNReal
open _root_.MeasureTheory

namespace Commons.Analysis.Measure

/-- From an integrable bound on an interval, one point where the value is small. -/
theorem exists_le_of_lintegral_le (F : ℝ → ENNReal) (hF : Measurable F)
    {a b : ℝ} (hab : a < b) {K : ENNReal}
    (hint : ∫⁻ x in Set.Ioo a b, F x ∂(volume : Measure ℝ) ≤ K) (hKtop : K ≠ ⊤) :
    ∃ y ∈ Set.Ioo a b, ENNReal.ofReal (b - a) * F y ≤ (K + K) := by
  by_contra h
  push_neg at h
  have hvol : (volume : Measure ℝ) (Set.Ioo a b) = ENNReal.ofReal (b - a) := Real.volume_Ioo
  have hvolne0 : (volume : Measure ℝ) (Set.Ioo a b) ≠ 0 := by
    rw [hvol]; exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)).ne'
  have hvollt : (volume : Measure ℝ) (Set.Ioo a b) ≠ ⊤ := by
    rw [hvol]; exact ENNReal.ofReal_ne_top
  have hlow : (volume : Measure ℝ) (Set.Ioo a b) * ((K + K) / (volume (Set.Ioo a b)))
      ≤ ∫⁻ x in Set.Ioo a b, F x ∂(volume : Measure ℝ) := by
    calc (volume : Measure ℝ) (Set.Ioo a b) * ((K + K) / (volume (Set.Ioo a b)))
        = ∫⁻ x in Set.Ioo a b, (K + K) / (volume (Set.Ioo a b)) ∂(volume : Measure ℝ) :=
          (by rw [MeasureTheory.setLIntegral_const (μ := volume) (Set.Ioo a b)
              ((K + K) / (volume (Set.Ioo a b))), mul_comm])
      _ ≤ ∫⁻ x in Set.Ioo a b, F x ∂(volume : Measure ℝ) := by
          refine setLIntegral_mono' measurableSet_Ioo fun y hy => ?_
          rw [ENNReal.div_le_iff_le_mul (Or.inl hvolne0) (Or.inl hvollt)]
          rw [mul_comm]
          exact le_of_lt (by simpa only [hvol, mul_comm] using h y hy)
  have hK2 : K + K ≤ K := by
    refine le_trans ?_ hint
    calc K + K = (volume : Measure ℝ) (Set.Ioo a b) * ((K + K) / (volume (Set.Ioo a b))) :=
          (ENNReal.mul_div_cancel hvolne0 hvollt).symm
      _ ≤ _ := hlow
  have hK0 : K = 0 := by
    by_contra h0
    exact absurd hK2 (not_le.mpr (ENNReal.lt_add_right hKtop h0))
  subst hK0
  have hF0 : ∀ᵐ x ∂((volume : Measure ℝ).restrict (Set.Ioo a b)), F x = 0 := by
    refine (MeasureTheory.lintegral_eq_zero_iff' hF.aemeasurable).mp ?_
    simpa using hint
  have hzero : (volume : Measure ℝ) ({y : ℝ | F y ≠ 0} ∩ Set.Ioo a b) = 0 := by
    have h1 := MeasureTheory.ae_iff.mp hF0
    have hmeas : MeasurableSet {y : ℝ | F y ≠ 0} := (hF (measurableSet_singleton 0)).compl
    rw [Measure.restrict_apply hmeas] at h1
    exact h1
  have hsub : Set.Ioo a b ⊆ {y : ℝ | F y ≠ 0} ∩ Set.Ioo a b := by
    intro y hy
    refine ⟨?_, hy⟩
    have hh := h y hy
    simp only [zero_add] at hh
    intro hzy
    rw [hzy, mul_zero] at hh
    exact lt_irrefl _ hh
  exact hvolne0 (le_antisymm (by rw [← hzero]; exact measure_mono hsub) bot_le)

end Commons.Analysis.Measure

/-- The same as `exists_le_of_lintegral_le`, with a.e.-measurability instead of measurability. -/
theorem exists_le_of_lintegral_le_ae (F : ℝ → ENNReal) (hF : AEMeasurable F (volume : Measure ℝ))
    {a b : ℝ} (hab : a < b) {K : ENNReal}
    (hint : ∫⁻ x in Set.Ioo a b, F x ∂(volume : Measure ℝ) ≤ K) (hKtop : K ≠ ⊤) :
    ∃ y ∈ Set.Ioo a b, ENNReal.ofReal (b - a) * F y ≤ (K + K) := by
  by_contra h
  push_neg at h
  have hvol : (volume : Measure ℝ) (Set.Ioo a b) = ENNReal.ofReal (b - a) := Real.volume_Ioo
  have hvolne0 : (volume : Measure ℝ) (Set.Ioo a b) ≠ 0 := by
    rw [hvol]; exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)).ne'
  have hvollt : (volume : Measure ℝ) (Set.Ioo a b) ≠ ⊤ := by
    rw [hvol]; exact ENNReal.ofReal_ne_top
  have hlow : (volume : Measure ℝ) (Set.Ioo a b) * ((K + K) / (volume (Set.Ioo a b)))
      ≤ ∫⁻ x in Set.Ioo a b, F x ∂(volume : Measure ℝ) := by
    calc (volume : Measure ℝ) (Set.Ioo a b) * ((K + K) / (volume (Set.Ioo a b)))
        = ∫⁻ x in Set.Ioo a b, (K + K) / (volume (Set.Ioo a b)) ∂(volume : Measure ℝ) :=
          (by rw [MeasureTheory.setLIntegral_const (μ := volume) (Set.Ioo a b)
              ((K + K) / (volume (Set.Ioo a b))), mul_comm])
      _ ≤ ∫⁻ x in Set.Ioo a b, F x ∂(volume : Measure ℝ) := by
          refine setLIntegral_mono' measurableSet_Ioo fun y hy => ?_
          rw [ENNReal.div_le_iff_le_mul (Or.inl hvolne0) (Or.inl hvollt)]
          rw [mul_comm]
          exact le_of_lt (by simpa only [hvol, mul_comm] using h y hy)
  have hK2 : K + K ≤ K := by
    refine le_trans ?_ hint
    calc K + K = (volume : Measure ℝ) (Set.Ioo a b) * ((K + K) / (volume (Set.Ioo a b))) :=
          (ENNReal.mul_div_cancel hvolne0 hvollt).symm
      _ ≤ _ := hlow
  have hK0 : K = 0 := by
    by_contra h0
    exact absurd hK2 (not_le.mpr (ENNReal.lt_add_right hKtop h0))
  subst hK0
  have hF0 : ∀ᵐ x ∂((volume : Measure ℝ).restrict (Set.Ioo a b)), F x = 0 := by
    refine (MeasureTheory.lintegral_eq_zero_iff' (hF.mono_measure Measure.restrict_le_self)).mp ?_
    simpa using hint
  have hzero : ((volume : Measure ℝ).restrict (Set.Ioo a b)) {y : ℝ | F y ≠ 0} = 0 :=
    MeasureTheory.ae_iff.mp hF0
  have hsub : Set.Ioo a b ⊆ {y : ℝ | F y ≠ 0} := by
    intro y hy
    have hh := h y hy
    simp only [zero_add] at hh
    intro hzy
    rw [hzy, mul_zero] at hh
    exact lt_irrefl _ hh
  have hzero' : (volume : Measure ℝ) (Set.Ioo a b) ≤ 0 := by
    calc (volume : Measure ℝ) (Set.Ioo a b)
        = ((volume : Measure ℝ).restrict (Set.Ioo a b)) (Set.Ioo a b) :=
          (Measure.restrict_apply_self _ _).symm
      _ ≤ ((volume : Measure ℝ).restrict (Set.Ioo a b)) {y : ℝ | F y ≠ 0} :=
          measure_mono hsub
      _ = 0 := hzero
  exact hvolne0 (le_antisymm hzero' bot_le)


open _root_.MeasureTheory Finset
open scoped BigOperators _root_.ENNReal _root_.Topology

namespace Commons.Analysis.Fourier

noncomputable section

variable {K : ℕ}

/-!
# The Tonelli / `z`-integration step of Bourgain's smooth-window estimate

Starting from `chain_bound_at_z` (the per-`z` chained entropy bound) we integrate in `z`.  The
plan (see `STATUS_entropy_step.md`):

1. `bandMaxTr Ψ lam H S y` is the maximal function of the translate `T_y H` with the inner sup
   truncated at level `S`; by `bandMax_translate` (framework) and the phase identity
   `e^{Iλy}·e^{-Iλz} = e^{Iλ(y-z)}` it equals the `chain_bound_at_z` integrand with `y - z`.
2. Tonelli in `(y,z)` plus the range inclusion `(0, 9/10) - z ⊆ (-z, 1-z)` gives
   `∫_{y∈(0,9/10)} bandMaxTr y dy ≤ ∫_z (chain bound at z)`.
3. The `z`-integral of the chain bound is finite: `∫_z (curveRad)² ≤ ∫_z (winFL2)²` (the
   sup-norm/dilation bound extracted from `bourgain_entropy_integral_l2_l2vec`) and
   `∫_z I(z)²` is the deep input `bourgain_entropy_integral_l2_l2vec` itself
   (`I(z) = ∫_r min (√K) (winML2 Ψ H z r)^{1/2}`), with `bandSq` on the right.
4. `exists_le_of_lintegral_le` (proved in `Submission/Work/Analysis/Measure/`) then selects a
   single `y ∈ (0, 9/10)` with `ofReal (9/10) * bandMaxTr y ≤ 2 K₀`.
-/

/-- The (truncated) maximal function of the translate `T_y H`, as a function of the shift `y`. -/
noncomputable def bandMaxTr (Ψ : SchwartzMap ℝ ℂ) (lam : Fin K → ℝ) (H : Fin K → ℝ → ℂ)
    (S : ℕ) (y : ℝ) : ENNReal :=
  ∫⁻ z, (⨆ i : Fin (S+2), ‖∑ k : Fin K, curvePt Ψ H (i:ℕ) z k
    * Complex.exp (Complex.I * (lam k : ℂ) * ((y - z : ℝ) : ℂ))‖ₑ) ^ (2:ℝ)

/-- The same quantity written with the phase split off, i.e. the form produced by
`bandMax_translate`. -/
lemma bandMaxTr_eq (Ψ : SchwartzMap ℝ ℂ) (lam : Fin K → ℝ) (H : Fin K → ℝ → ℂ)
    (S : ℕ) (y : ℝ) :
    bandMaxTr Ψ lam H S y
      = ∫⁻ z, (⨆ i : Fin (S+2), ‖∑ k : Fin K,
          Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ)) * curvePtPh Ψ lam H (i:ℕ) z k‖ₑ) ^ (2:ℝ) := by
  unfold bandMaxTr
  refine lintegral_congr fun z => ?_
  have h : (fun i : Fin (S+2) => ‖∑ k : Fin K, curvePt Ψ H (i:ℕ) z k
        * Complex.exp (Complex.I * (lam k : ℂ) * ((y - z : ℝ) : ℂ))‖ₑ)
      = fun i : Fin (S+2) => ‖∑ k : Fin K,
          Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ)) * curvePtPh Ψ lam H (i:ℕ) z k‖ₑ := by
    funext i
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    unfold curvePtPh
    rw [show Complex.exp (Complex.I * (lam k : ℂ) * ((y - z : ℝ) : ℂ))
        = Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))
          * Complex.exp (-(Complex.I * (lam k : ℂ) * (z : ℂ))) from by
      rw [← Complex.exp_add]; congr 1; push_cast; ring]
    ring
  rw [h]

lemma iSup_enorm_eq_ofReal_iSup_norm {ι : Type*} [Fintype ι] [Nonempty ι] (f : ι → ℂ) :
    (⨆ i, ‖f i‖ₑ) = ENNReal.ofReal (⨆ i, ‖f i‖) := by
  have h1 : ∀ i : ι, ‖f i‖ₑ = ENNReal.ofReal ‖f i‖ := fun i => Commons.Analysis.Fourier.BoundaryLayer.enorm_eq_ofReal_norm _
  have hbdd : BddAbove (Set.range fun i : ι => ‖f i‖) := (Set.finite_range _).bddAbove
  rw [show (⨆ i, ‖f i‖ₑ) = ⨆ i, ENNReal.ofReal (‖f i‖) from by simp only [h1]]
  refine le_antisymm ?_ ?_
  · refine ciSup_le fun i => ENNReal.ofReal_le_ofReal (le_ciSup hbdd i)
  · obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image (Finset.univ : Finset ι) (fun i : ι => ‖f i‖)
      Finset.univ_nonempty
    have hsup : (⨆ i, ‖f i‖) = ‖f i₀‖ :=
      le_antisymm (ciSup_le fun i => hi₀ i (Finset.mem_univ i)) (le_ciSup hbdd i₀)
    rw [hsup]
    exact le_iSup (fun i : ι => ENNReal.ofReal ‖f i‖) i₀

end

end Commons.Analysis.Fourier


open _root_.MeasureTheory Finset
open scoped BigOperators _root_.ENNReal _root_.Topology

namespace Commons.Analysis.Fourier

noncomputable section

variable {K : ℕ}

/-!
# The two analytic inputs of the `z`-integration step

The composition of `chain_bound_at_z` with `lintegral_shift_le` reduces the Tonelli step to two
estimates, one for each summand of the chain bound's right-hand side.  They are stated here in the
exact form the composition consumes.

* **(A) the sup-norm (dilation) input**: `∫_z (winFL2 Ψ H z)² ≤ C · bandSq H`.
  `winFL2 Ψ H z` is the sup over `t > 0` of the `ℓ²`-norm of the windowed curve, and
  `curveRad Ψ H (S+1) z ≤ winFL2 Ψ H z` (a max over the dyadic points is a sup over `t > 0`).
  Recipe: copy `hh`/`hFle`/`hhfin` out of the proof of `bourgain_entropy_integral_l2_l2vec`
  (lines ~415–470 of `bourgain_entropy_l2_vec.lean`): `winFL2 ≤ hh` pointwise, and
  `∫ hh² ≤ ofReal (C₀² C₁²) · A` where `A = ∫⁻ x, ofReal (∑ k, ‖H k x‖²)` is *definitionally*
  `bandSq H`.

* **(B) the deep entropy input**: `∫_z I(z)² ≤ ofReal ((C log²(K+2))²) · bandSq H` where
  `I(z) = ∫⁻ r in Ioi 0, min (ofReal √K) ((winML2 Ψ H z r) ^ (1/2))`.
  This is literally `bourgain_entropy_integral_l2_l2vec Ψ M hM` (with `winML2` respelled via
  `Metric.coveringNumber`), under the extra hypothesis `H k ∈ L^∞` (needed for the
  boundedness of the curve range).  The `L^∞` hypothesis is discharged later by truncation +
  Fatou.
-/

/-- The sup-norm (`winFL2`) squared integral bound, **with the constant uniform in `H`**. -/
theorem lintegral_winFL2_sq_le_uniform (Ψ : SchwartzMap ℝ ℂ) (K : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (H : Fin K → ℝ → ℂ),
      (∀ k : Fin K, MemLp (H k) 2 (volume : Measure ℝ)) →
      (∫⁻ z, (winFL2 Ψ H z) ^ (2:ℝ)) ≤ ENNReal.ofReal C * bandSq H := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := maximal_dilation_convolution_enorm_le_hlMax Ψ
  obtain ⟨C₀, hC₀pos, hC₀⟩ := Commons.Analysis.Maximal.real_maximal_strong_type 2 (by norm_num)
  refine ⟨C₀ ^ 2 * C₁ ^ 2, by positivity, ?_⟩
  intro H hH2
  set hh : ℝ → ENNReal := fun x => (∑ k : Fin K,
      (ENNReal.ofReal C₁ * Commons.Analysis.Maximal.hlMax (fun y : ℝ => ‖H k y‖ₑ) x) ^ (2:ℝ))
      ^ ((1:ℝ)/2) with hhdef
  have hFle : ∀ x, winFL2 Ψ H x ≤ hh x := by
    intro x
    have h1 : winFL2 Ψ H x ≤ (⨆ (t : {t : ℝ // 0 < t}),
        (∑ k : Fin K, ‖winCurveL2 Ψ H x t k‖ₑ ^ (2:ℝ)) ^ ((1:ℝ)/2)) :=
      iSup_le fun t => (enorm_eq_sqrt_sum_L2 (winCurveL2 Ψ H x t)).le.trans
        (le_iSup (fun t : {t : ℝ // 0 < t} =>
          (∑ k : Fin K, ‖winCurveL2 Ψ H x t k‖ₑ ^ (2:ℝ)) ^ ((1:ℝ)/2)) t)
    refine h1.trans ?_
    rw [hhdef]
    refine iSup_le fun t => ?_
    refine ENNReal.rpow_le_rpow (Finset.sum_le_sum fun k _ => ?_) (by norm_num)
    exact ENNReal.rpow_le_rpow ((le_iSup (fun t : {t : ℝ // 0 < t} =>
      ‖winCurveL2 Ψ H x t k‖ₑ) t).trans (hC₁ (H k) (hH2 k) x)) (by norm_num)
  have hhmeas : Measurable hh := by
    rw [hhdef]
    exact (ENNReal.continuous_rpow_const.measurable).comp
      (Finset.measurable_sum _ fun k _ =>
        (measurable_const.mul (Commons.Analysis.Maximal.measurable_hlMax _)).pow_const 2)
  have hb : ∀ k : Fin K, AEMeasurable
      (fun x => (ENNReal.ofReal C₁ * Commons.Analysis.Maximal.hlMax (fun y : ℝ => ‖H k y‖ₑ) x) ^ (2:ℝ))
      volume := fun k => ((measurable_const.mul
        (Commons.Analysis.Maximal.measurable_hlMax _)).pow_const 2).aemeasurable
  have hAfin : bandSq H < ⊤ := by
    unfold bandSq
    have hcongr : (fun x : ℝ => ENNReal.ofReal (∑ k : Fin K, ‖H k x‖ ^ 2))
        = fun x => ∑ k : Fin K, ENNReal.ofReal (‖H k x‖ ^ 2) := by
      funext x
      exact ENNReal.ofReal_sum_of_nonneg (fun k _ => sq_nonneg _)
    rw [hcongr, lintegral_finsetSum' (Finset.univ)
      (f := fun k : Fin K => fun x : ℝ => ENNReal.ofReal (‖H k x‖ ^ 2))
      (fun k _ => ((hH2 k).aemeasurable.norm.pow_const 2).ennreal_ofReal)]
    refine ENNReal.sum_lt_top.mpr fun k _ => ?_
    have h1 : Integrable (fun x : ℝ => ‖H k x‖ ^ 2) volume := by
      have := (hH2 k).integrable_norm_rpow (p := 2) (by norm_num) (by norm_num)
      simpa using this
    have h2 := h1.lintegral_lt_top
    simpa only [enorm_eq_ofReal_norm'] using h2
  have hhfin : ∫⁻ x, hh x ^ (2:ℝ) ≤ ENNReal.ofReal (C₀ ^ 2 * C₁ ^ 2) * bandSq H := by
    have hpow : ∀ x : ℝ, hh x ^ (2:ℝ)
        = ∑ k : Fin K, (ENNReal.ofReal C₁ * Commons.Analysis.Maximal.hlMax (fun y : ℝ => ‖H k y‖ₑ) x) ^ (2:ℝ) := by
      intro x
      rw [hhdef, ← ENNReal.rpow_mul, show ((1:ℝ)/2) * 2 = 1 by norm_num, ENNReal.rpow_one]
    have hstep : ∀ k : Fin K, ∫⁻ x, (ENNReal.ofReal C₁ *
          Commons.Analysis.Maximal.hlMax (fun y : ℝ => ‖H k y‖ₑ) x) ^ (2:ℝ)
        ≤ ENNReal.ofReal (C₀ ^ 2 * C₁ ^ 2) * ∫⁻ x, ENNReal.ofReal (‖H k x‖ ^ 2) := by
      intro k
      have hfac : (fun x : ℝ => (ENNReal.ofReal C₁ *
            Commons.Analysis.Maximal.hlMax (fun y : ℝ => ‖H k y‖ₑ) x) ^ (2:ℝ))
          = fun x => (ENNReal.ofReal C₁) ^ (2:ℝ) *
              (Commons.Analysis.Maximal.hlMax (fun y : ℝ => ‖H k y‖ₑ) x) ^ (2:ℝ) := by
        funext x; rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
      rw [hfac, lintegral_const_mul'' _
        (((Commons.Analysis.Maximal.measurable_hlMax _).pow_const 2).aemeasurable)]
      rw [show (ENNReal.ofReal C₁) ^ (2:ℝ) = ENNReal.ofReal (C₁ ^ 2) by
        rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast,
          ENNReal.ofReal_pow hC₁pos.le]]
      have h32 : ∫⁻ x : ℝ, (Commons.Analysis.Maximal.hlMax (fun y : ℝ => ‖H k y‖ₑ) x) ^ (2:ℝ)
          ≤ ENNReal.ofReal (C₀ ^ 2) * ∫⁻ x : ℝ, ENNReal.ofReal (‖H k x‖ ^ 2) := by
        have h := hC₀ (fun y : ℝ => ‖H k y‖)
        have h1 : (fun y : ℝ => ‖(fun y : ℝ => ‖H k y‖) y‖ₑ) = fun y => ‖H k y‖ₑ := by
          funext y; exact enorm_norm_eq_enorm (H k y)
        rw [h1] at h
        have h2 : (fun x : ℝ => ‖‖H k x‖‖ₑ ^ (2:ℝ)) = fun x => ENNReal.ofReal (‖H k x‖ ^ 2) := by
          funext x
          rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast, enorm_norm_eq_enorm,
            enorm_eq_ofReal_norm', ENNReal.ofReal_pow (norm_nonneg _)]
        rw [h2] at h
        have hC : (C₀ : ℝ) ^ (2:ℝ) = C₀ ^ 2 := by
          rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
        rw [hC] at h
        simpa only [Commons.Analysis.Maximal.hlMax] using h
      calc ENNReal.ofReal (C₁ ^ 2) * ∫⁻ x, (Commons.Analysis.Maximal.hlMax (fun y : ℝ => ‖H k y‖ₑ) x) ^ (2:ℝ)
          ≤ ENNReal.ofReal (C₁ ^ 2) * (ENNReal.ofReal (C₀ ^ 2) * ∫⁻ x, ENNReal.ofReal (‖H k x‖ ^ 2)) :=
            mul_le_mul_of_nonneg_left h32 bot_le
        _ = ENNReal.ofReal (C₀ ^ 2 * C₁ ^ 2) * ∫⁻ x, ENNReal.ofReal (‖H k x‖ ^ 2) := by
            rw [ENNReal.ofReal_mul (sq_nonneg C₀)]
            ring
    calc ∫⁻ x, hh x ^ (2:ℝ)
        = ∑ k : Fin K, ∫⁻ x, (ENNReal.ofReal C₁ *
            Commons.Analysis.Maximal.hlMax (fun y : ℝ => ‖H k y‖ₑ) x) ^ (2:ℝ) := by
          rw [lintegral_congr fun x => hpow x, lintegral_finsetSum' Finset.univ (fun k _ => hb k)]
      _ ≤ ∑ k : Fin K, ENNReal.ofReal (C₀ ^ 2 * C₁ ^ 2) * ∫⁻ x, ENNReal.ofReal (‖H k x‖ ^ 2) :=
          Finset.sum_le_sum fun k _ => hstep k
      _ = ENNReal.ofReal (C₀ ^ 2 * C₁ ^ 2) * bandSq H := by
          rw [← Finset.mul_sum, show bandSq H = ∫⁻ x, ENNReal.ofReal (∑ k : Fin K, ‖H k x‖ ^ 2) from rfl]
          congr 1
          rw [← lintegral_finsetSum' Finset.univ
            (f := fun k : Fin K => fun x : ℝ => ENNReal.ofReal (‖H k x‖ ^ 2))
            (fun k _ => ((hH2 k).aemeasurable.norm.pow_const 2).ennreal_ofReal)]
          exact lintegral_congr fun x =>
            (ENNReal.ofReal_sum_of_nonneg (fun k _ => sq_nonneg _)).symm
  calc ∫⁻ z, (winFL2 Ψ H z) ^ (2:ℝ)
      ≤ ∫⁻ z, (hh z) ^ (2:ℝ) := lintegral_mono fun z => ENNReal.rpow_le_rpow (hFle z) (by norm_num)
    _ ≤ ENNReal.ofReal (C₀ ^ 2 * C₁ ^ 2) * bandSq H := hhfin

/-- The sup-norm (`winFL2`) squared integral bound: the (A) input. -/
theorem lintegral_winFL2_sq_le (Ψ : SchwartzMap ℝ ℂ) (H : Fin K → ℝ → ℂ)
    (hH2 : ∀ k : Fin K, MemLp (H k) 2 (volume : Measure ℝ)) :
    ∃ C : ℝ, 0 < C ∧ (∫⁻ z, (winFL2 Ψ H z) ^ (2:ℝ)) ≤ ENNReal.ofReal C * bandSq H := by
  obtain ⟨C, hCpos, hC⟩ := lintegral_winFL2_sq_le_uniform Ψ K
  exact ⟨C, hCpos, hC H hH2⟩

/-- `curveRad` is dominated by `winFL2` (a max over dyadic points is a sup over all `t > 0`). -/
theorem curveRad_le_winFL2 (Ψ : SchwartzMap ℝ ℂ) (H : Fin K → ℝ → ℂ) (S : ℕ) (z : ℝ) :
    ENNReal.ofReal (curveRad Ψ H S z) ≤ winFL2 Ψ H z := by
  obtain ⟨i₀, _, hi₀⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin (S+1)))
    (fun i : Fin (S+1) => ‖curveVec Ψ H S z i‖) Finset.univ_nonempty
  have hsup : Finset.univ.sup' Finset.univ_nonempty (fun i : Fin (S+1) => ‖curveVec Ψ H S z i‖)
      = ‖curveVec Ψ H S z i₀‖ :=
    le_antisymm (Finset.sup'_le Finset.univ_nonempty (fun i : Fin (S+1) => ‖curveVec Ψ H S z i‖)
        (fun i _ => hi₀ i (Finset.mem_univ i)))
      (Finset.le_sup' (fun i : Fin (S+1) => ‖curveVec Ψ H S z i‖) (Finset.mem_univ i₀))
  calc ENNReal.ofReal (curveRad Ψ H S z)
      = ENNReal.ofReal ‖curveVec Ψ H S z i₀‖ := by
        unfold curveRad
        rw [hsup]
    _ = ‖winCurveL2 Ψ H z ⟨scaleTj (i₀:ℕ), scaleTj_pos (i₀:ℕ)⟩‖ₑ := by
        unfold curveVec
        rw [ofReal_norm]
    _ ≤ winFL2 Ψ H z := by
        unfold winFL2
        exact le_iSup (fun t : {t : ℝ // 0 < t} => ‖winCurveL2 Ψ H z t‖ₑ) _

end

end Commons.Analysis.Fourier

open scoped _root_.ENNReal
open _root_.MeasureTheory

namespace Commons.Analysis.Measure

private lemma setLIntegral_comp_sub (F : ℝ → ENNReal) (z a b : ℝ) :
    ∫⁻ y in Set.Ioo a b, F (y - z) = ∫⁻ w in Set.Ioo (a - z) (b - z), F w := by
  rw [← lintegral_indicator measurableSet_Ioo, ← lintegral_indicator measurableSet_Ioo]
  have h : ∀ y : ℝ, (Set.Ioo a b).indicator (fun y => F (y - z)) y
      = (Set.Ioo (a - z) (b - z)).indicator F (y - z) := by
    intro y
    rw [Set.indicator_apply, Set.indicator_apply]
    by_cases hy : y ∈ Set.Ioo a b
    · rw [if_pos hy, if_pos ⟨by linarith [hy.1], by linarith [hy.2]⟩]
    · rw [if_neg hy]
      by_cases hy' : y - z ∈ Set.Ioo (a - z) (b - z)
      · exact absurd ⟨by linarith [hy'.1], by linarith [hy'.2]⟩ hy
      · rw [if_neg hy']
  rw [lintegral_congr h]
  exact lintegral_add_right_eq_self (fun w : ℝ => (Set.Ioo (a - z) (b - z)).indicator F w) (-z)

/-- Tonelli for the shifted integrand. -/
theorem lintegral_shift_le (f : ℝ → ℝ → ENNReal) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hf : AEMeasurable (Function.uncurry fun y z : ℝ => f z (y - z))
      ((volume.restrict (Set.Ioo (0:ℝ) δ)).prod (volume : Measure ℝ))) :
    ∫⁻ y in Set.Ioo (0:ℝ) δ, ∫⁻ z, f z (y - z)
      ≤ ∫⁻ z, ∫⁻ w in Set.Ioc (-z) (-z + 1), f z w := by
  rw [MeasureTheory.lintegral_lintegral_swap hf]
  refine lintegral_mono fun z => ?_
  rw [setLIntegral_comp_sub]
  exact lintegral_mono_set (fun w hw => ⟨by linarith [hw.1], by linarith [hw.2, hδ1]⟩)

end Commons.Analysis.Measure


open _root_.MeasureTheory Finset
open scoped BigOperators _root_.ENNReal _root_.Topology

namespace Commons.Analysis.Fourier

noncomputable section

variable {K : ℕ}

/-- The per-`z` integrand consumed by `chain_bound_at_z` and `lintegral_shift_le`. -/
noncomputable def tonelliFun (Ψ : SchwartzMap ℝ ℂ) (lam : Fin K → ℝ) (H : Fin K → ℝ → ℂ)
    (S : ℕ) (z w : ℝ) : ENNReal :=
  ENNReal.ofReal (⨆ i : Fin (S+2), ‖∑ k : Fin K, curvePt Ψ H (i:ℕ) z k
    * Complex.exp (Complex.I * (lam k : ℂ) * (w : ℂ))‖) ^ (2:ℝ)

/-- The truncated maximal function of the translate as a `z`-integral of `tonelliFun`. -/
lemma bandMaxTr_eq_integral_tonelliFun (Ψ : SchwartzMap ℝ ℂ) (lam : Fin K → ℝ)
    (H : Fin K → ℝ → ℂ) (S : ℕ) (y : ℝ) :
    bandMaxTr Ψ lam H S y = ∫⁻ z, tonelliFun Ψ lam H S z (y - z) := by
  unfold bandMaxTr tonelliFun
  refine lintegral_congr fun z => ?_
  rw [iSup_enorm_eq_ofReal_iSup_norm (fun i : Fin (S+2) => ∑ k : Fin K, curvePt Ψ H (i:ℕ) z k
    * Complex.exp (Complex.I * (lam k : ℂ) * ((y - z : ℝ) : ℂ)))]

/-- **The wiring**: the `y`-average of the truncated maximal function of the translate is bounded
by the `z`-integral of the per-`z` chain bound.  The hypothesis `hchain` is exactly the conclusion
of `chain_bound_at_z` (rearranged), and its right-hand side is what inputs (A)+(B) then integrate. -/
theorem bandMaxTr_average_le (Ψ : SchwartzMap ℝ ℂ) (lam : Fin K → ℝ) (H : Fin K → ℝ → ℂ)
    (S : ℕ) {A : ℝ} (hA : 0 < A)
    (hchain : ∀ z : ℝ, ∫⁻ w in Set.Ioc (-z) (-z + 1), tonelliFun Ψ lam H S z w
      ≤ ENNReal.ofReal (A ^ 2) * (256 * (ENNReal.ofReal (curveRad Ψ H (S+1) z)) ^ (2:ℝ)
          + 16 * (∫⁻ r in Set.Ioi (0:ℝ), min (ENNReal.ofReal (Real.sqrt (K:ℝ)))
                    ((winML2 Ψ H z r) ^ ((1:ℝ)/2))) ^ (2:ℝ)))
    (hmeas : AEMeasurable (Function.uncurry fun y z : ℝ => tonelliFun Ψ lam H S z (y - z))
      ((volume.restrict (Set.Ioo (0:ℝ) (9/10))).prod (volume : Measure ℝ))) :
    ∫⁻ y in Set.Ioo (0:ℝ) (9/10), bandMaxTr Ψ lam H S y
      ≤ ∫⁻ z, ENNReal.ofReal (A ^ 2) * (256 * (ENNReal.ofReal (curveRad Ψ H (S+1) z)) ^ (2:ℝ)
          + 16 * (∫⁻ r in Set.Ioi (0:ℝ), min (ENNReal.ofReal (Real.sqrt (K:ℝ)))
                    ((winML2 Ψ H z r) ^ ((1:ℝ)/2))) ^ (2:ℝ)) := by
  have hdef : ∀ y : ℝ, bandMaxTr Ψ lam H S y
      = ∫⁻ z, tonelliFun Ψ lam H S z (y - z) :=
    fun y => bandMaxTr_eq_integral_tonelliFun Ψ lam H S y
  calc ∫⁻ y in Set.Ioo (0:ℝ) (9/10), bandMaxTr Ψ lam H S y
      = ∫⁻ y in Set.Ioo (0:ℝ) (9/10), ∫⁻ z, tonelliFun Ψ lam H S z (y - z) := by
        refine lintegral_congr fun y => hdef y
    _ ≤ ∫⁻ z, ∫⁻ w in Set.Ioc (-z) (-z + 1), tonelliFun Ψ lam H S z w :=
        Commons.Analysis.Measure.lintegral_shift_le (fun z w => tonelliFun Ψ lam H S z w) (by norm_num) (by norm_num) hmeas
    _ ≤ ∫⁻ z, ENNReal.ofReal (A ^ 2) * (256 * (ENNReal.ofReal (curveRad Ψ H (S+1) z)) ^ (2:ℝ)
          + 16 * (∫⁻ r in Set.Ioi (0:ℝ), min (ENNReal.ofReal (Real.sqrt (K:ℝ)))
                    ((winML2 Ψ H z r) ^ ((1:ℝ)/2))) ^ (2:ℝ)) :=
        lintegral_mono hchain

/-- **Item 1 of the assembly**: instantiate the `hchain` hypothesis with `chain_bound_at_z`. -/
theorem bandMaxTr_average_le' (Ψ : SchwartzMap ℝ ℂ) (lam : Fin K → ℝ)
    (hsep : ∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|)
    (H : Fin K → ℝ → ℂ) (S : ℕ)
    (hmeas : AEMeasurable (Function.uncurry fun y z : ℝ => tonelliFun Ψ lam H S z (y - z))
      ((volume.restrict (Set.Ioo (0:ℝ) (9/10))).prod (volume : Measure ℝ))) :
    ∃ C : ℝ, 0 < C ∧
      ∫⁻ y in Set.Ioo (0:ℝ) (9/10), bandMaxTr Ψ lam H S y
        ≤ ∫⁻ z, ENNReal.ofReal (C ^ 2) * (256 * (ENNReal.ofReal (curveRad Ψ H (S+1) z)) ^ (2:ℝ)
            + 16 * (∫⁻ r in Set.Ioi (0:ℝ), min (ENNReal.ofReal (Real.sqrt (K:ℝ)))
                      ((winML2 Ψ H z r) ^ ((1:ℝ)/2))) ^ (2:ℝ)) := by
  obtain ⟨C, hCpos, hC⟩ := chain_bound_at_z Ψ lam hsep
  exact ⟨C, hCpos, bandMaxTr_average_le Ψ lam H S hCpos (fun z => hC H S z) hmeas⟩

/-- `ofReal` of the finite sup `curveRad` is the supremum of the `enorm`s of the curve points. -/
lemma ofReal_curveRad_eq_iSup (Ψ : SchwartzMap ℝ ℂ) (H : Fin K → ℝ → ℂ) (S : ℕ) (z : ℝ) :
    ENNReal.ofReal (curveRad Ψ H S z)
      = ⨆ i : Fin (S+1), ‖curveVec Ψ H S z i‖ₑ := by
  refine le_antisymm ?_ ?_
  · obtain ⟨i₀, _, hi₀⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin (S+1)))
      (fun i : Fin (S+1) => ‖curveVec Ψ H S z i‖) Finset.univ_nonempty
    have hsup : Finset.univ.sup' Finset.univ_nonempty
        (fun i : Fin (S+1) => ‖curveVec Ψ H S z i‖) = ‖curveVec Ψ H S z i₀‖ :=
      le_antisymm (Finset.sup'_le Finset.univ_nonempty _
          (fun i _ => hi₀ i (Finset.mem_univ i)))
        (Finset.le_sup' (fun i : Fin (S+1) => ‖curveVec Ψ H S z i‖) (Finset.mem_univ i₀))
    have hstep : ENNReal.ofReal (curveRad Ψ H S z) = ‖curveVec Ψ H S z i₀‖ₑ := by
      rw [curveRad, hsup, ofReal_norm]
    rw [hstep]
    exact le_iSup (fun i : Fin (S+1) => ‖curveVec Ψ H S z i‖ₑ) i₀
  · refine iSup_le fun i => ?_
    have hle : ‖curveVec Ψ H S z i‖ ≤ curveRad Ψ H S z := by
      rw [curveRad]
      exact Finset.le_sup' (fun i : Fin (S+1) => ‖curveVec Ψ H S z i‖) (Finset.mem_univ i)
    calc ‖curveVec Ψ H S z i‖ₑ = ENNReal.ofReal ‖curveVec Ψ H S z i‖ := by rw [ofReal_norm]
      _ ≤ ENNReal.ofReal (curveRad Ψ H S z) := ENNReal.ofReal_le_ofReal hle

/-- A.e.-measurability of `z ↦ (ofReal (curveRad Ψ H S z))^(2:ℝ)`. -/
lemma aemeasurable_ofReal_curveRad_rpow (Ψ : SchwartzMap ℝ ℂ) (H : Fin K → ℝ → ℂ)
    (hH : ∀ k : Fin K, MemLp (H k) 2 (volume : Measure ℝ)) (S : ℕ) :
    AEMeasurable (fun z : ℝ => (ENNReal.ofReal (curveRad Ψ H S z)) ^ (2:ℝ)) volume := by
  have hcurve : ∀ i : Fin (S+1), AEMeasurable (fun z : ℝ => ‖curveVec Ψ H S z i‖ₑ) volume := by
    intro i
    have hc : ∀ k : Fin K, AEMeasurable (fun z : ℝ => ‖curveVec Ψ H S z i k‖ₑ) volume := by
      intro k
      have h1 : (fun z : ℝ => ‖curveVec Ψ H S z i k‖ₑ)
          = fun z : ℝ => ‖curvePt Ψ H (i:ℕ) z k‖ₑ := by
        funext z
        rw [curveVec_apply]
        congr 1
        refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
        show H k u * ((scaleTj (i:ℕ) : ℝ)⁻¹ • (Ψ : ℝ → ℂ) ((z - u) / scaleTj (i:ℕ)))
            = H k u * winK Ψ (i:ℕ) (z - u)
        rw [winK_eq_smul]
        rw [Complex.real_smul]
      rw [h1]
      exact (aemeasurable_curvePt Ψ (hH k) (i:ℕ)).enorm
    have hsum : AEMeasurable (fun z : ℝ =>
        ∑ k : Fin K, ‖curveVec Ψ H S z i k‖ₑ ^ (2:ℝ)) volume := by
      have h := Finset.aemeasurable_sum (Finset.univ : Finset (Fin K))
        (f := fun k : Fin K => fun z : ℝ => ‖curveVec Ψ H S z i k‖ₑ ^ (2:ℝ))
        (fun k _ => Measurable.comp_aemeasurable
          (ENNReal.continuous_rpow_const (y := (2:ℝ))).measurable (hc k))
      rw [show (fun z : ℝ => ∑ k : Fin K, ‖curveVec Ψ H S z i k‖ₑ ^ (2:ℝ))
          = ∑ k : Fin K, (fun z : ℝ => ‖curveVec Ψ H S z i k‖ₑ ^ (2:ℝ)) from by
            funext z; rw [Finset.sum_apply]]
      exact h
    have hrpow := Measurable.comp_aemeasurable
      (ENNReal.continuous_rpow_const (y := ((1:ℝ)/2))).measurable hsum
    have heq : (fun z : ℝ => ‖curveVec Ψ H S z i‖ₑ)
        = fun z : ℝ => (∑ k : Fin K, ‖curveVec Ψ H S z i k‖ₑ ^ (2:ℝ)) ^ ((1:ℝ)/2) := by
      funext z
      exact enorm_eq_sqrt_sum_L2 (v := curveVec Ψ H S z i)
    rw [heq]
    simpa only [Function.comp_def] using hrpow
  have hsup : AEMeasurable (fun z : ℝ => ⨆ i : Fin (S+1), ‖curveVec Ψ H S z i‖ₑ) volume :=
    AEMeasurable.iSup hcurve
  have hof : AEMeasurable (fun z : ℝ => ENNReal.ofReal (curveRad Ψ H S z)) volume :=
    AEMeasurable.congr hsup (Filter.Eventually.of_forall fun z =>
      (ofReal_curveRad_eq_iSup Ψ H S z).symm)
  exact Measurable.comp_aemeasurable (ENNReal.continuous_rpow_const (y := (2:ℝ))).measurable hof

/-- **Item 2, algebraic part**: pull the constant and use linearity, given the two integral
bounds (inputs (A) and (B)) and the measurability of the `curveRad` summand. -/
theorem z_integral_le (Ψ : SchwartzMap ℝ ℂ) (H : Fin K → ℝ → ℂ) (S : ℕ) {C CA CB : ℝ}
    (hC : 0 < C)
    (hmA : AEMeasurable (fun z : ℝ => (ENNReal.ofReal (curveRad Ψ H (S+1) z)) ^ (2:ℝ)) volume)
    (hA : ∫⁻ z, (ENNReal.ofReal (curveRad Ψ H (S+1) z)) ^ (2:ℝ)
      ≤ ENNReal.ofReal CA * bandSq H)
    (hB : ∫⁻ z, (∫⁻ r in Set.Ioi (0:ℝ), min (ENNReal.ofReal (Real.sqrt (K:ℝ)))
          ((winML2 Ψ H z r) ^ ((1:ℝ)/2))) ^ (2:ℝ) ≤ ENNReal.ofReal CB * bandSq H) :
    ∫⁻ z, ENNReal.ofReal (C ^ 2) *
        (256 * (ENNReal.ofReal (curveRad Ψ H (S+1) z)) ^ (2:ℝ)
          + 16 * (∫⁻ r in Set.Ioi (0:ℝ), min (ENNReal.ofReal (Real.sqrt (K:ℝ)))
                    ((winML2 Ψ H z r) ^ ((1:ℝ)/2))) ^ (2:ℝ))
      ≤ ENNReal.ofReal (C ^ 2) *
          (256 * (ENNReal.ofReal CA * bandSq H) + 16 * (ENNReal.ofReal CB * bandSq H)) := by
  have h1 : (∫⁻ z, ENNReal.ofReal (C ^ 2) *
        ((256:ENNReal) * (ENNReal.ofReal (curveRad Ψ H (S+1) z)) ^ (2:ℝ)
          + 16 * (∫⁻ r in Set.Ioi (0:ℝ), min (ENNReal.ofReal (Real.sqrt (K:ℝ)))
                    ((winML2 Ψ H z r) ^ ((1:ℝ)/2))) ^ (2:ℝ)))
      = ENNReal.ofReal (C ^ 2) * (∫⁻ z,
        ((256:ENNReal) * (ENNReal.ofReal (curveRad Ψ H (S+1) z)) ^ (2:ℝ)
          + 16 * (∫⁻ r in Set.Ioi (0:ℝ), min (ENNReal.ofReal (Real.sqrt (K:ℝ)))
                    ((winML2 Ψ H z r) ^ ((1:ℝ)/2))) ^ (2:ℝ))) :=
    lintegral_const_mul' (ENNReal.ofReal (C ^ 2)) _ (ENNReal.ofReal_ne_top)
  have h2 : (∫⁻ z, ((256:ENNReal) * (ENNReal.ofReal (curveRad Ψ H (S+1) z)) ^ (2:ℝ)
          + 16 * (∫⁻ r in Set.Ioi (0:ℝ), min (ENNReal.ofReal (Real.sqrt (K:ℝ)))
                    ((winML2 Ψ H z r) ^ ((1:ℝ)/2))) ^ (2:ℝ)))
      = (256:ENNReal) * (∫⁻ z, (ENNReal.ofReal (curveRad Ψ H (S+1) z)) ^ (2:ℝ))
        + 16 * (∫⁻ z, (∫⁻ r in Set.Ioi (0:ℝ), min (ENNReal.ofReal (Real.sqrt (K:ℝ)))
                    ((winML2 Ψ H z r) ^ ((1:ℝ)/2))) ^ (2:ℝ)) := by
    rw [lintegral_add_left' (f := fun z : ℝ =>
      (256:ENNReal) * (ENNReal.ofReal (curveRad Ψ H (S+1) z)) ^ (2:ℝ))
      (aemeasurable_const.mul hmA)]
    rw [lintegral_const_mul'' 256 hmA, lintegral_const_mul' 16 _ (by norm_num)]
  rw [h1, h2]
  exact mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_left hA bot_le) (mul_le_mul_of_nonneg_left hB bot_le)) bot_le

/-- **The averaged one-step bound**: the `y`-average of the truncated maximal function of the
translate is bounded by an absolute constant times the `ℓ²` energy, using the chain bound and the
two analytic inputs (A) and (B). -/
theorem bandMaxTr_average_bound (Ψ : SchwartzMap ℝ ℂ) (lam : Fin K → ℝ)
    (hsep : ∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|)
    (H : Fin K → ℝ → ℂ) (S : ℕ) {M : ℝ} (hM : ∀ x : ℝ, ‖(Ψ : ℝ → ℂ) x‖ ≤ M)
    (hH2 : ∀ k : Fin K, MemLp (H k) 2 (volume : Measure ℝ))
    (hHinf : ∀ k : Fin K, MemLp (H k) ⊤ (volume : Measure ℝ))
    (hmeas : AEMeasurable (Function.uncurry fun y z : ℝ => tonelliFun Ψ lam H S z (y - z))
      ((volume.restrict (Set.Ioo (0:ℝ) (9/10))).prod (volume : Measure ℝ))) :
    ∃ Cc : ℝ, 0 < Cc ∧
      ∫⁻ y in Set.Ioo (0:ℝ) (9/10), bandMaxTr Ψ lam H S y ≤ ENNReal.ofReal Cc * bandSq H := by
  obtain ⟨Cch, hCchpos, hCch⟩ := bandMaxTr_average_le' Ψ lam hsep H S hmeas
  obtain ⟨CA, hCApos, hCA0⟩ := lintegral_winFL2_sq_le Ψ H hH2
  obtain ⟨CB₀, hCB₀pos, hCB0⟩ := bourgain_entropy_integral_l2_l2vec Ψ M hM
  set CB : ℝ := (CB₀ * (Real.log ((K:ℝ)+2))^2)^2 with hCBdef
  have hCBpos : 0 < CB := by
    rw [hCBdef]
    have hK : (1:ℝ) < (K:ℝ) + 2 := by
      have h : (0:ℝ) ≤ (K:ℝ) := Nat.cast_nonneg K
      linarith
    exact pow_pos (mul_pos hCB₀pos (pow_pos (Real.log_pos hK) 2)) 2
  have hA : ∫⁻ z, (ENNReal.ofReal (curveRad Ψ H (S+1) z)) ^ (2:ℝ)
      ≤ ENNReal.ofReal CA * bandSq H :=
    le_trans (lintegral_mono fun z =>
      ENNReal.rpow_le_rpow (curveRad_le_winFL2 Ψ H (S+1) z) (by norm_num)) hCA0
  have hB : ∫⁻ z, (∫⁻ r in Set.Ioi (0:ℝ), min (ENNReal.ofReal (Real.sqrt (K:ℝ)))
        ((winML2 Ψ H z r) ^ ((1:ℝ)/2))) ^ (2:ℝ) ≤ ENNReal.ofReal CB * bandSq H := by
    have h := hCB0 K H hH2 hHinf
    rw [hCBdef]
    simpa only [bandSq, winML2, min_comm] using h
  have hmA := aemeasurable_ofReal_curveRad_rpow Ψ H hH2 (S+1)
  have hres := z_integral_le Ψ H S hCchpos hmA hA hB
  refine ⟨Cch ^ 2 * (256 * CA + 16 * CB), by positivity, ?_⟩
  calc ∫⁻ y in Set.Ioo (0:ℝ) (9/10), bandMaxTr Ψ lam H S y
      ≤ ∫⁻ z, ENNReal.ofReal (Cch ^ 2) *
          (256 * (ENNReal.ofReal (curveRad Ψ H (S+1) z)) ^ (2:ℝ)
            + 16 * (∫⁻ r in Set.Ioi (0:ℝ), min (ENNReal.ofReal (Real.sqrt (K:ℝ)))
                      ((winML2 Ψ H z r) ^ ((1:ℝ)/2))) ^ (2:ℝ)) := hCch
    _ ≤ ENNReal.ofReal (Cch ^ 2) *
          (256 * (ENNReal.ofReal CA * bandSq H) + 16 * (ENNReal.ofReal CB * bandSq H)) := hres
    _ = ENNReal.ofReal (Cch ^ 2 * (256 * CA + 16 * CB)) * bandSq H := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_ofNat, ENNReal.ofReal_ofNat]
        ring

end

end Commons.Analysis.Fourier

open scoped _root_.ENNReal

namespace Commons.Analysis.Maximal

/-- **Abstract geometric iteration with a state-dependent shift.**

If `M x ≤ A·SQ x + M (T x)`, the shifted state contracts the energy,
`SQ (T x) ≤ θ²·SQ x`, there is an a priori bound `M x ≤ CK·SQ x`, and `2 θ² < 1`, then
`M x ≤ (A/(1-θ²))·SQ x`.  The shift `T` may depend on the state; this is the form in which
Bourgain's `u`-averaging bootstrap is applied (the shift is chosen by averaging over the
translation parameter). -/
theorem iter_bound_shift {X : Type*} (M SQ : X → ENNReal) (T : X → X) {A ρ CK : ℝ}
    (hA : 0 ≤ A) (hApos : 0 < A) (hρ0 : 0 ≤ ρ) (hρ : ρ < 1) (hCK : 0 ≤ CK)
    (hone : ∀ x : X, M x ≤ ENNReal.ofReal A * SQ x + 2 * M (T x))
    (hcon : ∀ x : X, 2 * SQ (T x) ≤ ENNReal.ofReal ρ * SQ x)
    (hap : ∀ x : X, M x ≤ ENNReal.ofReal CK * SQ x) (x : X) :
    M x ≤ ENNReal.ofReal (A / (1 - ρ)) * SQ x := by
  set xₙ : ℕ → X := fun n => Nat.rec x (fun _ y => T y) n with hxndef
  have hxₙ_succ : ∀ n, xₙ (n+1) = T (xₙ n) := fun n => rfl
  have hrec : ∀ n, M (xₙ n) ≤ ENNReal.ofReal A * SQ (xₙ n) + 2 * M (xₙ (n+1)) := by
    intro n
    rw [hxₙ_succ n]
    exact hone (xₙ n)
  have hsq : ∀ n, 2 * SQ (xₙ (n+1)) ≤ ENNReal.ofReal ρ * SQ (xₙ n) := by
    intro n
    rw [hxₙ_succ n]
    exact hcon (xₙ n)
  have hsq_pow : ∀ n, 2 ^ n * SQ (xₙ n) ≤ (ENNReal.ofReal ρ) ^ n * SQ x := by
    intro n
    induction n with
    | zero => simp [hxndef]
    | succ n ih =>
        calc 2 ^ (n+1) * SQ (xₙ (n+1))
            = 2 ^ n * (2 * SQ (xₙ (n+1))) := by ring
          _ ≤ 2 ^ n * (ENNReal.ofReal ρ * SQ (xₙ n)) :=
              mul_le_mul_of_nonneg_left (hsq n) (bot_le)
          _ = ENNReal.ofReal ρ * (2 ^ n * SQ (xₙ n)) := by ring
          _ ≤ ENNReal.ofReal ρ * ((ENNReal.ofReal ρ) ^ n * SQ x) :=
              mul_le_mul_of_nonneg_left ih (bot_le)
          _ = (ENNReal.ofReal ρ) ^ (n+1) * SQ x := by ring
  have htot : ∀ n, M x
      ≤ (∑ i ∈ Finset.range n, ENNReal.ofReal A * (ENNReal.ofReal ρ) ^ i) * SQ x
        + 2 ^ n * M (xₙ n) := by
    intro n
    induction n with
    | zero => simp [hxndef]
    | succ n ih =>
        calc M x
            ≤ (∑ i ∈ Finset.range n, ENNReal.ofReal A * (ENNReal.ofReal ρ) ^ i) * SQ x
              + 2 ^ n * M (xₙ n) := ih
          _ ≤ (∑ i ∈ Finset.range n, ENNReal.ofReal A * (ENNReal.ofReal ρ) ^ i) * SQ x
              + 2 ^ n * (ENNReal.ofReal A * SQ (xₙ n) + 2 * M (xₙ (n+1))) :=
              add_le_add (le_refl _) (mul_le_mul_of_nonneg_left (hrec n) (bot_le))
          _ = (∑ i ∈ Finset.range n, ENNReal.ofReal A * (ENNReal.ofReal ρ) ^ i) * SQ x
              + ENNReal.ofReal A * (2 ^ n * SQ (xₙ n)) + 2 ^ (n+1) * M (xₙ (n+1)) := by ring
          _ ≤ (∑ i ∈ Finset.range n, ENNReal.ofReal A * (ENNReal.ofReal ρ) ^ i) * SQ x
              + ENNReal.ofReal A * ((ENNReal.ofReal ρ) ^ n * SQ x)
              + 2 ^ (n+1) * M (xₙ (n+1)) := by
              refine add_le_add (add_le_add (le_refl _) ?_) (le_refl _)
              exact mul_le_mul_of_nonneg_left (hsq_pow n) (bot_le)
          _ = (∑ i ∈ Finset.range (n+1), ENNReal.ofReal A * (ENNReal.ofReal ρ) ^ i) * SQ x
              + 2 ^ (n+1) * M (xₙ (n+1)) := by
              rw [Finset.sum_range_succ]; ring
  have htail : ∀ n, 2 ^ n * M (xₙ n) ≤ ENNReal.ofReal CK * (ENNReal.ofReal ρ) ^ n * SQ x := by
    intro n
    calc 2 ^ n * M (xₙ n) ≤ 2 ^ n * (ENNReal.ofReal CK * SQ (xₙ n)) :=
          mul_le_mul_of_nonneg_left (hap (xₙ n)) (bot_le)
      _ = ENNReal.ofReal CK * (2 ^ n * SQ (xₙ n)) := by ring
      _ ≤ ENNReal.ofReal CK * ((ENNReal.ofReal ρ) ^ n * SQ x) :=
          mul_le_mul_of_nonneg_left (hsq_pow n) (bot_le)
      _ = ENNReal.ofReal CK * (ENNReal.ofReal ρ) ^ n * SQ x := by ring
  have hcast1 : ∀ n, (∑ i ∈ Finset.range n, ENNReal.ofReal A * (ENNReal.ofReal ρ) ^ i)
      = ENNReal.ofReal (A * (∑ i ∈ Finset.range n, ρ ^ i)) := by
    intro n
    have hterm : ∀ i, ENNReal.ofReal A * (ENNReal.ofReal ρ) ^ i
        = ENNReal.ofReal (A * ρ^i) := by
      intro i
      rw [ENNReal.ofReal_mul hA, ENNReal.ofReal_pow (hρ0)]
    rw [Finset.sum_congr rfl (fun i _ => hterm i),
      ← ENNReal.ofReal_sum_of_nonneg
        (fun i _ => mul_nonneg hA (pow_nonneg (hρ0) i))]
    conv_rhs => rw [Finset.mul_sum]
  have hcast2 : ∀ n, ENNReal.ofReal CK * (ENNReal.ofReal ρ) ^ n
      = ENNReal.ofReal (CK * ρ ^ n) := by
    intro n
    rw [ENNReal.ofReal_mul hCK, ENNReal.ofReal_pow (hρ0)]
  have hcast : ∀ n, ((∑ i ∈ Finset.range n, ENNReal.ofReal A * (ENNReal.ofReal ρ) ^ i)
      + ENNReal.ofReal CK * (ENNReal.ofReal ρ) ^ n)
      = ENNReal.ofReal (A * (∑ i ∈ Finset.range n, ρ ^ i) + CK * ρ ^ n) := by
    intro n
    rw [hcast1 n, hcast2 n, ← ENNReal.ofReal_add
      (mul_nonneg hA (Finset.sum_nonneg fun i _ => pow_nonneg (hρ0) i))
      (mul_nonneg hCK (pow_nonneg (hρ0) _))]
  have hgeo : ∀ n, (∑ i ∈ Finset.range n, ρ^i) ≤ (1 - ρ)⁻¹ := by
    intro n
    have hden : 0 < 1 - ρ := by linarith
    rw [inv_eq_one_div, le_div_iff₀ hden]
    have h1 : (∑ i ∈ Finset.range n, ρ^i) * (1 - ρ) = 1 - ρ^n := by
      have hg := geom_sum_mul ρ n
      rw [show (1:ℝ) - ρ = -(ρ - 1) by ring, mul_neg, hg]
      ring
    rw [h1]
    have : (0:ℝ) ≤ ρ^n := pow_nonneg (hρ0) n
    linarith
  have hkey : ∀ ε : NNReal, 0 < ε → ∃ n : ℕ, ((∑ i ∈ Finset.range (n+1),
      ENNReal.ofReal A * (ENNReal.ofReal ρ) ^ i)
      + ENNReal.ofReal CK * (ENNReal.ofReal ρ) ^ (n+1))
      ≤ ENNReal.ofReal (A / (1 - ρ)) + (ε : ENNReal) := by
    intro ε hε
    have hlt : ρ < 1 := hρ
    have hε' : (0:ℝ) < (ε:ℝ) := by exact_mod_cast hε
    obtain ⟨n, hn⟩ : ∃ n : ℕ, CK * ρ^(n+1) ≤ (ε : ℝ) := by
      rcases eq_or_lt_of_le hCK with h0 | hpos
      · refine ⟨0, ?_⟩
        rw [← h0, zero_mul]
        exact hε'.le
      · obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (by positivity : (0:ℝ) < (ε:ℝ)/CK) hlt
        refine ⟨m, le_of_lt ?_⟩
        calc CK * ρ^(m+1) = (CK * ρ^m) * ρ := by ring
          _ ≤ (CK * ρ^m) * 1 :=
              mul_le_mul_of_nonneg_left hlt.le (by positivity)
          _ = CK * ρ^m := by ring
          _ < CK * ((ε:ℝ)/CK) := mul_lt_mul_of_pos_left hm hpos
          _ = (ε:ℝ) := by field_simp
    refine ⟨n, ?_⟩
    calc ((∑ i ∈ Finset.range (n+1), ENNReal.ofReal A * (ENNReal.ofReal ρ) ^ i)
          + ENNReal.ofReal CK * (ENNReal.ofReal ρ) ^ (n+1))
        = ENNReal.ofReal (A * (∑ i ∈ Finset.range (n+1), ρ ^ i) + CK * ρ ^ (n+1)) :=
          hcast (n+1)
      _ ≤ ENNReal.ofReal (A * (1 - ρ)⁻¹ + (ε : ℝ)) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have hge := hgeo (n+1)
          have hA1 : A * (∑ i ∈ Finset.range (n+1), ρ^i) ≤ A * (1 - ρ)⁻¹ :=
            mul_le_mul_of_nonneg_left hge hA
          linarith [hn]
      _ = ENNReal.ofReal (A * (1 - ρ)⁻¹) + ENNReal.ofReal ((ε : ℝ)) :=
          ENNReal.ofReal_add (by positivity) (by positivity)
      _ = ENNReal.ofReal (A / (1 - ρ)) + (ε : ENNReal) := by
          rw [ENNReal.ofReal_coe_nnreal]
          congr 1
  have hlimShift : (⨅ n, ((∑ i ∈ Finset.range (n+1),
      ENNReal.ofReal A * (ENNReal.ofReal ρ) ^ i)
      + ENNReal.ofReal CK * (ENNReal.ofReal ρ) ^ (n+1))) ≤ ENNReal.ofReal (A / (1 - ρ)) := by
    refine ENNReal.le_of_forall_pos_le_add (fun ε hε _ => ?_)
    obtain ⟨n, hn⟩ := hkey ε hε
    exact (iInf_le _ n).trans hn
  have hX1 : ∀ n : ℕ, ENNReal.ofReal A ≤ (∑ i ∈ Finset.range (n+1),
      ENNReal.ofReal A * (ENNReal.ofReal ρ) ^ i)
      + ENNReal.ofReal CK * (ENNReal.ofReal ρ) ^ (n+1) := by
    intro n
    have h1 : ENNReal.ofReal A ≤ ∑ i ∈ Finset.range (n+1),
        ENNReal.ofReal A * (ENNReal.ofReal ρ) ^ i := by
      have := Finset.single_le_sum
        (f := fun i => ENNReal.ofReal A * (ENNReal.ofReal ρ) ^ i)
        (fun i _ => bot_le) (Finset.mem_range.mpr (Nat.succ_pos n))
      simpa using this
    exact le_add_right h1
  have hLpos : 0 < ⨅ n, ((∑ i ∈ Finset.range (n+1), ENNReal.ofReal A * (ENNReal.ofReal ρ) ^ i)
      + ENNReal.ofReal CK * (ENNReal.ofReal ρ) ^ (n+1)) :=
    lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hApos) (le_iInf fun n => hX1 n)
  have hfin : M x ≤ ⨅ n, ((∑ i ∈ Finset.range (n+1),
      ENNReal.ofReal A * (ENNReal.ofReal ρ) ^ i)
      + ENNReal.ofReal CK * (ENNReal.ofReal ρ) ^ (n+1)) * SQ x := by
    refine le_iInf fun n => ?_
    calc M x
        ≤ (∑ i ∈ Finset.range (n+1), ENNReal.ofReal A * (ENNReal.ofReal ρ) ^ i) * SQ x
          + 2 ^ (n+1) * M (xₙ (n+1)) := htot (n+1)
      _ ≤ (∑ i ∈ Finset.range (n+1), ENNReal.ofReal A * (ENNReal.ofReal ρ) ^ i) * SQ x
          + ENNReal.ofReal CK * (ENNReal.ofReal ρ) ^ (n+1) * SQ x :=
          add_le_add (le_refl _) (htail (n+1))
      _ = ((∑ i ∈ Finset.range (n+1), ENNReal.ofReal A * (ENNReal.ofReal ρ) ^ i)
            + ENNReal.ofReal CK * (ENNReal.ofReal ρ) ^ (n+1)) * SQ x := by ring
  calc M x
      ≤ ⨅ n, ((∑ i ∈ Finset.range (n+1), ENNReal.ofReal A * (ENNReal.ofReal ρ) ^ i)
          + ENNReal.ofReal CK * (ENNReal.ofReal ρ) ^ (n+1)) * SQ x := hfin
    _ = (⨅ n, ((∑ i ∈ Finset.range (n+1), ENNReal.ofReal A * (ENNReal.ofReal ρ) ^ i)
          + ENNReal.ofReal CK * (ENNReal.ofReal ρ) ^ (n+1))) * SQ x :=
        (ENNReal.iInf_mul (f := fun n => (∑ i ∈ Finset.range (n+1),
            ENNReal.ofReal A * (ENNReal.ofReal ρ) ^ i)
            + ENNReal.ofReal CK * (ENNReal.ofReal ρ) ^ (n+1))
          (a := SQ x) (fun _ h0 => absurd h0 hLpos.ne')).symm
    _ ≤ ENNReal.ofReal (A / (1 - ρ)) * SQ x :=
        mul_le_mul_of_nonneg_right hlimShift bot_le

end Commons.Analysis.Maximal


open _root_.MeasureTheory Finset
open scoped BigOperators _root_.ENNReal _root_.Topology FourierTransform

set_option maxHeartbeats 4000000

namespace Commons.Analysis.Fourier

noncomputable section

variable {K : ℕ}

/-- A.e.-measurability in `z` of `curvePt` transfers to the product measure by pullback along
`Prod.snd`. -/
lemma aemeasurable_curvePt_snd (Ψ : SchwartzMap ℝ ℂ) {H : ℝ → ℂ}
    (hH : MemLp H 2 (volume : Measure ℝ)) (j : ℕ) (s : Set ℝ) :
    AEMeasurable (fun p : ℝ × ℝ => ∫ u : ℝ, H u * winK Ψ j (p.2 - u))
      ((volume.restrict s).prod (volume : Measure ℝ)) := by
  have hz := aemeasurable_curvePt Ψ hH j
  set g : ℝ → ℂ := AEMeasurable.mk (fun z : ℝ => ∫ u : ℝ, H u * winK Ψ j (z - u)) hz with hg
  have hgm : Measurable g := hz.measurable_mk
  have h1 : AEMeasurable (fun p : ℝ × ℝ => g p.2)
      ((volume.restrict s).prod (volume : Measure ℝ)) :=
    (hgm.comp measurable_snd).aemeasurable
  refine h1.congr ?_
  exact (MeasureTheory.Measure.quasiMeasurePreserving_snd).ae hz.ae_eq_mk.symm

/-- The `Fin K`-indexed form of `aemeasurable_curvePt_snd`, stated with `curvePt`. -/
lemma aemeasurable_curvePt_snd' (Ψ : SchwartzMap ℝ ℂ) (H : Fin K → ℝ → ℂ)
    (hH : ∀ k : Fin K, MemLp (H k) 2 (volume : Measure ℝ)) (j : ℕ) (k : Fin K) (s : Set ℝ) :
    AEMeasurable (fun p : ℝ × ℝ => curvePt Ψ H j p.2 k)
      ((volume.restrict s).prod (volume : Measure ℝ)) :=
  aemeasurable_curvePt_snd Ψ (hH k) j s

/-- The same, for the full product measure. -/
lemma aemeasurable_curvePt_snd_univ (Ψ : SchwartzMap ℝ ℂ) (H : Fin K → ℝ → ℂ)
    (hH : ∀ k : Fin K, MemLp (H k) 2 (volume : Measure ℝ)) (j : ℕ) (k : Fin K) :
    AEMeasurable (fun p : ℝ × ℝ => curvePt Ψ H j p.2 k)
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
  simpa using aemeasurable_curvePt_snd' Ψ H hH j k (Set.univ : Set ℝ)

/-- The uncurried integrand `(y,z) ↦ tonelliFun Ψ lam H S z (y - z)` of the averaged one-step
bound is a.e. measurable (componentwise a.e. measurability of `curvePt` in `z`, and a continuous
phase). -/
lemma aemeasurable_uncurry_tonelliFun (Ψ : SchwartzMap ℝ ℂ) (lam : Fin K → ℝ)
    (H : Fin K → ℝ → ℂ) (hH : ∀ k : Fin K, MemLp (H k) 2 (volume : Measure ℝ)) (S : ℕ) :
    AEMeasurable (Function.uncurry fun y z : ℝ => tonelliFun Ψ lam H S z (y - z))
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
  set μ : Measure (ℝ × ℝ) := (volume : Measure ℝ).prod (volume : Measure ℝ) with hμ
  have hT : ∀ i : Fin (S+2), AEMeasurable (fun p : ℝ × ℝ =>
      ∑ k : Fin K, curvePt Ψ H (i:ℕ) p.2 k
        * Complex.exp (Complex.I * (lam k : ℂ) * ((p.1 - p.2 : ℝ) : ℂ))) μ := by
    intro i
    have hterm : ∀ k : Fin K, AEMeasurable (fun p : ℝ × ℝ =>
        curvePt Ψ H (i:ℕ) p.2 k
          * Complex.exp (Complex.I * (lam k : ℂ) * ((p.1 - p.2 : ℝ) : ℂ))) μ := fun k =>
      (aemeasurable_curvePt_snd_univ Ψ H hH (i:ℕ) k).mul
        ((by fun_prop : Continuous fun p : ℝ × ℝ =>
          Complex.exp (Complex.I * (lam k : ℂ) * ((p.1 - p.2 : ℝ) : ℂ)))).aemeasurable
    have hs := Finset.aemeasurable_sum Finset.univ (f := fun k : Fin K => fun p : ℝ × ℝ =>
      curvePt Ψ H (i:ℕ) p.2 k
        * Complex.exp (Complex.I * (lam k : ℂ) * ((p.1 - p.2 : ℝ) : ℂ))) (fun k _ => hterm k)
    refine hs.congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [Finset.sum_apply]
  have hsupR : AEMeasurable (fun p : ℝ × ℝ =>
      ⨆ i : Fin (S+2), ‖∑ k : Fin K, curvePt Ψ H (i:ℕ) p.2 k
        * Complex.exp (Complex.I * (lam k : ℂ) * ((p.1 - p.2 : ℝ) : ℂ))‖) μ :=
    AEMeasurable.iSup (f := fun i : Fin (S+2) => fun p : ℝ × ℝ =>
      ‖∑ k : Fin K, curvePt Ψ H (i:ℕ) p.2 k
        * Complex.exp (Complex.I * (lam k : ℂ) * ((p.1 - p.2 : ℝ) : ℂ))‖)
      (fun i => (hT i).norm)
  have hof : AEMeasurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal (⨆ i : Fin (S+2), ‖∑ k : Fin K, curvePt Ψ H (i:ℕ) p.2 k
        * Complex.exp (Complex.I * (lam k : ℂ) * ((p.1 - p.2 : ℝ) : ℂ))‖)) μ :=
    ENNReal.continuous_ofReal.measurable.comp_aemeasurable hsupR
  have hfin : AEMeasurable (fun p : ℝ × ℝ =>
      (ENNReal.ofReal (⨆ i : Fin (S+2), ‖∑ k : Fin K, curvePt Ψ H (i:ℕ) p.2 k
        * Complex.exp (Complex.I * (lam k : ℂ) * ((p.1 - p.2 : ℝ) : ℂ))‖)) ^ (2:ℝ)) μ :=
    Measurable.comp_aemeasurable (ENNReal.continuous_rpow_const (y := (2:ℝ))).measurable hof
  refine hfin.congr (Filter.Eventually.of_forall fun p => ?_)
  show (ENNReal.ofReal (⨆ i : Fin (S+2), ‖∑ k : Fin K, curvePt Ψ H (i:ℕ) p.2 k
      * Complex.exp (Complex.I * (lam k : ℂ) * ((p.1 - p.2 : ℝ) : ℂ))‖)) ^ (2:ℝ)
    = tonelliFun Ψ lam H S p.2 (p.1 - p.2)
  rw [tonelliFun]

/-! ### Elementary `ENNReal` suprema lemmas -/

/-- The partial suprema `S ↦ ⨆_{i < S+2} f i` are monotone. -/
lemma iSup_fin_succ_mono (f : ℕ → ENNReal) :
    Monotone (fun S : ℕ => ⨆ i : Fin (S+2), f (i:ℕ)) := by
  intro S S' h
  refine iSup_le fun i => ?_
  exact le_iSup (fun i' : Fin (S'+2) => f (i':ℕ)) (Fin.castLE (by omega) i)

/-- The partial suprema `S ↦ ⨆_{i < S+2} f i` increase to `⨆ j, f j`. -/
lemma iSup_fin_succ_eq_iSup_nat (f : ℕ → ENNReal) :
    (⨆ S : ℕ, ⨆ i : Fin (S+2), f (i:ℕ)) = ⨆ j : ℕ, f j := by
  refine le_antisymm ?_ ?_
  · exact iSup_le fun S => iSup_le fun i => le_iSup (fun j : ℕ => f j) (i:ℕ)
  · refine iSup_le fun j => ?_
    exact le_trans (le_iSup (fun i : Fin (j+2) => f (i:ℕ)) ⟨j, by omega⟩)
      (le_iSup (fun S : ℕ => ⨆ i : Fin (S+2), f (i:ℕ)) j)

/-- The squared partial suprema increase to the square of the full supremum. -/
lemma iSup_fin_succ_rpow_two_eq (f : ℕ → ENNReal) :
    (⨆ S : ℕ, (⨆ i : Fin (S+2), f (i:ℕ)) ^ (2:ℝ)) = (⨆ j : ℕ, f j) ^ (2:ℝ) := by
  rw [← iSup_rpow_two (fun S : ℕ => ⨆ i : Fin (S+2), f (i:ℕ)), iSup_fin_succ_eq_iSup_nat f]

/-- A.e.-measurability of `y ↦ bandMaxTr Ψ lam H S y`. -/
lemma aemeasurable_bandMaxTr (Ψ : SchwartzMap ℝ ℂ) (lam : Fin K → ℝ) (H : Fin K → ℝ → ℂ)
    (hH : ∀ k : Fin K, MemLp (H k) 2 (volume : Measure ℝ)) (S : ℕ) :
    AEMeasurable (fun y : ℝ => bandMaxTr Ψ lam H S y) volume := by
  have h := AEMeasurable.lintegral_prod_right
    (ν := (volume : Measure ℝ)) (aemeasurable_uncurry_tonelliFun Ψ lam H hH S)
  refine h.congr (Filter.Eventually.of_forall fun y => ?_)
  exact (bandMaxTr_eq_integral_tonelliFun Ψ lam H S y).symm

/-- The truncated maximal functions of the translate increase to the maximal function of the
translate. -/
lemma bandMax_translate_eq_iSup_bandMaxTr (Ψ : SchwartzMap ℝ ℂ) (lam : Fin K → ℝ)
    (H : Fin K → ℝ → ℂ) (hH : ∀ k : Fin K, MemLp (H k) 2 (volume : Measure ℝ)) (y : ℝ) :
    bandMax Ψ lam (transH H y) = ⨆ S : ℕ, bandMaxTr Ψ lam H S y := by
  rw [bandMax_translate Ψ lam H hH y]
  rw [show (⨆ S : ℕ, bandMaxTr Ψ lam H S y)
      = ⨆ S : ℕ, ∫⁻ z, (⨆ i : Fin (S+2), ‖∑ k : Fin K,
          Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ)) * curvePtPh Ψ lam H (i:ℕ) z k‖ₑ) ^ (2:ℝ)
      from iSup_congr (fun S => bandMaxTr_eq Ψ lam H S y)]
  rw [← lintegral_iSup' (f := fun S : ℕ => fun z : ℝ =>
        (⨆ i : Fin (S+2), ‖∑ k : Fin K, Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))
          * curvePtPh Ψ lam H (i:ℕ) z k‖ₑ) ^ (2:ℝ)) ?_ ?_]
  · congr 1
    funext z
    exact (iSup_fin_succ_rpow_two_eq (fun j : ℕ => ‖∑ k : Fin K,
      Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ)) * curvePtPh Ψ lam H j z k‖ₑ)).symm
  · intro S
    have hsum : ∀ i : Fin (S+2), AEMeasurable (fun z : ℝ =>
        ∑ k : Fin K, Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))
          * curvePtPh Ψ lam H (i:ℕ) z k) volume := by
      intro i
      have hs := Finset.aemeasurable_sum (Finset.univ : Finset (Fin K))
        (f := fun k : Fin K => fun z : ℝ => Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))
          * curvePtPh Ψ lam H (i:ℕ) z k)
        (fun k _ => aemeasurable_const.mul (aemeasurable_curvePtPh Ψ lam H (hH k)))
      refine hs.congr (Filter.Eventually.of_forall fun z => ?_)
      simp only [Finset.sum_apply]
    have hsq : AEMeasurable (fun z : ℝ => (⨆ i : Fin (S+2), ‖∑ k : Fin K,
        Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ)) * curvePtPh Ψ lam H (i:ℕ) z k‖ₑ)) volume :=
      AEMeasurable.iSup (f := fun i : Fin (S+2) => fun z : ℝ => ‖∑ k : Fin K,
        Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ)) * curvePtPh Ψ lam H (i:ℕ) z k‖ₑ)
        (fun i => (hsum i).enorm)
    exact Measurable.comp_aemeasurable (ENNReal.continuous_rpow_const (y := (2:ℝ))).measurable hsq
  · refine Filter.Eventually.of_forall fun z => ?_
    intro S S' h
    refine ENNReal.rpow_le_rpow (iSup_le fun i => ?_) (by norm_num)
    exact le_iSup (fun i' : Fin (S'+2) => ‖∑ k : Fin K,
      Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ)) * curvePtPh Ψ lam H (i':ℕ) z k‖ₑ)
      (Fin.castLE (by omega) i)

/-- The `ℓ²` energy is finite for an `L²` tuple. -/
lemma bandSq_lt_top (H : Fin K → ℝ → ℂ) (hH : ∀ k : Fin K, MemLp (H k) 2 (volume : Measure ℝ)) :
    bandSq H < ⊤ := by
  unfold bandSq
  have hcongr : (fun x : ℝ => ENNReal.ofReal (∑ k : Fin K, ‖H k x‖ ^ 2))
      = fun x => ∑ k : Fin K, ENNReal.ofReal (‖H k x‖ ^ 2) := by
    funext x
    exact ENNReal.ofReal_sum_of_nonneg (fun k _ => sq_nonneg _)
  rw [hcongr, lintegral_finsetSum' (Finset.univ)
    (f := fun k : Fin K => fun x : ℝ => ENNReal.ofReal (‖H k x‖ ^ 2))
    (fun k _ => ((hH k).aemeasurable.norm.pow_const 2).ennreal_ofReal)]
  refine ENNReal.sum_lt_top.mpr fun k _ => ?_
  have h1 : Integrable (fun x : ℝ => ‖H k x‖ ^ 2) volume := by
    have := (hH k).integrable_norm_rpow (p := 2) (by norm_num) (by norm_num)
    simpa using this
  have h2 := h1.lintegral_lt_top
  simpa only [enorm_eq_ofReal_norm'] using h2

/-- A.e.-measurability in `y` of the maximal function of the translate. -/
lemma aemeasurable_bandMax_translate (Ψ : SchwartzMap ℝ ℂ) (lam : Fin K → ℝ)
    (H : Fin K → ℝ → ℂ) (hH : ∀ k : Fin K, MemLp (H k) 2 (volume : Measure ℝ)) :
    AEMeasurable (fun y : ℝ => bandMax Ψ lam (transH H y)) volume := by
  have hsup : AEMeasurable (fun y : ℝ => ⨆ S : ℕ, bandMaxTr Ψ lam H S y) volume :=
    AEMeasurable.iSup (fun S => aemeasurable_bandMaxTr Ψ lam H hH S)
  exact hsup.congr (Filter.Eventually.of_forall fun y =>
    (bandMax_translate_eq_iSup_bandMaxTr Ψ lam H hH y).symm)

/-- **The averaged one-step bound, uniformly in `S` and in `H`**: the constant depends only on
`Ψ`, `lam`, `K` and `M`. -/
theorem bandMaxTr_average_bound_uniform (Ψ : SchwartzMap ℝ ℂ) (lam : Fin K → ℝ)
    (hsep : ∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|) {M : ℝ}
    (hM : ∀ x : ℝ, ‖(Ψ : ℝ → ℂ) x‖ ≤ M) :
    ∃ Cc : ℝ, 0 < Cc ∧ ∀ (H : Fin K → ℝ → ℂ),
      (∀ k : Fin K, MemLp (H k) 2 (volume : Measure ℝ)) →
      (∀ k : Fin K, MemLp (H k) ⊤ (volume : Measure ℝ)) →
      ∀ S : ℕ, ∫⁻ y in Set.Ioo (0:ℝ) (9/10), bandMaxTr Ψ lam H S y
        ≤ ENNReal.ofReal Cc * bandSq H := by
  obtain ⟨Cch, hCchpos, hCch0⟩ := chain_bound_at_z Ψ lam hsep
  obtain ⟨CA, hCApos, hCA0⟩ := lintegral_winFL2_sq_le_uniform (Ψ := Ψ) (K := K)
  obtain ⟨CB₀, hCB₀pos, hCB0⟩ := bourgain_entropy_integral_l2_l2vec Ψ M hM
  set CB : ℝ := (CB₀ * (Real.log ((K:ℝ)+2))^2)^2 with hCBdef
  have hCBpos : 0 < CB := by
    rw [hCBdef]
    have hK : (1:ℝ) < (K:ℝ) + 2 := by
      have h : (0:ℝ) ≤ (K:ℝ) := Nat.cast_nonneg K
      linarith
    exact pow_pos (mul_pos hCB₀pos (pow_pos (Real.log_pos hK) 2)) 2
  refine ⟨Cch ^ 2 * (256 * CA + 16 * CB), by positivity, fun H hH2 hHinf S => ?_⟩
  have hA : ∫⁻ z, (ENNReal.ofReal (curveRad Ψ H (S+1) z)) ^ (2:ℝ)
      ≤ ENNReal.ofReal CA * bandSq H :=
    le_trans (lintegral_mono fun z =>
      ENNReal.rpow_le_rpow (curveRad_le_winFL2 Ψ H (S+1) z) (by norm_num)) (hCA0 H hH2)
  have hB : ∫⁻ z, (∫⁻ r in Set.Ioi (0:ℝ), min (ENNReal.ofReal (Real.sqrt (K:ℝ)))
        ((winML2 Ψ H z r) ^ ((1:ℝ)/2))) ^ (2:ℝ) ≤ ENNReal.ofReal CB * bandSq H := by
    have h := hCB0 K H hH2 hHinf
    rw [hCBdef]
    simpa only [bandSq, winML2, min_comm] using h
  refine le_trans (bandMaxTr_average_le Ψ lam H S hCchpos (fun z => hCch0 H S z)
    ((aemeasurable_uncurry_tonelliFun Ψ lam H hH2 S).mono_measure
      (MeasureTheory.Measure.prod_mono Measure.restrict_le_self le_rfl))) ?_
  refine le_trans (z_integral_le Ψ H S hCchpos
    (aemeasurable_ofReal_curveRad_rpow Ψ H hH2 (S+1)) hA hB) ?_
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_ofNat, ENNReal.ofReal_ofNat]
  exact le_of_eq (by ring)

/-- **The averaged one-step bound** in the form needed downstream, uniform in `H`. -/
theorem lintegral_bandMax_translate_le (Ψ : SchwartzMap ℝ ℂ) (lam : Fin K → ℝ)
    (hsep : ∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|) {M : ℝ}
    (hM : ∀ x : ℝ, ‖(Ψ : ℝ → ℂ) x‖ ≤ M) :
    ∃ Cc : ℝ, 0 < Cc ∧ ∀ (H : Fin K → ℝ → ℂ),
      (∀ k : Fin K, MemLp (H k) 2 (volume : Measure ℝ)) →
      (∀ k : Fin K, MemLp (H k) ⊤ (volume : Measure ℝ)) →
      ∫⁻ y in Set.Ioo (0:ℝ) (9/10), bandMax Ψ lam (transH H y) ≤ ENNReal.ofReal Cc * bandSq H := by
  obtain ⟨Cc, hCcpos, hCc⟩ := bandMaxTr_average_bound_uniform Ψ lam hsep hM
  refine ⟨Cc, hCcpos, fun H hH2 hHinf => ?_⟩
  rw [show (∫⁻ y in Set.Ioo (0:ℝ) (9/10), bandMax Ψ lam (transH H y))
      = ∫⁻ y in Set.Ioo (0:ℝ) (9/10), ⨆ S : ℕ, bandMaxTr Ψ lam H S y from
      lintegral_congr fun y => bandMax_translate_eq_iSup_bandMaxTr Ψ lam H hH2 y]
  rw [lintegral_iSup' (f := fun S : ℕ => fun y : ℝ => bandMaxTr Ψ lam H S y) ?_ ?_]
  · exact iSup_le (fun S => hCc H hH2 hHinf S)
  · intro S
    exact (aemeasurable_bandMaxTr Ψ lam H hH2 S).mono_measure Measure.restrict_le_self
  · refine Filter.Eventually.of_forall fun y => ?_
    intro S S' h
    refine lintegral_mono fun z => ENNReal.rpow_le_rpow (iSup_le fun i => ?_) (by norm_num)
    exact le_iSup (fun i' : Fin (S'+2) => ‖∑ k : Fin K, curvePt Ψ H (i':ℕ) z k
      * Complex.exp (Complex.I * (lam k : ℂ) * (((y - z : ℝ)) : ℂ))‖ₑ)
      (Fin.castLE (by omega) i)

/-! ### The band-limited `K`-function maximal bound -/

/-- Membership in `L²` is preserved by the translate `transH` / the difference `shiftH`. -/
lemma memLp_transH {H : Fin K → ℝ → ℂ} (hH : ∀ k : Fin K, MemLp (H k) 2 (volume : Measure ℝ))
    (y : ℝ) : ∀ k : Fin K, MemLp (transH H y k) 2 (volume : Measure ℝ) := fun k =>
  (hH k).comp_measurePreserving (measurePreserving_add_right volume y)

lemma memLp_shiftH {H : Fin K → ℝ → ℂ} (hH : ∀ k : Fin K, MemLp (H k) 2 (volume : Measure ℝ))
    (y : ℝ) : ∀ k : Fin K, MemLp (shiftH H y k) 2 (volume : Measure ℝ) := fun k =>
  (hH k).sub ((hH k).comp_measurePreserving (measurePreserving_add_right volume y))

/-- **The band-limited `K`-function maximal bound.**  For a tuple `H` of functions that are
band-limited to `[-a,a]` with `2·(2πa·(9/10))² < 1`, the maximal function of the band sum is
bounded by `log⁴(K+2)` times the `ℓ²` energy.  The hypotheses on the class `Adm` are exactly what
the two analytic inputs and the contraction need, so that this is a purely formal consequence of
the chain bound, the entropy input and the iteration. -/
theorem bandMax_le_of_bandlimited (Ψ : SchwartzMap ℝ ℂ) (lam : Fin K → ℝ)
    (hsep : ∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|) {M : ℝ}
    (hM : ∀ x : ℝ, ‖(Ψ : ℝ → ℂ) x‖ ≤ M)
    {a : ℝ} (ha : 0 ≤ a) (hth : 2 * (2 * Real.pi * a * (9/10)) ^ 2 < 1)
    (Adm : (Fin K → ℝ → ℂ) → Prop)
    (h2 : ∀ H, Adm H → ∀ k, MemLp (H k) 2 (volume : Measure ℝ))
    (hinf : ∀ H, Adm H → ∀ k, MemLp (H k) ⊤ (volume : Measure ℝ))
    (hint : ∀ H, Adm H → ∀ k, Integrable (H k))
    (hsup : ∀ H, Adm H → ∀ k ξ, a < |ξ| → 𝓕 (H k) ξ = 0)
    (hpres : ∀ H y, Adm H → |y| ≤ 9/10 → Adm (shiftH H y)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (H : Fin K → ℝ → ℂ) (hH : Adm H), bandMax Ψ lam H
      ≤ ENNReal.ofReal (((C * (Real.log ((K:ℝ)+2))^2)^2)) * bandSq H := by
  obtain ⟨Cc, hCcpos, hCc⟩ := lintegral_bandMax_translate_le Ψ lam hsep hM
  have hCc0 : 0 < 2 * (10/9) * Cc := by positivity
  -- the selection of the shift
  have hsel : ∀ G : {G : Fin K → ℝ → ℂ // Adm G}, ∃ y : ℝ, y ∈ Set.Ioo (0:ℝ) (9/10) ∧
      bandMax Ψ lam (transH G.1 y) ≤ ENNReal.ofReal (2 * (10/9) * Cc) * bandSq G.1 := by
    intro G
    have hG2 := h2 G.1 G.2
    have hGinf := hinf G.1 G.2
    have hfin : bandSq G.1 < ⊤ := bandSq_lt_top G.1 hG2
    have hKtop : ENNReal.ofReal Cc * bandSq G.1 ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin.ne
    obtain ⟨y, hy, hyle⟩ := exists_le_of_lintegral_le_ae (fun y : ℝ => bandMax Ψ lam (transH G.1 y))
      (aemeasurable_bandMax_translate Ψ lam G.1 hG2) (by norm_num) (hCc G.1 hG2 hGinf) hKtop
    refine ⟨y, hy, ?_⟩
    rw [show ENNReal.ofReal (9/10 - 0) = ENNReal.ofReal (9/10) by norm_num,
      show (ENNReal.ofReal Cc * bandSq G.1) + (ENNReal.ofReal Cc * bandSq G.1)
        = 2 * (ENNReal.ofReal Cc * bandSq G.1) by ring,
      mul_comm (ENNReal.ofReal (9/10)) (bandMax Ψ lam (transH G.1 y))] at hyle
    have h9 : (ENNReal.ofReal (9/10)) ≠ 0 := by simp
    have h9t : (ENNReal.ofReal (9/10)) ≠ ⊤ := ENNReal.ofReal_ne_top
    have hgoal : bandMax Ψ lam (transH G.1 y)
        ≤ (2 * (ENNReal.ofReal Cc * bandSq G.1)) / (ENNReal.ofReal (9/10)) :=
      (ENNReal.le_div_iff_mul_le (Or.inl h9) (Or.inl h9t)).mpr hyle
    have h1 : (ENNReal.ofReal (9/10))⁻¹ = ENNReal.ofReal (10/9) := by
      rw [← ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ) < 9/10)]
      congr 1
      norm_num
    have h2 : ENNReal.ofReal (2 * (10/9) * Cc)
        = (2:ENNReal) * ENNReal.ofReal (10/9) * ENNReal.ofReal Cc := by
      rw [show (2 * (10/9) * Cc : ℝ) = 2 * (10/9) * Cc by ring,
        ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_ofNat]
    calc bandMax Ψ lam (transH G.1 y)
        ≤ (2 * (ENNReal.ofReal Cc * bandSq G.1)) / (ENNReal.ofReal (9/10)) := hgoal
      _ = (2 * (ENNReal.ofReal Cc * bandSq G.1)) * (ENNReal.ofReal (9/10))⁻¹ := by
          rw [div_eq_mul_inv]
      _ = (2 * (ENNReal.ofReal Cc * bandSq G.1)) * ENNReal.ofReal (10/9) := by rw [h1]
      _ = ENNReal.ofReal (2 * (10/9) * Cc) * bandSq G.1 := by rw [h2]; ring
  let ysh : {G : Fin K → ℝ → ℂ // Adm G} → ℝ := fun G => Classical.choose (hsel G)
  have hysh_mem : ∀ G : {G : Fin K → ℝ → ℂ // Adm G}, ysh G ∈ Set.Ioo (0:ℝ) (9/10) :=
    fun G => (Classical.choose_spec (hsel G)).1
  have hysh_le : ∀ G : {G : Fin K → ℝ → ℂ // Adm G},
      bandMax Ψ lam (transH G.1 (ysh G)) ≤ ENNReal.ofReal (2 * (10/9) * Cc) * bandSq G.1 :=
    fun G => (Classical.choose_spec (hsel G)).2
  obtain ⟨CK, hCKpos, hCK⟩ := bandMax_apriori Ψ lam
  -- subadditivity (with the factor `2` coming from the squared norm)
  have hdecomp : ∀ G : {G : Fin K → ℝ → ℂ // Adm G},
      (fun k z => transH G.1 (ysh G) k z + shiftH G.1 (ysh G) k z) = G.1 := by
    intro G
    funext k z
    simp only [transH, shiftH]
    ring
  have hone : ∀ G : {G : Fin K → ℝ → ℂ // Adm G},
      bandMax Ψ lam G.1 ≤ ENNReal.ofReal (4 * (10/9) * Cc) * bandSq G.1
        + 2 * bandMax Ψ lam (shiftH G.1 (ysh G)) := by
    intro G
    have hle := bandMax_add_le Ψ lam (transH G.1 (ysh G)) (shiftH G.1 (ysh G))
      (memLp_transH (h2 G.1 G.2) (ysh G)) (memLp_shiftH (h2 G.1 G.2) (ysh G))
    rw [hdecomp G] at hle
    have hconst : (2:ENNReal) * (ENNReal.ofReal (2 * (10/9) * Cc) * bandSq G.1)
        = ENNReal.ofReal (4 * (10/9) * Cc) * bandSq G.1 := by
      have h4 : ENNReal.ofReal (4 * (10/9) * Cc)
          = (2:ENNReal) * ENNReal.ofReal (2 * (10/9) * Cc) := by
        rw [show (4 * (10/9) * Cc : ℝ) = 2 * (2 * (10/9) * Cc) by ring,
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_ofNat]
      rw [h4]; ring
    calc bandMax Ψ lam G.1
        ≤ 2 * bandMax Ψ lam (transH G.1 (ysh G)) + 2 * bandMax Ψ lam (shiftH G.1 (ysh G)) := hle
      _ ≤ 2 * (ENNReal.ofReal (2 * (10/9) * Cc) * bandSq G.1)
            + 2 * bandMax Ψ lam (shiftH G.1 (ysh G)) :=
          add_le_add (mul_le_mul_of_nonneg_left (hysh_le G) (bot_le)) (le_refl _)
      _ = ENNReal.ofReal (4 * (10/9) * Cc) * bandSq G.1
            + 2 * bandMax Ψ lam (shiftH G.1 (ysh G)) := by rw [hconst]
  -- the contraction, in the `2 · SQ` form
  have hcon : ∀ G : {G : Fin K → ℝ → ℂ // Adm G},
      2 * bandSq (shiftH G.1 (ysh G)) ≤ ENNReal.ofReal (2 * (2 * Real.pi * a * (9/10)) ^ 2) * bandSq G.1 := by
    intro G
    have hbase := bandSq_translate_sub_le (H := G.1) (a := a) (y := ysh G) ha
      (hint G.1 G.2) (h2 G.1 G.2) (hsup G.1 G.2)
    have hstep : 2 * bandSq (shiftH G.1 (ysh G))
        ≤ 2 * (ENNReal.ofReal ((2 * Real.pi * a * |ysh G|) ^ 2) * bandSq G.1) :=
      mul_le_mul_of_nonneg_left hbase (bot_le)
    have hyabs : |ysh G| ≤ 9/10 := le_of_lt (by rw [abs_of_pos (hysh_mem G).1]; exact (hysh_mem G).2)
    have hnn : 0 ≤ 2 * Real.pi * a := by positivity
    have hle2 : (2 * Real.pi * a * |ysh G|) ^ 2 ≤ (2 * Real.pi * a * (9/10)) ^ 2 := by
      have h1 : 2 * Real.pi * a * |ysh G| ≤ 2 * Real.pi * a * (9/10) :=
        mul_le_mul_of_nonneg_left hyabs hnn
      have h2 : 0 ≤ 2 * Real.pi * a * |ysh G| := by positivity
      nlinarith [h1, h2, hnn, abs_nonneg (ysh G)]
    have hconst : 2 * (ENNReal.ofReal ((2 * Real.pi * a * |ysh G|) ^ 2) * bandSq G.1)
        = ENNReal.ofReal (2 * (2 * Real.pi * a * |ysh G|) ^ 2) * bandSq G.1 := by
      rw [show (2 * (2 * Real.pi * a * |ysh G|) ^ 2 : ℝ) = 2 * ((2 * Real.pi * a * |ysh G|) ^ 2)
          by ring, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_ofNat]
      ring
    calc 2 * bandSq (shiftH G.1 (ysh G))
        ≤ 2 * (ENNReal.ofReal ((2 * Real.pi * a * |ysh G|) ^ 2) * bandSq G.1) := hstep
      _ = ENNReal.ofReal (2 * (2 * Real.pi * a * |ysh G|) ^ 2) * bandSq G.1 := by rw [hconst]
      _ ≤ ENNReal.ofReal (2 * (2 * Real.pi * a * (9/10)) ^ 2) * bandSq G.1 := by
          refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) bot_le
          linarith [hle2]
  -- the iteration
  refine ⟨Real.sqrt (4 * (10/9) * Cc / (1 - 2 * (2 * Real.pi * a * (9/10)) ^ 2))
      / (Real.log ((K:ℝ) + 2)) ^ 2 + 1, by positivity, fun H hH => ?_⟩
  have hiter := Commons.Analysis.Maximal.iter_bound_shift (X := {G : Fin K → ℝ → ℂ // Adm G})
    (M := fun G : {G : Fin K → ℝ → ℂ // Adm G} => bandMax Ψ lam G.1)
    (SQ := fun G : {G : Fin K → ℝ → ℂ // Adm G} => bandSq G.1)
    (T := fun G : {G : Fin K → ℝ → ℂ // Adm G} =>
      ⟨shiftH G.1 (ysh G), hpres G.1 (ysh G) G.2
        (le_of_lt (by rw [abs_of_pos (hysh_mem G).1]; exact (hysh_mem G).2))⟩)
    (A := 4 * (10/9) * Cc) (ρ := 2 * (2 * Real.pi * a * (9/10)) ^ 2) (CK := CK * (K:ℝ))
    (by positivity) (by positivity) (by positivity) hth (by positivity)
    (fun G => hone G) (fun G => hcon G) (fun G => hCK G.1 (h2 G.1 G.2))
    ⟨H, hH⟩
  -- constant bookkeeping: `A/(1-ρ) ≤ ((sqrt(A/(1-ρ))/log² + 1) · log²)²`
  refine hiter.trans ?_
  refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) bot_le
  have hlog : 0 < Real.log ((K:ℝ) + 2) := by
    refine Real.log_pos ?_
    have h : (0:ℝ) ≤ (K:ℝ) := Nat.cast_nonneg K
    linarith
  have hlog2 : 0 < (Real.log ((K:ℝ) + 2)) ^ 2 := pow_pos hlog 2
  have hsq : (Real.sqrt (4 * (10/9) * Cc / (1 - 2 * (2 * Real.pi * a * (9/10)) ^ 2))
      / (Real.log ((K:ℝ) + 2)) ^ 2 + 1) * (Real.log ((K:ℝ) + 2)) ^ 2
      = Real.sqrt (4 * (10/9) * Cc / (1 - 2 * (2 * Real.pi * a * (9/10)) ^ 2))
        + (Real.log ((K:ℝ) + 2)) ^ 2 := by
    field_simp
  have hnn : 0 ≤ Real.sqrt (4 * (10/9) * Cc / (1 - 2 * (2 * Real.pi * a * (9/10)) ^ 2)) :=
    Real.sqrt_nonneg _
  rw [hsq]
  have hx : Real.sqrt (4 * (10/9) * Cc / (1 - 2 * (2 * Real.pi * a * (9/10)) ^ 2)) ^ 2
      = 4 * (10/9) * Cc / (1 - 2 * (2 * Real.pi * a * (9/10)) ^ 2) :=
    Real.sq_sqrt (by positivity)
  have hexp : (Real.sqrt (4 * (10/9) * Cc / (1 - 2 * (2 * Real.pi * a * (9/10)) ^ 2))
        + (Real.log ((K:ℝ) + 2)) ^ 2) ^ 2
      = Real.sqrt (4 * (10/9) * Cc / (1 - 2 * (2 * Real.pi * a * (9/10)) ^ 2)) ^ 2
        + 2 * Real.sqrt (4 * (10/9) * Cc / (1 - 2 * (2 * Real.pi * a * (9/10)) ^ 2))
          * (Real.log ((K:ℝ) + 2)) ^ 2
        + ((Real.log ((K:ℝ) + 2)) ^ 2) ^ 2 := by ring
  rw [hexp, hx]
  nlinarith [hnn, hlog2, sq_nonneg ((Real.log ((K:ℝ) + 2)) ^ 2)]

end

end Commons.Analysis.Fourier

open _root_.MeasureTheory
open scoped _root_.ENNReal FourierTransform

namespace Commons.Analysis.Fourier

/-- **The convolution theorem** (function level, `ℝ → ℂ`, `L¹` functions):
`𝓕(f ★ κ) = 𝓕f · 𝓕κ`, where `(f ★ κ)(x) = ∫ y, f y * κ (x - y)`.

(Mathlib's `Real.fourier_mul_convolution_eq`, unfolded to the integral convolution.) -/
theorem fourier_convolution (f κ : ℝ → ℂ) (hf : Integrable f (volume : Measure ℝ))
    (hκ : Integrable κ (volume : Measure ℝ)) (η : ℝ) :
    FourierTransform.fourier (fun x : ℝ => ∫ y, f y * κ (x - y)) η
      = FourierTransform.fourier f η * FourierTransform.fourier κ η := by
  have h := Real.fourier_mul_convolution_eq (f₁ := f) (f₂ := κ) hf hκ η
  have hconv : (fun x : ℝ => ∫ y, f y * κ (x - y))
      = MeasureTheory.convolution f κ (ContinuousLinearMap.mul ℂ ℂ) (volume : Measure ℝ) := by
    funext x
    rw [convolution_def]
    rfl
  rw [hconv]
  exact h

/-- **The convolution theorem with a compactly supported smooth kernel**: the slices are
`f ★ κ` with `κ = 𝓕⁻ψ`, so we record the `𝓕κ = ψ` side as well (for Schwartz kernels). -/
theorem fourier_convolution_schwartz (f : ℝ → ℂ) (κ : SchwartzMap ℝ ℂ)
    (hf : Integrable f (volume : Measure ℝ)) (η : ℝ) :
    FourierTransform.fourier (fun x : ℝ => ∫ y, f y * (κ : ℝ → ℂ) (x - y)) η
      = FourierTransform.fourier f η * FourierTransform.fourier (κ : ℝ → ℂ) η :=
  fourier_convolution f (κ : ℝ → ℂ) hf κ.integrable η

end Commons.Analysis.Fourier

open _root_.MeasureTheory
open scoped _root_.ENNReal FourierTransform

set_option maxHeartbeats 8000000

namespace Commons.Analysis.Fourier

/-- **The per-slice Plancherel identity.**  For `f ∈ L²` and `κ ∈ L¹` with `𝓕κ = ψ`, the `L²` mass
of the slice `f ★ κ` is the weighted `L²` mass of the `L²`-transform of `f`:
`∫⁻ x, ‖(f★κ) x‖² = ∫⁻ ξ, ‖𝓕(toLp f) ξ‖² · ψ(ξ)²`.

This is `lintegral_convolution_sq_eq_l2` (which pairs the *`L²`-transform* of `f` with the
*function-level* transform of `κ`) followed by `𝓕κ = ψ`.  **Every exponent below is the real
exponent `(2:ℝ)`** — a `^ 2` would be a `Nat` power and would not match the commons lemma. -/
theorem lintegral_slice_sq_eq (f : ℝ → ℂ) (κ : ℝ → ℂ) (ψ : ℝ → ℝ)
    (hf2 : MemLp f 2 (volume : Measure ℝ)) (hκ1 : MemLp κ 1 (volume : Measure ℝ))
    (hκF : ∀ ξ : ℝ, FourierTransform.fourier κ ξ = (ψ ξ : ℂ)) (hψnn : ∀ ξ : ℝ, 0 ≤ ψ ξ) :
    ∫⁻ x, ENNReal.ofReal ‖∫ y : ℝ, f y * κ (x - y)‖ ^ (2:ℝ)
      = ∫⁻ ξ, (ENNReal.ofReal
            ‖((FourierTransform.fourier (hf2.toLp f) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) ξ‖)
          ^ (2:ℝ) * (ENNReal.ofReal (ψ ξ)) ^ (2:ℝ) := by
  rw [lintegral_convolution_sq_eq_l2 (g := f) (k := κ) hf2 hκ1]
  refine lintegral_congr fun ξ => ?_
  rw [hκF ξ]
  rw [show ‖(ψ ξ : ℂ)‖ = ψ ξ by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hψnn ξ)],
    ENNReal.ofReal_mul (norm_nonneg _),
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ (2:ℝ))]

/-- **The bracketing bridge.**  `bandSq`'s form of the energy,
`ENNReal.ofReal (∑_k ‖H_k x‖ ^ 2)`, has the (Nat) power *inside* `ofReal`; the per-slice Plancherel
identity `lintegral_slice_sq_eq` produces `(ENNReal.ofReal ‖·‖) ^ (2:ℝ)` with the exponent on the
`ENNReal`.  This lemma converts the first into the second **once**, pointwise, so that everything
downstream inherits the right normal form. -/
lemma bandSq_eq_sum_ofReal_rpow {K : ℕ} (H : Fin K → ℝ → ℂ) (x : ℝ) :
    ENNReal.ofReal (∑ k : Fin K, ‖H k x‖ ^ 2)
      = ∑ k : Fin K, (ENNReal.ofReal ‖H k x‖) ^ (2:ℝ) := by
  rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => sq_nonneg _)]
  exact Finset.sum_congr rfl fun k _ => by
    rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast,
      ← ENNReal.ofReal_pow (norm_nonneg _)]

/-- **The real-valued bridge.**  For a *nonnegative* real family `a` (`‖·‖` always is),
`ofReal (∑_k a_k²) = ∑_k (ofReal a_k) ^ (2:ℝ)`.

The nonnegativity hypothesis is **not** cosmetic: `ENNReal.ofReal` truncates negatives, so without it
the identity is false (`ENNReal.ofReal_pow` itself carries `0 ≤ p`).  This is the form the slice
energy bound instantiates at `a k = ‖∫ y, f y * κ k (x - y)‖`. -/
lemma sum_sq_ofReal_eq_sum_rpow {K : ℕ} (a : Fin K → ℝ) (ha : ∀ k : Fin K, 0 ≤ a k) :
    ENNReal.ofReal (∑ k : Fin K, a k ^ 2)
      = ∑ k : Fin K, (ENNReal.ofReal (a k)) ^ (2:ℝ) := by
  rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => sq_nonneg _)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast]
  exact ENNReal.ofReal_pow (p := a k) (ha k) 2

/-- **The instantiation of the bridge at the slices.**  The energy integrand of the slice
construction, `ENNReal.ofReal (∑_k ‖(f ★ κ_k) x‖²)`, is rewritten *as a function* into the normal
form produced by `lintegral_slice_sq_eq`.  Doing it as a function-level `funext` (rather than inside
the integral) keeps the normal form fixed for everything downstream. -/
lemma slice_energy_integrand_eq {K : ℕ} (f : ℝ → ℂ) (κ : Fin K → ℝ → ℂ) :
    (fun x : ℝ => ENNReal.ofReal (∑ k : Fin K, ‖∫ y : ℝ, f y * κ k (x - y)‖ ^ 2))
      = fun x : ℝ => ∑ k : Fin K,
          (ENNReal.ofReal ‖∫ y : ℝ, f y * κ k (x - y)‖) ^ (2:ℝ) := by
  funext x
  exact sum_sq_ofReal_eq_sum_rpow
    (fun k : Fin K => ‖∫ y : ℝ, f y * κ k (x - y)‖) (fun _ => norm_nonneg _)

/-- **The `eLpNorm`/`enorm` bridge for an `Lp` element**: the `eLpNorm` of the representative is the
`enorm` of the `Lp` norm.  (The naive statement `eLpNorm (⇑u) 2 = ‖u‖` is a **type** error —
`eLpNorm` is `ℝ≥0∞`-valued and `‖u‖` is `ℝ`.) -/
lemma eLpNorm_coeFn_eq_enorm_norm (u : Lp ℂ 2 (volume : Measure ℝ)) :
    eLpNorm (⇑u) 2 (volume : Measure ℝ) = ‖u‖ₑ := by
  rw [← ofReal_norm, MeasureTheory.Lp.norm_def, ENNReal.ofReal_toReal]
  exact ne_of_lt (MeasureTheory.Lp.eLpNorm_lt_top u)

/-- A.e.-measurability is preserved by the `(2:ℝ)`-power on `ℝ≥0∞`. -/
lemma aemeasurable_rpow_two {a : ℝ → ENNReal} (ha : AEMeasurable a (volume : Measure ℝ)) :
    AEMeasurable (fun ξ : ℝ => (a ξ) ^ (2:ℝ)) (volume : Measure ℝ) :=
  Measurable.comp_aemeasurable (ENNReal.continuous_rpow_const (y := (2:ℝ))).measurable ha

/-- **`Lp`-level Plancherel against the slice energy form**: the `L²` mass of the `L²`-transform of
`f`, written at the `ℝ≥0∞` level, equals the `L²` mass of `f`.

This is the final step of `slice_energy_le`, isolated here on purpose: in this standalone context
there are no `set`-abbreviations interfering with the bracketing-sensitive rewrites below. -/
lemma lintegral_enorm_fourier_toLp_eq (f : ℝ → ℂ) (hf2 : MemLp f 2 (volume : Measure ℝ)) :
    ∫⁻ ξ, ‖((FourierTransform.fourier (hf2.toLp f) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) ξ‖ₑ
        ^ (2:ℝ)
      = ∫⁻ x, ‖f x‖ₑ ^ (2:ℝ) := by
  have hLa : ∫⁻ ξ, ‖((FourierTransform.fourier (hf2.toLp f) : Lp ℂ 2 (volume : Measure ℝ)) :
          ℝ → ℂ) ξ‖ₑ ^ (2:ℝ)
      = (eLpNorm (fun ξ : ℝ => ((FourierTransform.fourier (hf2.toLp f) :
            Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) ξ) 2 (volume : Measure ℝ)) ^ (2:ℝ) := by
    rw [eLpNorm_two_eq _ (Lp.aestronglyMeasurable _), ← ENNReal.rpow_mul, show ((1:ℝ)/2) * 2 = 1 by norm_num,
      ENNReal.rpow_one]
  have hLb : ∫⁻ x, ‖f x‖ₑ ^ (2:ℝ) = (eLpNorm f 2 (volume : Measure ℝ)) ^ (2:ℝ) := by
    rw [eLpNorm_two_eq _ hf2.aestronglyMeasurable, ← ENNReal.rpow_mul, show ((1:ℝ)/2) * 2 = 1 by norm_num,
      ENNReal.rpow_one]
  rw [hLa, hLb, eLpNorm_coeFn_eq_enorm_norm (FourierTransform.fourier (hf2.toLp f)),
    ← ofReal_norm, MeasureTheory.Lp.norm_fourier_eq]
  congr 1
  rw [ofReal_norm, ← eLpNorm_coeFn_eq_enorm_norm (hf2.toLp f)]
  exact eLpNorm_congr_ae hf2.coeFn_toLp

/-- The `ℝ≥0∞`-level form of the same Plancherel statement, with the *slice* normal form
`(ENNReal.ofReal ‖𝓕u ξ‖) ^ (2:ℝ)` produced by `lintegral_slice_sq_eq`, and with the right-hand side
in the `ofReal (‖f x‖ ^ 2)` normal form produced by `bandSq`/`sum_sq_ofReal_eq_sum_rpow`. -/
lemma lintegral_rpow_two_ofReal_fourier_toLp_eq (f : ℝ → ℂ)
    (hf2 : MemLp f 2 (volume : Measure ℝ)) :
    ∫⁻ ξ, (ENNReal.ofReal ‖((FourierTransform.fourier (hf2.toLp f) :
        Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) ξ‖) ^ (2:ℝ)
      = ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2) := by
  rw [lintegral_congr (fun ξ => by rw [ofReal_norm])]
  rw [lintegral_enorm_fourier_toLp_eq f hf2]
  refine lintegral_congr fun x => ?_
  rw [← ofReal_norm, show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast,
    ← ENNReal.ofReal_pow (norm_nonneg (f x)) 2]

/-- **The slice energy bound.**  If `κ_k ∈ L¹` has `𝓕κ_k = ψ_k`, all `ψ_k ≥ 0`, and `∑_k ψ_k² ≤ 2`
pointwise, then the total `L²` energy of the slices `f ★ κ_k` (for `f ∈ L²`) is at most `2` times
the `L²` energy of `f`.  This is the completed-square version of the classical partition-of-unity
energy bound, with the `L²` mass written in the `ℝ≥0∞` normal form used by `bandSq`. -/
lemma slice_energy_le {K : ℕ} (f : ℝ → ℂ) (κ : Fin K → ℝ → ℂ) (ψ : Fin K → ℝ → ℝ)
    (hf2 : MemLp f 2 (volume : Measure ℝ))
    (hκ1 : ∀ k : Fin K, MemLp (κ k) 1 (volume : Measure ℝ))
    (hκm : ∀ k : Fin K, Measurable (κ k))
    (hκF : ∀ k : Fin K, ∀ ξ : ℝ, FourierTransform.fourier (κ k) ξ = (ψ k ξ : ℂ))
    (hψm : ∀ k : Fin K, Measurable (ψ k))
    (hψnn : ∀ k : Fin K, ∀ ξ : ℝ, 0 ≤ ψ k ξ)
    (hbound : ∀ ξ : ℝ, ∑ k : Fin K, (ψ k ξ) ^ 2 ≤ 2) :
    ∫⁻ x, ENNReal.ofReal (∑ k : Fin K, ‖∫ y : ℝ, f y * κ k (x - y)‖ ^ 2)
      ≤ 2 * ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2) := by
  have hslice_meas : ∀ k : Fin K, AEMeasurable
      (fun x : ℝ => (ENNReal.ofReal ‖∫ y : ℝ, f y * κ k (x - y)‖) ^ (2:ℝ))
      (volume : Measure ℝ) :=
    fun k => aemeasurable_rpow_two
      ((aestronglyMeasurable_conv hf2 (hκm k)).aemeasurable.norm.ennreal_ofReal)
  have hGm : AEMeasurable (fun ξ : ℝ => ENNReal.ofReal
      ‖((FourierTransform.fourier (hf2.toLp f) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) ξ‖)
      (volume : Measure ℝ) :=
    (MeasureTheory.Lp.aestronglyMeasurable (FourierTransform.fourier (hf2.toLp f))).aemeasurable.norm.ennreal_ofReal
  have hspec_meas : ∀ k : Fin K, AEMeasurable (fun ξ : ℝ =>
      (ENNReal.ofReal ‖((FourierTransform.fourier (hf2.toLp f) :
          Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) ξ‖) ^ (2:ℝ)
        * (ENNReal.ofReal (ψ k ξ)) ^ (2:ℝ)) (volume : Measure ℝ) :=
    fun k => (aemeasurable_rpow_two hGm).mul
      (aemeasurable_rpow_two ((hψm k).aemeasurable.ennreal_ofReal))
  calc ∫⁻ x, ENNReal.ofReal (∑ k : Fin K, ‖∫ y : ℝ, f y * κ k (x - y)‖ ^ 2)
      = ∑ k : Fin K, ∫⁻ x, (ENNReal.ofReal ‖∫ y : ℝ, f y * κ k (x - y)‖) ^ (2:ℝ) := by
        rw [lintegral_congr (fun x => sum_sq_ofReal_eq_sum_rpow _ (fun _ => norm_nonneg _))]
        exact lintegral_finsetSum' Finset.univ (fun k _ => hslice_meas k)
    _ = ∑ k : Fin K, ∫⁻ ξ, (ENNReal.ofReal ‖((FourierTransform.fourier (hf2.toLp f) :
            Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) ξ‖) ^ (2:ℝ)
          * (ENNReal.ofReal (ψ k ξ)) ^ (2:ℝ) :=
        Finset.sum_congr rfl
          fun k _ => lintegral_slice_sq_eq f (κ k) (ψ k) hf2 (hκ1 k) (hκF k) (hψnn k)
    _ = ∫⁻ ξ, ∑ k : Fin K, (ENNReal.ofReal ‖((FourierTransform.fourier (hf2.toLp f) :
            Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) ξ‖) ^ (2:ℝ)
          * (ENNReal.ofReal (ψ k ξ)) ^ (2:ℝ) :=
        (lintegral_finsetSum' Finset.univ (fun k _ => hspec_meas k)).symm
    _ ≤ ∫⁻ ξ, (ENNReal.ofReal ‖((FourierTransform.fourier (hf2.toLp f) :
            Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) ξ‖) ^ (2:ℝ) * 2 := by
        refine lintegral_mono fun ξ => ?_
        rw [← Finset.mul_sum]
        gcongr
        rw [← sum_sq_ofReal_eq_sum_rpow (fun k : Fin K => ψ k ξ) (fun k => hψnn k ξ)]
        simpa using ENNReal.ofReal_le_ofReal (hbound ξ)
    _ = 2 * ∫⁻ ξ, (ENNReal.ofReal ‖((FourierTransform.fourier (hf2.toLp f) :
            Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) ξ‖) ^ (2:ℝ) := by
        rw [lintegral_mul_const'' (2 : ℝ≥0∞) (aemeasurable_rpow_two hGm)]
        exact mul_comm _ _
    _ = 2 * ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2) := by
        rw [lintegral_rpow_two_ofReal_fourier_toLp_eq f hf2]

end Commons.Analysis.Fourier

open _root_.MeasureTheory
open scoped _root_.ENNReal

namespace Commons.Analysis.Fourier

/-- **A smooth cell bump.**  For `0 < w` and `0 < η` there is a `C^∞` function `ψ` with
`0 ≤ ψ ≤ 1`, `ψ ≡ 1` on the closed cell `[c-w, c+w]` and `ψ = 0` off the enlarged cell of
half-width `w + η`.

The construction uses the square (`(x-c)²`) rather than `|x - c|`, which makes the composition with
the (smooth) cutoff automatic: the inner function is a polynomial. -/
theorem exists_cellBump (c w η : ℝ) (hw : 0 < w) (hη : 0 < η) :
    ∃ ψ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ ∧ (∀ x, 0 ≤ ψ x) ∧ (∀ x, ψ x ≤ 1) ∧
      (∀ x : ℝ, |x - c| ≤ w → ψ x = 1) ∧ (∀ x : ℝ, w + η ≤ |x - c| → ψ x = 0) := by
  obtain ⟨f, hfc, hf1, hf0, hfnn, hfle, -⟩ :=
    Commons.Analysis.ContDiff.exists_smooth_cutoff_infty 1 1 le_rfl le_rfl
  have hD : 0 < (w + η) ^ 2 - w ^ 2 := by nlinarith
  refine ⟨fun x : ℝ => f (((x - c) ^ 2 - w ^ 2) / ((w + η) ^ 2 - w ^ 2)),
    ?_, ?_, ?_, ?_, ?_⟩
  · exact hfc.comp ((by fun_prop : ContDiff ℝ (⊤ : ℕ∞)
      fun x : ℝ => ((x - c) ^ 2 - w ^ 2) / ((w + η) ^ 2 - w ^ 2)))
  · intro x
    exact hfnn _
  · intro x
    exact hfle _
  · intro x hx
    refine hf1 _ ?_
    have h1 : (x - c) ^ 2 ≤ w ^ 2 := by
      nlinarith [hx, abs_nonneg (x - c), hw, sq_abs (x - c)]
    have h2 : ((x - c) ^ 2 - w ^ 2) / ((w + η) ^ 2 - w ^ 2) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt hD)
    simpa using h2
  · intro x hx
    refine hf0 _ ?_
    have h1 : (w + η) ^ 2 ≤ (x - c) ^ 2 := by
      have h3 : (w + η) * (w + η) ≤ |x - c| * |x - c| :=
        mul_self_le_mul_self (by linarith : (0:ℝ) ≤ w + η) hx
      nlinarith [h3, sq_abs (x - c)]
    rw [le_div_iff₀ hD]
    linarith

/-- **At most two cells meet.**  If the centres `c k` are `D`-separated and each `k ∈ s` has its
centre within `a < D` of `x`, then `s` has at most two elements.  (Equivalently: three pairwise
`D`-separated centres cannot all lie in an interval of length `2a < 2D`.) -/
lemma card_le_two_of_lt {K : ℕ} (c : Fin K → ℝ) {a D : ℝ}
    (hD : ∀ k l : Fin K, k ≠ l → D ≤ |c k - c l|) (haD : a < D) (x : ℝ) (s : Finset (Fin K))
    (hs : ∀ k ∈ s, |x - c k| < a) : s.card ≤ 2 := by
  by_contra hcard
  push_neg at hcard
  have hne : s.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨q, hq, hqmax⟩ := Finset.exists_max_image s c hne
  obtain ⟨p, hp, hpmin⟩ := Finset.exists_min_image s c hne
  have hcpq : c p ≤ c q := hqmax p hp
  -- a third element
  have h21 : 1 < (s.erase p).card := by
    rw [Finset.card_erase_of_mem hp]
    omega
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp h21
  have hthird : ∃ t ∈ s.erase p, t ≠ q := by
    by_cases huq : u = q
    · exact ⟨v, hv, fun hvq => huv (by rw [huq, hvq])⟩
    · exact ⟨u, hu, huq⟩
  obtain ⟨t, ht, htq⟩ := hthird
  have hts : t ∈ s := Finset.mem_of_mem_erase ht
  have htp : t ≠ p := Finset.ne_of_mem_erase ht
  have hcpt : c p ≤ c t := hpmin t hts
  have hctq : c t ≤ c q := hqmax t hts
  have h1 : D ≤ c t - c p := by
    have h := hD p t (Ne.symm htp)
    rw [abs_sub_comm, abs_of_nonneg (by linarith)] at h
    linarith
  have h2 : D ≤ c q - c t := by
    have h := hD q t (Ne.symm htq)
    rw [abs_of_nonneg (by linarith)] at h
    linarith
  have h3 : c q - c p ≤ |x - c q| + |x - c p| := by
    have h := abs_sub_le (c q) x (c p)
    rw [abs_of_nonneg (by linarith)] at h
    linarith [abs_sub_comm x (c q), abs_sub_comm x (c p)]
  have h4 : |x - c q| + |x - c p| < 2 * a := by
    have := hs q hq
    have := hs p hp
    linarith
  linarith

/-- **The cell bumps of a `1`-separated frequency family**, with the two-overlap bound
`∑_k ψ_k² ≤ 2`.  The cells have half-width `w` (so one needs `4πw ≤ 1` for them to fit between
the `1`-separated frequencies) and the supports are contained in the cells of half-width `w + η`
with `η < w`. -/
theorem exists_cellBumps {K : ℕ} (lam : Fin K → ℝ)
    (hsep : ∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|)
    (w η : ℝ) (hw : 0 < w) (hw4 : 4 * Real.pi * w ≤ 1) (hη : 0 < η) (hηw : η < w) :
    ∃ ψ : Fin K → ℝ → ℝ,
      (∀ k, ContDiff ℝ (⊤ : ℕ∞) (ψ k)) ∧
      (∀ k x, 0 ≤ ψ k x) ∧ (∀ k x, ψ k x ≤ 1) ∧
      (∀ k x, |x + lam k / (2 * Real.pi)| ≤ w → ψ k x = 1) ∧
      (∀ k x, w + η ≤ |x + lam k / (2 * Real.pi)| → ψ k x = 0) ∧
      (∀ x, ∑ k, (ψ k x) ^ 2 ≤ 2) := by
  choose ψ hψ using fun k : Fin K =>
    exists_cellBump (-(lam k) / (2 * Real.pi)) w η hw hη
  have hcenter : ∀ (x : ℝ) (k : Fin K), x - (-(lam k) / (2 * Real.pi)) = x + lam k / (2 * Real.pi) := by
    intro x k; ring
  refine ⟨ψ, fun k => (hψ k).1, fun k x => (hψ k).2.1 x, fun k x => (hψ k).2.2.1 x,
    fun k x hx => (hψ k).2.2.2.1 x (by rw [hcenter]; exact hx),
    fun k x hx => (hψ k).2.2.2.2 x (by rw [hcenter]; exact hx), ?_⟩
  intro x
  have hsupp : ∀ k : Fin K, ψ k x ≠ 0 → |x + lam k / (2 * Real.pi)| < w + η := by
    intro k hk
    by_contra hlt
    push_neg at hlt
    exact hk ((hψ k).2.2.2.2 x (by rw [hcenter]; exact hlt))
  have hcent : ∀ k l : Fin K, k ≠ l →
      2 * w ≤ |(-(lam k) / (2 * Real.pi)) - (-(lam l) / (2 * Real.pi))| := by
    intro k l hkl
    have hkl' : 4 * Real.pi * w ≤ |lam k - lam l| := le_trans hw4 (hsep k l hkl)
    rw [show (-(lam k) / (2 * Real.pi)) - (-(lam l) / (2 * Real.pi))
        = (lam l - lam k) / (2 * Real.pi) by ring, abs_div,
      abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi),
      le_div_iff₀ (by positivity : (0:ℝ) < 2 * Real.pi), abs_sub_comm]
    linarith
  have hcard := card_le_two_of_lt (fun k : Fin K => -(lam k) / (2 * Real.pi)) hcent
    (by linarith : w + η < 2 * w) x (Finset.univ.filter fun k => ψ k x ≠ 0)
    (fun k hk => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
      rw [hcenter]
      exact hsupp k hk)
  have hsum : ∑ k : Fin K, (ψ k x) ^ 2
      = ∑ k ∈ Finset.univ.filter (fun k => ψ k x ≠ 0), (ψ k x) ^ 2 := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : ψ k x = 0
    · rw [if_neg (by simpa using hk), hk]; ring
    · rw [if_pos (by simpa using hk)]
  rw [hsum]
  calc ∑ k ∈ Finset.univ.filter (fun k => ψ k x ≠ 0), (ψ k x) ^ 2
      ≤ ∑ _k ∈ Finset.univ.filter (fun k => ψ k x ≠ 0), (1 : ℝ) := by
        refine Finset.sum_le_sum fun k _ => ?_
        have h1 := (hψ k).2.1 x
        have h2 := (hψ k).2.2.1 x
        nlinarith
    _ = ((Finset.univ.filter fun k => ψ k x ≠ 0).card : ℝ) := by simp
    _ ≤ 2 := by exact_mod_cast hcard

end Commons.Analysis.Fourier

open _root_.MeasureTheory
open scoped _root_.ENNReal FourierTransform

namespace Commons.Analysis.Fourier

/-- **The `𝓕⁻`-kernel of a smooth bump.**  If `ψ` is `C^∞` and vanishes outside the cell of
half-width `R` around `c`, then `κ := 𝓕⁻ψ` is an `L¹ ∩ L²` function with `𝓕κ = ψ` (function
level). -/
lemma exists_fourierInv_kernel (ψ : ℝ → ℝ) (hψc : ContDiff ℝ (⊤ : ℕ∞) ψ) (c R : ℝ)
    (hR : 0 < R) (hψR : ∀ x : ℝ, R ≤ |x - c| → ψ x = 0) :
    ∃ κ : ℝ → ℂ, Continuous κ ∧ Integrable κ (volume : Measure ℝ) ∧
      MemLp κ 2 (volume : Measure ℝ) ∧ MemLp κ ⊤ (volume : Measure ℝ) ∧
      (∃ C : ℝ, ∀ x : ℝ, ‖κ x‖ ≤ C) ∧
      (∀ ξ : ℝ, FourierTransform.fourier κ ξ = (ψ ξ : ℂ)) := by
  have hcont : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => (ψ x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hψc
  have hsupp : HasCompactSupport (fun x : ℝ => (ψ x : ℂ)) :=
    HasCompactSupport.intro (isCompact_Icc (a := c - R) (b := c + R)) (fun x hx => by
      have h : R ≤ |x - c| := by
        rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
        rcases hx with h | h
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; linarith
      rw [hψR x h]; simp)
  let ψcS : SchwartzMap ℝ ℂ := hsupp.toSchwartzMap hcont
  have hcoe : (⇑ψcS : ℝ → ℂ) = fun x : ℝ => (ψ x : ℂ) := rfl
  let κS : SchwartzMap ℝ ℂ := 𝓕⁻ ψcS
  have hκS : κS = 𝓕⁻ ψcS := rfl
  refine ⟨⇑κS, κS.continuous, ?_, ?_, ?_, ?_, ?_⟩
  · exact SchwartzMap.integrable κS
  · exact SchwartzMap.memLp κS (p := 2)
  · exact SchwartzMap.memLp κS (p := ⊤)
  · exact ⟨SchwartzMap.seminorm ℂ 0 0 κS, fun x => SchwartzMap.norm_le_seminorm ℂ κS x⟩
  · intro ξ
    rw [← SchwartzMap.fourier_coe, hκS, FourierInvPair.fourier_fourierInv_eq, hcoe]

/-- **The slice kernels of a `1`-separated frequency family**: smooth bumps `ψ_k` on the cells
together with their inverse-Fourier kernels `κ_k := 𝓕⁻ψ_k`.  We record exactly the transform-side
properties the slice construction consumes: `𝓕κ_k = ψ_k` (so the convolution theorem gives
`𝓕(f ★ κ_k) = ψ_k · 𝓕f`), `L¹`/`L²`, `Σ_k ψ_k² ≤ 2` (hence `Σ_k ‖𝓕κ_k‖² ≤ 2`), the cell
conditions needed for the *identification* (`ψ_k ≡ 1` on the band's support), and the support
bound needed by the crux (`𝓕κ_k` supported in the cell of half-width `w + η`). -/
theorem exists_cellKernels {K : ℕ} (lam : Fin K → ℝ)
    (hsep : ∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|)
    (w η : ℝ) (hw : 0 < w) (hw4 : 4 * Real.pi * w ≤ 1) (hη : 0 < η) (hηw : η < w) :
    ∃ (ψ : Fin K → ℝ → ℝ) (κ : Fin K → ℝ → ℂ),
      (∀ k, ContDiff ℝ (⊤ : ℕ∞) (ψ k)) ∧
      (∀ k x, 0 ≤ ψ k x) ∧ (∀ k x, ψ k x ≤ 1) ∧
      (∀ k x, |x + lam k / (2 * Real.pi)| ≤ w → ψ k x = 1) ∧
      (∀ k x, w + η ≤ |x + lam k / (2 * Real.pi)| → ψ k x = 0) ∧
      (∀ k, Continuous (κ k)) ∧
      (∀ k, Integrable (κ k) (volume : Measure ℝ)) ∧
      (∀ k, MemLp (κ k) 2 (volume : Measure ℝ)) ∧
      (∀ k, MemLp (κ k) ⊤ (volume : Measure ℝ)) ∧
      (∀ k, ∃ C : ℝ, ∀ x : ℝ, ‖κ k x‖ ≤ C) ∧
      (∀ (k : Fin K) (ξ : ℝ), FourierTransform.fourier (κ k) ξ = (ψ k ξ : ℂ)) ∧
      (∀ ξ : ℝ, ∑ k, ‖FourierTransform.fourier (κ k) ξ‖ ^ 2 ≤ 2) := by
  obtain ⟨ψ, hψc, hψnn, hψle, hψone, hψzero, hψsum⟩ :=
    exists_cellBumps lam hsep w η hw hw4 hη hηw
  have hker : ∀ k : Fin K, ∃ κ : ℝ → ℂ, Continuous κ ∧ Integrable κ (volume : Measure ℝ) ∧
      MemLp κ 2 (volume : Measure ℝ) ∧ MemLp κ ⊤ (volume : Measure ℝ) ∧
      (∃ C : ℝ, ∀ x : ℝ, ‖κ x‖ ≤ C) ∧
      (∀ ξ : ℝ, FourierTransform.fourier κ ξ = (ψ k ξ : ℂ)) := fun k =>
    exists_fourierInv_kernel (ψ k) (hψc k) (-(lam k) / (2 * Real.pi)) (w + η)
      (by linarith) (fun x hx => hψzero k x (by
        have : x + lam k / (2 * Real.pi) = x - (-(lam k) / (2 * Real.pi)) := by ring
        rw [this]; exact hx))
  choose κ hκcont hκ1 hκ2 hκtop hκbd hκF using hker
  refine ⟨ψ, κ, hψc, hψnn, hψle, hψone, hψzero, hκcont, hκ1, hκ2, hκtop, hκbd, hκF, ?_⟩
  intro ξ
  have hterm : ∀ k : Fin K, ‖FourierTransform.fourier (κ k) ξ‖ ^ 2 = (ψ k ξ) ^ 2 := by
    intro k
    rw [hκF k ξ, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  calc ∑ k, ‖FourierTransform.fourier (κ k) ξ‖ ^ 2 = ∑ k, (ψ k ξ) ^ 2 :=
        Finset.sum_congr rfl fun k _ => hterm k
    _ ≤ 2 := hψsum ξ

end Commons.Analysis.Fourier

open _root_.MeasureTheory
open scoped _root_.ENNReal FourierTransform

namespace Commons.Analysis.Fourier

/-- **Linearity of the function-level Fourier transform**: `𝓕(f - g) = 𝓕f - 𝓕g` for `L¹` functions
`f, g`.  (The `𝐞`-form produced by `Real.fourierIntegral_convergent_iff` is converted to the
`Complex.exp`-form produced by `Real.fourier_eq'` pointwise, once.) -/
lemma fourier_sub_of_integrable (f g : ℝ → ℂ) (hf : Integrable f (volume : Measure ℝ))
    (hg : Integrable g (volume : Measure ℝ)) (ξ : ℝ) :
    FourierTransform.fourier (f - g) ξ
      = FourierTransform.fourier f ξ - FourierTransform.fourier g ξ := by
  rw [Real.fourier_eq', Real.fourier_eq', Real.fourier_eq']
  simp only [Real.inner_apply]
  have hint : ∀ (h : ℝ → ℂ), Integrable h (volume : Measure ℝ) →
      Integrable (fun x : ℝ =>
        Complex.exp ((↑(-2 * Real.pi * (x * ξ)) * Complex.I) : ℂ) • h x) (volume : Measure ℝ) := by
    intro h hh
    have hc := (Real.fourierIntegral_convergent_iff ξ).2 hh
    refine hc.congr (Filter.Eventually.of_forall fun x => ?_)
    show (𝐞 (-(inner ℝ x ξ))) • h x
      = Complex.exp ((↑(-2 * Real.pi * (x * ξ)) * Complex.I) : ℂ) • h x
    rw [Circle.smul_def, Real.fourierChar_apply, Real.inner_apply]
    congr 1
    push_cast
    ring
  have h1 := hint f hf
  have h2 := hint g hg
  have hpt : (fun x : ℝ => Complex.exp ((↑(-2 * Real.pi * (x * ξ)) * Complex.I) : ℂ) • (f - g) x)
      = fun x : ℝ => Complex.exp ((↑(-2 * Real.pi * (x * ξ)) * Complex.I) : ℂ) • f x
          - Complex.exp ((↑(-2 * Real.pi * (x * ξ)) * Complex.I) : ℂ) • g x := by
    funext x
    simp only [Pi.sub_apply, smul_sub]
  rw [hpt, MeasureTheory.integral_sub h1 h2]

end Commons.Analysis.Fourier

open _root_.MeasureTheory
open scoped _root_.ENNReal FourierTransform

namespace Commons.Analysis.Fourier

/-- **The translate rule for the one-dimensional Fourier transform** (function level):
`𝓕(f(·+y))(ξ) = e^{2πiyξ}·𝓕f(ξ)`. -/
lemma fourier_comp_add (f : ℝ → ℂ) (y η : ℝ) :
    FourierTransform.fourier (fun z : ℝ => f (z + y)) η
      = Complex.exp ((↑(2 * Real.pi * y * η) * Complex.I) : ℂ) *
        FourierTransform.fourier f η := by
  rw [Real.fourier_eq', Real.fourier_eq']
  simp only [Real.inner_apply]
  have hshift : (fun z : ℝ => Complex.exp ((↑(-2 * Real.pi * (z * η)) * Complex.I) : ℂ) • f (z + y))
      = fun z : ℝ => (fun u : ℝ =>
          Complex.exp ((↑(-2 * Real.pi * ((u - y) * η)) * Complex.I) : ℂ) • f u) (z + y) := by
    funext z
    simp only [add_sub_cancel_right]
  have hkey : (∫ z : ℝ, (fun u : ℝ =>
        Complex.exp ((↑(-2 * Real.pi * ((u - y) * η)) * Complex.I) : ℂ) • f u) (z + y))
      = ∫ u : ℝ, Complex.exp ((↑(-2 * Real.pi * ((u - y) * η)) * Complex.I) : ℂ) • f u :=
    MeasureTheory.integral_add_right_eq_self (f := fun u : ℝ =>
      Complex.exp ((↑(-2 * Real.pi * ((u - y) * η)) * Complex.I) : ℂ) • f u) y
  rw [hshift, hkey]
  rw [← MeasureTheory.integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [smul_eq_mul]
  rw [show (-2 * Real.pi * ((u - y) * η) : ℝ)
      = 2 * Real.pi * y * η + (-(2 * Real.pi * (u * η))) by ring]
  rw [Complex.ofReal_add]
  rw [show ((↑(2 * Real.pi * y * η) : ℂ) + ↑(-(2 * Real.pi * (u * η)))) * Complex.I
      = ↑(2 * Real.pi * y * η) * Complex.I + ↑(-(2 * Real.pi * (u * η))) * Complex.I by ring]
  rw [Complex.exp_add]
  ring

end Commons.Analysis.Fourier

open _root_.MeasureTheory
open scoped _root_.ENNReal FourierTransform

namespace Commons.Analysis.Fourier

variable {K : ℕ}

/-- The class of "admissible" `K`-tuples for the fixed-window maximal estimate: `L¹`, `L²`,
`L^∞`, and band-limited in the function-level Fourier sense. -/
def AdmB (a : ℝ) (H : Fin K → ℝ → ℂ) : Prop :=
  (∀ k : Fin K, MemLp (H k) 1 (volume : Measure ℝ)) ∧
  (∀ k : Fin K, MemLp (H k) 2 (volume : Measure ℝ)) ∧
  (∀ k : Fin K, MemLp (H k) ⊤ (volume : Measure ℝ)) ∧
  (∀ (k : Fin K) (ξ : ℝ), a < |ξ| → 𝓕 (H k) ξ = 0)

/-- **The class `AdmB` is preserved by the shifted difference** `H ↦ H - H(·+y)`, for *every*
shift `y` (no smallness needed: the band-limitation is preserved exactly). -/
theorem admB_shiftH {a : ℝ} {H : Fin K → ℝ → ℂ} (hH : AdmB a H) (y : ℝ) :
    AdmB a (shiftH H y) := by
  obtain ⟨h1, h2, htop, hsupp⟩ := hH
  have htr : ∀ p : ℝ≥0∞, (∀ k : Fin K, MemLp (H k) p (volume : Measure ℝ)) →
      ∀ k : Fin K, MemLp (fun x : ℝ => H k (x + y)) p (volume : Measure ℝ) := fun p hp k =>
    (hp k).comp_measurePreserving (measurePreserving_add_right volume y)
  refine ⟨fun k => (h1 k).sub (htr 1 h1 k), fun k => (h2 k).sub (htr 2 h2 k),
    fun k => (htop k).sub (htr ⊤ htop k), fun k ξ hξ => ?_⟩
  have hinte : Integrable (H k) (volume : Measure ℝ) := memLp_one_iff_integrable.mp (h1 k)
  have hinte' : Integrable (fun x : ℝ => H k (x + y)) (volume : Measure ℝ) :=
    memLp_one_iff_integrable.mp (htr 1 h1 k)
  have hshift : shiftH H y k = H k - fun x : ℝ => H k (x + y) := rfl
  rw [hshift, fourier_sub_of_integrable (H k) (fun x : ℝ => H k (x + y)) hinte hinte' ξ,
    fourier_comp_add (H k) y ξ, hsupp k ξ hξ]
  ring

end Commons.Analysis.Fourier

open _root_.MeasureTheory
open scoped _root_.ENNReal FourierTransform

namespace Commons.Analysis.Fourier

/-- Multiplication by a unimodular function preserves `MemLp`. -/
lemma memLp_mul_unimodular {p : ℝ≥0∞} {g e : ℝ → ℂ} (hg : MemLp g p (volume : Measure ℝ))
    (he : AEStronglyMeasurable e (volume : Measure ℝ)) (hE : ∀ x : ℝ, ‖e x‖ = 1) :
    MemLp (fun x : ℝ => g x * e x) p (volume : Measure ℝ) := by
  have hm : AEStronglyMeasurable (fun x : ℝ => g x * e x) (volume : Measure ℝ) :=
    hg.aestronglyMeasurable.mul he
  refine hg.congr_norm hm (Filter.Eventually.of_forall fun x => ?_)
  rw [norm_mul, hE x, mul_one]

/-- **The modulation rule**: `𝓕(G · e^{2πi c ·})(ξ) = 𝓕G(ξ - c)`, in the normalisation used by
the slices. -/
lemma fourier_mul_exp_rule (G : ℝ → ℂ) (c η : ℝ) :
    FourierTransform.fourier
        (fun x : ℝ => G x * Complex.exp ((↑(2 * Real.pi * c * x) * Complex.I) : ℂ)) η
      = FourierTransform.fourier G (η - c) := by
  rw [Real.fourier_eq', Real.fourier_eq']
  simp only [Real.inner_apply]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [smul_eq_mul]
  have hpt : Complex.exp ((↑(-2 * Real.pi * (x * η)) * Complex.I) : ℂ) *
        (G x * Complex.exp ((↑(2 * Real.pi * c * x) * Complex.I) : ℂ))
      = Complex.exp ((↑(-2 * Real.pi * (x * (η - c))) * Complex.I) : ℂ) * G x := by
    rw [show Complex.exp ((↑(-2 * Real.pi * (x * η)) * Complex.I) : ℂ) *
          (G x * Complex.exp ((↑(2 * Real.pi * c * x) * Complex.I) : ℂ))
        = (Complex.exp ((↑(-2 * Real.pi * (x * η)) * Complex.I) : ℂ) *
            Complex.exp ((↑(2 * Real.pi * c * x) * Complex.I) : ℂ)) * G x by ring,
      ← Complex.exp_add]
    congr 1
    congr 1
    push_cast
    ring
  exact hpt

/-- **The modulation shifts the band.**  If `𝓕G` vanishes outside the band of half-width `a`
around `0`, then `𝓕(G·e^{Iλ·})` vanishes outside the band of half-width `a` around `λ/(2π)`.
This is the step that turns the (cell-centred) bands of the slice kernels into the bands around
`0` required by the fixed-window crux. -/
lemma fourier_modulation_support {G : ℝ → ℂ} {lam a : ℝ} (_hG : Integrable G (volume : Measure ℝ))
    (hsupp : ∀ ξ : ℝ, a < |ξ| → FourierTransform.fourier G ξ = 0) (ξ : ℝ)
    (hξ : a < |ξ - lam / (2 * Real.pi)|) :
    FourierTransform.fourier (fun x : ℝ => G x * Complex.exp (Complex.I * (lam : ℂ) * (x : ℂ))) ξ = 0 := by
  rw [show (fun x : ℝ => G x * Complex.exp (Complex.I * (lam : ℂ) * (x : ℂ)))
      = fun x : ℝ => G x * Complex.exp ((↑(2 * Real.pi * (lam / (2 * Real.pi)) * x) * Complex.I) : ℂ)
      from by
        funext x
        congr 2
        push_cast
        field_simp]
  rw [fourier_mul_exp_rule G (lam / (2 * Real.pi)) ξ]
  exact hsupp (ξ - lam / (2 * Real.pi)) hξ

end Commons.Analysis.Fourier


namespace Commons.Analysis.Fourier

open _root_.MeasureTheory Finset Function Filter
open scoped _root_.ENNReal _root_.Topology BigOperators _root_.FourierTransform

noncomputable section

/-! ## Uniform-in-`lam` constants for the entropy chain

The commons lemmas `max_finset_exponential_sum_l2` and `chain_exp_sum_le_entropy` quantify their
constant *after* `K` and `lam`; the target theorem needs a constant that is uniform in `K` and
`lam` (only the explicit `log²(K+2)` factor may depend on `K`).  This file re-proves them with the
`∃ C` moved to the front.  In both cases the constant was already independent of the parameters —
it is built from the universal constant of `separated_exponentials_near_orthogonal` — so the
proofs are the originals with the quantifier order changed. -/

private lemma iSup_finset_nonneg_u' {α : Type*} (B : Finset α) (u : α → ℝ)
    (h : ∀ a, 0 ≤ u a) : 0 ≤ (⨆ a ∈ B, u a) := by
  rcases B.eq_empty_or_nonempty with hB | hB
  · subst hB
    simp
  · obtain ⟨a₀, ha₀⟩ := hB
    have hbdd : BddAbove (Set.range (fun a => ⨆ (_ : a ∈ B), u a)) := by
      refine ⟨∑ a ∈ B, u a, ?_⟩
      rintro _ ⟨a, rfl⟩
      change (⨆ (_ : a ∈ B), u a) ≤ ∑ a ∈ B, u a
      by_cases ha : a ∈ B
      · rw [show (⨆ (_ : a ∈ B), u a) = u a from ciSup_pos (f := fun _ => u a) ha]
        exact Finset.single_le_sum (fun i _ => h i) ha
      · rw [show (⨆ (_ : a ∈ B), u a) = sSup (∅ : Set ℝ) from
            ciSup_neg (f := fun _ => u a) ha, Real.sSup_empty]
        exact Finset.sum_nonneg (fun _ _ => h _)
    have h1 : u a₀ ≤ ⨆ a, ⨆ (_ : a ∈ B), u a := by
      calc u a₀ = ⨆ (_ : a₀ ∈ B), u a₀ := (ciSup_pos (f := fun _ => u a₀) ha₀).symm
        _ ≤ ⨆ a, ⨆ (_ : a ∈ B), u a := le_ciSup hbdd a₀
    exact le_trans (h a₀) h1

/-- For a finite family of nonnegative reals the square of the supremum is at most the sum of
the squares (a consequence of `(sup u)² ≤ ∑ u²`, i.e. of the fact that a maximum of
nonnegative numbers is dominated in square by the sum of all squares). -/
private lemma iSup_finset_sq_le_sum_u' {α : Type*} (B : Finset α) (u : α → ℝ)
    (h : ∀ a, 0 ≤ u a) : (⨆ a ∈ B, u a) ^ 2 ≤ ∑ a ∈ B, (u a) ^ 2 := by
  have hnn : 0 ≤ (⨆ a ∈ B, u a) := iSup_finset_nonneg_u' B u h
  have h1 : (⨆ a ∈ B, u a) ≤ Real.sqrt (∑ a ∈ B, (u a) ^ 2) := by
    rcases isEmpty_or_nonempty α with hα | hα
    · have hB : B = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp (fun hne => hne.elim fun a _ => isEmptyElim a)
      rw [show (⨆ a : α, ⨆ (_ : a ∈ B), u a) = (⨆ a : α, (0 : ℝ)) from by
            apply iSup_congr; intro a
            rw [show (⨆ (_ : a ∈ B), u a) = sSup (∅ : Set ℝ) from
              ciSup_neg (f := fun _ => u a) (by rw [hB]; simp)]
            exact Real.sSup_empty]
      rw [Real.iSup_of_isEmpty]
      simp [hB]
    · apply ciSup_le
      intro b
      by_cases hb : b ∈ B
      · rw [show (⨆ (_ : b ∈ B), u b) = u b from ciSup_pos (f := fun _ => u b) hb]
        rw [← Real.sqrt_sq (h b)]
        exact Real.sqrt_le_sqrt (Finset.single_le_sum (fun _ _ => sq_nonneg _) hb)
      · rw [show (⨆ (_ : b ∈ B), u b) = sSup (∅ : Set ℝ) from
            ciSup_neg (f := fun _ => u b) hb, Real.sSup_empty]
        exact Real.sqrt_nonneg _
  calc (⨆ a ∈ B, u a) ^ 2 ≤ (Real.sqrt (∑ a ∈ B, (u a) ^ 2)) ^ 2 :=
        pow_le_pow_left₀ hnn h1 2
    _ = ∑ a ∈ B, (u a) ^ 2 := Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

/-- **The maximal exponential sum over a finite class of coefficient vectors, mean-square bound.**
Let `lam : Fin K → ℝ` be `1`-separated, and let `B` be a finite set of coefficient vectors with
`∑ k, ‖b k‖ ^ 2 ≤ R ^ 2` for every `b ∈ B`.  Then the mean square over `y ∈ [0,1]` of the maximal
exponential sum `sup_{b ∈ B} ‖∑ k, b k * exp(I * lam k * y)‖` is at most `C * R ^ 2 * #B`.

This is the per-level estimate (4.24)–(4.25) in Bourgain's proof of his Lemma 4.13: the
near-orthogonality of `1`-separated exponentials
(`Commons.Analysis.Fourier.separated_exponentials_near_orthogonal`) controls the mean square of
each individual exponential sum, and the maximum over the *finite* set `B` is controlled by the
sum over `B` through the pointwise inequality `(sup_{b ∈ B} u b) ^ 2 ≤ ∑_{b ∈ B} (u b) ^ 2`.  The
integral is a Lebesgue integral over `[0,1]` in `ℝ≥0∞`, so no measurability of the pointwise
supremum is needed. -/
theorem max_finset_exponential_sum_l2_uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : ℕ) (lam : Fin K → ℝ)
      (hsep : ∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|),
      ∀ (B : Finset (Fin K → ℂ)) (R : ℝ), 0 ≤ R →
      (∀ b ∈ B, ∑ k : Fin K, ‖b k‖ ^ 2 ≤ R ^ 2) →
      ∫⁻ y in Set.Ioc (0 : ℝ) 1,
          ENNReal.ofReal (⨆ b ∈ B, ‖∑ k : Fin K,
            b k * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖) ^ 2
        ≤ ENNReal.ofReal (C * R ^ 2 * (B.card : ℝ)) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := separated_exponentials_near_orthogonal
  refine ⟨C₀, hC₀pos, fun K lam hsep => ?_⟩
  classical
  intro B R hR hB
  set U : (Fin K → ℂ) → ℝ → ℝ :=
    fun b y => ‖∑ k : Fin K, b k * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖ with hU
  have hUcont : ∀ b, Continuous (U b) := by
    intro b
    have : Continuous fun y : ℝ => ∑ k : Fin K, b k * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ)) :=
      continuous_finsetSum _ (fun k _ => by fun_prop)
    simpa only [hU] using this.norm
  have hUnn : ∀ b y, 0 ≤ U b y := fun b y => norm_nonneg _
  have hpt : ∀ y : ℝ,
      ENNReal.ofReal (⨆ b ∈ B, U b y) ^ 2 ≤ ∑ b ∈ B, ENNReal.ofReal (U b y) ^ 2 := by
    intro y
    have hsup := iSup_finset_sq_le_sum_u' B (fun b => U b y) (fun b => hUnn b y)
    have hnn : 0 ≤ (⨆ b ∈ B, U b y) := iSup_finset_nonneg_u' B (fun b => U b y) (fun b => hUnn b y)
    calc ENNReal.ofReal (⨆ b ∈ B, U b y) ^ 2
        = ENNReal.ofReal ((⨆ b ∈ B, U b y) ^ 2) := (ENNReal.ofReal_pow hnn 2).symm
      _ ≤ ENNReal.ofReal (∑ b ∈ B, (U b y) ^ 2) := ENNReal.ofReal_le_ofReal hsup
      _ = ∑ b ∈ B, ENNReal.ofReal ((U b y) ^ 2) :=
            ENNReal.ofReal_sum_of_nonneg (fun b _ => sq_nonneg _)
      _ = ∑ b ∈ B, ENNReal.ofReal (U b y) ^ 2 := by
            apply Finset.sum_congr rfl; intro b _
            rw [ENNReal.ofReal_pow (hUnn b y) 2]
  have hmeas : ∀ b ∈ B, Measurable (fun y : ℝ => ENNReal.ofReal (U b y) ^ 2) := by
    intro b _
    exact ((hUcont b).measurable.ennreal_ofReal.pow_const 2)
  have hint : ∀ b ∈ B, Integrable (fun y : ℝ => (U b y) ^ 2)
      (volume.restrict (Set.Ioc 0 1)) := by
    intro b _
    have hcont : Continuous (fun y : ℝ => (U b y) ^ 2) := (hUcont b).pow 2
    exact (hcont.continuousOn.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  calc ∫⁻ y in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (⨆ b ∈ B, U b y) ^ 2
      ≤ ∫⁻ y in Set.Ioc (0 : ℝ) 1, ∑ b ∈ B, ENNReal.ofReal (U b y) ^ 2 := lintegral_mono hpt
    _ = ∑ b ∈ B, ∫⁻ y in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (U b y) ^ 2 := by
          rw [lintegral_finsetSum]
          intro b hb; exact hmeas b hb
    _ = ∑ b ∈ B, ENNReal.ofReal (∫ y in (0 : ℝ)..1, (U b y) ^ 2) := by
          apply Finset.sum_congr rfl; intro b hb
          have h1 : ∫⁻ y in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (U b y) ^ 2
              = ∫⁻ y in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal ((U b y) ^ 2) := by
            apply lintegral_congr; intro y
            rw [ENNReal.ofReal_pow (hUnn b y) 2]
          rw [h1]
          have h2 := ofReal_integral_eq_lintegral_ofReal (hint b hb)
            (ae_of_all _ (fun y => sq_nonneg (U b y)))
          rw [← h2]
          congr 1
          rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    _ ≤ ∑ b ∈ B, ENNReal.ofReal (C₀ * R ^ 2) := by
          apply Finset.sum_le_sum; intro b hb
          apply ENNReal.ofReal_le_ofReal
          have hc := hC₀ K lam hsep b
          calc ∫ y in (0 : ℝ)..1, (U b y) ^ 2
              ≤ C₀ * ∑ k : Fin K, ‖b k‖ ^ 2 := by
                rw [hU]; exact hc
            _ ≤ C₀ * R ^ 2 :=
                mul_le_mul_of_nonneg_left (hB b hb) (le_of_lt hC₀pos)
    _ = ENNReal.ofReal (C₀ * R ^ 2 * (B.card : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast (B.card),
              ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ ((B.card : ℕ) : ℝ) by positivity)]
          ring_nf

private lemma norm_cexp_lin_u (lam y : ℝ) :
    ‖Complex.exp (Complex.I * (lam : ℂ) * (y : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  have h : (Complex.I * (lam : ℂ) * (y : ℂ)).re = 0 := by
    rw [Complex.mul_re, Complex.mul_re]; simp
  rw [h, Real.exp_zero]

/-- Cauchy–Schwarz: `∑ ‖d k‖ ≤ √K · √(∑ ‖d k‖²)`. -/
private lemma sum_norm_le_sqrt_card_mul_sqrt_sum_sq_u {K : ℕ} (d : Fin K → ℂ) :
    ∑ k : Fin K, ‖d k‖ ≤ Real.sqrt K * Real.sqrt (∑ k : Fin K, ‖d k‖ ^ 2) := by
  have h1 : (∑ k : Fin K, ‖d k‖ * 1) ^ 2
      ≤ (∑ k : Fin K, ‖d k‖ ^ 2) * (∑ _ : Fin K, (1 : ℝ) ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun k => ‖d k‖) (fun _ => 1)
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] at h1
  have h3 : 0 ≤ ∑ k : Fin K, ‖d k‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  calc ∑ k : Fin K, ‖d k‖ ≤ Real.sqrt ((∑ k : Fin K, ‖d k‖ ^ 2) * (K : ℝ)) := by
        rw [← Real.sqrt_sq h3]; exact Real.sqrt_le_sqrt h1
    _ = Real.sqrt K * Real.sqrt (∑ k : Fin K, ‖d k‖ ^ 2) := by
        rw [Real.sqrt_mul (by positivity), mul_comm]

/-- A member of a finite family of nonnegative reals is at most the finite supremum. -/
private lemma le_iSup_finset_u {α : Type*} (B : Finset α) (u : α → ℝ) (h : ∀ a, 0 ≤ u a)
    {a : α} (ha : a ∈ B) : u a ≤ ⨆ b ∈ B, u b := by
  have hbdd : BddAbove (Set.range (fun b => ⨆ (_ : b ∈ B), u b)) := by
    refine ⟨∑ b ∈ B, u b, ?_⟩
    rintro _ ⟨b, rfl⟩
    change (⨆ (_ : b ∈ B), u b) ≤ ∑ b ∈ B, u b
    by_cases hb : b ∈ B
    · rw [show (⨆ (_ : b ∈ B), u b) = u b from ciSup_pos (f := fun _ => u b) hb]
      exact Finset.single_le_sum (fun i _ => h i) hb
    · rw [show (⨆ (_ : b ∈ B), u b) = sSup (∅ : Set ℝ) from ciSup_neg (f := fun _ => u b) hb,
        Real.sSup_empty]
      exact Finset.sum_nonneg (fun _ _ => h _)
  calc u a = ⨆ (_ : a ∈ B), u a := (ciSup_pos (f := fun _ => u a) ha).symm
    _ ≤ ⨆ b, ⨆ (_ : b ∈ B), u b := le_ciSup hbdd a

/-- For a nonempty finset, the bi-supremum of a nonnegative family equals its `sup'`. -/
private lemma iSup_finset_eq_sup'_u {ι : Type*} (F : Finset ι) (hF : F.Nonempty) (f : ι → ℝ)
    (hf : ∀ i, 0 ≤ f i) : (⨆ i ∈ F, f i) = F.sup' hF f := by
  have hFne : F.Nonempty := hF
  obtain ⟨i₀, hi₀⟩ := hFne
  haveI : Nonempty ι := ⟨i₀⟩
  have hsupnn : 0 ≤ F.sup' hF f := le_trans (hf i₀) (Finset.le_sup' f hi₀)
  refine le_antisymm ?_ (Finset.sup'_le hF f (fun i hi => le_iSup_finset_u F f hf hi))
  refine ciSup_le (fun i => ?_)
  by_cases hi : i ∈ F
  · rw [ciSup_pos (f := fun _ => f i) hi]
    exact Finset.le_sup' f hi
  · rw [ciSup_neg (f := fun _ => f i) hi, Real.sSup_empty]
    exact hsupnn

/-- **The entropy chain bound for a finite family.**  Let `lam : Fin K → ℝ` be `1`-separated and
`a : Fin (N+1) → (Fin K → ℂ)` a family of coefficient vectors that is approximately constant along
each net `σ t` at the dyadic accuracy `2·2^{-t}`.  Then the `L²` norm over `[0,1]` of the maximal
exponential sum `sup_i ‖∑ k, a i k · e^{I λ_k y}‖` is bounded by the square of
`√(∑ ‖a (σ 0 0) k‖²) + ∑_{t ≤ S} 2^{-t} √(min (K, M t + 1))`.

This is the entropy/chaining estimate (4.24)–(4.26) in Bourgain's proof of Lemma 4.13: the
telescoping along a dyadic chain of nets decomposes the family into at most `M t` classes at level
`t`, each class is handled by the mean-square bound for a maximal exponential sum
(`Commons.Analysis.Fourier.max_finset_exponential_sum_l2`), the `√K` term is Cauchy–Schwarz, and
the classes are then recombined with the abstract `L²` class bound
(`Commons.Analysis.Fourier.lintegral_sq_sum_le_of_class_bounds`). -/
theorem chain_exp_sum_le_entropy_uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : ℕ) (lam : Fin K → ℝ)
      (hsep : ∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|),
      ∀ (N S : ℕ) (a : Fin (N+1) → Fin K → ℂ)
        (σ : ℕ → Fin (N+1) → Fin (N+1)) (M : ℕ → ℕ), 1 ≤ S →
      (∀ i : Fin (N+1), σ 0 i = σ 0 0) →
      (N+1) ≤ M S →
      (∀ t, t ≤ S → (Finset.univ.image (σ t)).card ≤ M t) →
      (∀ t, t ≤ S → ∀ i : Fin (N+1),
        ∑ k : Fin K, ‖a i k - a (σ t i) k‖ ^ 2 ≤ (2 * (1/2:ℝ)^t)^2) →
      ∫⁻ y in Set.Ioc (0:ℝ) 1, ENNReal.ofReal
          (⨆ i : Fin (N+1), ‖∑ k : Fin K, a i k * Complex.exp (Complex.I * (lam k:ℂ) * (y:ℂ))‖) ^ 2
        ≤ ENNReal.ofReal ((C * (Real.sqrt (∑ k : Fin K, ‖a (σ 0 0) k‖ ^ 2)
            + ∑ t ∈ Finset.range (S+1),
                (1/2:ℝ)^t * Real.sqrt (min (K:ℝ) ((M t : ℝ) + 1)))) ^ 2) := by
  obtain ⟨c₀, hc₀pos, hc₀u⟩ := max_finset_exponential_sum_l2_uniform
  obtain ⟨c₁, hc₁pos, hc₁⟩ := separated_exponentials_near_orthogonal
  refine ⟨200 * (c₀ + c₁ + 1), by positivity, fun K lam hsep => ?_⟩
  classical
  have hc₀ := hc₀u K lam hsep
  rcases Nat.eq_zero_or_pos K with hK0 | hKpos
  · subst hK0
    intro N S a σ M hS hconst hNM hcard hnet2
    have hz : (fun y : ℝ => ENNReal.ofReal
        (⨆ i : Fin (N+1), ‖∑ k : Fin 0,
          a i k * Complex.exp (Complex.I * (lam k:ℂ) * (y:ℂ))‖) ^ 2)
        = fun _ => (0 : ℝ≥0∞) := by
      funext y
      simp
    rw [hz, lintegral_zero]
    exact bot_le
  intro N S a σ M hS hconst hNM hcard hnet2
  -- Convert the `ℓ²` hypothesis into a uniform norm bound.
  have hnet : ∀ t, t ≤ S → ∀ i : Fin (N+1), ‖a i - a (σ t i)‖ ≤ 2 * (1/2:ℝ)^t := by
    intro t ht i
    have h2 := hnet2 t ht i
    have hsqrt : Real.sqrt (∑ k : Fin K, ‖a i k - a (σ t i) k‖^2) ≤ 2 * (1/2:ℝ)^t := by
      rw [← Real.sqrt_sq (by positivity : (0:ℝ) ≤ 2 * (1/2:ℝ)^t)]
      exact Real.sqrt_le_sqrt h2
    refine le_trans ?_ hsqrt
    rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
    intro m
    calc ‖(a i - a (σ t i)) m‖ = ‖a i m - a (σ t i) m‖ := by rw [Pi.sub_apply]
      _ = Real.sqrt (‖a i m - a (σ t i) m‖^2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (∑ x : Fin K, ‖a i x - a (σ t i) x‖^2) :=
          Real.sqrt_le_sqrt (Finset.single_le_sum
            (fun x (_ : x ∈ Finset.univ) => sq_nonneg (‖a i x - a (σ t i) x‖))
            (Finset.mem_univ m))
  -- The dyadic chain and the finite difference classes.
  let q : ℕ → Fin (N+1) → Fin (N+1) := dyadicChain (N+1) S σ
  let B : ℕ → Finset (Fin K → ℂ) := dyadicDiff (N+1) S a σ
  have hqmem : ∀ k, 1 ≤ k → k ≤ S → ∀ i, q k i ∈ Finset.univ.image (σ (S - k)) := by
    intro k hk _ i
    exact dyadicChain_mem_image (N+1) S σ hk i
  have hqdiff : ∀ k, k < S → ∀ i, a (q k i) - a (q (k+1) i) ∈ B k := by
    intro k _ i
    have hqsucc : q (k+1) i = σ (S - k - 1) (q k i) := dyadicChain_succ_apply (N+1) S σ k i
    rw [hqsucc]
    simp only [B]
    refine Finset.mem_image.mpr ⟨q k i, ?_, rfl⟩
    by_cases hk0 : k = 0
    · subst hk0; simp [dyadicDiff_def]
    · rw [if_neg hk0]
      exact dyadicChain_mem_image (N+1) S σ (by omega) i
  have hqcard : ∀ k, 1 ≤ k → k < S →
      (B k).card ≤ (Finset.univ.image (σ (S - k))).card := by
    intro k hk1 _
    have hk0 : k ≠ 0 := by omega
    simp only [B]
    rw [dyadicDiff_def, if_neg hk0]
    exact Finset.card_image_le
  have hqcard0 : (B 0).card ≤ N+1 := by
    simp only [B]
    rw [dyadicDiff_def, if_pos rfl]
    calc (Finset.univ.image (fun v => a v - a (σ (S - 0 - 1) v))).card
        ≤ (Finset.univ : Finset (Fin (N+1))).card := Finset.card_image_le
      _ = N+1 := by simp
  have hqnorm : ∀ k, k < S → ∀ b ∈ B k, ‖b‖ ≤ 2 * (1/2:ℝ)^(S-k-1) := by
    intro k _ b hb
    simp only [B] at hb
    rw [dyadicDiff_def] at hb
    rw [Finset.mem_image] at hb
    obtain ⟨v, _, hv⟩ := hb
    rw [← hv]
    exact hnet (S - k - 1) (by omega) v
  have hqdecomp : ∀ i, a i = a (q S i) + ∑ k ∈ Finset.range S, (a (q k i) - a (q (k+1) i)) := by
    intro i
    have hsum := Finset.sum_range_sub' (fun k => a (q k i)) S
    rw [hsum]
    rw [show q 0 i = i from dyadicChain_zero_apply (N+1) S σ i]
    exact (add_sub_cancel (a (q S i)) (a i)).symm
  have hqS : ∀ i : Fin (N+1), q S i = σ 0 0 := by
    intro i
    have hmem := hqmem S hS le_rfl i
    rw [Nat.sub_self] at hmem
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hmem
    rw [← hj, hconst j]
  let p : Fin K → ℂ := a (σ 0 0)
  let D : ℝ := Real.sqrt (∑ k : Fin K, ‖p k‖ ^ 2)
  let Φ : ℝ → (Fin K → ℂ) → ℂ :=
    fun y v => ∑ k : Fin K, v k * Complex.exp (Complex.I * (lam k:ℂ) * (y:ℂ))
  have hΦadd : ∀ y (u v : Fin K → ℂ), Φ y (u + v) = Φ y u + Φ y v := by
    intro y u v
    simp only [Φ, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  have hΦsum : ∀ y (s : Finset ℕ) (u : ℕ → Fin K → ℂ),
      Φ y (∑ k ∈ s, u k) = ∑ k ∈ s, Φ y (u k) := by
    intro y s u
    simp only [Φ, Finset.sum_apply, Finset.sum_mul]
    exact Finset.sum_comm
  have hΦcont : ∀ b : Fin K → ℂ, Continuous (fun y : ℝ => Φ y b) := by
    intro b
    simp only [Φ]
    exact continuous_finsetSum _ (fun k _ => by fun_prop)
  have hB_ne : ∀ k, k < S → (B k).Nonempty := fun k hk => ⟨_, hqdiff k hk 0⟩
  let cls : ℕ → Finset (Fin K → ℂ) := fun j => if j < S then B j else {p}
  have hcls_ne : ∀ j, (cls j).Nonempty := by
    intro j
    by_cases hj : j < S
    · have h1 : cls j = B j := by simp [cls, hj]
      rw [h1]
      exact hB_ne j hj
    · have h1 : cls j = {p} := by simp [cls, hj]
      rw [h1]
      exact ⟨p, Finset.mem_singleton_self p⟩
  have hclsS : cls S = {p} := by simp [cls]
  have hclsj : ∀ j, j < S → cls j = B j := fun j hj => by simp [cls, hj]
  let Acls : ℕ → ℝ → ℝ := fun j y => (cls j).sup' (hcls_ne j) (fun b => ‖Φ y b‖)
  have hAcls_cont : ∀ j, Continuous (Acls j) := by
    intro j
    exact Continuous.finset_sup'_apply (hcls_ne j) (fun b _ => (hΦcont b).norm)
  have hAcls_nn : ∀ j y, 0 ≤ Acls j y := by
    intro j y
    exact le_trans (norm_nonneg _) (Finset.le_sup' (fun b => ‖Φ y b‖) (hcls_ne j).choose_spec)
  have hAeqS : ∀ y, Acls S y = (⨆ b ∈ cls S, ‖Φ y b‖) := by
    intro y
    simp only [Acls]
    exact (iSup_finset_eq_sup'_u (cls S) (hcls_ne S) (fun b => ‖Φ y b‖)
      (fun b => norm_nonneg _)).symm
  have hAeqk : ∀ k, k < S → ∀ y, Acls k y = (⨆ b ∈ B k, ‖Φ y b‖) := by
    intro k hk y
    simp only [Acls, hclsj k hk]
    exact (iSup_finset_eq_sup'_u (B k) (hB_ne k hk) (fun b => ‖Φ y b‖)
      (fun b => norm_nonneg _)).symm
  have hAeqS' : ∀ y, Acls S y = ‖Φ y p‖ := by
    intro y
    simp only [Acls, hclsS]
    rw [Finset.sup'_singleton]
  have hper : ∀ y i, ‖Φ y (a i)‖ ≤ Acls S y + ∑ k ∈ Finset.range S, Acls k y := by
    intro y i
    have hsumk : ∑ k ∈ Finset.range S, Acls k y
        = ∑ k ∈ Finset.range S, (⨆ b ∈ B k, ‖Φ y b‖) :=
      Finset.sum_congr rfl (fun k hk => hAeqk k (Finset.mem_range.mp hk) y)
    rw [hAeqS y, hsumk]
    have hsplit2 : Φ y (a i) = Φ y (a (q S i))
        + ∑ k ∈ Finset.range S, Φ y (a (q k i) - a (q (k+1) i)) := by
      conv_lhs => rw [hqdecomp i]
      rw [hΦadd, hΦsum]
    calc ‖Φ y (a i)‖
        = ‖Φ y (a (q S i)) + ∑ k ∈ Finset.range S, Φ y (a (q k i) - a (q (k+1) i))‖ := by
          rw [hsplit2]
      _ ≤ ‖Φ y (a (q S i))‖
            + ‖∑ k ∈ Finset.range S, Φ y (a (q k i) - a (q (k+1) i))‖ := norm_add_le _ _
      _ ≤ (⨆ b ∈ cls S, ‖Φ y b‖) + ∑ k ∈ Finset.range S, (⨆ b ∈ B k, ‖Φ y b‖) := by
          apply add_le_add
          · refine le_iSup_finset_u (cls S) (fun b => ‖Φ y b‖) (fun b => norm_nonneg _) ?_
            rw [hqS i, hclsS]
            exact Finset.mem_singleton_self p
          · refine (norm_sum_le _ _).trans ?_
            apply Finset.sum_le_sum; intro k hk
            exact le_iSup_finset_u (B k) (fun b => ‖Φ y b‖) (fun b => norm_nonneg _)
              (hqdiff k (Finset.mem_range.mp hk) i)
  have hdom : ∀ y, (⨆ i : Fin (N+1), ‖Φ y (a i)‖) ≤ ∑ j ∈ Finset.range (S+1), Acls j y := by
    intro y
    rw [Finset.sum_range_succ]
    exact ciSup_le (fun i => (hper y i).trans (le_of_eq (add_comm _ _)))
  have hsup0 : ∀ y, (0:ℝ) ≤ ⨆ i : Fin (N+1), ‖Φ y (a i)‖ := by
    intro y
    have hbdd : BddAbove (Set.range (fun i : Fin (N+1) => ‖Φ y (a i)‖)) := by
      refine ⟨Acls S y + ∑ k ∈ Finset.range S, Acls k y, ?_⟩
      rintro z ⟨i, rfl⟩
      exact hper y i
    exact le_trans (norm_nonneg _) (le_ciSup hbdd 0)
  -- Per-class mean-square bounds.
  have hcls_bound : ∀ k, k < S →
      ∫⁻ y in Set.Ioc (0:ℝ) 1, ENNReal.ofReal (Acls k y) ^ 2
        ≤ ENNReal.ofReal ((2 * (1/2:ℝ)^(S-k-1)) ^ 2
            * min (K:ℝ) (c₀ * ((B k).card : ℝ) + 1)) := by
    intro k hk
    set R : ℝ := 2 * (1/2:ℝ)^(S-k-1) with hRdef
    have hRpos : 0 < R := by rw [hRdef]; positivity
    have hmemB : ∀ b ∈ B k, ∑ j : Fin K, ‖b j‖ ^ 2 ≤ R ^ 2 := by
      intro b hb
      simp only [B] at hb
      rw [dyadicDiff_def] at hb
      rw [Finset.mem_image] at hb
      obtain ⟨v, _, hv⟩ := hb
      rw [← hv, hRdef]
      exact hnet2 (S-k-1) (by omega) v
    have hpt : ∀ y, Acls k y ≤ Real.sqrt (K:ℝ) * R := by
      intro y
      have hsup : Acls k y = (B k).sup' (hB_ne k hk) (fun b => ‖Φ y b‖) := by
        simp only [Acls, hclsj k hk]
      rw [hsup]
      refine Finset.sup'_le (hB_ne k hk) (fun b => ‖Φ y b‖) (fun b hb => ?_)
      have hb2 := hmemB b hb
      have hnorm : ‖Φ y b‖ ≤ Real.sqrt (K:ℝ) * Real.sqrt (∑ j : Fin K, ‖b j‖ ^ 2) := by
        have h1 : ‖Φ y b‖ ≤ ∑ j : Fin K, ‖b j‖ := by
          calc ‖Φ y b‖
              = ‖∑ j : Fin K, b j * Complex.exp (Complex.I * (lam j:ℂ) * (y:ℂ))‖ := rfl
            _ ≤ ∑ j : Fin K, ‖b j * Complex.exp (Complex.I * (lam j:ℂ) * (y:ℂ))‖ :=
                norm_sum_le _ _
            _ = ∑ j : Fin K, ‖b j‖ := by
                apply Finset.sum_congr rfl; intro j _
                rw [norm_mul, norm_cexp_lin_u, mul_one]
        exact h1.trans (sum_norm_le_sqrt_card_mul_sqrt_sum_sq_u b)
      calc ‖Φ y b‖ ≤ Real.sqrt (K:ℝ) * Real.sqrt (∑ j : Fin K, ‖b j‖ ^ 2) := hnorm
        _ ≤ Real.sqrt (K:ℝ) * Real.sqrt (R^2) :=
            mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hb2) (Real.sqrt_nonneg _)
        _ = Real.sqrt (K:ℝ) * R := by rw [Real.sqrt_sq hRpos.le]
    have hpt_int : ∫⁻ y in Set.Ioc (0:ℝ) 1, ENNReal.ofReal (Acls k y) ^ 2
        ≤ ENNReal.ofReal (K * R^2) := by
      have hstep : ∀ y : ℝ, ENNReal.ofReal (Acls k y) ^ 2
          ≤ ENNReal.ofReal (Real.sqrt (K:ℝ) * R) ^ 2 := by
        intro y
        rw [← ENNReal.ofReal_pow (hAcls_nn k y) 2,
          ← ENNReal.ofReal_pow (by positivity : (0:ℝ) ≤ Real.sqrt (K:ℝ) * R) 2]
        exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (hAcls_nn k y) (hpt y) 2)
      calc ∫⁻ y in Set.Ioc (0:ℝ) 1, ENNReal.ofReal (Acls k y) ^ 2
          ≤ ∫⁻ y in Set.Ioc (0:ℝ) 1, ENNReal.ofReal (Real.sqrt (K:ℝ) * R) ^ 2 :=
            lintegral_mono hstep
        _ = ENNReal.ofReal (Real.sqrt (K:ℝ) * R) ^ 2 * volume (Set.Ioc (0:ℝ) 1) := by
            rw [setLIntegral_const]
        _ = ENNReal.ofReal (K * R^2) := by
            rw [Real.volume_Ioc, sub_zero, ENNReal.ofReal_one, mul_one]
            rw [← ENNReal.ofReal_pow (by positivity : (0:ℝ) ≤ Real.sqrt (K:ℝ) * R) 2]
            congr 1
            rw [mul_pow, Real.sq_sqrt (by positivity : (0:ℝ) ≤ (K:ℝ))]
    have hlev : ∫⁻ y in Set.Ioc (0:ℝ) 1, ENNReal.ofReal (Acls k y) ^ 2
        ≤ ENNReal.ofReal (c₀ * R^2 * ((B k).card : ℝ)) := by
      have hAeq : Acls k = fun y => (⨆ b ∈ B k, ‖Φ y b‖) := funext (fun y => hAeqk k hk y)
      rw [hAeq]
      exact hc₀ (B k) R hRpos.le hmemB
    refine le_trans (le_min hpt_int hlev) ?_
    rw [← ENNReal.ofReal_min]
    apply ENNReal.ofReal_le_ofReal
    rcases le_total (K:ℝ) (c₀ * ((B k).card : ℝ) + 1) with hle | hle
    · rw [min_eq_left hle]
      calc min (K * R^2) (c₀ * R^2 * ((B k).card : ℝ)) ≤ K * R^2 := min_le_left _ _
        _ = R^2 * K := by ring
    · rw [min_eq_right hle]
      have h2 : c₀ * R^2 * ((B k).card : ℝ) ≤ R^2 * (c₀ * ((B k).card : ℝ) + 1) := by
        nlinarith [hRpos, sq_nonneg R, (Nat.cast_nonneg ((B k).card) : (0:ℝ) ≤ ((B k).card : ℝ)),
          mul_pos hc₀pos hRpos]
      calc min (K * R^2) (c₀ * R^2 * ((B k).card : ℝ)) ≤ c₀ * R^2 * ((B k).card : ℝ) :=
            min_le_right _ _
        _ ≤ R^2 * (c₀ * ((B k).card : ℝ) + 1) := h2
  -- Top class bound.
  have htop_bound : ∫⁻ y in Set.Ioc (0:ℝ) 1, ENNReal.ofReal (Acls S y) ^ 2
      ≤ ENNReal.ofReal ((Real.sqrt c₁ * D) ^ 2) := by
    have hAeq : Acls S = fun y => ‖Φ y p‖ := funext hAeqS'
    rw [hAeq]
    have hcont : Continuous (fun y : ℝ => (‖Φ y p‖) ^ 2) := (hΦcont p).norm.pow 2
    have hint : Integrable (fun y : ℝ => (‖Φ y p‖) ^ 2)
        (volume.restrict (Set.Ioc (0:ℝ) 1)) :=
      (hcont.continuousOn.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
    have hrepr : (fun y : ℝ => ENNReal.ofReal (‖Φ y p‖) ^ 2)
        = fun y : ℝ => ENNReal.ofReal ((‖Φ y p‖) ^ 2) := by
      funext y
      rw [ENNReal.ofReal_pow (norm_nonneg _) 2]
    rw [hrepr]
    have h2 := ofReal_integral_eq_lintegral_ofReal (μ := volume.restrict (Set.Ioc (0:ℝ) 1))
      (f := fun y : ℝ => (‖Φ y p‖) ^ 2) hint (ae_of_all _ (fun y => sq_nonneg _))
    rw [← h2]
    rw [← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
    apply ENNReal.ofReal_le_ofReal
    have hc1 := hc₁ K lam hsep p
    have hD2 : D ^ 2 = ∑ k : Fin K, ‖p k‖ ^ 2 := by
      rw [show D = Real.sqrt (∑ k : Fin K, ‖p k‖ ^ 2) from rfl,
        Real.sq_sqrt (Finset.sum_nonneg (fun k _ => sq_nonneg _))]
    calc ∫ u in (0:ℝ)..1, (‖Φ u p‖) ^ 2
        ≤ c₁ * ∑ k : Fin K, ‖p k‖ ^ 2 := hc1
      _ = (Real.sqrt c₁ * D) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hc₁pos.le, hD2]
  -- The weights.
  let X : ℕ → ℝ := fun t => Real.sqrt (min (K:ℝ) ((M t : ℝ) + 1))
  let Tsum : ℝ := ∑ t ∈ Finset.range (S+1), (1/2:ℝ)^t * X t
  let w : ℕ → ℝ := fun j => if j < S
      then (2 * (1/2:ℝ)^(S-j-1)) * Real.sqrt (min (K:ℝ) (c₀ * ((B j).card : ℝ) + 1))
      else Real.sqrt c₁ * D
  let uu : ℕ → ℝ := fun j => w j + (1/2:ℝ)^(j+1)
  have hXnn : ∀ t, 0 ≤ X t := fun t => Real.sqrt_nonneg _
  have hwnn : ∀ j, 0 ≤ w j := by
    intro j
    by_cases hj : j < S
    · have h1 : w j = (2 * (1/2:ℝ)^(S-j-1))
          * Real.sqrt (min (K:ℝ) (c₀ * ((B j).card : ℝ) + 1)) := by
        simp only [w]; rw [if_pos hj]
      rw [h1]
      exact mul_nonneg (by positivity) (Real.sqrt_nonneg _)
    · have h1 : w j = Real.sqrt c₁ * D := by simp only [w]; rw [if_neg hj]
      rw [h1]
      exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have huun : ∀ j, 0 ≤ uu j := fun j =>
    add_nonneg (hwnn j) (by positivity)
  have huu_pos : ∀ j ∈ Finset.range (S+1), 0 < uu j := by
    intro j _
    have h1 : 0 < (1/2:ℝ)^(j+1) := by positivity
    have h2 : 0 ≤ w j := hwnn j
    exact lt_of_lt_of_le h1 (le_add_of_nonneg_left h2)
  have hminKnn : ∀ j, (0:ℝ) ≤ min (K:ℝ) (c₀ * ((B j).card : ℝ) + 1) := fun j =>
    le_min (by positivity) (add_nonneg (mul_nonneg hc₀pos.le (Nat.cast_nonneg _)) zero_le_one)
  have huu_bound : ∀ j ∈ Finset.range (S+1),
      ∫⁻ y in Set.Ioc (0:ℝ) 1, ENNReal.ofReal (Acls j y) ^ 2
        ≤ ENNReal.ofReal ((uu j) ^ 2) := by
    intro j hj
    rw [Finset.mem_range] at hj
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with hlt | heq
    · have h1 : uu j = (2 * (1/2:ℝ)^(S-j-1))
          * Real.sqrt (min (K:ℝ) (c₀ * ((B j).card : ℝ) + 1)) + (1/2:ℝ)^(j+1) := by
        have hwj : w j = (2 * (1/2:ℝ)^(S-j-1))
            * Real.sqrt (min (K:ℝ) (c₀ * ((B j).card : ℝ) + 1)) := by
          dsimp only [w]
          rw [if_pos hlt]
        show w j + (1/2:ℝ)^(j+1) = _
        rw [hwj]
      rw [h1]
      refine (hcls_bound j hlt).trans (ENNReal.ofReal_le_ofReal ?_)
      have hb : 0 ≤ (2 * (1/2:ℝ)^(S-j-1))
          * Real.sqrt (min (K:ℝ) (c₀ * ((B j).card : ℝ) + 1)) :=
        mul_nonneg (by positivity) (Real.sqrt_nonneg _)
      have hsq : ((2 * (1/2:ℝ)^(S-j-1))
          * Real.sqrt (min (K:ℝ) (c₀ * ((B j).card : ℝ) + 1))) ^ 2
          = (2 * (1/2:ℝ)^(S-j-1)) ^ 2 * min (K:ℝ) (c₀ * ((B j).card : ℝ) + 1) := by
        rw [mul_pow, Real.sq_sqrt (hminKnn j)]
      rw [← hsq]
      exact pow_le_pow_left₀ hb (le_add_of_nonneg_right (by positivity)) 2
    · rw [heq]
      have h1 : uu S = Real.sqrt c₁ * D + (1/2:ℝ)^(S+1) := by
        have hwS : w S = Real.sqrt c₁ * D := by
          dsimp only [w]
          rw [if_neg (lt_irrefl S)]
        show w S + (1/2:ℝ)^(S+1) = _
        rw [hwS]
      rw [h1]
      refine htop_bound.trans ?_
      apply ENNReal.ofReal_le_ofReal
      exact pow_le_pow_left₀ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
        (le_add_of_nonneg_right (by positivity)) 2
  obtain hmain := lintegral_sq_sum_le_of_class_bounds (Finset.range (S+1)) Acls uu huu_pos
    (fun j _ y => hAcls_nn j y)
    (fun j _ => ((hAcls_cont j).measurable.ennreal_ofReal.pow_const 2).aemeasurable)
    huu_bound
  have hstep1 : ∫⁻ y in Set.Ioc (0:ℝ) 1, ENNReal.ofReal
      (⨆ i : Fin (N+1), ‖∑ k : Fin K, a i k * Complex.exp (Complex.I * (lam k:ℂ) * (y:ℂ))‖) ^ 2
      ≤ ∫⁻ y in Set.Ioc (0:ℝ) 1, ENNReal.ofReal (∑ j ∈ Finset.range (S+1), Acls j y) ^ 2 := by
    apply lintegral_mono
    intro y
    simp only
    have hsum0 : (0:ℝ) ≤ ∑ j ∈ Finset.range (S+1), Acls j y :=
      Finset.sum_nonneg (fun j _ => hAcls_nn j y)
    rw [← ENNReal.ofReal_pow hsum0 2, ← ENNReal.ofReal_pow (hsup0 y) 2]
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (hsup0 y) (hdom y) 2)
  refine le_trans hstep1 (le_trans hmain ?_)
  apply ENNReal.ofReal_le_ofReal
  -- Numerical bound on `(∑ uu)²`.
  have hDnn : 0 ≤ D := Real.sqrt_nonneg _
  have hTsum_ge_one : 1 ≤ Tsum := by
    have hmem : 0 ∈ Finset.range (S+1) := Finset.mem_range.mpr (by omega)
    have hX0 : 1 ≤ X 0 := by
      have hK1 : (1:ℝ) ≤ (K:ℝ) := by exact_mod_cast hKpos
      have hM1 : 1 ≤ M 0 := by
        have h1 : 1 ≤ (Finset.univ.image (σ 0)).card :=
          Finset.card_pos.mpr (Finset.image_nonempty.mpr ⟨0, Finset.mem_univ 0⟩)
        exact le_trans h1 (hcard 0 (by omega))
      have hM01 : (1:ℝ) ≤ (M 0 : ℝ) := by exact_mod_cast hM1
      have hmin1 : (1:ℝ) ≤ min (K:ℝ) ((M 0 : ℝ) + 1) := le_min hK1 (by linarith)
      show (1:ℝ) ≤ Real.sqrt (min (K:ℝ) ((M 0 : ℝ) + 1))
      rw [Real.le_sqrt (by norm_num) (by linarith [hmin1])]
      simpa using hmin1
    calc (1:ℝ) ≤ X 0 := hX0
      _ = (1/2:ℝ)^0 * X 0 := by rw [pow_zero, one_mul]
      _ ≤ Tsum := Finset.single_le_sum (f := fun t => (1/2:ℝ)^t * X t)
          (fun t _ => mul_nonneg (by positivity) (hXnn t)) hmem
  have hgeom2 : ∑ j ∈ Finset.range S, (1/2:ℝ)^(j+1) ≤ 1 := by
    rw [show (∑ j ∈ Finset.range S, (1/2:ℝ)^(j+1))
        = (1/2:ℝ) * ∑ j ∈ Finset.range S, (1/2:ℝ)^j from by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _
          rw [pow_succ]; ring]
    have hgs : ∑ j ∈ Finset.range S, (1/2:ℝ)^j ≤ 2 := by
      have h1 : ∑ j ∈ Finset.range S, ((1/2:ℝ)^j - (1/2:ℝ)^(j+1)) = 1 - (1/2:ℝ)^S := by
        have h3 := Finset.sum_range_sub (fun j => (1/2:ℝ)^j) S
        rw [pow_zero] at h3
        have h4 : ∑ j ∈ Finset.range S, ((1/2:ℝ)^j - (1/2:ℝ)^(j+1))
            = -∑ j ∈ Finset.range S, ((1/2:ℝ)^(j+1) - (1/2:ℝ)^j) := by
          rw [← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl (fun j _ => by ring)
        rw [h4, h3]; ring
      have h2 : ∑ j ∈ Finset.range S, ((1/2:ℝ)^j - (1/2:ℝ)^(j+1))
          = (1/2) * ∑ j ∈ Finset.range S, (1/2:ℝ)^j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro j _
        rw [pow_succ]; ring
      rw [h2] at h1
      nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 1/2) S]
    linarith
  have hBcard_le : ∀ j, j < S → (B j).card ≤ M (S-j) := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · subst hj0
      rw [Nat.sub_zero]
      exact le_trans hqcard0 hNM
    · exact le_trans (hqcard j hjpos hj) (hcard (S-j) (by omega))
  have hwbound : ∑ j ∈ Finset.range S, w j ≤ 4 * Real.sqrt (c₀ + 1) * Tsum := by
    have hterm : ∀ j ∈ Finset.range S, w j
        ≤ 2 * (1/2:ℝ)^(S-j-1) * Real.sqrt (c₀+1) * X (S-j) := by
      intro j hj
      rw [Finset.mem_range] at hj
      have hweq : w j = (2 * (1/2:ℝ)^(S-j-1))
          * Real.sqrt (min (K:ℝ) (c₀ * ((B j).card : ℝ) + 1)) := by
        dsimp only [w]; rw [if_pos hj]
      rw [hweq]
      have h1 : Real.sqrt (min (K:ℝ) (c₀ * ((B j).card : ℝ) + 1))
          ≤ Real.sqrt (c₀+1) * X (S-j) := by
        have h4 : ((B j).card : ℝ) ≤ (M (S-j) : ℝ) := by exact_mod_cast hBcard_le j hj
        have hx : c₀ * ((B j).card : ℝ) + 1 ≤ (c₀+1) * ((M (S-j) : ℝ) + 1) := by
          have hM' : (0:ℝ) ≤ (M (S-j) : ℝ) := Nat.cast_nonneg _
          have h5 := mul_le_mul_of_nonneg_left h4 hc₀pos.le
          nlinarith [h5, hM', hc₀pos]
        have hmin : min (K:ℝ) (c₀ * ((B j).card : ℝ) + 1)
            ≤ (c₀+1) * min (K:ℝ) ((M (S-j) : ℝ) + 1) := by
          rcases le_total ((M (S-j) : ℝ) + 1) (K:ℝ) with hle | hle
          · rw [min_eq_right hle]
            exact le_trans (min_le_right _ _) hx
          · rw [min_eq_left hle]
            calc min (K:ℝ) (c₀ * ((B j).card : ℝ) + 1) ≤ (K:ℝ) := min_le_left _ _
              _ ≤ (c₀+1) * K := by nlinarith [mul_nonneg hc₀pos.le (Nat.cast_nonneg K)]
        calc Real.sqrt (min (K:ℝ) (c₀ * ((B j).card : ℝ) + 1))
            ≤ Real.sqrt ((c₀+1) * min (K:ℝ) ((M (S-j) : ℝ) + 1)) := Real.sqrt_le_sqrt hmin
          _ = Real.sqrt (c₀+1) * X (S-j) := by
              rw [Real.sqrt_mul (show (0:ℝ) ≤ c₀+1 by linarith)]
      calc (2 * (1/2:ℝ)^(S-j-1)) * Real.sqrt (min (K:ℝ) (c₀ * ((B j).card : ℝ) + 1))
          ≤ (2 * (1/2:ℝ)^(S-j-1)) * (Real.sqrt (c₀+1) * X (S-j)) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = 2 * (1/2:ℝ)^(S-j-1) * Real.sqrt (c₀+1) * X (S-j) := by ring
    refine (Finset.sum_le_sum hterm).trans ?_
    have hcongr : (∑ j ∈ Finset.range S,
          2 * (1/2:ℝ)^(S-j-1) * Real.sqrt (c₀+1) * X (S-j))
        = ∑ j ∈ Finset.range S,
            2 * (1/2:ℝ)^(S-1-j) * Real.sqrt (c₀+1) * X (S-1-j+1) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_range] at hj
      have h4 : S - j - 1 = S - 1 - j := tsub_right_comm
      have h5 : S - j = S - 1 - j + 1 := by
        rw [← h4, Nat.sub_add_cancel (by omega : 1 ≤ S - j)]
      rw [h4, h5]
    have hrefl : (∑ j ∈ Finset.range S,
          2 * (1/2:ℝ)^(S-j-1) * Real.sqrt (c₀+1) * X (S-j))
        = ∑ i ∈ Finset.range S, 2 * (1/2:ℝ)^i * Real.sqrt (c₀+1) * X (i+1) := by
      rw [hcongr]
      exact Finset.sum_range_reflect
        (fun i => 2 * (1/2:ℝ)^i * Real.sqrt (c₀+1) * X (i+1)) S
    rw [hrefl]
    have himg : (∑ i ∈ Finset.range S, 2 * (1/2:ℝ)^i * Real.sqrt (c₀+1) * X (i+1))
        = 4 * Real.sqrt (c₀+1)
          * ∑ i ∈ Finset.range S, (1/2:ℝ)^(i+1) * X (i+1) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro i _
      rw [pow_succ]; ring
    rw [himg]
    have hsubset : (∑ i ∈ Finset.range S, (1/2:ℝ)^(i+1) * X (i+1))
        ≤ ∑ t ∈ Finset.range (S+1), (1/2:ℝ)^t * X t := by
      rw [Finset.sum_range_succ']
      have h0 : 0 ≤ (1/2:ℝ)^0 * X 0 := mul_nonneg (by norm_num) (hXnn 0)
      have hsum0 : 0 ≤ ∑ i ∈ Finset.range S, (1/2:ℝ)^(i+1) * X (i+1) :=
        Finset.sum_nonneg (fun i _ => mul_nonneg (by positivity) (hXnn (i+1)))
      linarith [h0, hsum0]
    calc 4 * Real.sqrt (c₀+1) * (∑ i ∈ Finset.range S, (1/2:ℝ)^(i+1) * X (i+1))
        ≤ 4 * Real.sqrt (c₀+1) * Tsum := by
          apply mul_le_mul_of_nonneg_left hsubset (by positivity)
      _ = 4 * Real.sqrt (c₀+1) * Tsum := rfl
  have hsum_uu : ∑ j ∈ Finset.range (S+1), uu j ≤ 100 * (c₀ + c₁ + 1) * (D + Tsum) := by
    rw [Finset.sum_range_succ]
    have hfirst : ∑ j ∈ Finset.range S, uu j ≤ 4 * Real.sqrt (c₀+1) * Tsum + 1 := by
      have h2 : ∑ j ∈ Finset.range S, uu j
          ≤ ∑ j ∈ Finset.range S, w j + ∑ j ∈ Finset.range S, (1/2:ℝ)^(j+1) := by
        have h2' : ∑ j ∈ Finset.range S, uu j
            = ∑ j ∈ Finset.range S, (w j + (1/2:ℝ)^(j+1)) := rfl
        rw [h2', Finset.sum_add_distrib]
      linarith [h2, hwbound, hgeom2]
    have hlast : uu S ≤ Real.sqrt c₁ * D + 1 := by
      have h1 : uu S = w S + (1/2:ℝ)^(S+1) := rfl
      have hwS : w S = Real.sqrt c₁ * D := by
        dsimp only [w]; rw [if_neg (lt_irrefl S)]
      rw [h1, hwS]
      have : (1/2:ℝ)^(S+1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      linarith
    have hsqrtc01 : Real.sqrt (c₀+1) ≤ c₀ + 1 := by
      nlinarith [Real.sq_sqrt (by positivity : (0:ℝ) ≤ c₀+1), Real.sqrt_nonneg (c₀+1),
        sq_nonneg (Real.sqrt (c₀+1) - 1)]
    have hsqrtc1 : Real.sqrt c₁ ≤ c₁ + 1 := by
      nlinarith [Real.sq_sqrt hc₁pos.le, Real.sqrt_nonneg c₁, sq_nonneg (Real.sqrt c₁ - 1)]
    have hDsum : 1 ≤ D + Tsum := le_trans hTsum_ge_one (le_add_of_nonneg_left hDnn)
    have hTnn : 0 ≤ Tsum := Finset.sum_nonneg (fun t _ => mul_nonneg (by positivity) (hXnn t))
    have hTle : Tsum ≤ D + Tsum := le_add_of_nonneg_left hDnn
    have hDle : D ≤ D + Tsum := le_add_of_nonneg_right hTnn
    nlinarith [hfirst, hlast, hsqrtc01, hsqrtc1, hDsum, hDle, hTle, hDnn, hTnn,
      Real.sqrt_nonneg (c₀+1), Real.sqrt_nonneg c₁, mul_nonneg hc₀pos.le hTnn,
      mul_nonneg (Real.sqrt_nonneg (c₀+1)) hTnn]
  have hnn : 0 ≤ ∑ j ∈ Finset.range (S+1), uu j := Finset.sum_nonneg (fun j hj => (huu_pos j hj).le)
  calc (∑ j ∈ Finset.range (S+1), uu j) ^ 2
      ≤ (100 * (c₀ + c₁ + 1) * (D + Tsum)) ^ 2 := pow_le_pow_left₀ hnn hsum_uu 2
    _ ≤ (200 * (c₀ + c₁ + 1) * (D + Tsum)) ^ 2 := by
        have hDsum0 : 0 ≤ D + Tsum :=
          le_trans (le_trans zero_le_one hTsum_ge_one) (le_add_of_nonneg_left hDnn)
        have hnn1 : 0 ≤ 100 * (c₀ + c₁ + 1) * (D + Tsum) :=
          mul_nonneg (mul_nonneg (by norm_num) (by linarith)) hDsum0
        have hle2 : 100 * (c₀ + c₁ + 1) * (D + Tsum) ≤ 200 * (c₀ + c₁ + 1) * (D + Tsum) := by
          nlinarith [hc₀pos, hc₁pos, hDsum0]
        exact pow_le_pow_left₀ hnn1 hle2 2

private lemma lintegral_Ioc_add_right_u (F : ℝ → ℝ≥0∞) (c : ℝ) :
    ∫⁻ y in Set.Ioc (0:ℝ) 1, F (y + c) = ∫⁻ y in Set.Ioc c (c + 1), F y := by
  rw [← MeasureTheory.lintegral_indicator measurableSet_Ioc,
      ← MeasureTheory.lintegral_indicator measurableSet_Ioc]
  have h1 : ∀ y, Set.indicator (Set.Ioc (0:ℝ) 1) (fun z => F (z + c)) y
      = Set.indicator (Set.Ioc c (c + 1)) F (y + c) := by
    intro y
    rw [Set.indicator_apply, Set.indicator_apply]
    by_cases h : y ∈ Set.Ioc (0:ℝ) 1
    · rw [if_pos h, if_pos ⟨by linarith [h.1], by linarith [h.2]⟩]
    · rw [if_neg h]
      by_cases h2 : y + c ∈ Set.Ioc c (c + 1)
      · exact absurd ⟨by linarith [h2.1], by linarith [h2.2]⟩ h
      · rw [if_neg h2]
  calc ∫⁻ y, Set.indicator (Set.Ioc (0:ℝ) 1) (fun z => F (z + c)) y
      = ∫⁻ y, Set.indicator (Set.Ioc c (c + 1)) F (y + c) := by simp only [h1]
    _ = ∫⁻ y, Set.indicator (Set.Ioc c (c + 1)) F y :=
        MeasureTheory.lintegral_add_right_eq_self _ c


/-- **The entropy chain on an arbitrary interval of length one** (uniform in `K`, `lam`). -/
theorem chain_exp_sum_le_entropy_Ioc_uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : ℕ) (lam : Fin K → ℝ)
      (hsep : ∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|),
      ∀ (N S : ℕ) (a : Fin (N+1) → Fin K → ℂ)
        (σ : ℕ → Fin (N+1) → Fin (N+1)) (M : ℕ → ℕ) (c : ℝ),
      1 ≤ S →
      (∀ i : Fin (N+1), σ 0 i = σ 0 0) →
      (N+1) ≤ M S →
      (∀ t, t ≤ S → (Finset.univ.image (σ t)).card ≤ M t) →
      (∀ t, t ≤ S → ∀ i : Fin (N+1),
        ∑ k : Fin K, ‖a i k - a (σ t i) k‖ ^ 2 ≤ (2 * (1/2:ℝ)^t)^2) →
      ∫⁻ y in Set.Ioc c (c + 1),
          ENNReal.ofReal (⨆ i : Fin (N+1),
            ‖∑ k : Fin K, a i k * Complex.exp (Complex.I * (lam k:ℂ) * (y:ℂ))‖) ^ 2
        ≤ ENNReal.ofReal ((C * (Real.sqrt (∑ k : Fin K, ‖a (σ 0 0) k‖ ^ 2)
            + ∑ t ∈ Finset.range (S+1),
                (1/2:ℝ)^t * Real.sqrt (min (K:ℝ) ((M t : ℝ) + 1)))) ^ 2) := by
  obtain ⟨C, hCpos, hCu⟩ := chain_exp_sum_le_entropy_uniform
  refine ⟨C, hCpos, fun K lam hsep => ?_⟩
  have hC := hCu K lam hsep
  intro N S a σ M c hS hconst hNM hcard hnet
  set a' : Fin (N+1) → Fin K → ℂ :=
    fun i k => a i k * Complex.exp (Complex.I * (lam k : ℂ) * (c : ℂ)) with ha'
  have hnet' : ∀ t, t ≤ S → ∀ i : Fin (N+1),
      ∑ k : Fin K, ‖a' i k - a' (σ t i) k‖ ^ 2 ≤ (2 * (1/2:ℝ)^t)^2 := by
    intro t ht i
    have h : ∀ k : Fin K, ‖a' i k - a' (σ t i) k‖ = ‖a i k - a (σ t i) k‖ := by
      intro k
      have he : a' i k - a' (σ t i) k
          = (a i k - a (σ t i) k) * Complex.exp (Complex.I * (lam k:ℂ) * (c:ℂ)) := by
        rw [ha']; ring
      rw [he, norm_mul, norm_cexp_lin_u (lam k) c, mul_one]
    simpa only [h] using hnet t ht i
  have hmain := hC N S a' σ M hS hconst hNM hcard hnet'
  have hbase : (∑ k : Fin K, ‖a' (σ 0 0) k‖ ^ 2) = ∑ k : Fin K, ‖a (σ 0 0) k‖ ^ 2 := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [ha', norm_mul, norm_cexp_lin_u (lam k) c, mul_one]
  rw [hbase] at hmain
  have hchar : ∀ (i : Fin (N+1)) (y : ℝ),
      (∑ k : Fin K, a' i k * Complex.exp (Complex.I * (lam k:ℂ) * (y:ℂ)))
        = ∑ k : Fin K, a i k * Complex.exp (Complex.I * (lam k:ℂ) * ((y + c : ℝ):ℂ)) := by
    intro i y
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [ha']
    rw [mul_assoc]
    rw [show Complex.exp (Complex.I * (lam k : ℂ) * (c : ℂ))
            * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))
          = Complex.exp (Complex.I * (lam k : ℂ) * ((y + c : ℝ) : ℂ)) from by
        rw [← Complex.exp_add]; congr 1; push_cast; ring]
  have hshift : ∫⁻ y in Set.Ioc (0:ℝ) 1,
        ENNReal.ofReal (⨆ i : Fin (N+1),
          ‖∑ k : Fin K, a' i k * Complex.exp (Complex.I * (lam k:ℂ) * (y:ℂ))‖) ^ 2
      = ∫⁻ y in Set.Ioc c (c + 1),
        ENNReal.ofReal (⨆ i : Fin (N+1),
          ‖∑ k : Fin K, a i k * Complex.exp (Complex.I * (lam k:ℂ) * (y:ℂ))‖) ^ 2 := by
    rw [← lintegral_Ioc_add_right_u (fun y => ENNReal.ofReal (⨆ i : Fin (N+1),
      ‖∑ k : Fin K, a i k * Complex.exp (Complex.I * (lam k:ℂ) * (y:ℂ))‖) ^ 2) c]
    refine lintegral_congr (fun y => ?_)
    simp only [hchar]
  rw [hshift] at hmain
  exact hmain

/-! ### Covers from covering numbers -/



end

private lemma one_le_add_one_u (a : ENNReal) : 1 ≤ a + 1 := by
  calc (1:ENNReal) = 0 + 1 := by simp
    _ ≤ a + 1 := add_le_add bot_le le_rfl

/-- The last dyadic term of the entropy sum is at most one. -/
private lemma dyadic_tail_le_one_u (K S : ℕ) :
    (1/2:ℝ)^(S+1) * Real.sqrt (min (K:ℝ) ((S:ℝ) + 3)) ≤ 1 := by
  have h4 : ∀ S : ℕ, S + 3 ≤ 4^(S+1) := by
    intro S
    induction S with
    | zero => norm_num
    | succ k ih =>
        have hstep : k + 1 + 3 ≤ 4 * (k + 3) := by omega
        calc k + 1 + 3 ≤ 4 * (k + 3) := hstep
          _ ≤ 4 * 4^(k+1) := Nat.mul_le_mul_left 4 ih
          _ = 4^(k+2) := by ring
  have hsqrt : Real.sqrt (min (K:ℝ) ((S:ℝ) + 3)) ≤ 2^(S+1) := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have h5 : min (K:ℝ) ((S:ℝ) + 3) ≤ (S:ℝ) + 3 := min_le_right _ _
    have h6 : ((S:ℝ) + 3) ≤ (4:ℝ)^(S+1) := by exact_mod_cast h4 S
    have h7 : ((4:ℝ)^(S+1)) = (2:ℝ)^(S+1) * 2^(S+1) := by
      have : (4:ℝ) = 2 * 2 := by norm_num
      rw [this, mul_pow]
    rw [sq]
    linarith [h5, h6, h7]
  calc (1/2:ℝ)^(S+1) * Real.sqrt (min (K:ℝ) ((S:ℝ) + 3))
      ≤ (1/2:ℝ)^(S+1) * 2^(S+1) := mul_le_mul_of_nonneg_left hsqrt (by positivity)
    _ = 1 := by rw [← mul_pow]; norm_num


theorem chain_bound_at_z_uniform (Ψ : SchwartzMap ℝ ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : ℕ) (lam : Fin K → ℝ)
      (hsep : ∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|),
      ∀ (H : Fin K → ℝ → ℂ) (S : ℕ) (z : ℝ),
      ∫⁻ y in Set.Ioc (-z) (-z + 1),
        ENNReal.ofReal (⨆ i : Fin (S+2), ‖∑ k : Fin K,
          curvePt Ψ H (i:ℕ) z k * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖) ^ (2:ℝ)
      ≤ ENNReal.ofReal (C ^ 2) *
          (256 * (ENNReal.ofReal (curveRad Ψ H (S+1) z)) ^ (2:ℝ)
           + 16 * (∫⁻ r in Set.Ioi (0:ℝ), min (ENNReal.ofReal (Real.sqrt (K:ℝ)))
                    ((winML2 Ψ H z r) ^ ((1:ℝ)/2))) ^ (2:ℝ)) := by
  obtain ⟨Cch, hCchpos, hCchu⟩ := chain_exp_sum_le_entropy_Ioc_uniform
  refine ⟨16 * (Cch + 1), by positivity, fun K lam hsep => ?_⟩
  have hCch := hCchu K lam hsep
  intro H S z
  set I : ENNReal := ∫⁻ r in Set.Ioi (0:ℝ), min (ENNReal.ofReal (Real.sqrt (K:ℝ)))
    ((winML2 Ψ H z r) ^ ((1:ℝ)/2)) with hI
  set c : ℝ := curveRad Ψ H (S+1) z with hc
  have hcle : 0 ≤ c := by rw [hc]; exact curveRad_nonneg Ψ H (S+1) z
  by_cases hc0 : c = 0
  · -- degenerate: all curve points vanish
    have hcurve0 : ∀ i : Fin (S+2), curveVec Ψ H (S+1) z i = 0 := by
      intro i
      have hle : ‖curveVec Ψ H (S+1) z i‖ ≤ 0 := by
        have h := norm_curveVec_le_curveRad Ψ H (S+1) z i
        rw [← hc] at h
        rw [hc0] at h
        exact h
      exact norm_eq_zero.mp (le_antisymm hle (norm_nonneg _))
    have hpt0 : ∀ (i : Fin (S+2)) (k : Fin K), curvePt Ψ H (i:ℕ) z k = 0 := by
      intro i k
      rw [← curveVec_eq_curvePt]
      simp [hcurve0 i]
    have hsup0 : ∀ y : ℝ, (⨆ i : Fin (S+2), ‖∑ k : Fin K,
        curvePt Ψ H (i:ℕ) z k * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖) = 0 := by
      intro y
      rw [show (fun i : Fin (S+2) => ‖∑ k : Fin K,
          curvePt Ψ H (i:ℕ) z k * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖)
          = fun _ => (0:ℝ) from funext fun i => by simp [hpt0 i]]
      simp
    have hLHS0 : ∫⁻ y in Set.Ioc (-z) (-z + 1),
        ENNReal.ofReal (⨆ i : Fin (S+2), ‖∑ k : Fin K,
          curvePt Ψ H (i:ℕ) z k * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖) ^ (2:ℝ)
        = 0 := by
      simp [hsup0]
    rw [hLHS0]
    exact bot_le
  · have hcpos : 0 < c := lt_of_le_of_ne hcle (Ne.symm hc0)
    set κ : ℝ := 2 * c with hκ
    have hκpos : 0 < κ := by rw [hκ]; positivity
    have hκne : (κ:ℂ) ≠ 0 := by
      rw [ne_eq, Complex.ofReal_eq_zero]; exact hκpos.ne'
    -- the normalised family
    set b : Fin (S+2) → Fin K → ℂ := fun i k => ((κ:ℂ))⁻¹ * curvePt Ψ H (i:ℕ) z k with hb
    have hb_eq : ∀ (i : Fin (S+2)) (k : Fin K), curvePt Ψ H (i:ℕ) z k = (κ:ℂ) * b i k := by
      intro i k
      rw [hb, ← mul_assoc, mul_inv_cancel₀ hκne, one_mul]
    -- norm bound for the normalised family
    have hbnorm : ∀ i : Fin (S+2), ∑ k : Fin K, ‖b i k‖ ^ 2 ≤ (1:ℝ) := by
      intro i
      have h1 : ∑ k : Fin K, ‖curvePt Ψ H (i:ℕ) z k‖ ^ 2 ≤ c ^ 2 := by
        refine le_trans (sum_norm_sq_curvePt_le Ψ H (S+1) z i) ?_
        rw [hc]
      have h2 : ∀ k : Fin K,
          ‖b i k‖ ^ 2 = (κ⁻¹) ^ 2 * ‖curvePt Ψ H (i:ℕ) z k‖ ^ 2 := by
        intro k
        rw [hb]
        simp only [norm_mul, norm_inv, Complex.norm_of_nonneg hκpos.le]
        ring
      calc ∑ k : Fin K, ‖b i k‖ ^ 2
          = (κ⁻¹) ^ 2 * ∑ k : Fin K, ‖curvePt Ψ H (i:ℕ) z k‖ ^ 2 := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun k _ => h2 k
        _ ≤ (κ⁻¹) ^ 2 * c ^ 2 := mul_le_mul_of_nonneg_left h1 (by positivity)
        _ ≤ 1 := by
            rw [hκ]
            have hcne : c ≠ 0 := hcpos.ne'
            field_simp
            nlinarith [hcpos]
    -- the nets
    obtain ⟨σ, M, hσ0, hM0, hMS, hcard, hnetUn, hMbound⟩ := exists_nets Ψ H S z c hcpos (by rw [hc])
    -- the normalised net hypothesis
    have hnet : ∀ t, t ≤ S+1 → ∀ i : Fin (S+2),
        ∑ k : Fin K, ‖b i k - b (σ t i) k‖ ^ 2 ≤ (2 * (1/2:ℝ)^t)^2 := by
      intro t ht i
      have h := hnetUn t ht i
      have h3 : ∀ k : Fin K,
          ‖b i k - b (σ t i) k‖ ^ 2 = (κ⁻¹) ^ 2 * ‖curvePt Ψ H (i:ℕ) z k
            - curvePt Ψ H ((σ t i : Fin (S+2)):ℕ) z k‖ ^ 2 := by
        intro k
        rw [hb]
        have hrw : ((κ:ℂ))⁻¹ * curvePt Ψ H (i:ℕ) z k
            - ((κ:ℂ))⁻¹ * curvePt Ψ H ((σ t i : Fin (S+2)):ℕ) z k
            = ((κ:ℂ))⁻¹ * (curvePt Ψ H (i:ℕ) z k
                - curvePt Ψ H ((σ t i : Fin (S+2)):ℕ) z k) := by ring
        rw [hrw, norm_mul, norm_inv, Complex.norm_of_nonneg hκpos.le]
        ring
      calc ∑ k : Fin K, ‖b i k - b (σ t i) k‖ ^ 2
          = (κ⁻¹) ^ 2 * ∑ k : Fin K, ‖curvePt Ψ H (i:ℕ) z k
              - curvePt Ψ H ((σ t i : Fin (S+2)):ℕ) z k‖ ^ 2 := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun k _ => h3 k
        _ ≤ (κ⁻¹) ^ 2 * (4 * c * (1/2:ℝ)^t) ^ 2 := mul_le_mul_of_nonneg_left h (by positivity)
        _ = (2 * (1/2:ℝ)^t) ^ 2 := by
            rw [hκ]
            have hcne : c ≠ 0 := hcpos.ne'
            field_simp
            ring
    -- the chain bound
    have hchain := hCch (S+1) (S+1) b σ M (-z) (by omega) hσ0 (by rw [hMS]) hcard hnet
    -- bounds on the two summands of the chain RHS
    have hbase : Real.sqrt (∑ k : Fin K, ‖b (σ 0 0) k‖ ^ 2) ≤ 1 := by
      rw [Real.sqrt_le_one]
      exact hbnorm (σ 0 0)
    have hdyadic : ∀ r : ℝ, winML2 Ψ H z r + 1 - 1 = winML2 Ψ H z r := by
      intro r
      exact ENNReal.add_sub_cancel_right (by norm_num : (1:ENNReal) ≠ ∞)
    have hsumE : ENNReal.ofReal (∑ t ∈ Finset.range (S+1),
        (1/2:ℝ)^t * Real.sqrt (min (K:ℝ) ((M t : ℝ) + 1)))
        ≤ ENNReal.ofReal c⁻¹ * (2 * I) + 4 := by
      have hanti : ∀ r r' : ℝ, 0 < r → r ≤ r' →
          (fun r => winML2 Ψ H z r + 1) r' ≤ (fun r => winML2 Ψ H z r + 1) r := by
        intro r r' hr hrr
        refine add_le_add ?_ le_rfl
        have h1 : r.toNNReal ≤ r'.toNNReal := Real.toNNReal_mono hrr
        have h2 := Metric.coveringNumber_anti (A := Set.range (winCurveL2 Ψ H z))
          (ε := r.toNNReal) (δ := r'.toNNReal) h1
        have h3 : ((Metric.coveringNumber r'.toNNReal (Set.range (winCurveL2 Ψ H z)) : ℕ∞) : ENNReal)
            ≤ ((Metric.coveringNumber r.toNNReal (Set.range (winCurveL2 Ψ H z)) : ℕ∞) : ENNReal) := by
          exact_mod_cast h2
        unfold winML2
        exact tsub_le_tsub_right h3 1
      have hE1 : ∀ r : ℝ, 0 < r → 1 ≤ (fun r => winML2 Ψ H z r + 1) r :=
        fun r _ => one_le_add_one_u _
      have hhyp : ∀ t : ℕ, ((if t ≤ S then M t else 1 : ℕ) : ENNReal)
          ≤ (fun r => winML2 Ψ H z r + 1) (c * (1/2:ℝ)^t) := by
        intro t
        show ((if t ≤ S then M t else 1 : ℕ) : ENNReal)
          ≤ winML2 Ψ H z (c * (1/2:ℝ)^t) + 1
        by_cases ht : t ≤ S
        · rw [if_pos ht]
          rcases Nat.eq_zero_or_pos t with h0 | hpos
          · subst h0
            rw [hM0]
            simpa using one_le_add_one_u (winML2 Ψ H z (c * (1/2:ℝ)^0))
          · exact hMbound t hpos (by omega)
        · rw [if_neg ht]
          simpa using one_le_add_one_u (winML2 Ψ H z (c * (1/2:ℝ)^t))
      have h := dyadic_sum_le_lintegral_entropy (fun r => winML2 Ψ H z r + 1) hanti hE1 K
        (fun t => if t ≤ S then M t else 1) hcpos (S+1) hhyp
      have hIeq : (∫⁻ r in Set.Ioi (0:ℝ), min (ENNReal.ofReal (Real.sqrt (K:ℝ)))
            ((winML2 Ψ H z r + 1 - 1) ^ ((1:ℝ)/2))) = I := by
        rw [hI]
        exact lintegral_congr fun r => by rw [hdyadic r]
      have hsum_eq : (∑ t ∈ Finset.range (S+1), (1/2:ℝ)^t
            * Real.sqrt (min (K:ℝ) (((if t ≤ S then M t else 1 : ℕ) : ℝ) + 1)))
          = ∑ t ∈ Finset.range (S+1), (1/2:ℝ)^t
            * Real.sqrt (min (K:ℝ) ((M t : ℝ) + 1)) := by
        refine Finset.sum_congr rfl fun t ht => ?_
        rw [if_pos (Nat.lt_succ_iff.mp (Finset.mem_range.mp ht))]
      rw [hsum_eq, hIeq] at h
      exact h
    have htailTerm : ENNReal.ofReal ((1/2:ℝ)^(S+1) * Real.sqrt (min (K:ℝ) ((M (S+1) : ℝ) + 1)))
        ≤ 1 := by
      rw [hMS]
      have : ((S + 2 : ℕ) : ℝ) + 1 = (S:ℝ) + 3 := by push_cast; ring
      rw [this]
      exact ENNReal.ofReal_le_one.mpr (dyadic_tail_le_one_u K S)
    have hsumTot : ENNReal.ofReal (∑ t ∈ Finset.range (S+2),
        (1/2:ℝ)^t * Real.sqrt (min (K:ℝ) ((M t : ℝ) + 1)))
        ≤ ENNReal.ofReal c⁻¹ * (2 * I) + 5 := by
      rw [Finset.sum_range_succ, ENNReal.ofReal_add (by positivity) (by positivity)]
      refine (add_le_add hsumE htailTerm).trans (le_of_eq ?_)
      ring
    -- the sup comparison: the un-normalised sup is `κ` times the normalised one
    have hsup : ∀ y : ℝ, ENNReal.ofReal (⨆ i : Fin (S+2), ‖∑ k : Fin K,
        curvePt Ψ H (i:ℕ) z k * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖) ^ (2:ℝ)
        ≤ (ENNReal.ofReal κ) ^ 2 * ENNReal.ofReal (⨆ i : Fin (S+2), ‖∑ k : Fin K,
            b i k * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖) ^ (2:ℝ) := by
      intro y
      have h1 : (⨆ i : Fin (S+2), ‖∑ k : Fin K,
            curvePt Ψ H (i:ℕ) z k * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖)
          ≤ κ * (⨆ i : Fin (S+2), ‖∑ k : Fin K,
            b i k * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖) := by
        refine ciSup_le fun i => ?_
        have h2 : (∑ k : Fin K, curvePt Ψ H (i:ℕ) z k
              * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ)))
            = (κ:ℂ) * ∑ k : Fin K, b i k * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ)) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by rw [hb_eq i k]; ring
        rw [h2, norm_mul, Complex.norm_of_nonneg hκpos.le]
        have hbdd : BddAbove (Set.range (fun i : Fin (S+2) => ‖∑ k : Fin K,
            b i k * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖)) :=
          (Set.finite_range _).bddAbove
        exact mul_le_mul_of_nonneg_left (le_ciSup hbdd i) hκpos.le
      calc ENNReal.ofReal (⨆ i : Fin (S+2), ‖∑ k : Fin K,
            curvePt Ψ H (i:ℕ) z k * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖) ^ (2:ℝ)
          ≤ ENNReal.ofReal (κ * (⨆ i : Fin (S+2), ‖∑ k : Fin K,
              b i k * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖)) ^ (2:ℝ) :=
            ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal h1) (by norm_num)
        _ = (ENNReal.ofReal κ) ^ 2 * ENNReal.ofReal (⨆ i : Fin (S+2), ‖∑ k : Fin K,
              b i k * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖) ^ (2:ℝ) := by
            rw [ENNReal.ofReal_mul hκpos.le]
            rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast,
              ENNReal.rpow_natCast]
            ring
    -- integrability of the normalised integrand
    have hmeas : AEMeasurable (fun y : ℝ => ENNReal.ofReal (⨆ i : Fin (S+2), ‖∑ k : Fin K,
        b i k * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖) ^ (2:ℝ))
        (volume.restrict (Set.Ioc (-z) (-z+1))) := by
      refine (AEMeasurable.pow_const ?_ 2).mono_measure Measure.restrict_le_self
      refine ENNReal.continuous_ofReal.measurable.comp_aemeasurable ?_
      refine AEMeasurable.iSup fun i => ?_
      exact (by fun_prop : Continuous (fun y : ℝ => ‖∑ k : Fin K,
        b i k * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖)).aemeasurable
    -- integrate the sup comparison against the constant `(ofReal κ)²`
    have hLHSle : ∫⁻ y in Set.Ioc (-z) (-z + 1),
        ENNReal.ofReal (⨆ i : Fin (S+2), ‖∑ k : Fin K,
          curvePt Ψ H (i:ℕ) z k * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖) ^ (2:ℝ)
        ≤ (ENNReal.ofReal κ) ^ 2 * ∫⁻ y in Set.Ioc (-z) (-z + 1),
            ENNReal.ofReal (⨆ i : Fin (S+2), ‖∑ k : Fin K,
              b i k * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖) ^ (2:ℝ) :=
      calc ∫⁻ y in Set.Ioc (-z) (-z + 1),
            ENNReal.ofReal (⨆ i : Fin (S+2), ‖∑ k : Fin K,
              curvePt Ψ H (i:ℕ) z k * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖) ^ (2:ℝ)
          ≤ ∫⁻ y in Set.Ioc (-z) (-z + 1), (ENNReal.ofReal κ) ^ 2
              * ENNReal.ofReal (⨆ i : Fin (S+2), ‖∑ k : Fin K,
                b i k * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖) ^ (2:ℝ) :=
            lintegral_mono hsup
        _ = (ENNReal.ofReal κ) ^ 2 * ∫⁻ y in Set.Ioc (-z) (-z + 1),
              ENNReal.ofReal (⨆ i : Fin (S+2), ‖∑ k : Fin K,
                b i k * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖) ^ (2:ℝ) :=
            MeasureTheory.lintegral_const_mul'' _ hmeas
    -- the two bounds on the summands of the chain RHS, inside the chain bound
    have hbase' : ENNReal.ofReal (Real.sqrt (∑ k : Fin K, ‖b (σ 0 0) k‖ ^ 2)) ≤ 1 :=
      ENNReal.ofReal_le_one.mpr hbase
    have hSumM : ENNReal.ofReal (∑ t ∈ Finset.range (S+2),
        (1/2:ℝ)^t * Real.sqrt (min (K:ℝ) ((M t : ℝ) + 1)))
        ≤ ENNReal.ofReal c⁻¹ * (2 * I) + 5 := hsumTot
    have hinner : ENNReal.ofReal ((Cch * (Real.sqrt (∑ k : Fin K, ‖b (σ 0 0) k‖ ^ 2)
          + ∑ t ∈ Finset.range (S+2), (1/2:ℝ)^t * Real.sqrt (min (K:ℝ) ((M t : ℝ) + 1)))) ^ 2)
        ≤ (ENNReal.ofReal Cch * (1 + (ENNReal.ofReal c⁻¹ * (2 * I) + 5))) ^ (2:ℝ) := by
      rw [ENNReal.ofReal_pow (mul_nonneg hCchpos.le
          (add_nonneg (Real.sqrt_nonneg _)
            (Finset.sum_nonneg fun t _ => mul_nonneg
              (pow_nonneg (by norm_num : (0:ℝ) ≤ 1/2) t) (Real.sqrt_nonneg _)))),
        show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast]
      refine pow_le_pow_left₀ bot_le ?_ 2
      rw [ENNReal.ofReal_mul hCchpos.le]
      have hfac : ENNReal.ofReal (Real.sqrt (∑ k : Fin K, ‖b (σ 0 0) k‖ ^ 2)
            + ∑ i ∈ Finset.range (S+2), (1/2:ℝ)^i * Real.sqrt (min (K:ℝ) ((M i : ℝ) + 1)))
          ≤ 1 + (ENNReal.ofReal c⁻¹ * (2 * I) + 5) := by
        rw [ENNReal.ofReal_add (Real.sqrt_nonneg _)
          (Finset.sum_nonneg fun t _ => mul_nonneg
            (pow_nonneg (by norm_num : (0:ℝ) ≤ 1/2) t) (Real.sqrt_nonneg _))]
        exact add_le_add hbase' hSumM
      exact mul_le_mul_of_nonneg_left hfac bot_le
    -- **first identity**: `ofReal κ * ofReal c⁻¹ = 2`, since `κ * c⁻¹ = 2`.
    have hκc : ENNReal.ofReal κ * ENNReal.ofReal c⁻¹ = 2 := by
      rw [← ENNReal.ofReal_mul hκpos.le,
        show κ * c⁻¹ = 2 from by rw [hκ]; field_simp]
      norm_num
    -- the squared bound for `ofReal κ · Z`
    have hsq : ((ENNReal.ofReal κ) ^ 2) *
          (ENNReal.ofReal Cch * (1 + (ENNReal.ofReal c⁻¹ * (2 * I) + 5))) ^ (2:ℝ)
        ≤ ENNReal.ofReal ((16 * (Cch + 1)) ^ 2) *
          (256 * (ENNReal.ofReal c) ^ (2:ℝ) + 16 * I ^ (2:ℝ)) := by
      -- Step A: `ofReal κ * Z ≤ 6 * ofReal κ * ofReal Cch + 4 * ofReal Cch * I`
      have hZ : ENNReal.ofReal κ * (ENNReal.ofReal Cch
            * (1 + (ENNReal.ofReal c⁻¹ * (2 * I) + 5)))
          ≤ 6 * (ENNReal.ofReal κ * ENNReal.ofReal Cch) + 4 * ENNReal.ofReal Cch * I := by
        have h2 : (ENNReal.ofReal κ * ENNReal.ofReal Cch * ENNReal.ofReal c⁻¹)
            = 2 * ENNReal.ofReal Cch := by
          rw [mul_assoc, mul_comm (ENNReal.ofReal Cch) (ENNReal.ofReal c⁻¹), ← mul_assoc, hκc]
        have heq : ENNReal.ofReal κ * (ENNReal.ofReal Cch
              * (1 + (ENNReal.ofReal c⁻¹ * (2 * I) + 5)))
            = 6 * (ENNReal.ofReal κ * ENNReal.ofReal Cch) + 4 * ENNReal.ofReal Cch * I := by
          calc ENNReal.ofReal κ * (ENNReal.ofReal Cch
                * (1 + (ENNReal.ofReal c⁻¹ * (2 * I) + 5)))
              = ENNReal.ofReal κ * ENNReal.ofReal Cch
                + (ENNReal.ofReal κ * ENNReal.ofReal Cch * ENNReal.ofReal c⁻¹) * (2 * I)
                + 5 * (ENNReal.ofReal κ * ENNReal.ofReal Cch) := by ring
            _ = 6 * (ENNReal.ofReal κ * ENNReal.ofReal Cch) + 4 * ENNReal.ofReal Cch * I := by
                rw [h2]; ring
        rw [heq]
      -- Step B: `(ofReal κ)² * Z² = (ofReal κ * Z)²`
      have hB : ((ENNReal.ofReal κ) ^ 2) * (ENNReal.ofReal Cch
            * (1 + (ENNReal.ofReal c⁻¹ * (2 * I) + 5))) ^ (2:ℝ)
          = (ENNReal.ofReal κ * (ENNReal.ofReal Cch
              * (1 + (ENNReal.ofReal c⁻¹ * (2 * I) + 5)))) ^ (2:ℝ) := by
        rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num]
        simp only [ENNReal.rpow_natCast]
        rw [mul_pow]
        ring_nf
      -- Step C: the square of the bound
      have hC : (6 * (ENNReal.ofReal κ * ENNReal.ofReal Cch) + 4 * ENNReal.ofReal Cch * I) ^ (2:ℝ)
          ≤ 288 * (ENNReal.ofReal c) ^ (2:ℝ) * (ENNReal.ofReal Cch) ^ (2:ℝ)
            + 32 * (ENNReal.ofReal Cch) ^ (2:ℝ) * I ^ (2:ℝ) := by
        have h2 : (ENNReal.ofReal κ) ^ (2:ℝ) = 4 * (ENNReal.ofReal c) ^ (2:ℝ) := by
          rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num]
          simp only [ENNReal.rpow_natCast]
          rw [← ENNReal.ofReal_pow hκpos.le, ← ENNReal.ofReal_pow hcpos.le, hκ,
            show (2 * c) ^ 2 = 4 * c ^ 2 by ring,
            ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4),
            show ENNReal.ofReal (4:ℝ) = 4 from by norm_num]
        have hA : (6 * (ENNReal.ofReal κ * ENNReal.ofReal Cch)) ^ (2:ℝ)
            = 36 * ((ENNReal.ofReal κ) ^ (2:ℝ) * (ENNReal.ofReal Cch) ^ (2:ℝ)) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (z := (2:ℝ)) (show (0:ℝ) ≤ (2:ℝ) by norm_num),
            ENNReal.mul_rpow_of_nonneg _ _ (z := (2:ℝ)) (show (0:ℝ) ≤ (2:ℝ) by norm_num),
            show (6:ENNReal) ^ (2:ℝ) = 36 from by
              rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast]; norm_num]
        have hB2 : (4 * ENNReal.ofReal Cch * I) ^ (2:ℝ)
            = 16 * ((ENNReal.ofReal Cch) ^ (2:ℝ) * I ^ (2:ℝ)) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (z := (2:ℝ)) (show (0:ℝ) ≤ (2:ℝ) by norm_num),
            ENNReal.mul_rpow_of_nonneg _ _ (z := (2:ℝ)) (show (0:ℝ) ≤ (2:ℝ) by norm_num),
            show (4:ENNReal) ^ (2:ℝ) = 16 from by
              rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast]; norm_num]
          ring_nf
        calc (6 * (ENNReal.ofReal κ * ENNReal.ofReal Cch) + 4 * ENNReal.ofReal Cch * I) ^ (2:ℝ)
            ≤ 2 * (6 * (ENNReal.ofReal κ * ENNReal.ofReal Cch)) ^ (2:ℝ)
              + 2 * (4 * ENNReal.ofReal Cch * I) ^ (2:ℝ) :=
              Commons.Analysis.ENNReal.add_rpow_two_le_two_mul _ _
          _ = 2 * (36 * ((ENNReal.ofReal κ) ^ (2:ℝ) * (ENNReal.ofReal Cch) ^ (2:ℝ)))
              + 2 * (16 * ((ENNReal.ofReal Cch) ^ (2:ℝ) * I ^ (2:ℝ))) := by rw [hA, hB2]
          _ = 288 * (ENNReal.ofReal c) ^ (2:ℝ) * (ENNReal.ofReal Cch) ^ (2:ℝ)
              + 32 * (ENNReal.ofReal Cch) ^ (2:ℝ) * I ^ (2:ℝ) := by
              rw [h2]; ring_nf
      -- Step D: the constant comparison
      have hD : 288 * (ENNReal.ofReal c) ^ (2:ℝ) * (ENNReal.ofReal Cch) ^ (2:ℝ)
            + 32 * (ENNReal.ofReal Cch) ^ (2:ℝ) * I ^ (2:ℝ)
          ≤ ENNReal.ofReal ((16 * (Cch + 1)) ^ 2) *
            (256 * (ENNReal.ofReal c) ^ (2:ℝ) + 16 * I ^ (2:ℝ)) := by
        have h4 : (ENNReal.ofReal Cch) ^ (2:ℝ) ≤ ENNReal.ofReal ((Cch + 1) ^ 2) := by
          rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast,
            ← ENNReal.ofReal_pow hCchpos.le]
          exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hCchpos.le
            (le_trans (le_refl Cch) (le_add_of_nonneg_right (by norm_num : (0:ℝ) ≤ 1))) 2)
        have hC' : ENNReal.ofReal ((16 * (Cch + 1)) ^ 2)
            = 256 * ENNReal.ofReal ((Cch + 1) ^ 2) := by
          rw [show (16 * (Cch + 1)) ^ 2 = 256 * (Cch + 1) ^ 2 by ring,
            ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 256), ENNReal.ofReal_pow (by positivity)]
          norm_num
        rw [hC']
        refine (add_le_add (mul_le_mul le_rfl h4 (bot_le : (0:ENNReal) ≤ _) (bot_le : (0:ENNReal) ≤ _))
          (mul_le_mul (mul_le_mul le_rfl h4 (bot_le : (0:ENNReal) ≤ _) (bot_le : (0:ENNReal) ≤ _)) le_rfl (bot_le : (0:ENNReal) ≤ _) (bot_le : (0:ENNReal) ≤ _))).trans ?_
        rw [mul_add]
        refine add_le_add ?_ ?_
        · calc 288 * (ENNReal.ofReal c) ^ (2:ℝ) * ENNReal.ofReal ((Cch + 1) ^ 2)
              ≤ 65536 * (ENNReal.ofReal c) ^ (2:ℝ) * ENNReal.ofReal ((Cch + 1) ^ 2) :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by norm_num) bot_le) bot_le
            _ = 256 * ENNReal.ofReal ((Cch + 1) ^ 2) * (256 * (ENNReal.ofReal c) ^ (2:ℝ)) := by ring
        · calc 32 * ENNReal.ofReal ((Cch + 1) ^ 2) * I ^ (2:ℝ)
              ≤ 4096 * ENNReal.ofReal ((Cch + 1) ^ 2) * I ^ (2:ℝ) :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by norm_num) bot_le) bot_le
            _ = 256 * ENNReal.ofReal ((Cch + 1) ^ 2) * (16 * I ^ (2:ℝ)) := by ring
      calc ((ENNReal.ofReal κ) ^ 2) * (ENNReal.ofReal Cch
            * (1 + (ENNReal.ofReal c⁻¹ * (2 * I) + 5))) ^ (2:ℝ)
          = (ENNReal.ofReal κ * (ENNReal.ofReal Cch
              * (1 + (ENNReal.ofReal c⁻¹ * (2 * I) + 5)))) ^ (2:ℝ) := hB
        _ ≤ (6 * (ENNReal.ofReal κ * ENNReal.ofReal Cch) + 4 * ENNReal.ofReal Cch * I) ^ (2:ℝ) :=
            ENNReal.rpow_le_rpow hZ (show (0:ℝ) ≤ (2:ℝ) by norm_num)
        _ ≤ 288 * (ENNReal.ofReal c) ^ (2:ℝ) * (ENNReal.ofReal Cch) ^ (2:ℝ)
              + 32 * (ENNReal.ofReal Cch) ^ (2:ℝ) * I ^ (2:ℝ) := hC
        _ ≤ ENNReal.ofReal ((16 * (Cch + 1)) ^ 2) *
              (256 * (ENNReal.ofReal c) ^ (2:ℝ) + 16 * I ^ (2:ℝ)) := hD
    -- The chain bound with the exponent written as an rpow (matching the goal's integrand).
    -- NOTE (hard-won): `simpa only [...] using hchain` CANNOT descend into the integrand's lambda
    -- to change the exponent; restate as an explicit `(∫ …) = (∫ …)` and prove it with
    -- `congr 1`, `funext y`, then the `rpow_natCast` rewrite.  Same for any ℕ-vs-ℝ exponent
    -- mismatch under an integral.
    have hchainR : ∫⁻ y in Set.Ioc (-z) (-z + 1), ENNReal.ofReal (⨆ i : Fin (S+2), ‖∑ k : Fin K,
          b i k * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖) ^ (2:ℝ)
        ≤ ENNReal.ofReal ((Cch * (Real.sqrt (∑ k : Fin K, ‖b (σ 0 0) k‖ ^ 2)
            + ∑ t ∈ Finset.range (S+2), (1/2:ℝ)^t
                * Real.sqrt (min (K:ℝ) ((M t : ℝ) + 1)))) ^ 2) := by
      have h1 : (∫⁻ y in Set.Ioc (-z) (-z + 1), ENNReal.ofReal (⨆ i : Fin (S+2), ‖∑ k : Fin K,
            b i k * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖) ^ (2:ℝ))
          = (∫⁻ y in Set.Ioc (-z) (-z + 1), ENNReal.ofReal (⨆ i : Fin (S+2), ‖∑ k : Fin K,
            b i k * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖) ^ (2:ℕ)) := by
        congr 1
        funext y
        rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast]
      rw [h1]
      exact hchain
    -- final assembly
    calc ∫⁻ y in Set.Ioc (-z) (-z + 1),
          ENNReal.ofReal (⨆ i : Fin (S+2), ‖∑ k : Fin K,
            curvePt Ψ H (i:ℕ) z k * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖) ^ (2:ℝ)
        ≤ (ENNReal.ofReal κ) ^ 2 * ∫⁻ y in Set.Ioc (-z) (-z + 1),
            ENNReal.ofReal (⨆ i : Fin (S+2), ‖∑ k : Fin K,
              b i k * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ))‖) ^ (2:ℝ) := hLHSle
      _ ≤ (ENNReal.ofReal κ) ^ 2 * ENNReal.ofReal ((Cch * (Real.sqrt (∑ k : Fin K,
            ‖b (σ 0 0) k‖ ^ 2) + ∑ t ∈ Finset.range (S+2),
              (1/2:ℝ)^t * Real.sqrt (min (K:ℝ) ((M t : ℝ) + 1)))) ^ 2) :=
           mul_le_mul le_rfl hchainR (bot_le : (0:ENNReal) ≤ _) (bot_le : (0:ENNReal) ≤ _)
      _ ≤ (ENNReal.ofReal κ) ^ 2 * (ENNReal.ofReal Cch
            * (1 + (ENNReal.ofReal c⁻¹ * (2 * I) + 5))) ^ (2:ℝ) :=
          mul_le_mul le_rfl hinner (bot_le : (0:ENNReal) ≤ _) (bot_le : (0:ENNReal) ≤ _)
      _ ≤ ENNReal.ofReal ((16 * (Cch + 1)) ^ 2) *
          (256 * (ENNReal.ofReal c) ^ (2:ℝ) + 16 * I ^ (2:ℝ)) := hsq
      _ = ENNReal.ofReal ((16 * (Cch + 1)) ^ 2) *
          (256 * (ENNReal.ofReal (curveRad Ψ H (S+1) z)) ^ (2:ℝ)
           + 16 * (∫⁻ r in Set.Ioi (0:ℝ), min (ENNReal.ofReal (Real.sqrt (K:ℝ)))
                    ((winML2 Ψ H z r) ^ ((1:ℝ)/2))) ^ (2:ℝ)) := by rw [hc, hI]


theorem lintegral_winFL2_sq_le_uniform' (Ψ : SchwartzMap ℝ ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : ℕ) (H : Fin K → ℝ → ℂ),
      (∀ k : Fin K, MemLp (H k) 2 (volume : Measure ℝ)) →
      (∫⁻ z, (winFL2 Ψ H z) ^ (2:ℝ)) ≤ ENNReal.ofReal C * bandSq H := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := maximal_dilation_convolution_enorm_le_hlMax Ψ
  obtain ⟨C₀, hC₀pos, hC₀⟩ := Commons.Analysis.Maximal.real_maximal_strong_type 2 (by norm_num)
  refine ⟨C₀ ^ 2 * C₁ ^ 2, by positivity, fun K H hH2 => ?_⟩
  set hh : ℝ → ENNReal := fun x => (∑ k : Fin K,
      (ENNReal.ofReal C₁ * Commons.Analysis.Maximal.hlMax (fun y : ℝ => ‖H k y‖ₑ) x) ^ (2:ℝ))
      ^ ((1:ℝ)/2) with hhdef
  have hFle : ∀ x, winFL2 Ψ H x ≤ hh x := by
    intro x
    have h1 : winFL2 Ψ H x ≤ (⨆ (t : {t : ℝ // 0 < t}),
        (∑ k : Fin K, ‖winCurveL2 Ψ H x t k‖ₑ ^ (2:ℝ)) ^ ((1:ℝ)/2)) :=
      iSup_le fun t => (enorm_eq_sqrt_sum_L2 (winCurveL2 Ψ H x t)).le.trans
        (le_iSup (fun t : {t : ℝ // 0 < t} =>
          (∑ k : Fin K, ‖winCurveL2 Ψ H x t k‖ₑ ^ (2:ℝ)) ^ ((1:ℝ)/2)) t)
    refine h1.trans ?_
    rw [hhdef]
    refine iSup_le fun t => ?_
    refine ENNReal.rpow_le_rpow (Finset.sum_le_sum fun k _ => ?_) (by norm_num)
    exact ENNReal.rpow_le_rpow ((le_iSup (fun t : {t : ℝ // 0 < t} =>
      ‖winCurveL2 Ψ H x t k‖ₑ) t).trans (hC₁ (H k) (hH2 k) x)) (by norm_num)
  have hhmeas : Measurable hh := by
    rw [hhdef]
    exact (ENNReal.continuous_rpow_const.measurable).comp
      (Finset.measurable_sum _ fun k _ =>
        (measurable_const.mul (Commons.Analysis.Maximal.measurable_hlMax _)).pow_const 2)
  have hb : ∀ k : Fin K, AEMeasurable
      (fun x => (ENNReal.ofReal C₁ * Commons.Analysis.Maximal.hlMax (fun y : ℝ => ‖H k y‖ₑ) x) ^ (2:ℝ))
      volume := fun k => ((measurable_const.mul
        (Commons.Analysis.Maximal.measurable_hlMax _)).pow_const 2).aemeasurable
  have hAfin : bandSq H < ⊤ := by
    unfold bandSq
    have hcongr : (fun x : ℝ => ENNReal.ofReal (∑ k : Fin K, ‖H k x‖ ^ 2))
        = fun x => ∑ k : Fin K, ENNReal.ofReal (‖H k x‖ ^ 2) := by
      funext x
      exact ENNReal.ofReal_sum_of_nonneg (fun k _ => sq_nonneg _)
    rw [hcongr, lintegral_finsetSum' (Finset.univ)
      (f := fun k : Fin K => fun x : ℝ => ENNReal.ofReal (‖H k x‖ ^ 2))
      (fun k _ => ((hH2 k).aemeasurable.norm.pow_const 2).ennreal_ofReal)]
    refine ENNReal.sum_lt_top.mpr fun k _ => ?_
    have h1 : Integrable (fun x : ℝ => ‖H k x‖ ^ 2) volume := by
      have := (hH2 k).integrable_norm_rpow (p := 2) (by norm_num) (by norm_num)
      simpa using this
    have h2 := h1.lintegral_lt_top
    simpa only [enorm_eq_ofReal_norm'] using h2
  have hhfin : ∫⁻ x, hh x ^ (2:ℝ) ≤ ENNReal.ofReal (C₀ ^ 2 * C₁ ^ 2) * bandSq H := by
    have hpow : ∀ x : ℝ, hh x ^ (2:ℝ)
        = ∑ k : Fin K, (ENNReal.ofReal C₁ * Commons.Analysis.Maximal.hlMax (fun y : ℝ => ‖H k y‖ₑ) x) ^ (2:ℝ) := by
      intro x
      rw [hhdef, ← ENNReal.rpow_mul, show ((1:ℝ)/2) * 2 = 1 by norm_num, ENNReal.rpow_one]
    have hstep : ∀ k : Fin K, ∫⁻ x, (ENNReal.ofReal C₁ *
          Commons.Analysis.Maximal.hlMax (fun y : ℝ => ‖H k y‖ₑ) x) ^ (2:ℝ)
        ≤ ENNReal.ofReal (C₀ ^ 2 * C₁ ^ 2) * ∫⁻ x, ENNReal.ofReal (‖H k x‖ ^ 2) := by
      intro k
      have hfac : (fun x : ℝ => (ENNReal.ofReal C₁ *
            Commons.Analysis.Maximal.hlMax (fun y : ℝ => ‖H k y‖ₑ) x) ^ (2:ℝ))
          = fun x => (ENNReal.ofReal C₁) ^ (2:ℝ) *
              (Commons.Analysis.Maximal.hlMax (fun y : ℝ => ‖H k y‖ₑ) x) ^ (2:ℝ) := by
        funext x; rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
      rw [hfac, lintegral_const_mul'' _
        (((Commons.Analysis.Maximal.measurable_hlMax _).pow_const 2).aemeasurable)]
      rw [show (ENNReal.ofReal C₁) ^ (2:ℝ) = ENNReal.ofReal (C₁ ^ 2) by
        rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast,
          ENNReal.ofReal_pow hC₁pos.le]]
      have h32 : ∫⁻ x : ℝ, (Commons.Analysis.Maximal.hlMax (fun y : ℝ => ‖H k y‖ₑ) x) ^ (2:ℝ)
          ≤ ENNReal.ofReal (C₀ ^ 2) * ∫⁻ x : ℝ, ENNReal.ofReal (‖H k x‖ ^ 2) := by
        have h := hC₀ (fun y : ℝ => ‖H k y‖)
        have h1 : (fun y : ℝ => ‖(fun y : ℝ => ‖H k y‖) y‖ₑ) = fun y => ‖H k y‖ₑ := by
          funext y; exact enorm_norm_eq_enorm (H k y)
        rw [h1] at h
        have h2 : (fun x : ℝ => ‖‖H k x‖‖ₑ ^ (2:ℝ)) = fun x => ENNReal.ofReal (‖H k x‖ ^ 2) := by
          funext x
          rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast, enorm_norm_eq_enorm,
            enorm_eq_ofReal_norm', ENNReal.ofReal_pow (norm_nonneg _)]
        rw [h2] at h
        have hC : (C₀ : ℝ) ^ (2:ℝ) = C₀ ^ 2 := by
          rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
        rw [hC] at h
        simpa only [Commons.Analysis.Maximal.hlMax] using h
      calc ENNReal.ofReal (C₁ ^ 2) * ∫⁻ x, (Commons.Analysis.Maximal.hlMax (fun y : ℝ => ‖H k y‖ₑ) x) ^ (2:ℝ)
          ≤ ENNReal.ofReal (C₁ ^ 2) * (ENNReal.ofReal (C₀ ^ 2) * ∫⁻ x, ENNReal.ofReal (‖H k x‖ ^ 2)) :=
            mul_le_mul_of_nonneg_left h32 bot_le
        _ = ENNReal.ofReal (C₀ ^ 2 * C₁ ^ 2) * ∫⁻ x, ENNReal.ofReal (‖H k x‖ ^ 2) := by
            rw [ENNReal.ofReal_mul (sq_nonneg C₀)]
            ring
    calc ∫⁻ x, hh x ^ (2:ℝ)
        = ∑ k : Fin K, ∫⁻ x, (ENNReal.ofReal C₁ *
            Commons.Analysis.Maximal.hlMax (fun y : ℝ => ‖H k y‖ₑ) x) ^ (2:ℝ) := by
          rw [lintegral_congr fun x => hpow x, lintegral_finsetSum' Finset.univ (fun k _ => hb k)]
      _ ≤ ∑ k : Fin K, ENNReal.ofReal (C₀ ^ 2 * C₁ ^ 2) * ∫⁻ x, ENNReal.ofReal (‖H k x‖ ^ 2) :=
          Finset.sum_le_sum fun k _ => hstep k
      _ = ENNReal.ofReal (C₀ ^ 2 * C₁ ^ 2) * bandSq H := by
          rw [← Finset.mul_sum, show bandSq H = ∫⁻ x, ENNReal.ofReal (∑ k : Fin K, ‖H k x‖ ^ 2) from rfl]
          congr 1
          rw [← lintegral_finsetSum' Finset.univ
            (f := fun k : Fin K => fun x : ℝ => ENNReal.ofReal (‖H k x‖ ^ 2))
            (fun k _ => ((hH2 k).aemeasurable.norm.pow_const 2).ennreal_ofReal)]
          exact lintegral_congr fun x =>
            (ENNReal.ofReal_sum_of_nonneg (fun k _ => sq_nonneg _)).symm
  calc ∫⁻ z, (winFL2 Ψ H z) ^ (2:ℝ)
      ≤ ∫⁻ z, (hh z) ^ (2:ℝ) := lintegral_mono fun z => ENNReal.rpow_le_rpow (hFle z) (by norm_num)
    _ ≤ ENNReal.ofReal (C₀ ^ 2 * C₁ ^ 2) * bandSq H := hhfin

theorem bandMaxTr_average_bound_uniform' (Ψ : SchwartzMap ℝ ℂ) {M : ℝ}
    (hM : ∀ x : ℝ, ‖(Ψ : ℝ → ℂ) x‖ ≤ M) :
    ∃ Cc : ℝ, 0 < Cc ∧ ∀ (K : ℕ) (lam : Fin K → ℝ)
      (hsep : ∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|)
      (H : Fin K → ℝ → ℂ),
      (∀ k : Fin K, MemLp (H k) 2 (volume : Measure ℝ)) →
      (∀ k : Fin K, MemLp (H k) ⊤ (volume : Measure ℝ)) →
      ∀ S : ℕ, ∫⁻ y in Set.Ioo (0:ℝ) (9/10), bandMaxTr Ψ lam H S y
        ≤ ENNReal.ofReal (Cc * (1 + (Real.log ((K:ℝ)+2))^4)) * bandSq H := by
  obtain ⟨Cch, hCchpos, hCchU⟩ := chain_bound_at_z_uniform Ψ
  obtain ⟨CA, hCApos, hCAU⟩ := lintegral_winFL2_sq_le_uniform' (Ψ := Ψ)
  obtain ⟨CB₀, hCB₀pos, hCB0⟩ := bourgain_entropy_integral_l2_l2vec Ψ M hM
  refine ⟨Cch ^ 2 * (256 * CA + 16 * CB₀ ^ 2), by positivity,
    fun K lam hsep H hH2 hHinf S => ?_⟩
  have hCch0 := hCchU K lam hsep
  have hCA0 : ∀ (G : Fin K → ℝ → ℂ), (∀ k, MemLp (G k) 2 (volume : Measure ℝ)) →
      ∫⁻ z, (winFL2 Ψ G z) ^ (2:ℝ) ≤ ENNReal.ofReal CA * bandSq G := hCAU K
  set CB : ℝ := (CB₀ * (Real.log ((K:ℝ)+2))^2)^2 with hCBdef
  have hCBpos : 0 < CB := by
    rw [hCBdef]
    have hK : (1:ℝ) < (K:ℝ) + 2 := by
      have h : (0:ℝ) ≤ (K:ℝ) := Nat.cast_nonneg K
      linarith
    exact pow_pos (mul_pos hCB₀pos (pow_pos (Real.log_pos hK) 2)) 2
  have hcore : ∫⁻ y in Set.Ioo (0:ℝ) (9/10), bandMaxTr Ψ lam H S y
      ≤ ENNReal.ofReal (Cch ^ 2 * (256 * CA + 16 * CB)) * bandSq H := by
    have hA : ∫⁻ z, (ENNReal.ofReal (curveRad Ψ H (S+1) z)) ^ (2:ℝ)
        ≤ ENNReal.ofReal CA * bandSq H :=
      le_trans (lintegral_mono fun z =>
        ENNReal.rpow_le_rpow (curveRad_le_winFL2 Ψ H (S+1) z) (by norm_num)) (hCA0 H hH2)
    have hB : ∫⁻ z, (∫⁻ r in Set.Ioi (0:ℝ), min (ENNReal.ofReal (Real.sqrt (K:ℝ)))
          ((winML2 Ψ H z r) ^ ((1:ℝ)/2))) ^ (2:ℝ) ≤ ENNReal.ofReal CB * bandSq H := by
      have h := hCB0 K H hH2 hHinf
      rw [hCBdef]
      simpa only [bandSq, winML2, min_comm] using h
    refine le_trans (bandMaxTr_average_le Ψ lam H S hCchpos (fun z => hCch0 H S z)
      ((aemeasurable_uncurry_tonelliFun Ψ lam H hH2 S).mono_measure
        (MeasureTheory.Measure.prod_mono Measure.restrict_le_self le_rfl))) ?_
    refine le_trans (z_integral_le Ψ H S hCchpos
      (aemeasurable_ofReal_curveRad_rpow Ψ H hH2 (S+1)) hA hB) ?_
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_ofNat, ENNReal.ofReal_ofNat]
    exact le_of_eq (by ring)
  refine le_trans hcore ?_
  refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) bot_le
  rw [hCBdef]
  have hu : 0 ≤ Real.log ((K:ℝ) + 2) ^ 2 := sq_nonneg _
  nlinarith [hCchpos, hCApos, hCB₀pos, hu,
    mul_nonneg (sq_nonneg Cch) (sq_nonneg (CB₀ * Real.log ((K:ℝ)+2)^2)),
    mul_nonneg (mul_nonneg (sq_nonneg Cch) hCApos.le) (sq_nonneg (Real.log ((K:ℝ)+2)^2))]

theorem lintegral_bandMax_translate_le' (Ψ : SchwartzMap ℝ ℂ) {M : ℝ}
    (hM : ∀ x : ℝ, ‖(Ψ : ℝ → ℂ) x‖ ≤ M) :
    ∃ Cc : ℝ, 0 < Cc ∧ ∀ (K : ℕ) (lam : Fin K → ℝ)
      (hsep : ∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|)
      (H : Fin K → ℝ → ℂ),
      (∀ k : Fin K, MemLp (H k) 2 (volume : Measure ℝ)) →
      (∀ k : Fin K, MemLp (H k) ⊤ (volume : Measure ℝ)) →
      ∫⁻ y in Set.Ioo (0:ℝ) (9/10), bandMax Ψ lam (transH H y)
        ≤ ENNReal.ofReal (Cc * (1 + (Real.log ((K:ℝ)+2))^4)) * bandSq H := by
  obtain ⟨Cc, hCcpos, hCc⟩ := bandMaxTr_average_bound_uniform' Ψ hM
  refine ⟨Cc, hCcpos, fun K lam hsep H hH2 hHinf => ?_⟩
  rw [show (∫⁻ y in Set.Ioo (0:ℝ) (9/10), bandMax Ψ lam (transH H y))
      = ∫⁻ y in Set.Ioo (0:ℝ) (9/10), ⨆ S : ℕ, bandMaxTr Ψ lam H S y from
      lintegral_congr fun y => bandMax_translate_eq_iSup_bandMaxTr Ψ lam H hH2 y]
  rw [lintegral_iSup' (f := fun S : ℕ => fun y : ℝ => bandMaxTr Ψ lam H S y) ?_ ?_]
  · exact iSup_le (fun S => hCc K lam hsep H hH2 hHinf S)
  · intro S
    exact (aemeasurable_bandMaxTr Ψ lam H hH2 S).mono_measure Measure.restrict_le_self
  · refine Filter.Eventually.of_forall fun y => ?_
    intro S S' h
    refine lintegral_mono fun z => ENNReal.rpow_le_rpow (iSup_le fun i => ?_) (by norm_num)
    exact le_iSup (fun i' : Fin (S'+2) => ‖∑ k : Fin K, curvePt Ψ H (i':ℕ) z k
      * Complex.exp (Complex.I * (lam k : ℂ) * (((y - z : ℝ)) : ℂ))‖ₑ)
      (Fin.castLE (by omega) i)


/-- **The band-limited maximal bound, uniform in `lam` (and in the constant).**

Version of `bandMax_le_of_bandlimited` in which the constant is quantified *before* `K`, `lam`,
`hsep` and the admissibility bundle, so that it can be fed to `smooth_window_of_fixed_bump`. -/
theorem bandMax_le_of_bandlimited' (Ψ : SchwartzMap ℝ ℂ) {M : ℝ}
    (hM : ∀ x : ℝ, ‖(Ψ : ℝ → ℂ) x‖ ≤ M)
    {a : ℝ} (ha : 0 ≤ a) (hth : 2 * (2 * Real.pi * a * (9/10)) ^ 2 < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : ℕ) (lam : Fin K → ℝ)
      (hsep : ∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|)
      (Adm : (Fin K → ℝ → ℂ) → Prop)
      (h2 : ∀ H, Adm H → ∀ k, MemLp (H k) 2 (volume : Measure ℝ))
      (hinf : ∀ H, Adm H → ∀ k, MemLp (H k) ⊤ (volume : Measure ℝ))
      (hint : ∀ H, Adm H → ∀ k, Integrable (H k))
      (hsup : ∀ H, Adm H → ∀ k ξ, a < |ξ| → 𝓕 (H k) ξ = 0)
      (hpres : ∀ H (y : ℝ), Adm H → |y| ≤ 9/10 → Adm (shiftH H y)),
      ∀ (H : Fin K → ℝ → ℂ) (hH : Adm H), bandMax Ψ lam H
        ≤ ENNReal.ofReal (((C * (Real.log ((K:ℝ)+2))^2)^2)) * bandSq H := by
  obtain ⟨Ccu, hCcupos, hCcu⟩ := lintegral_bandMax_translate_le' Ψ hM
  refine ⟨Real.sqrt (4 * (10/9) * Ccu / (1 - 2 * (2 * Real.pi * a * (9/10)) ^ 2))
      * Real.sqrt 2 * (1 + 1 / (Real.log 2)^2)
      + 1 / (Real.log 2)^2, by positivity,
    fun K lam hsep Adm h2 hinf hint hsup hpres H hH => ?_⟩
  set Cc : ℝ := Ccu * (1 + (Real.log ((K:ℝ)+2))^4) with hCcdef
  have hCcpos : 0 < Cc := by rw [hCcdef]; positivity
  have hCc : ∀ (G : Fin K → ℝ → ℂ), (∀ k : Fin K, MemLp (G k) 2 (volume : Measure ℝ)) →
      (∀ k : Fin K, MemLp (G k) ⊤ (volume : Measure ℝ)) →
      ∫⁻ y in Set.Ioo (0:ℝ) (9/10), bandMax Ψ lam (transH G y) ≤ ENNReal.ofReal Cc * bandSq G := by
    intro G hG2 hGinf
    rw [hCcdef]
    exact hCcu K lam hsep G hG2 hGinf
  have hmain : bandMax Ψ lam H ≤ ENNReal.ofReal
      ((((Real.sqrt (4 * (10/9) * Cc / (1 - 2 * (2 * Real.pi * a * (9/10)) ^ 2)))
          / (Real.log ((K:ℝ) + 2)) ^ 2 + 1) * (Real.log ((K:ℝ) + 2)) ^ 2) ^ 2) * bandSq H := by
    have hCc0 : 0 < 2 * (10/9) * Cc := by positivity
    -- the selection of the shift
    have hsel : ∀ G : {G : Fin K → ℝ → ℂ // Adm G}, ∃ y : ℝ, y ∈ Set.Ioo (0:ℝ) (9/10) ∧
        bandMax Ψ lam (transH G.1 y) ≤ ENNReal.ofReal (2 * (10/9) * Cc) * bandSq G.1 := by
      intro G
      have hG2 := h2 G.1 G.2
      have hGinf := hinf G.1 G.2
      have hfin : bandSq G.1 < ⊤ := bandSq_lt_top G.1 hG2
      have hKtop : ENNReal.ofReal Cc * bandSq G.1 ≠ ⊤ :=
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin.ne
      obtain ⟨y, hy, hyle⟩ := exists_le_of_lintegral_le_ae (fun y : ℝ => bandMax Ψ lam (transH G.1 y))
        (aemeasurable_bandMax_translate Ψ lam G.1 hG2) (by norm_num) (hCc G.1 hG2 hGinf) hKtop
      refine ⟨y, hy, ?_⟩
      rw [show ENNReal.ofReal (9/10 - 0) = ENNReal.ofReal (9/10) by norm_num,
        show (ENNReal.ofReal Cc * bandSq G.1) + (ENNReal.ofReal Cc * bandSq G.1)
          = 2 * (ENNReal.ofReal Cc * bandSq G.1) by ring,
        mul_comm (ENNReal.ofReal (9/10)) (bandMax Ψ lam (transH G.1 y))] at hyle
      have h9 : (ENNReal.ofReal (9/10)) ≠ 0 := by simp
      have h9t : (ENNReal.ofReal (9/10)) ≠ ⊤ := ENNReal.ofReal_ne_top
      have hgoal : bandMax Ψ lam (transH G.1 y)
          ≤ (2 * (ENNReal.ofReal Cc * bandSq G.1)) / (ENNReal.ofReal (9/10)) :=
        (ENNReal.le_div_iff_mul_le (Or.inl h9) (Or.inl h9t)).mpr hyle
      have h1 : (ENNReal.ofReal (9/10))⁻¹ = ENNReal.ofReal (10/9) := by
        rw [← ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ) < 9/10)]
        congr 1
        norm_num
      have h2 : ENNReal.ofReal (2 * (10/9) * Cc)
          = (2:ENNReal) * ENNReal.ofReal (10/9) * ENNReal.ofReal Cc := by
        rw [show (2 * (10/9) * Cc : ℝ) = 2 * (10/9) * Cc by ring,
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_ofNat]
      calc bandMax Ψ lam (transH G.1 y)
          ≤ (2 * (ENNReal.ofReal Cc * bandSq G.1)) / (ENNReal.ofReal (9/10)) := hgoal
        _ = (2 * (ENNReal.ofReal Cc * bandSq G.1)) * (ENNReal.ofReal (9/10))⁻¹ := by
            rw [div_eq_mul_inv]
        _ = (2 * (ENNReal.ofReal Cc * bandSq G.1)) * ENNReal.ofReal (10/9) := by rw [h1]
        _ = ENNReal.ofReal (2 * (10/9) * Cc) * bandSq G.1 := by rw [h2]; ring
    let ysh : {G : Fin K → ℝ → ℂ // Adm G} → ℝ := fun G => Classical.choose (hsel G)
    have hysh_mem : ∀ G : {G : Fin K → ℝ → ℂ // Adm G}, ysh G ∈ Set.Ioo (0:ℝ) (9/10) :=
      fun G => (Classical.choose_spec (hsel G)).1
    have hysh_le : ∀ G : {G : Fin K → ℝ → ℂ // Adm G},
        bandMax Ψ lam (transH G.1 (ysh G)) ≤ ENNReal.ofReal (2 * (10/9) * Cc) * bandSq G.1 :=
      fun G => (Classical.choose_spec (hsel G)).2
    obtain ⟨CK, hCKpos, hCK⟩ := bandMax_apriori Ψ lam
    -- subadditivity (with the factor `2` coming from the squared norm)
    have hdecomp : ∀ G : {G : Fin K → ℝ → ℂ // Adm G},
        (fun k z => transH G.1 (ysh G) k z + shiftH G.1 (ysh G) k z) = G.1 := by
      intro G
      funext k z
      simp only [transH, shiftH]
      ring
    have hone : ∀ G : {G : Fin K → ℝ → ℂ // Adm G},
        bandMax Ψ lam G.1 ≤ ENNReal.ofReal (4 * (10/9) * Cc) * bandSq G.1
          + 2 * bandMax Ψ lam (shiftH G.1 (ysh G)) := by
      intro G
      have hle := bandMax_add_le Ψ lam (transH G.1 (ysh G)) (shiftH G.1 (ysh G))
        (memLp_transH (h2 G.1 G.2) (ysh G)) (memLp_shiftH (h2 G.1 G.2) (ysh G))
      rw [hdecomp G] at hle
      have hconst : (2:ENNReal) * (ENNReal.ofReal (2 * (10/9) * Cc) * bandSq G.1)
          = ENNReal.ofReal (4 * (10/9) * Cc) * bandSq G.1 := by
        have h4 : ENNReal.ofReal (4 * (10/9) * Cc)
            = (2:ENNReal) * ENNReal.ofReal (2 * (10/9) * Cc) := by
          rw [show (4 * (10/9) * Cc : ℝ) = 2 * (2 * (10/9) * Cc) by ring,
            ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_ofNat]
        rw [h4]; ring
      calc bandMax Ψ lam G.1
          ≤ 2 * bandMax Ψ lam (transH G.1 (ysh G)) + 2 * bandMax Ψ lam (shiftH G.1 (ysh G)) := hle
        _ ≤ 2 * (ENNReal.ofReal (2 * (10/9) * Cc) * bandSq G.1)
              + 2 * bandMax Ψ lam (shiftH G.1 (ysh G)) :=
            add_le_add (mul_le_mul_of_nonneg_left (hysh_le G) (bot_le)) (le_refl _)
        _ = ENNReal.ofReal (4 * (10/9) * Cc) * bandSq G.1
              + 2 * bandMax Ψ lam (shiftH G.1 (ysh G)) := by rw [hconst]
    -- the contraction, in the `2 · SQ` form
    have hcon : ∀ G : {G : Fin K → ℝ → ℂ // Adm G},
        2 * bandSq (shiftH G.1 (ysh G)) ≤ ENNReal.ofReal (2 * (2 * Real.pi * a * (9/10)) ^ 2) * bandSq G.1 := by
      intro G
      have hbase := bandSq_translate_sub_le (H := G.1) (a := a) (y := ysh G) ha
        (hint G.1 G.2) (h2 G.1 G.2) (hsup G.1 G.2)
      have hstep : 2 * bandSq (shiftH G.1 (ysh G))
          ≤ 2 * (ENNReal.ofReal ((2 * Real.pi * a * |ysh G|) ^ 2) * bandSq G.1) :=
        mul_le_mul_of_nonneg_left hbase (bot_le)
      have hyabs : |ysh G| ≤ 9/10 := le_of_lt (by rw [abs_of_pos (hysh_mem G).1]; exact (hysh_mem G).2)
      have hnn : 0 ≤ 2 * Real.pi * a := by positivity
      have hle2 : (2 * Real.pi * a * |ysh G|) ^ 2 ≤ (2 * Real.pi * a * (9/10)) ^ 2 := by
        have h1 : 2 * Real.pi * a * |ysh G| ≤ 2 * Real.pi * a * (9/10) :=
          mul_le_mul_of_nonneg_left hyabs hnn
        have h2 : 0 ≤ 2 * Real.pi * a * |ysh G| := by positivity
        nlinarith [h1, h2, hnn, abs_nonneg (ysh G)]
      have hconst : 2 * (ENNReal.ofReal ((2 * Real.pi * a * |ysh G|) ^ 2) * bandSq G.1)
          = ENNReal.ofReal (2 * (2 * Real.pi * a * |ysh G|) ^ 2) * bandSq G.1 := by
        rw [show (2 * (2 * Real.pi * a * |ysh G|) ^ 2 : ℝ) = 2 * ((2 * Real.pi * a * |ysh G|) ^ 2)
            by ring, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_ofNat]
        ring
      calc 2 * bandSq (shiftH G.1 (ysh G))
          ≤ 2 * (ENNReal.ofReal ((2 * Real.pi * a * |ysh G|) ^ 2) * bandSq G.1) := hstep
        _ = ENNReal.ofReal (2 * (2 * Real.pi * a * |ysh G|) ^ 2) * bandSq G.1 := by rw [hconst]
        _ ≤ ENNReal.ofReal (2 * (2 * Real.pi * a * (9/10)) ^ 2) * bandSq G.1 := by
            refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) bot_le
            linarith [hle2]
    have hiter := Commons.Analysis.Maximal.iter_bound_shift (X := {G : Fin K → ℝ → ℂ // Adm G})
      (M := fun G : {G : Fin K → ℝ → ℂ // Adm G} => bandMax Ψ lam G.1)
      (SQ := fun G : {G : Fin K → ℝ → ℂ // Adm G} => bandSq G.1)
      (T := fun G : {G : Fin K → ℝ → ℂ // Adm G} =>
        ⟨shiftH G.1 (ysh G), hpres G.1 (ysh G) G.2
          (le_of_lt (by rw [abs_of_pos (hysh_mem G).1]; exact (hysh_mem G).2))⟩)
      (A := 4 * (10/9) * Cc) (ρ := 2 * (2 * Real.pi * a * (9/10)) ^ 2) (CK := CK * (K:ℝ))
      (by positivity) (by positivity) (by positivity) hth (by positivity)
      (fun G => hone G) (fun G => hcon G) (fun G => hCK G.1 (h2 G.1 G.2))
      ⟨H, hH⟩
    -- constant bookkeeping: `A/(1-ρ) ≤ ((sqrt(A/(1-ρ))/log² + 1) · log²)²`
    refine hiter.trans ?_
    refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) bot_le
    have hlog : 0 < Real.log ((K:ℝ) + 2) := by
      refine Real.log_pos ?_
      have h : (0:ℝ) ≤ (K:ℝ) := Nat.cast_nonneg K
      linarith
    have hlog2 : 0 < (Real.log ((K:ℝ) + 2)) ^ 2 := pow_pos hlog 2
    have hsq : (Real.sqrt (4 * (10/9) * Cc / (1 - 2 * (2 * Real.pi * a * (9/10)) ^ 2))
        / (Real.log ((K:ℝ) + 2)) ^ 2 + 1) * (Real.log ((K:ℝ) + 2)) ^ 2
        = Real.sqrt (4 * (10/9) * Cc / (1 - 2 * (2 * Real.pi * a * (9/10)) ^ 2))
          + (Real.log ((K:ℝ) + 2)) ^ 2 := by
      field_simp
    have hnn : 0 ≤ Real.sqrt (4 * (10/9) * Cc / (1 - 2 * (2 * Real.pi * a * (9/10)) ^ 2)) :=
      Real.sqrt_nonneg _
    rw [hsq]
    have hx : Real.sqrt (4 * (10/9) * Cc / (1 - 2 * (2 * Real.pi * a * (9/10)) ^ 2)) ^ 2
        = 4 * (10/9) * Cc / (1 - 2 * (2 * Real.pi * a * (9/10)) ^ 2) :=
      Real.sq_sqrt (by positivity)
    have hexp : (Real.sqrt (4 * (10/9) * Cc / (1 - 2 * (2 * Real.pi * a * (9/10)) ^ 2))
          + (Real.log ((K:ℝ) + 2)) ^ 2) ^ 2
        = Real.sqrt (4 * (10/9) * Cc / (1 - 2 * (2 * Real.pi * a * (9/10)) ^ 2)) ^ 2
          + 2 * Real.sqrt (4 * (10/9) * Cc / (1 - 2 * (2 * Real.pi * a * (9/10)) ^ 2))
            * (Real.log ((K:ℝ) + 2)) ^ 2
          + ((Real.log ((K:ℝ) + 2)) ^ 2) ^ 2 := by ring
    rw [hexp, hx]
    nlinarith [hnn, hlog2, sq_nonneg ((Real.log ((K:ℝ) + 2)) ^ 2)]

  -- Bridge: trade the `K`-dependent constant `Cc` for the uniform one.
  refine le_trans hmain ?_
  refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) bot_le
  set u : ℝ := (Real.log ((K:ℝ) + 2)) ^ 2 with hudef
  have hlog : 0 < Real.log ((K:ℝ) + 2) := by
    refine Real.log_pos ?_
    have h : (0:ℝ) ≤ (K:ℝ) := Nat.cast_nonneg K
    linarith
  have hu : 0 < u := by rw [hudef]; exact pow_pos hlog 2
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2le : (Real.log 2) ^ 2 ≤ 1 := by
    have h : Real.log 2 ≤ 1 :=
      le_trans (Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)) (by norm_num)
    nlinarith [hlog2pos]
  have hulog2 : (Real.log 2) ^ 2 ≤ u := by
    rw [hudef]
    refine pow_le_pow_left₀ (Real.log_nonneg (by norm_num)) ?_ 2
    refine Real.log_le_log (by norm_num) ?_
    have h : (0:ℝ) ≤ (K:ℝ) := Nat.cast_nonneg K
    linarith
  have hmul : (Real.sqrt (4 * (10/9) * Cc / (1 - 2 * (2 * Real.pi * a * (9/10)) ^ 2)) / u + 1) * u
      = Real.sqrt (4 * (10/9) * Cc / (1 - 2 * (2 * Real.pi * a * (9/10)) ^ 2)) + u := by
    rw [add_mul, div_mul_cancel₀ _ hu.ne', one_mul]
  rw [hmul]
  set A : ℝ := Real.sqrt (4 * (10/9) * Ccu / (1 - 2 * (2 * Real.pi * a * (9/10)) ^ 2)) with hAdef
  have hA0 : 0 ≤ A := by rw [hAdef]; exact Real.sqrt_nonneg _
  have hsqrt2 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hden : (1 - 2 * (2 * Real.pi * a * (9/10)) ^ 2) ≠ 0 := by
    have h : (0:ℝ) < 1 - 2 * (2 * Real.pi * a * (9/10)) ^ 2 := by linarith [hth]
    exact ne_of_gt h
  have hCc_eq : Cc = Ccu * (1 + u ^ 2) := by rw [hCcdef, hudef]; ring
  have hD : Real.sqrt (4 * (10/9) * Cc / (1 - 2 * (2 * Real.pi * a * (9/10)) ^ 2))
      = A * Real.sqrt (1 + u ^ 2) := by
    have harg : 4 * (10/9) * Cc / (1 - 2 * (2 * Real.pi * a * (9/10)) ^ 2)
        = (4 * (10/9) * Ccu / (1 - 2 * (2 * Real.pi * a * (9/10)) ^ 2)) * (1 + u ^ 2) := by
      rw [hCc_eq]; field_simp
    rw [harg, hAdef]
    exact Real.sqrt_mul (x := 4 * (10/9) * Ccu / (1 - 2 * (2 * Real.pi * a * (9/10)) ^ 2))
      (by positivity) (1 + u ^ 2)
  rw [hD]
  have hsqrt1 : Real.sqrt (1 + u ^ 2) ≤ Real.sqrt 2 * (1 + u) := by
    have h1 : 1 + u ^ 2 ≤ 2 * (1 + u) ^ 2 := by nlinarith [hu]
    calc Real.sqrt (1 + u ^ 2) ≤ Real.sqrt (2 * (1 + u) ^ 2) := Real.sqrt_le_sqrt h1
      _ = Real.sqrt 2 * (1 + u) := by
          rw [Real.sqrt_mul (x := 2) (by norm_num) ((1 + u) ^ 2),
            Real.sqrt_sq (x := 1 + u) (by linarith [hu])]
  have h1u : 1 + u ≤ (1 + 1 / (Real.log 2) ^ 2) * u := by
    have hge : 1 ≤ (1 / (Real.log 2) ^ 2) * u := by
      have h1 : (1 / (Real.log 2) ^ 2) * (Real.log 2) ^ 2 = 1 := by
        rw [one_div, inv_mul_cancel₀ (by positivity : (Real.log 2) ^ 2 ≠ 0)]
      calc 1 = (1 / (Real.log 2) ^ 2) * (Real.log 2) ^ 2 := h1.symm
        _ ≤ (1 / (Real.log 2) ^ 2) * u := mul_le_mul_of_nonneg_left hulog2 (by positivity)
    calc 1 + u ≤ (1 / (Real.log 2) ^ 2) * u + u := by linarith
      _ = (1 + 1 / (Real.log 2) ^ 2) * u := by ring
  have h2u : u ≤ (1 / (Real.log 2) ^ 2) * u := by
    have hge : 1 ≤ 1 / (Real.log 2) ^ 2 := by
      rw [le_div_iff₀ (pow_pos hlog2pos 2)]
      linarith [hlog2le]
    calc u = 1 * u := by ring
      _ ≤ (1 / (Real.log 2) ^ 2) * u := mul_le_mul_of_nonneg_right hge (le_of_lt hu)
  have hstep : A * Real.sqrt (1 + u ^ 2) ≤ A * (Real.sqrt 2 * (1 + u)) :=
    mul_le_mul_of_nonneg_left hsqrt1 hA0
  have hstep2 : A * (Real.sqrt 2 * (1 + u))
      ≤ A * (Real.sqrt 2 * ((1 + 1 / (Real.log 2) ^ 2) * u)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1u hsqrt2) hA0
  have hval : A * (Real.sqrt 2 * ((1 + 1 / (Real.log 2) ^ 2) * u))
      = (A * Real.sqrt 2 * (1 + 1 / (Real.log 2) ^ 2)) * u := by ring
  have hlin : A * Real.sqrt (1 + u ^ 2) + u
      ≤ (A * Real.sqrt 2 * (1 + 1 / (Real.log 2) ^ 2) + 1 / (Real.log 2) ^ 2) * u := by
    calc A * Real.sqrt (1 + u ^ 2) + u
        ≤ A * (Real.sqrt 2 * (1 + u)) + u := add_le_add hstep le_rfl
      _ ≤ A * (Real.sqrt 2 * ((1 + 1 / (Real.log 2) ^ 2) * u)) + (1 / (Real.log 2) ^ 2) * u :=
          add_le_add hstep2 h2u
      _ = (A * Real.sqrt 2 * (1 + 1 / (Real.log 2) ^ 2) + 1 / (Real.log 2) ^ 2) * u := by
          rw [hval]; ring
  have hnnu : 0 ≤ A * Real.sqrt (1 + u ^ 2) + u := by positivity
  exact pow_le_pow_left₀ hnnu hlin 2

end Commons.Analysis.Fourier


open _root_.MeasureTheory Finset Filter
open scoped _root_.Topology
open scoped BigOperators _root_.ENNReal FourierTransform

set_option maxHeartbeats 1600000

namespace Commons.Analysis.Fourier
namespace FixWin

/-! ## Part 1: the window `Ψ = 𝓕(bump)(·/2π)`

The fixed bump `SepWin.bump` (`= 1` on `[-1/2,1/2]`, `= 0` off `[-1,1]`) defines, through its
Fourier transform, the Schwartz window `winSmooth` with
`winSmooth t = ∫_{-1}^{1} bump u · e^{-I t u} du`.
This is the window whose dyadic dilations are the band-pass kernels of the target operator. -/

lemma hasCompactSupport_bumpC :
    HasCompactSupport (fun x : ℝ => ((SepWin.bump x : ℝ) : ℂ)) := by
  refine HasCompactSupport.intro (K := Set.Icc (-1:ℝ) 1) isCompact_Icc ?_
  intro x hx
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
  rw [Complex.ofReal_eq_zero]
  exact SepWin.bump_zero x (by
    rcases hx with h | h
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith)

lemma contDiff_bumpC :
    ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => ((SepWin.bump x : ℝ) : ℂ)) := by
  have h : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => ((SepWin.bump x : ℝ) : ℂ)) := by
    rw [contDiff_iff_forall_nat_le]
    intro m _
    exact Complex.ofRealCLM.contDiff.comp (SepWin.bump_contDiff m)
  exact h

/-- `SepWin.bump` as a Schwartz map. -/
noncomputable def bumpS : SchwartzMap ℝ ℂ :=
  HasCompactSupport.toSchwartzMap hasCompactSupport_bumpC contDiff_bumpC

lemma bumpS_apply (x : ℝ) : (bumpS : ℝ → ℂ) x = ((SepWin.bump x : ℝ) : ℂ) :=
  HasCompactSupport.toSchwartzMap_toFun _ _ x

/-- Scaling by a nonzero constant as a continuous linear equivalence of `ℝ`. -/
noncomputable def scaleCLE (c : ℝ) (hc : c ≠ 0) : ℝ ≃L[ℝ] ℝ where
  toLinearEquiv :=
    { toFun := fun x => c * x
      invFun := fun x => c⁻¹ * x
      map_add' := fun x y => by ring
      map_smul' := fun r x => by simp only [smul_eq_mul, RingHom.id_apply]; ring
      left_inv := fun x => by field_simp
      right_inv := fun x => by field_simp }
  continuous_toFun := continuous_const.mul continuous_id
  continuous_invFun := continuous_const.mul continuous_id

@[simp] lemma scaleCLE_apply (c : ℝ) (hc : c ≠ 0) (x : ℝ) : scaleCLE c hc x = c * x := rfl

/-- **The window**: `Ψ = 𝓕(bump)(·/2π)`, so that `Ψ t = ∫_{-1}^{1} bump u e^{-Itu} du`. -/
noncomputable def winSmooth : SchwartzMap ℝ ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (scaleCLE (1 / (2 * Real.pi)) (by positivity)) (𝓕 bumpS)

lemma scaleCLE_one_div_two_pi (t : ℝ) :
    scaleCLE (1 / (2 * Real.pi)) (by positivity : (1 / (2 * Real.pi)) ≠ 0) t
      = t / (2 * Real.pi) := by
  rw [scaleCLE_apply, one_div, inv_mul_eq_div]

lemma winSmooth_apply_fourier (t : ℝ) :
    (winSmooth : ℝ → ℂ) t = (𝓕 (bumpS : ℝ → ℂ)) (t / (2 * Real.pi)) := by
  rw [winSmooth, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    scaleCLE_one_div_two_pi, SchwartzMap.fourier_coe]

/-- **The defining integral formula for the window.** -/
theorem winSmooth_apply (t : ℝ) :
    (winSmooth : ℝ → ℂ) t
      = ∫ u in (-1)..1, (SepWin.bump u : ℂ) * Complex.exp (-(Complex.I * (t : ℂ) * (u : ℂ))) := by
  rw [winSmooth_apply_fourier,
    Real.fourier_real_eq_integral_exp_smul]
  -- reduce the ℝ-integral to the integral over `(-1)..1`
  set g : ℝ → ℂ := fun v => Complex.exp (↑(-2 * Real.pi * v * (t / (2*Real.pi))) * Complex.I)
      • (bumpS : ℝ → ℂ) v with hg
  have hsupp : ∀ v : ℝ, v ∉ Set.Ioc (-1:ℝ) 1 → g v = 0 := by
    intro v hv
    rw [Set.mem_Ioc, not_and_or, not_lt, not_le] at hv
    rcases hv with hv | hv
    · have h1 : (1:ℝ) ≤ |v| := by rw [abs_of_nonpos (by linarith)]; linarith
      rw [hg]
      simp only [bumpS_apply, SepWin.bump_zero v h1, Complex.ofReal_zero, smul_zero]
    · have h1 : (1:ℝ) ≤ |v| := by rw [abs_of_nonneg (by linarith)]; linarith
      rw [hg]
      simp only [bumpS_apply, SepWin.bump_zero v h1, Complex.ofReal_zero, smul_zero]
  have hswap : (∫ v : ℝ, g v) = ∫ v in Set.Ioc (-1:ℝ) 1, g v :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero hsupp).symm
  rw [hswap, ← intervalIntegral.integral_of_le (by norm_num : (-1:ℝ) ≤ 1)]
  refine intervalIntegral.integral_congr fun v _ => ?_
  rw [hg]
  simp only [bumpS_apply, smul_eq_mul]
  have hexp : ↑(-2 * Real.pi * v * (t / (2*Real.pi))) * Complex.I
      = -(Complex.I * (t : ℂ) * (v : ℂ)) := by
    push_cast
    field_simp
  rw [hexp, mul_comm]

/-! ## Part 2: the band kernels

The pointwise kernel of the target operator, `innerSmooth bump K lam j z`, is the sum over `k` of
the shifted band kernel `e^{-I λ_k z} · winK Ψ j z`. -/

/-- **The change of variables for a single band kernel.**  For a window with
`Ψ t = ∫_{-1}^{1} φ u e^{-Itu} du`,
`∫_{λ-h}^{λ+h} φ((θ-λ)/h) e^{-Izθ} dθ = e^{-Iλz} · h · Ψ(hz)`. -/
theorem intervalIntegral_smooth_eq_winK (φ : ℝ → ℝ) (Ψ : ℝ → ℂ) (h : ℝ) (hh : 0 < h)
    (la z : ℝ)
    (hΨ : ∀ t : ℝ, Ψ t = ∫ u in (-1)..1, (φ u : ℂ) * Complex.exp (-(Complex.I * (t : ℂ) * (u : ℂ)))) :
    (∫ θ in (la - h)..(la + h), (φ ((θ - la) / h) : ℂ) * Complex.exp (-(Complex.I * (z : ℂ) * (θ : ℂ))))
      = Complex.exp (-(Complex.I * (la : ℂ) * (z : ℂ))) * ((h : ℂ) * Ψ (h * z)) := by
  have h1 : (∫ θ in (la - h)..(la + h),
        (φ ((θ - la) / h) : ℂ) * Complex.exp (-(Complex.I * (z : ℂ) * (θ : ℂ))))
      = h • ∫ u in (-1:ℝ)..1,
        (φ (((la + h * u) - la) / h) : ℂ)
          * Complex.exp (-(Complex.I * (z : ℂ) * ((la + h * u : ℝ) : ℂ))) := by
    have hbase := intervalIntegral.smul_integral_comp_add_mul
      (a := (-1:ℝ)) (b := 1)
      (f := fun θ : ℝ => (φ ((θ - la) / h) : ℂ)
        * Complex.exp (-(Complex.I * (z : ℂ) * (θ : ℂ)))) h la
    rw [show la + h * (-1) = la - h by ring, show la + h * 1 = la + h by ring] at hbase
    rw [← hbase]
  have h2 : (∫ u in (-1:ℝ)..1,
        (φ (((la + h * u) - la) / h) : ℂ)
          * Complex.exp (-(Complex.I * (z : ℂ) * ((la + h * u : ℝ) : ℂ))))
      = Complex.exp (-(Complex.I * (la : ℂ) * (z : ℂ))) * Ψ (h * z) := by
    rw [hΨ (h * z), ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun u _ => ?_
    rw [show la + h * u - la = h * u by ring,
      show (h * u) / h = u by field_simp]
    have hexp : -(Complex.I * (z : ℂ) * ((la + h * u : ℝ) : ℂ))
        = -(Complex.I * (la : ℂ) * (z : ℂ)) + -(Complex.I * ((h * z : ℝ) : ℂ) * (u : ℂ)) := by
      push_cast
      ring
    rw [hexp, Complex.exp_add]
    ring
  rw [h1, h2]
  rw [Complex.real_smul]
  ring

/-- The band kernel at frequency `la` and dyadic scale `j`: `e^{-I la z} · winK Ψ j z`. -/
noncomputable def bandKer (Ψ : SchwartzMap ℝ ℂ) (la : ℝ) (j : ℕ) : ℝ → ℂ :=
  fun z => Complex.exp (-(Complex.I * (la : ℂ) * (z : ℂ))) * winK Ψ j z

lemma bandKer_apply (Ψ : SchwartzMap ℝ ℂ) (la : ℝ) (j : ℕ) (z : ℝ) :
    bandKer Ψ la j z = Complex.exp (-(Complex.I * (la : ℂ) * (z : ℂ))) * winK Ψ j z := rfl

/-- **The kernel identity**: the smooth-window kernel of the target operator is the sum of the
band kernels. -/
theorem innerSmooth_eq_sum_bandKer {K : ℕ} (lam : Fin K → ℝ) (j : ℕ) (z : ℝ) :
    SepWin.innerSmooth SepWin.bump K lam j z
      = ∑ k : Fin K, bandKer winSmooth (lam k) j z := by
  rw [SepWin.innerSmooth]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [bandKer_apply]
  exact intervalIntegral_smooth_eq_winK SepWin.bump (winSmooth : ℝ → ℂ) (SepWin.hJ j)
    (SepWin.hJ_pos j) (lam k) z (fun t => winSmooth_apply t)


/-! ## Part 3: the oscillatory kernel `MjKer` and the band-kernel identity

`MjKer la j θ = bump((θ-la)/h_j)`, a compactly supported bounded oscillation.  The band kernel is
its oscillatory integral, `bandKer la j z = ∫ θ, MjKer la j θ · e^{-I z θ}`, and this is what makes
the convolution with the slice kernel `κ_k` (whose Fourier transform is `1` on the relevant band)
a no-op. -/

/-- The `θ`-oscillation of the band around `la` at scale `j`. -/
noncomputable def MjKer (la : ℝ) (j : ℕ) : ℝ → ℂ :=
  fun θ => ((SepWin.bump ((θ - la) / SepWin.hJ j) : ℝ) : ℂ)

lemma MjKer_measurable (la : ℝ) (j : ℕ) : Measurable (MjKer la j) :=
  Complex.continuous_ofReal.measurable.comp
    (SepWin.bump_continuous.measurable.comp (by fun_prop))

lemma MjKer_bound (la : ℝ) (j : ℕ) (θ : ℝ) : ‖MjKer la j θ‖ ≤ 1 := by
  rw [MjKer, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (SepWin.bump_bounds _).1]
  exact (SepWin.bump_bounds _).2

lemma abs_div_hJ_ge_one (la : ℝ) (j : ℕ) {θ : ℝ}
    (h : θ ∉ Set.Icc (la - SepWin.hJ j) (la + SepWin.hJ j)) :
    (1:ℝ) ≤ |(θ - la) / SepWin.hJ j| := by
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at h
  have hpos := SepWin.hJ_pos j
  have key : -((θ - la) / SepWin.hJ j) = (la - θ) / SepWin.hJ j := by ring
  rcases h with h | h
  · rw [abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hpos.le), key,
      le_div_iff₀ hpos]
    linarith
  · rw [abs_of_pos (div_pos (by linarith) hpos), le_div_iff₀ hpos]
    linarith

lemma abs_div_hJ_ge_one_of_notMem_Ioc (la : ℝ) (j : ℕ) {θ : ℝ}
    (h : θ ∉ Set.Ioc (la - SepWin.hJ j) (la + SepWin.hJ j)) :
    (1:ℝ) ≤ |(θ - la) / SepWin.hJ j| := by
  rw [Set.mem_Ioc, not_and_or, not_lt, not_le] at h
  have hpos := SepWin.hJ_pos j
  have key : -((θ - la) / SepWin.hJ j) = (la - θ) / SepWin.hJ j := by ring
  rcases h with h | h
  · rw [abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hpos.le), key,
      le_div_iff₀ hpos]
    linarith
  · rw [abs_of_pos (div_pos (by linarith) hpos), le_div_iff₀ hpos]
    linarith

lemma MjKer_support (la : ℝ) (j : ℕ) {θ : ℝ}
    (h : θ ∉ Set.Icc (la - SepWin.hJ j) (la + SepWin.hJ j)) : MjKer la j θ = 0 := by
  rw [MjKer, Complex.ofReal_eq_zero]
  exact SepWin.bump_zero _ (abs_div_hJ_ge_one la j h)

lemma MjKer_le_one (la : ℝ) (j : ℕ) (θ : ℝ) : ‖MjKer la j θ‖ₑ ≤ 1 := by
  rw [← ofReal_norm, ← ENNReal.ofReal_one, ENNReal.ofReal_le_ofReal_iff zero_le_one]
  exact MjKer_bound la j θ

/-- A bounded measurable function supported in a compact interval is in every `L^p`. -/
lemma memLp_of_bound_support {f : ℝ → ℂ} (hmeas : AEStronglyMeasurable f (volume : Measure ℝ))
    {a b : ℝ} (hbound : ∀ θ : ℝ, ‖f θ‖ ≤ 1)
    (hsupp : ∀ θ : ℝ, θ ∉ Set.Icc a b → f θ = 0)
    {p : ℝ≥0∞} (hp0 : p ≠ 0) (hptop : p ≠ ⊤) :
    MemLp f p (volume : Measure ℝ) := by
  rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp0 hptop hmeas]
  have hstep : ∫⁻ θ, ‖f θ‖ₑ ^ p.toReal
      ≤ ∫⁻ θ, (Set.Icc a b).indicator (fun _ => (1 : ℝ≥0∞)) θ := by
    refine lintegral_mono fun θ => ?_
    by_cases hθ : θ ∈ Set.Icc a b
    · rw [Set.indicator_of_mem hθ]
      calc ‖f θ‖ₑ ^ p.toReal ≤ (1 : ℝ≥0∞) ^ p.toReal := by
            refine ENNReal.rpow_le_rpow ?_ (by positivity)
            rw [← ofReal_norm, ← ENNReal.ofReal_one, ENNReal.ofReal_le_ofReal_iff zero_le_one]
            exact hbound θ
        _ = 1 := ENNReal.one_rpow _
    · rw [Set.indicator_of_notMem hθ, hsupp θ hθ, enorm_zero,
        ENNReal.zero_rpow_of_pos (ENNReal.toReal_pos hp0 hptop)]
  refine lt_of_le_of_lt hstep ?_
  rw [lintegral_indicator_const measurableSet_Icc, one_mul]
  exact isCompact_Icc.measure_lt_top (μ := (volume : Measure ℝ))

/-- **The band kernel is the oscillatory integral of `MjKer`.** -/
theorem bandKer_eq_integral (la : ℝ) (j : ℕ) (z : ℝ) :
    bandKer winSmooth la j z
      = ∫ θ : ℝ, MjKer la j θ * Complex.exp (-(Complex.I * (z : ℂ) * (θ : ℂ))) := by
  have hpos : 0 < SepWin.hJ j := SepWin.hJ_pos j
  have hle : la - SepWin.hJ j ≤ la + SepWin.hJ j := by linarith
  have hR := intervalIntegral_smooth_eq_winK SepWin.bump (winSmooth : ℝ → ℂ) (SepWin.hJ j)
    hpos la z (fun t => winSmooth_apply t)
  have hunfold : bandKer winSmooth la j z
      = Complex.exp (-(Complex.I * (la : ℂ) * (z : ℂ)))
        * (((SepWin.hJ j : ℝ) : ℂ) * (winSmooth : ℝ → ℂ) (SepWin.hJ j * z)) := rfl
  have hker : bandKer winSmooth la j z
      = ∫ θ in (la - SepWin.hJ j)..(la + SepWin.hJ j),
          ((SepWin.bump ((θ - la) / SepWin.hJ j) : ℝ) : ℂ)
            * Complex.exp (-(Complex.I * (z : ℂ) * (θ : ℂ))) := by
    rw [hunfold, ← hR]
  rw [hker, intervalIntegral.integral_of_le hle,
    ← MeasureTheory.integral_indicator measurableSet_Ioc]
  refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
  rw [Set.indicator_apply]
  simp only [MjKer]
  by_cases hθ : θ ∈ Set.Ioc (la - SepWin.hJ j) (la + SepWin.hJ j)
  · rw [if_pos hθ]
  · rw [if_neg hθ,
      show ((SepWin.bump ((θ - la) / SepWin.hJ j) : ℝ) : ℂ) = 0 from by
        rw [Complex.ofReal_eq_zero]
        exact SepWin.bump_zero _ (abs_div_hJ_ge_one_of_notMem_Ioc la j hθ)]
    simp

lemma MjKer_fourier_point (la : ℝ) (j : ℕ) (ξ : ℝ) :
    MjKer la j (-(2 * Real.pi) * ξ)
      = ((SepWin.bump (-((2 * Real.pi) * ξ + la) / SepWin.hJ j) : ℝ) : ℂ) := by
  rw [MjKer]
  congr 2
  field_simp
  ring

/-! ## Part 4: `L^p` bookkeeping for `MjKer` and Young's inequality -/

lemma MjKer_memLp_one (la : ℝ) (j : ℕ) : MemLp (MjKer la j) 1 (volume : Measure ℝ) :=
  memLp_of_bound_support (MjKer_measurable la j).aestronglyMeasurable (MjKer_bound la j)
    (fun θ => MjKer_support la j) one_ne_zero ENNReal.one_ne_top

lemma MjKer_memLp_two (la : ℝ) (j : ℕ) : MemLp (MjKer la j) 2 (volume : Measure ℝ) :=
  memLp_of_bound_support (MjKer_measurable la j).aestronglyMeasurable (MjKer_bound la j)
    (fun θ => MjKer_support la j) (by norm_num) (by norm_num)

lemma MjKer_memLp_top (la : ℝ) (j : ℕ) : MemLp (MjKer la j) ⊤ (volume : Measure ℝ) :=
  memLp_top_of_bound (MjKer_measurable la j).aestronglyMeasurable 1
    (Eventually.of_forall fun θ => MjKer_bound la j θ)

lemma enorm_rpow_two_eq_ofReal_sq (z : ℂ) :
    ‖z‖ₑ ^ (2:ℝ) = ENNReal.ofReal (‖z‖ ^ 2) := by
  rw [← ofReal_norm, show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast,
    ← ENNReal.ofReal_pow (norm_nonneg z)]

/-- **Young's inequality, `L² ∗ L¹ → L²`**, in the quantitative form used here: if `𝓕κ` is bounded
by `1`, then `f ★ κ ∈ L²` for `f ∈ L²`. -/
lemma memLp_convolution_two_of_fourier_le_one {f κ : ℝ → ℂ}
    (hf2 : MemLp f 2 (volume : Measure ℝ)) (hκ1 : MemLp κ 1 (volume : Measure ℝ))
    (hκm : Measurable κ) (hC : ∀ ξ : ℝ, ‖FourierTransform.fourier κ ξ‖ ≤ 1) :
    MemLp (fun x : ℝ => ∫ y : ℝ, f y * κ (x - y)) 2 (volume : Measure ℝ) := by
  rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)
      (aestronglyMeasurable_conv hf2 hκm),
    show (2:ℝ≥0∞).toReal = (2:ℝ) by norm_num]
  have hconv := lintegral_convolution_sq_eq_l2 (g := f) (k := κ) hf2 hκ1
  have hL : ∫⁻ x : ℝ, ‖∫ y : ℝ, f y * κ (x - y)‖ₑ ^ (2:ℝ)
      = ∫⁻ ξ : ℝ, ENNReal.ofReal
          (‖(FourierTransform.fourier (hf2.toLp f) : Lp ℂ 2 (volume : Measure ℝ)) ξ‖
            * ‖FourierTransform.fourier κ ξ‖) ^ (2:ℝ) := by
    rw [show (fun x : ℝ => ‖∫ y : ℝ, f y * κ (x - y)‖ₑ ^ (2:ℝ))
        = (fun x : ℝ => ENNReal.ofReal ‖∫ y : ℝ, f y * κ (x - y)‖ ^ (2:ℝ)) from
        funext fun x => by rw [← ofReal_norm]]
    exact hconv
  rw [hL]
  have hbnd : ∀ ξ : ℝ, ENNReal.ofReal
        (‖(FourierTransform.fourier (hf2.toLp f) : Lp ℂ 2 (volume : Measure ℝ)) ξ‖
          * ‖FourierTransform.fourier κ ξ‖) ^ (2:ℝ)
      ≤ (ENNReal.ofReal
          ‖(FourierTransform.fourier (hf2.toLp f) : Lp ℂ 2 (volume : Measure ℝ)) ξ‖) ^ (2:ℝ) := by
    intro ξ
    have h1 : ENNReal.ofReal
          (‖(FourierTransform.fourier (hf2.toLp f) : Lp ℂ 2 (volume : Measure ℝ)) ξ‖
            * ‖FourierTransform.fourier κ ξ‖)
        ≤ ENNReal.ofReal
            ‖(FourierTransform.fourier (hf2.toLp f) : Lp ℂ 2 (volume : Measure ℝ)) ξ‖ := by
      rw [ENNReal.ofReal_le_ofReal_iff (norm_nonneg _)]
      calc ‖(FourierTransform.fourier (hf2.toLp f) : Lp ℂ 2 (volume : Measure ℝ)) ξ‖
              * ‖FourierTransform.fourier κ ξ‖
          ≤ ‖(FourierTransform.fourier (hf2.toLp f) : Lp ℂ 2 (volume : Measure ℝ)) ξ‖ * 1 :=
            mul_le_mul_of_nonneg_left (hC ξ) (norm_nonneg _)
        _ = ‖(FourierTransform.fourier (hf2.toLp f) : Lp ℂ 2 (volume : Measure ℝ)) ξ‖ := mul_one _
    exact ENNReal.rpow_le_rpow h1 (by norm_num)
  refine lt_of_le_of_lt (lintegral_mono hbnd) ?_
  rw [lintegral_rpow_two_ofReal_fourier_toLp_eq f hf2,
    show (∫⁻ x : ℝ, ENNReal.ofReal (‖f x‖ ^ 2)) = ∫⁻ x : ℝ, ‖f x‖ₑ ^ (2:ℝ) from
      lintegral_congr fun x => (enorm_rpow_two_eq_ofReal_sq (f x)).symm]
  exact (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)
    hf2.aestronglyMeasurable).mp hf2.eLpNorm_lt_top

/-! ## Part 5: the per-frequency identity -/

/-- The Fourier bound for `κ` from `𝓕κ = ψ` with `0 ≤ ψ ≤ 1`. -/
lemma norm_fourier_le_one_of_eq {κ : ℝ → ℂ} {ψ : ℝ → ℝ}
    (hκF : ∀ ξ : ℝ, FourierTransform.fourier κ ξ = (ψ ξ : ℂ))
    (hψnn : ∀ ξ : ℝ, 0 ≤ ψ ξ) (hψle : ∀ ξ : ℝ, ψ ξ ≤ 1) (ξ : ℝ) :
    ‖FourierTransform.fourier κ ξ‖ ≤ 1 := by
  rw [hκF ξ, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hψnn ξ)]
  exact hψle ξ

/-- The band where `ψ` is allowed to be below `1` sits strictly inside the support of the
`MjKer` oscillation, so the two can be exchanged. -/
lemma MjKer_mul_psi (la : ℝ) (j : ℕ) {ψ : ℝ → ℝ}
    (hψ1 : ∀ ξ : ℝ, |ξ + la / (2 * Real.pi)| ≤ 1 / (4 * Real.pi) → ψ ξ = 1) (ξ : ℝ) :
    MjKer la j (-(2 * Real.pi) * ξ) * (ψ ξ : ℂ)
      = MjKer la j (-(2 * Real.pi) * ξ) := by
  by_cases h0 : MjKer la j (-(2 * Real.pi) * ξ) = 0
  · rw [h0, zero_mul]
  · have hψξ : ψ ξ = 1 := hψ1 ξ (by
      have hpos := SepWin.hJ_pos j
      have hne : ((SepWin.bump ((-(2 * Real.pi) * ξ - la) / SepWin.hJ j) : ℝ) : ℂ) ≠ 0 := by
        intro hc
        exact h0 (by rw [MjKer]; exact hc)
      have hbne : SepWin.bump ((-(2 * Real.pi) * ξ - la) / SepWin.hJ j) ≠ 0 := by
        intro hc
        exact hne (by rw [hc, Complex.ofReal_zero])
      have habs : |(-(2 * Real.pi) * ξ - la) / SepWin.hJ j| < 1 := by
        by_contra hc
        rw [not_lt] at hc
        exact hbne (SepWin.bump_zero _ hc)
      have h2 : |-(2 * Real.pi) * ξ - la| < SepWin.hJ j := by
        rw [← div_lt_one hpos]
        rwa [abs_div, abs_of_pos hpos] at habs
      have h3 : |2 * Real.pi * ξ + la| < SepWin.hJ j := by
        rw [show -(2 * Real.pi) * ξ - la = -(2 * Real.pi * ξ + la) by ring, abs_neg] at h2
        exact h2
      have h4 : |2 * Real.pi * ξ + la| = |ξ + la / (2 * Real.pi)| * (2 * Real.pi) := by
        rw [show 2 * Real.pi * ξ + la = 2 * Real.pi * (ξ + la / (2 * Real.pi)) by
          field_simp, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
        ring
      rw [h4] at h3
      rw [le_div_iff₀ (by positivity : (0:ℝ) < 4 * Real.pi)]
      have hle := SepWin.hJ_le_half j
      nlinarith [h3, hle, abs_nonneg (ξ + la / (2 * Real.pi))])
    rw [hψξ, Complex.ofReal_one, mul_one]

/-- **The per-frequency band identity.**  For `f ∈ L¹ ∩ L²` and a slice kernel `κ` with
`𝓕κ = ψ` (`0 ≤ ψ ≤ 1`, `ψ ≡ 1` on the band `|ξ + la/(2π)| ≤ 1/(4π)`), the `la`-th term of the
band operator equals the `la`-th term of the target operator. -/
theorem bandOp_term_eq (la : ℝ) (j : ℕ) (ψ : ℝ → ℝ) (κ : ℝ → ℂ)
    (hκ1 : MemLp κ 1 (volume : Measure ℝ)) (hκm : Measurable κ)
    (hκF : ∀ ξ : ℝ, FourierTransform.fourier κ ξ = (ψ ξ : ℂ))
    (hψnn : ∀ ξ : ℝ, 0 ≤ ψ ξ) (hψle : ∀ ξ : ℝ, ψ ξ ≤ 1)
    (hψ1 : ∀ ξ : ℝ, |ξ + la / (2 * Real.pi)| ≤ 1 / (4 * Real.pi) → ψ ξ = 1)
    {f : ℝ → ℂ} (hf1 : MemLp f 1 (volume : Measure ℝ)) (hf2 : MemLp f 2 (volume : Measure ℝ))
    (x : ℝ) :
    Complex.exp (-(Complex.I * (la : ℂ) * (x : ℂ)))
        * (∫ t : ℝ, ((∫ y : ℝ, f y * κ (t - y))
              * Complex.exp (Complex.I * (la : ℂ) * (t : ℂ))) * winK winSmooth j (x - t))
      = ∫ y : ℝ, f y * bandKer winSmooth la j (x - y) := by
  set g : ℝ → ℂ := fun t => ∫ y : ℝ, f y * κ (t - y) with hg
  have hκI : Integrable κ := memLp_one_iff_integrable.mp hκ1
  have hfI : Integrable f := memLp_one_iff_integrable.mp hf1
  have hgI : Integrable g := by
    rw [hg]
    have h := hfI.integrable_convolution (L := ContinuousLinearMap.mul ℂ ℂ) hκI
    have hfun : (MeasureTheory.convolution f κ (ContinuousLinearMap.mul ℂ ℂ)
        (volume : Measure ℝ)) = fun t => ∫ y, f y * κ (t - y) := by
      funext t
      rw [convolution_def]
      rfl
    rwa [hfun] at h
  have hg1 : MemLp g 1 (volume : Measure ℝ) := memLp_one_iff_integrable.mpr hgI
  have hg2 : MemLp g 2 (volume : Measure ℝ) := by
    rw [hg]
    exact memLp_convolution_two_of_fourier_le_one hf2 hκ1 hκm
      (norm_fourier_le_one_of_eq hκF hψnn hψle)
  -- step 1: absorb the phase into the kernel
  have hstep1 : (fun t : ℝ => Complex.exp (-(Complex.I * (la : ℂ) * (x : ℂ)))
        * ((g t * Complex.exp (Complex.I * (la : ℂ) * (t : ℂ))) * winK winSmooth j (x - t)))
      = fun t : ℝ => g t * bandKer winSmooth la j (x - t) := by
    funext t
    rw [bandKer_apply]
    have hexp : Complex.exp (-(Complex.I * (la : ℂ) * (x : ℂ)))
          * Complex.exp (Complex.I * (la : ℂ) * (t : ℂ))
        = Complex.exp (-(Complex.I * (la : ℂ) * ((x - t : ℝ) : ℂ))) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    calc Complex.exp (-(Complex.I * (la : ℂ) * (x : ℂ)))
          * ((g t * Complex.exp (Complex.I * (la : ℂ) * (t : ℂ))) * winK winSmooth j (x - t))
        = g t * (Complex.exp (-(Complex.I * (la : ℂ) * (x : ℂ)))
            * Complex.exp (Complex.I * (la : ℂ) * (t : ℂ))) * winK winSmooth j (x - t) := by ring
      _ = g t * Complex.exp (-(Complex.I * (la : ℂ) * ((x - t : ℝ) : ℂ)))
            * winK winSmooth j (x - t) := by rw [hexp]
      _ = g t * (Complex.exp (-(Complex.I * (la : ℂ) * ((x - t : ℝ) : ℂ)))
            * winK winSmooth j (x - t)) := by ring
  rw [← integral_const_mul, hstep1]
  -- step 2: rewrite the band kernel as the oscillatory integral of `MjKer`
  have hstep2 : (fun t : ℝ => g t * bandKer winSmooth la j (x - t))
      = fun t : ℝ => g t * (∫ θ : ℝ, MjKer la j θ
          * Complex.exp (-(Complex.I * ((x - t : ℝ) : ℂ) * (θ : ℂ)))) := by
    funext t
    rw [bandKer_eq_integral]
  rw [hstep2]
  -- step 3: Fubini (the commons `convolution_kernel_fubini`)
  rw [convolution_kernel_fubini (MjKer la j) g (MjKer_measurable la j) (MjKer_memLp_one la j)
    (MjKer_memLp_two la j) (MjKer_memLp_top la j) hg1 hg2 x]
  -- step 4: `𝓕 g = ψ · 𝓕 f`, and `ψ` can be dropped on the band
  have hFg : ∀ ξ : ℝ, FourierTransform.fourier g ξ
      = (ψ ξ : ℂ) * FourierTransform.fourier f ξ := by
    intro ξ
    rw [hg, fourier_convolution f κ hfI hκI ξ, hκF ξ]
    ring
  rw [show (fun ξ : ℝ => MjKer la j (-(2 * Real.pi) * ξ) * FourierTransform.fourier g ξ)
      = (fun ξ : ℝ => MjKer la j (-(2 * Real.pi) * ξ) * FourierTransform.fourier f ξ) from by
    funext ξ
    rw [hFg ξ, ← mul_assoc, MjKer_mul_psi la j hψ1 ξ]]
  -- step 5: back to the target integral
  rw [← convolution_kernel_fubini (MjKer la j) f (MjKer_measurable la j) (MjKer_memLp_one la j)
    (MjKer_memLp_two la j) (MjKer_memLp_top la j) hf1 hf2 x]
  have hstep5 : (fun t : ℝ => f t * (∫ θ : ℝ, MjKer la j θ
        * Complex.exp (-(Complex.I * ((x - t : ℝ) : ℂ) * (θ : ℂ)))))
      = fun t : ℝ => f t * bandKer winSmooth la j (x - t) := by
    funext t
    rw [bandKer_eq_integral]
  rw [hstep5]

/-! ## Part 6: the fixed-window estimate for `f ∈ L¹ ∩ L²` -/

lemma winSmooth_bound (t : ℝ) : ‖(winSmooth : ℝ → ℂ) t‖ ≤ 2 := by
  rw [winSmooth_apply]
  have hle : ∀ u : ℝ, ‖(SepWin.bump u : ℂ)
      * Complex.exp (-(Complex.I * (t : ℂ) * (u : ℂ)))‖ ≤ 1 := by
    intro u
    rw [norm_mul, Complex.norm_exp]
    have hre : (-(Complex.I * (t : ℂ) * (u : ℂ))).re = 0 := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [hre, Real.exp_zero, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (SepWin.bump_bounds u).1]
    exact (SepWin.bump_bounds u).2
  refine le_trans (intervalIntegral.norm_integral_le_integral_norm (by norm_num : (-1:ℝ) ≤ 1)) ?_
  calc (∫ u in (-1:ℝ)..1, ‖(SepWin.bump u : ℂ)
        * Complex.exp (-(Complex.I * (t : ℂ) * (u : ℂ)))‖)
      ≤ ∫ u in (-1:ℝ)..1, (1 : ℝ) := by
        refine intervalIntegral.integral_mono_on (by norm_num)
          (Continuous.intervalIntegrable ?_ _ _) (Continuous.intervalIntegrable ?_ _ _) ?_
        · exact ((Complex.continuous_ofReal.comp SepWin.bump_continuous).mul
            (Complex.continuous_exp.comp (by fun_prop))).norm
        · exact continuous_const
        · intro u _
          exact hle u
    _ = 2 := by norm_num

lemma continuous_winK (j : ℕ) : Continuous (winK winSmooth j) := by
  have h : winK winSmooth j = fun u : ℝ =>
      (((2:ℝ)^(-(j:ℝ)-1) : ℝ) : ℂ) * (winSmooth : ℝ → ℂ) ((2:ℝ)^(-(j:ℝ)-1) * u) := by
    funext u
    rw [winK]
  rw [h]
  exact continuous_const.mul ((SchwartzMap.continuous winSmooth).comp (by fun_prop))

lemma continuous_bandKer (la : ℝ) (j : ℕ) : Continuous (bandKer winSmooth la j) := by
  have h : bandKer winSmooth la j = fun z : ℝ =>
      Complex.exp (-(Complex.I * (la : ℂ) * (z : ℂ))) * winK winSmooth j z := by
    funext z
    rw [bandKer_apply]
  rw [h]
  exact (Complex.continuous_exp.comp (by fun_prop)).mul (continuous_winK j)

lemma bandKer_bound (la : ℝ) (j : ℕ) (z : ℝ) : ‖bandKer winSmooth la j z‖ ≤ 2 := by
  rw [bandKer_apply, winK, norm_mul]
  have he : ‖Complex.exp (-(Complex.I * (la : ℂ) * (z : ℂ)))‖ = 1 := by
    rw [Complex.norm_exp]
    have hre : (-(Complex.I * (la : ℂ) * (z : ℂ))).re = 0 := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [hre, Real.exp_zero]
  rw [he, one_mul]
  calc ‖(((2:ℝ)^(-(j:ℝ)-1) : ℝ) : ℂ) * (winSmooth : ℝ → ℂ) ((2:ℝ)^(-(j:ℝ)-1) * z)‖
      = ‖(((2:ℝ)^(-(j:ℝ)-1) : ℝ) : ℂ)‖
        * ‖(winSmooth : ℝ → ℂ) ((2:ℝ)^(-(j:ℝ)-1) * z)‖ := norm_mul _ _
    _ ≤ 1 * 2 := by
        refine mul_le_mul ?_ (winSmooth_bound _) (norm_nonneg _) (by norm_num)
        rw [Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Real.rpow_nonneg (by norm_num) _)]
        exact le_trans (SepWin.hJ_le_half j) (by norm_num)
    _ = 2 := by norm_num

lemma integrable_mul_of_bound {f g : ℝ → ℂ} (hf : Integrable f (volume : Measure ℝ))
    {M : ℝ} (hM : 0 ≤ M) (hg : AEStronglyMeasurable g (volume : Measure ℝ))
    (hb : ∀ x : ℝ, ‖g x‖ ≤ M) : Integrable (fun x : ℝ => f x * g x) (volume : Measure ℝ) := by
  have hdom : Integrable (fun x : ℝ => M * ‖f x‖) (volume : Measure ℝ) := hf.norm.const_mul M
  refine hdom.mono' (hf.aestronglyMeasurable.mul hg) ?_
  filter_upwards with x
  rw [norm_mul]
  calc ‖f x‖ * ‖g x‖ ≤ ‖f x‖ * M := mul_le_mul_of_nonneg_left (hb x) (norm_nonneg _)
    _ = M * ‖f x‖ := by ring

/-- **The band operator computes the target operator.**  For `f ∈ L¹ ∩ L²` and slice kernels
`κ_k` with `𝓕κ_k = ψ_k` (`0 ≤ ψ_k ≤ 1`, `ψ_k ≡ 1` on the band), the target's smooth-window
operator equals the framework's band operator applied to the band-limited tuple
`H_k = (f ★ κ_k) · e^{Iλ_k·}`. -/
theorem smoothOp_eq_bandOpD {K : ℕ} (lam : Fin K → ℝ) {ψ : Fin K → ℝ → ℝ}
    {κ : Fin K → ℝ → ℂ}
    (hκ1 : ∀ k : Fin K, MemLp (κ k) 1 (volume : Measure ℝ))
    (hκm : ∀ k : Fin K, Measurable (κ k))
    (hκF : ∀ k : Fin K, ∀ ξ : ℝ, FourierTransform.fourier (κ k) ξ = (ψ k ξ : ℂ))
    (hψnn : ∀ k : Fin K, ∀ ξ : ℝ, 0 ≤ ψ k ξ)
    (hψle : ∀ k : Fin K, ∀ ξ : ℝ, ψ k ξ ≤ 1)
    (hψ1 : ∀ k : Fin K, ∀ ξ : ℝ, |ξ + lam k / (2 * Real.pi)| ≤ 1 / (4 * Real.pi) → ψ k ξ = 1)
    {f : ℝ → ℂ} (hf1 : MemLp f 1 (volume : Measure ℝ)) (hf2 : MemLp f 2 (volume : Measure ℝ))
    (j : ℕ) (x : ℝ) :
    SepWin.smoothOp SepWin.bump K lam f j x
      = bandOpD winSmooth lam (fun k t => (∫ y : ℝ, f y * κ k (t - y))
          * Complex.exp (Complex.I * (lam k : ℂ) * (t : ℂ))) j x := by
  have hfI : Integrable f (volume : Measure ℝ) := memLp_one_iff_integrable.mp hf1
  have hmeas_ker : ∀ k : Fin K, AEStronglyMeasurable
      (fun y : ℝ => bandKer winSmooth (lam k) j (x - y)) (volume : Measure ℝ) := fun k =>
    ((continuous_bandKer (lam k) j).comp
      (continuous_const.sub continuous_id)).aestronglyMeasurable
  have hL : (∫ y : ℝ, f y * SepWin.innerSmooth SepWin.bump K lam j (x - y))
      = ∑ k : Fin K, ∫ y : ℝ, f y * bandKer winSmooth (lam k) j (x - y) := by
    rw [show (fun y : ℝ => f y * SepWin.innerSmooth SepWin.bump K lam j (x - y))
        = fun y : ℝ => ∑ k : Fin K, f y * bandKer winSmooth (lam k) j (x - y) from by
      funext y
      rw [← Finset.mul_sum, innerSmooth_eq_sum_bandKer]]
    rw [integral_finsetSum]
    exact fun k _ => integrable_mul_of_bound hfI (by norm_num) (hmeas_ker k)
      (fun y => bandKer_bound (lam k) j (x - y))
  rw [SepWin.smoothOp, bandOpD, hL]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact (bandOp_term_eq (lam k) j (ψ k) (κ k) (hκ1 k) (hκm k) (hκF k) (hψnn k) (hψle k)
    (hψ1 k) hf1 hf2 x).symm

/-! ## Part 7: the fixed-window estimate for `f ∈ L¹ ∩ L²` -/

/-- A bounded multiplier of an `L¹` function is `L^∞` after convolution with an `L¹` function. -/
lemma memLp_convolution_top_of_bound {f κ : ℝ → ℂ} (hf1 : MemLp f 1 (volume : Measure ℝ))
    (hf2 : MemLp f 2 (volume : Measure ℝ)) (hκm : Measurable κ) {C : ℝ}
    (hC : ∀ x : ℝ, ‖κ x‖ ≤ C) :
    MemLp (fun t : ℝ => ∫ y : ℝ, f y * κ (t - y)) ⊤ (volume : Measure ℝ) := by
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 0)
  have hfI : Integrable f := memLp_one_iff_integrable.mp hf1
  refine memLp_top_of_bound (aestronglyMeasurable_conv hf2 hκm) (C * ∫ y, ‖f y‖) ?_
  filter_upwards with t
  have hInt : Integrable (fun y : ℝ => ‖f y‖ * ‖κ (t - y)‖) (volume : Measure ℝ) := by
    refine (hfI.norm.mul_const C).mono' ((hf1.aestronglyMeasurable.norm).mul
      (((hκm.comp (by fun_prop : Measurable fun y : ℝ => t - y)).aestronglyMeasurable).norm)) ?_
    filter_upwards with y
    rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
    exact mul_le_mul_of_nonneg_left (hC (t - y)) (norm_nonneg _)
  have hIntC : Integrable (fun y : ℝ => ‖f y‖ * C) (volume : Measure ℝ) := hfI.norm.mul_const C
  calc ‖∫ y : ℝ, f y * κ (t - y)‖ ≤ ∫ y : ℝ, ‖f y * κ (t - y)‖ :=
        norm_integral_le_integral_norm _
    _ = ∫ y : ℝ, ‖f y‖ * ‖κ (t - y)‖ := by
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        simp only [norm_mul]
    _ ≤ ∫ y : ℝ, ‖f y‖ * C :=
        integral_mono hInt hIntC fun y => mul_le_mul_of_nonneg_left (hC (t - y)) (norm_nonneg _)
    _ = (∫ y : ℝ, ‖f y‖) * C := integral_mul_const C _
    _ = C * ∫ y : ℝ, ‖f y‖ := by ring

theorem FW_uniform {K : ℕ} (lam : Fin K → ℝ)
    (hsep : ∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|) :
    ∃ C : ℝ, 0 < C ∧ ∀ {f : ℝ → ℂ}, MemLp f 1 (volume : Measure ℝ) →
      MemLp f 2 (volume : Measure ℝ) →
      (∫⁻ x, (⨆ j : ℕ, ‖SepWin.smoothOp SepWin.bump K lam f j x‖ₑ) ^ (2:ℝ))
        ≤ ENNReal.ofReal ((C * (Real.log ((K:ℝ) + 2)) ^ 2) ^ 2)
            * (∫⁻ x, ‖f x‖ₑ ^ (2:ℝ)) := by
  have hw : 0 < (1:ℝ) / (4 * Real.pi) := by positivity
  have hw4 : 4 * Real.pi * (1 / (4 * Real.pi)) ≤ 1 := by
    rw [mul_one_div, div_self (by positivity : (4 * Real.pi) ≠ 0)]
  have hη : 0 < (3:ℝ) / 100 := by norm_num
  have hηw : (3:ℝ) / 100 < 1 / (4 * Real.pi) := by
    rw [lt_div_iff₀ (by positivity : (0:ℝ) < 4 * Real.pi)]
    nlinarith [Real.pi_lt_four]
  obtain ⟨ψ, κ, hψc, hψnn, hψle, hψone, hψzero, hκc, hκI, hκ2, hκtop, hκbd, hκF, hκsum⟩ :=
    exists_cellKernels lam hsep (1 / (4 * Real.pi)) (3 / 100) hw hw4 hη hηw
  have hκm : ∀ k : Fin K, Measurable (κ k) := fun k => (hκc k).measurable
  have hψm : ∀ k : Fin K, Measurable (ψ k) := fun k => (hψc k).continuous.measurable
  -- the crux
  have hth : 2 * (2 * Real.pi * (1 / (4 * Real.pi) + 3 / 100) * (9 / 10)) ^ 2 < 1 := by
    have h1 : 2 * Real.pi * (1 / (4 * Real.pi) + 3 / 100) * (9 / 10)
        = 9 / 20 + 27 * Real.pi / 500 := by
      field_simp
      ring
    rw [h1]
    nlinarith [Real.pi_lt_four]
  obtain ⟨C, hCpos, hCbnd⟩ := bandMax_le_of_bandlimited winSmooth lam hsep winSmooth_bound
    (by positivity) hth (AdmB (1 / (4 * Real.pi) + 3 / 100))
    (fun H' h k => h.2.1 k) (fun H' h k => h.2.2.1 k)
    (fun H' h k => memLp_one_iff_integrable.mp (h.1 k)) (fun H' h k ξ hξ => h.2.2.2 k ξ hξ)
    (fun H' y h _ => admB_shiftH h y)
  refine ⟨Real.sqrt 2 * C, by positivity, fun {f} hf1 hf2 => ?_⟩
  have hfI : Integrable f := memLp_one_iff_integrable.mp hf1
  set H : Fin K → ℝ → ℂ := fun k t => (∫ y : ℝ, f y * κ k (t - y))
      * Complex.exp (Complex.I * (lam k : ℂ) * (t : ℂ)) with hHdef
  -- membership in `L^p` of the slices
  have hconvL1 : ∀ k : Fin K, MemLp (fun t : ℝ => ∫ y, f y * κ k (t - y)) 1
      (volume : Measure ℝ) := by
    intro k
    refine memLp_one_iff_integrable.mpr ?_
    have h := hfI.integrable_convolution (L := ContinuousLinearMap.mul ℂ ℂ) (hκI k)
    have hfun : (MeasureTheory.convolution f (κ k) (ContinuousLinearMap.mul ℂ ℂ)
        (volume : Measure ℝ)) = fun t => ∫ y, f y * κ k (t - y) := by
      funext t
      rw [convolution_def]
      rfl
    rwa [hfun] at h
  have hconvL2 : ∀ k : Fin K, MemLp (fun t : ℝ => ∫ y, f y * κ k (t - y)) 2
      (volume : Measure ℝ) := fun k =>
    memLp_convolution_two_of_fourier_le_one hf2 (memLp_one_iff_integrable.mpr (hκI k)) (hκm k)
      (norm_fourier_le_one_of_eq (hκF k) (hψnn k) (hψle k))
  have hconvLtop : ∀ k : Fin K, MemLp (fun t : ℝ => ∫ y, f y * κ k (t - y)) ⊤
      (volume : Measure ℝ) := fun k =>
    memLp_convolution_top_of_bound hf1 hf2 (hκm k) (hκbd k).choose_spec
  have hunimod : ∀ k : Fin K, AEStronglyMeasurable
      (fun t : ℝ => Complex.exp (Complex.I * (lam k : ℂ) * (t : ℂ))) (volume : Measure ℝ) :=
    fun k => (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable
  have hunimod1 : ∀ k : Fin K, ∀ t : ℝ,
      ‖Complex.exp (Complex.I * (lam k : ℂ) * (t : ℂ))‖ = 1 := by
    intro k t
    rw [Complex.norm_exp]
    have hre : (Complex.I * (lam k : ℂ) * (t : ℂ)).re = 0 := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [hre, Real.exp_zero]
  -- admissibility of `H`
  have hAdm : AdmB (1 / (4 * Real.pi) + 3 / 100) H := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro k
      rw [hHdef]
      exact memLp_mul_unimodular (hconvL1 k) (hunimod k) (hunimod1 k)
    · intro k
      rw [hHdef]
      exact memLp_mul_unimodular (hconvL2 k) (hunimod k) (hunimod1 k)
    · intro k
      rw [hHdef]
      exact memLp_mul_unimodular (hconvLtop k) (hunimod k) (hunimod1 k)
    · intro k ξ hξ
      simp only [hHdef]
      rw [show (fun t : ℝ => (∫ y : ℝ, f y * κ k (t - y)) * Complex.exp (Complex.I * (lam k : ℂ) * (t : ℂ)))
          = fun t : ℝ => (∫ y : ℝ, f y * κ k (t - y))
              * Complex.exp ((↑(2 * Real.pi * (lam k / (2 * Real.pi)) * t) * Complex.I) : ℂ) from by
        funext t
        congr 2
        push_cast
        field_simp]
      rw [fourier_mul_exp_rule]
      rw [fourier_convolution f (κ k) hfI (hκI k) (ξ - lam k / (2 * Real.pi)),
        hκF k (ξ - lam k / (2 * Real.pi)),
        hψzero k (ξ - lam k / (2 * Real.pi)) (by
          have h : ξ - lam k / (2 * Real.pi) + lam k / (2 * Real.pi) = ξ := by ring
          rw [h]
          exact le_of_lt hξ)]
      simp
  -- the slice energy bound
  have hbandSq : bandSq H ≤ 2 * ∫⁻ x, ‖f x‖ₑ ^ (2:ℝ) := by
    have hbound : ∀ ξ : ℝ, ∑ k : Fin K, (ψ k ξ) ^ 2 ≤ 2 := by
      intro ξ
      refine le_trans (le_of_eq ?_) (hκsum ξ)
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hκF k ξ, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have hslice := slice_energy_le f κ ψ hf2 (fun k => memLp_one_iff_integrable.mpr (hκI k))
      hκm hκF hψm hψnn hbound
    have h1 : bandSq H
        = ∫⁻ x, ENNReal.ofReal (∑ k : Fin K, ‖∫ y : ℝ, f y * κ k (x - y)‖ ^ 2) := by
      rw [bandSq]
      refine lintegral_congr fun x => ?_
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [hHdef]
      rw [norm_mul, Complex.norm_exp]
      have hre : (Complex.I * (lam k : ℂ) * (x : ℂ)).re = 0 := by
        simp [Complex.mul_re, Complex.mul_im]
      rw [hre, Real.exp_zero, mul_one]
    rw [h1]
    refine le_trans hslice ?_
    rw [show (2 * ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2)) = 2 * ∫⁻ x, ‖f x‖ₑ ^ (2:ℝ) from by
      rw [show (∫⁻ x : ℝ, ENNReal.ofReal (‖f x‖ ^ 2)) = ∫⁻ x : ℝ, ‖f x‖ₑ ^ (2:ℝ) from
        lintegral_congr fun x => (enorm_rpow_two_eq_ofReal_sq (f x)).symm]]
  have hcrux := hCbnd H hAdm
  -- the two sides agree pointwise
  have hident : (∫⁻ x, (⨆ j : ℕ, ‖SepWin.smoothOp SepWin.bump K lam f j x‖ₑ) ^ (2:ℝ))
      = bandMax winSmooth lam H := by
    refine lintegral_congr fun x => ?_
    congr 1
    refine iSup_congr fun j => ?_
    rw [smoothOp_eq_bandOpD lam (fun k => memLp_one_iff_integrable.mpr (hκI k)) hκm hκF hψnn
      hψle (fun k ξ hξ => hψone k ξ hξ) hf1 hf2 j x]
  rw [hident]
  -- assemble
  have hsq : 2 * (C * Real.log ((K:ℝ) + 2) ^ 2) ^ 2
      = ((Real.sqrt 2 * C) * Real.log ((K:ℝ) + 2) ^ 2) ^ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  calc bandMax winSmooth lam H
      ≤ ENNReal.ofReal ((C * Real.log ((K:ℝ) + 2) ^ 2) ^ 2) * bandSq H := hcrux
    _ ≤ ENNReal.ofReal ((C * Real.log ((K:ℝ) + 2) ^ 2) ^ 2)
          * (2 * ∫⁻ x, ‖f x‖ₑ ^ (2:ℝ)) := by gcongr
    _ = ENNReal.ofReal (((Real.sqrt 2 * C) * Real.log ((K:ℝ) + 2) ^ 2) ^ 2)
          * ∫⁻ x, ‖f x‖ₑ ^ (2:ℝ) := by
        rw [show (2:ℝ≥0∞) = ENNReal.ofReal 2 from by norm_num, ← mul_assoc,
          mul_comm (ENNReal.ofReal ((C * Real.log ((K:ℝ) + 2) ^ 2) ^ 2)) (ENNReal.ofReal 2),
          ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2), hsq]

/-! ## Part 8: from `L¹ ∩ L²` to `L²` -/

/-- **Pointwise Cauchy–Schwarz for a convolution** (in the `eLpNorm` normal form). -/
lemma norm_convolution_le_eLpNorm {h K : ℝ → ℂ} (hh : MemLp h 2 (volume : Measure ℝ))
    (hK : MemLp K 2 (volume : Measure ℝ)) (x : ℝ) :
    ‖∫ y : ℝ, h y * K (x - y)‖ ≤ (eLpNorm h 2 (volume : Measure ℝ)).toReal
      * (eLpNorm K 2 (volume : Measure ℝ)).toReal := by
  have hcomp : eLpNorm (fun y : ℝ => K (x - y)) 2 (volume : Measure ℝ)
      = eLpNorm K 2 (volume : Measure ℝ) :=
    eLpNorm_comp_measurePreserving hK.aestronglyMeasurable (BoundaryLayer.mpSub x)
  have hstep : ‖∫ y : ℝ, h y * K (x - y)‖ₑ
      ≤ eLpNorm h 2 (volume : Measure ℝ) * eLpNorm K 2 (volume : Measure ℝ) := by
    have hhold := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume : Measure ℝ)
      (p := 2) (q := 2) Real.HolderConjugate.two_two
      (hh.aestronglyMeasurable.aemeasurable.enorm)
      ((hK.aestronglyMeasurable.comp_measurePreserving (BoundaryLayer.mpSub x)).aemeasurable.enorm)
    have hx : (∫⁻ y : ℝ, ‖(fun y : ℝ => K (x - y)) y‖ₑ ^ (2:ℝ))
        = ∫⁻ y : ℝ, ‖K y‖ₑ ^ (2:ℝ) := by
      have h2 := congrArg (fun t : ℝ≥0∞ => t ^ (2:ℝ)) hcomp
      rw [eLpNorm_two_eq (fun y : ℝ => K (x - y))
          (hK.aestronglyMeasurable.comp_measurePreserving (BoundaryLayer.mpSub x)),
        eLpNorm_two_eq K hK.aestronglyMeasurable, ← ENNReal.rpow_mul,
        ← ENNReal.rpow_mul, show ((1:ℝ)/2) * 2 = 1 by norm_num, ENNReal.rpow_one,
        ENNReal.rpow_one] at h2
      exact h2
    rw [show (∫⁻ y : ℝ, ‖(K ∘ fun y : ℝ => x - y) y‖ₑ ^ (2:ℝ))
        = ∫⁻ y : ℝ, ‖(fun y : ℝ => K (x - y)) y‖ₑ ^ (2:ℝ) from rfl] at hhold
    rw [show (∫⁻ y : ℝ, ‖(fun y : ℝ => K (x - y)) y‖ₑ ^ (2:ℝ))
        = ∫⁻ y : ℝ, ‖K y‖ₑ ^ (2:ℝ) from hx] at hhold
    rw [← eLpNorm_two_eq h hh.aestronglyMeasurable] at hhold
    rw [← eLpNorm_two_eq K hK.aestronglyMeasurable] at hhold
    refine le_trans (enorm_integral_le_lintegral_enorm _) ?_
    refine le_trans (le_of_eq (lintegral_congr fun y => enorm_mul _ _)) ?_
    simpa using hhold
  refine le_trans (ENNReal.toReal_mono ?_ hstep) (le_of_eq ENNReal.toReal_mul)
  exact ENNReal.mul_ne_top (ne_of_lt hh.eLpNorm_lt_top) (ne_of_lt hK.eLpNorm_lt_top)

/-- **`L²`-convergence from a.e. convergence and domination** (the dominated convergence theorem
at the level of the `eLpNorm`). -/
theorem tendsto_eLpNorm_two_sub_of_dominated {f : ℕ → ℝ → ℂ} {g : ℝ → ℂ}
    (hf : ∀ n : ℕ, MemLp (f n) 2 (volume : Measure ℝ)) (hg : MemLp g 2 (volume : Measure ℝ))
    (hdom : ∀ n : ℕ, ∀ x : ℝ, ‖f n x‖ ≤ ‖g x‖)
    (hconv : ∀ x : ℝ, Tendsto (fun n : ℕ => f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n : ℕ => eLpNorm (fun x : ℝ => f n x - g x) 2 (volume : Measure ℝ))
      atTop (𝓝 0) := by
  have hgi : Integrable (fun x : ℝ => ‖g x‖ ^ 2) (volume : Measure ℝ) :=
    (hg.norm).integrable_sq
  have hsub : ∀ n : ℕ, MemLp (fun x : ℝ => f n x - g x) 2 (volume : Measure ℝ) :=
    fun n => (hf n).sub hg
  have hInt_tendsto : Tendsto (fun n : ℕ => ∫ x : ℝ, ‖f n x - g x‖ ^ 2) atTop (𝓝 0) := by
    have hmain := tendsto_integral_of_dominated_convergence
      (μ := (volume : Measure ℝ))
      (F := fun n : ℕ => fun x : ℝ => ‖f n x - g x‖ ^ 2) (f := fun _ : ℝ => (0:ℝ))
      (fun x : ℝ => 4 * ‖g x‖ ^ 2)
      (fun n => (((hsub n).aestronglyMeasurable).aemeasurable.norm.pow_const 2).aestronglyMeasurable)
      (by simpa [mul_comm] using hgi.const_mul 4)
      (fun n => Eventually.of_forall fun x => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        have h : ‖f n x - g x‖ ≤ 2 * ‖g x‖ := by
          calc ‖f n x - g x‖ ≤ ‖f n x‖ + ‖g x‖ := norm_sub_le _ _
            _ ≤ ‖g x‖ + ‖g x‖ := add_le_add (hdom n x) le_rfl
            _ = 2 * ‖g x‖ := by ring
        nlinarith [h, norm_nonneg (f n x - g x), norm_nonneg (g x)])
      (by
        refine Eventually.of_forall fun x => ?_
        have h : Tendsto (fun n : ℕ => ‖f n x - g x‖) atTop (𝓝 0) := by
          simpa using ((hconv x).sub
            (tendsto_const_nhds : Tendsto (fun _ : ℕ => g x) atTop (𝓝 (g x)))).norm
        simpa using h.pow 2)
    simpa using hmain
  have hbridge : ∀ n : ℕ, eLpNorm (fun x : ℝ => f n x - g x) 2 (volume : Measure ℝ)
      = (ENNReal.ofReal (∫ x : ℝ, ‖f n x - g x‖ ^ 2)) ^ (1/2:ℝ) := by
    intro n
    rw [eLpNorm_two_eq _ (hsub n).aestronglyMeasurable]
    congr 1
    rw [show (∫⁻ x : ℝ, ‖f n x - g x‖ₑ ^ (2:ℝ))
        = ∫⁻ x : ℝ, ENNReal.ofReal (‖f n x - g x‖ ^ 2) from
      lintegral_congr fun x => enorm_rpow_two_eq_ofReal_sq _,
      ← ofReal_integral_eq_lintegral_ofReal ((hsub n).norm).integrable_sq
        (Filter.Eventually.of_forall fun x => sq_nonneg _)]
  have h2 : Tendsto (fun n : ℕ => ENNReal.ofReal (∫ x : ℝ, ‖f n x - g x‖ ^ 2)) atTop
      (𝓝 (ENNReal.ofReal 0)) := ENNReal.continuous_ofReal.tendsto 0 |>.comp hInt_tendsto
  have h3 := (ENNReal.continuous_rpow_const (y := (1/2:ℝ))).tendsto (ENNReal.ofReal 0) |>.comp h2
  rw [ENNReal.ofReal_zero, ENNReal.zero_rpow_of_pos (by norm_num : (0:ℝ) < 1/2)] at h3
  exact h3.congr' (Eventually.of_forall fun n => (hbridge n).symm)

/-- **Truncations of an `L²` function by smooth cutoffs.** -/
lemma exists_truncations {f : ℝ → ℂ} (hf : MemLp f 2 (volume : Measure ℝ)) :
    ∃ g : ℕ → ℝ → ℂ, (∀ N : ℕ, MemLp (g N) 1 (volume : Measure ℝ)) ∧
      (∀ N : ℕ, MemLp (g N) 2 (volume : Measure ℝ)) ∧
      (∀ N : ℕ, ∀ x : ℝ, ‖g N x‖ ≤ ‖f x‖) ∧
      (∀ x : ℝ, Tendsto (fun N : ℕ => g N x) atTop (𝓝 (f x))) := by
  refine ⟨fun N x => f x * ((SepWin.bump (x / ((N:ℝ) + 1)) : ℝ) : ℂ), ?_, ?_, ?_, ?_⟩
  · -- `L¹`
    intro N
    have hN : 0 < (N:ℝ) + 1 := by positivity
    have hsupp : ∀ x : ℝ, x ∉ Set.Icc (-((N:ℝ) + 1)) ((N:ℝ) + 1) →
        ((SepWin.bump (x / ((N:ℝ) + 1)) : ℝ) : ℂ) = 0 := by
      intro x hx
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
      rw [Complex.ofReal_eq_zero]
      apply SepWin.bump_zero
      rcases hx with h | h
      · rw [abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hN.le)]
        rw [show -(x / ((N:ℝ) + 1)) = -x / ((N:ℝ) + 1) by ring, le_div_iff₀ hN]
        linarith
      · rw [abs_of_pos (div_pos (by linarith) hN), le_div_iff₀ hN]
        linarith
    have hpt : ∀ x : ℝ, ‖f x * ((SepWin.bump (x / ((N:ℝ) + 1)) : ℝ) : ℂ)‖ₑ
        ≤ ‖f x‖ₑ * (Set.Icc (-((N:ℝ) + 1)) ((N:ℝ) + 1)).indicator (fun _ => (1:ℝ≥0∞)) x := by
      intro x
      rw [enorm_mul]
      by_cases hx : x ∈ Set.Icc (-((N:ℝ) + 1)) ((N:ℝ) + 1)
      · rw [Set.indicator_of_mem hx]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [← ofReal_norm, ← ENNReal.ofReal_one, ENNReal.ofReal_le_ofReal_iff zero_le_one,
          Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (SepWin.bump_bounds _).1]
        exact (SepWin.bump_bounds _).2
      · rw [Set.indicator_of_notMem hx, hsupp x hx, enorm_zero, mul_zero]
    have hmeasN : AEStronglyMeasurable (fun x : ℝ => f x * ((SepWin.bump (x / ((N:ℝ) + 1)) : ℝ) : ℂ))
        (volume : Measure ℝ) :=
      hf.aestronglyMeasurable.mul
        (Complex.continuous_ofReal.comp (SepWin.bump_continuous.comp (by fun_prop))).aestronglyMeasurable
    · rw [memLp_iff]; beta_reduce; rw [eLpNorm_one_eq_lintegral_enorm hmeasN]
      refine lt_of_le_of_lt (lintegral_mono hpt) ?_
      have hhold := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume : Measure ℝ)
        (p := 2) (q := 2) Real.HolderConjugate.two_two
        (f := fun x : ℝ => ‖f x‖ₑ)
        (g := fun x : ℝ => (Set.Icc (-((N:ℝ) + 1)) ((N:ℝ) + 1)).indicator
          (fun _ => (1:ℝ≥0∞)) x)
        (hf.aestronglyMeasurable.aemeasurable.enorm)
        ((measurable_const.indicator (s := Set.Icc (-((N:ℝ) + 1)) ((N:ℝ) + 1))
          measurableSet_Icc).aemeasurable)
      rw [← eLpNorm_two_eq f hf.aestronglyMeasurable] at hhold
      refine lt_of_le_of_lt hhold (ENNReal.mul_lt_top hf.eLpNorm_lt_top ?_)
      rw [show (∫⁻ x : ℝ, (Set.Icc (-((N:ℝ) + 1)) ((N:ℝ) + 1)).indicator
            (fun _ => (1:ℝ≥0∞)) x ^ (2:ℝ)) = ENNReal.ofReal (2 * ((N:ℝ) + 1)) from ?_]
      · exact ENNReal.rpow_lt_top_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2) (by finiteness)
      · rw [show (fun x : ℝ => (Set.Icc (-((N:ℝ) + 1)) ((N:ℝ) + 1)).indicator
              (fun _ => (1:ℝ≥0∞)) x ^ (2:ℝ))
            = (Set.Icc (-((N:ℝ) + 1)) ((N:ℝ) + 1)).indicator (fun _ => (1:ℝ≥0∞)) from by
          funext x
          by_cases hx : x ∈ Set.Icc (-((N:ℝ) + 1)) ((N:ℝ) + 1)
          · rw [Set.indicator_of_mem hx, ENNReal.one_rpow]
          · rw [Set.indicator_of_notMem hx, ENNReal.zero_rpow_of_pos (by norm_num : (0:ℝ) < 2)],
        lintegral_indicator_const measurableSet_Icc, one_mul, Real.volume_Icc]
        congr 1
        ring
  · -- `L²`
    intro N
    refine hf.mono (hf.aestronglyMeasurable.mul ?_) (Eventually.of_forall fun x => ?_)
    · exact (Complex.continuous_ofReal.comp (SepWin.bump_continuous.comp (by fun_prop))).aestronglyMeasurable
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (SepWin.bump_bounds _).1]
      calc ‖f x‖ * SepWin.bump (x / ((N:ℝ) + 1))
          ≤ ‖f x‖ * 1 := mul_le_mul_of_nonneg_left (SepWin.bump_bounds _).2 (norm_nonneg _)
        _ = ‖f x‖ := mul_one _
  · -- pointwise norm bound
    intro N x
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (SepWin.bump_bounds _).1]
    calc ‖f x‖ * SepWin.bump (x / ((N:ℝ) + 1))
        ≤ ‖f x‖ * 1 := mul_le_mul_of_nonneg_left (SepWin.bump_bounds _).2 (norm_nonneg _)
      _ = ‖f x‖ := mul_one _
  · -- pointwise convergence
    intro x
    have hev : ∀ᶠ N : ℕ in atTop, (2 * |x| : ℝ) ≤ (N:ℝ) + 1 := by
      have h : Tendsto (fun N : ℕ => ((N:ℝ) + 1)) atTop atTop :=
        tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
      exact (tendsto_atTop.1 h) (2 * |x|)
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [hev] with N hN
    have hx1 : |x / ((N:ℝ) + 1)| ≤ 1/2 := by
      rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < (N:ℝ) + 1), div_le_iff₀ (by positivity)]
      linarith [abs_nonneg x]
    rw [SepWin.bump_one _ hx1, Complex.ofReal_one, mul_one]

/-- A Schwartz function evaluated at a linear scaling is again in `L²`. -/
lemma memLp_comp_mul_left_schwartz (Ψ : SchwartzMap ℝ ℂ) (c : ℝ) (hc : c ≠ 0) :
    MemLp (fun z : ℝ => (Ψ : ℝ → ℂ) (c * z)) 2 (volume : Measure ℝ) := by
  have htemp : Function.HasTemperateGrowth (fun z : ℝ => c * z) := by
    have h : Function.HasTemperateGrowth (fun z : ℝ => z * c) := by fun_prop
    simpa [mul_comm] using h
  have hanti : AntilipschitzWith (Real.toNNReal |c|⁻¹) (fun z : ℝ => c * z) := by
    refine AntilipschitzWith.of_le_mul_dist fun u v => ?_
    have htv : (↑(Real.toNNReal |c|⁻¹) : ℝ) = |c|⁻¹ := Real.coe_toNNReal _ (inv_nonneg.mpr (abs_nonneg c))
    rw [Real.dist_eq, Real.dist_eq, htv, show c * u - c * v = c * (u - v) by ring, abs_mul,
      ← mul_assoc, inv_mul_cancel₀ (abs_ne_zero.mpr hc), one_mul]
  have hS : MemLp (⇑(SchwartzMap.compCLMOfAntilipschitz (𝕜 := ℝ) (F := ℂ) htemp hanti Ψ)) 2
      (volume : Measure ℝ) :=
    (SchwartzMap.compCLMOfAntilipschitz (𝕜 := ℝ) (F := ℂ) htemp hanti Ψ).memLp 2 (volume : Measure ℝ)
  refine hS.ae_eq (Filter.Eventually.of_forall fun z => ?_)
  rw [SchwartzMap.compCLMOfAntilipschitz_apply]
  rfl

/-- Continuity of the target operator's kernel. -/
lemma continuous_innerSmooth (K : ℕ) (lam : Fin K → ℝ) (j : ℕ) :
    Continuous (SepWin.innerSmooth SepWin.bump K lam j) := by
  have h : SepWin.innerSmooth SepWin.bump K lam j
      = fun z : ℝ => ∑ k : Fin K, bandKer winSmooth (lam k) j z := by
    funext z
    exact innerSmooth_eq_sum_bandKer lam j z
  rw [h]
  exact continuous_finsetSum _ fun k _ => continuous_bandKer (lam k) j

lemma measurable_innerSmooth (K : ℕ) (lam : Fin K → ℝ) (j : ℕ) :
    Measurable (SepWin.innerSmooth SepWin.bump K lam j) :=
  (continuous_innerSmooth K lam j).measurable

lemma innerSmooth_bound (K : ℕ) (lam : Fin K → ℝ) (j : ℕ) (z : ℝ) :
    ‖SepWin.innerSmooth SepWin.bump K lam j z‖ ≤ 2 * K := by
  rw [innerSmooth_eq_sum_bandKer lam j z]
  calc ‖∑ k : Fin K, bandKer winSmooth (lam k) j z‖
      ≤ ∑ k : Fin K, ‖bandKer winSmooth (lam k) j z‖ := norm_sum_le _ _
    _ ≤ ∑ _k : Fin K, (2:ℝ) := Finset.sum_le_sum fun k _ => bandKer_bound (lam k) j z
    _ = 2 * K := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

lemma memLp_innerSmooth (K : ℕ) (lam : Fin K → ℝ) (j : ℕ) :
    MemLp (SepWin.innerSmooth SepWin.bump K lam j) 2 (volume : Measure ℝ) := by
  have hc : ((2:ℝ)^(-(j:ℝ)-1)) ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) _).ne'
  have hbig : MemLp (fun z : ℝ => (((K:ℝ):ℂ) * (winSmooth : ℝ → ℂ) ((2:ℝ)^(-(j:ℝ)-1) * z))) 2
      (volume : Measure ℝ) :=
    (memLp_comp_mul_left_schwartz winSmooth _ hc).const_mul _
  refine hbig.mono (continuous_innerSmooth K lam j).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg K)]
  calc ‖SepWin.innerSmooth SepWin.bump K lam j z‖
      ≤ ∑ k : Fin K, ‖bandKer winSmooth (lam k) j z‖ := by
        rw [innerSmooth_eq_sum_bandKer lam j z]
        exact norm_sum_le _ _
    _ ≤ ∑ _k : Fin K, ‖(((2:ℝ)^(-(j:ℝ)-1) : ℝ) : ℂ) * (winSmooth : ℝ → ℂ)
          ((2:ℝ)^(-(j:ℝ)-1) * z)‖ := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [bandKer_apply, norm_mul, Complex.norm_exp]
        have hre : (-(Complex.I * (lam k : ℂ) * (z : ℂ))).re = 0 := by
          simp [Complex.mul_re, Complex.mul_im]
        rw [hre, Real.exp_zero, one_mul, winK]
    _ ≤ ∑ _k : Fin K, ‖(winSmooth : ℝ → ℂ) ((2:ℝ)^(-(j:ℝ)-1) * z)‖ := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [norm_mul]
        refine mul_le_of_le_one_left (norm_nonneg _) ?_
        rw [Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Real.rpow_nonneg (by norm_num) _)]
        exact le_trans (SepWin.hJ_le_half j) (by norm_num)
    _ = (K:ℝ) * ‖(winSmooth : ℝ → ℂ) ((2:ℝ)^(-(j:ℝ)-1) * z)‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- `liminf` of a sequence bounded above by `a` is at most `a`. -/
lemma liminf_le_of_le_const {u : ℕ → ℝ≥0∞} {a : ℝ≥0∞} (h : ∀ n : ℕ, u n ≤ a) :
    Filter.liminf u Filter.atTop ≤ a := by
  refine Filter.liminf_le_of_le ⟨0, Filter.Eventually.of_forall fun n => by simp⟩ ?_
  intro b hb
  obtain ⟨n, hn⟩ := Filter.Eventually.exists hb
  exact le_trans hn (h n)

/-- **The fixed-window maximal estimate for `L²` functions.** -/
theorem FW_L2_uniform {K : ℕ} (lam : Fin K → ℝ)
    (hsep : ∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|) :
    ∃ C : ℝ, 0 < C ∧ ∀ {f : ℝ → ℂ}, MemLp f 2 (volume : Measure ℝ) →
      (∫⁻ x, (⨆ j : ℕ, ‖SepWin.smoothOp SepWin.bump K lam f j x‖ₑ) ^ (2:ℝ))
        ≤ ENNReal.ofReal ((C * (Real.log ((K:ℝ) + 2)) ^ 2) ^ 2)
            * (∫⁻ x, ‖f x‖ₑ ^ (2:ℝ)) := by
  obtain ⟨C, hCpos, hC⟩ := FW_uniform lam hsep
  refine ⟨C, hCpos, fun {f} hf => ?_⟩
  obtain ⟨g, hg1, hg2, hgle, hgconv⟩ := exists_truncations hf
  have hbnd : ∀ N : ℕ, (∫⁻ x, (⨆ j : ℕ, ‖SepWin.smoothOp SepWin.bump K lam (g N) j x‖ₑ) ^ (2:ℝ))
      ≤ ENNReal.ofReal ((C * (Real.log ((K:ℝ) + 2)) ^ 2) ^ 2) * (∫⁻ x, ‖f x‖ₑ ^ (2:ℝ)) := by
    intro N
    refine le_trans (hC (hg1 N) (hg2 N)) (mul_le_mul_of_nonneg_left ?_ bot_le)
    refine lintegral_mono fun x => ENNReal.rpow_le_rpow ?_ (by norm_num)
    rw [← ofReal_norm, ← ofReal_norm, ENNReal.ofReal_le_ofReal_iff (norm_nonneg _)]
    exact hgle N x
  have hconv_op : ∀ j : ℕ, ∀ x : ℝ,
      Tendsto (fun N : ℕ => SepWin.smoothOp SepWin.bump K lam (g N) j x) atTop
        (𝓝 (SepWin.smoothOp SepWin.bump K lam f j x)) := by
    intro j x
    have hK2 : MemLp (fun y : ℝ => SepWin.innerSmooth SepWin.bump K lam j (x - y)) 2
        (volume : Measure ℝ) :=
      (memLp_innerSmooth K lam j).comp_measurePreserving (BoundaryLayer.mpSub x)
    have hdiff : ∀ N : ℕ, SepWin.smoothOp SepWin.bump K lam (g N) j x
          - SepWin.smoothOp SepWin.bump K lam f j x
        = ∫ y : ℝ, (g N y - f y) * SepWin.innerSmooth SepWin.bump K lam j (x - y) := by
      intro N
      rw [SepWin.smoothOp, SepWin.smoothOp, ← integral_sub]
      · refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        ring
      · exact (hg2 N).integrable_mul hK2
      · exact hf.integrable_mul hK2
    have hnorm : Tendsto (fun N : ℕ => ‖SepWin.smoothOp SepWin.bump K lam (g N) j x
        - SepWin.smoothOp SepWin.bump K lam f j x‖) atTop (𝓝 0) := by
      have h1 : Tendsto (fun N : ℕ => (eLpNorm (fun x : ℝ => g N x - f x) 2
            (volume : Measure ℝ)).toReal) atTop (𝓝 0) := by
        have h2 := (ENNReal.tendsto_toReal (by simp : (0:ℝ≥0∞) ≠ ⊤)).comp
          (tendsto_eLpNorm_two_sub_of_dominated hg2 hf hgle hgconv)
        simpa [Function.comp_def, ENNReal.toReal_zero] using h2
      have h3 := h1.mul_const (eLpNorm (SepWin.innerSmooth SepWin.bump K lam j) 2
        (volume : Measure ℝ)).toReal
      refine squeeze_zero (fun N => norm_nonneg _) (fun N => ?_) (by simpa using h3)
      rw [hdiff N]
      exact norm_convolution_le_eLpNorm ((hg2 N).sub hf) (memLp_innerSmooth K lam j) x
    have hzero := tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
    rw [show (fun N : ℕ => SepWin.smoothOp SepWin.bump K lam (g N) j x)
        = fun N : ℕ => (SepWin.smoothOp SepWin.bump K lam (g N) j x
            - SepWin.smoothOp SepWin.bump K lam f j x)
          + SepWin.smoothOp SepWin.bump K lam f j x from by
      funext N
      ring]
    simpa using hzero.add_const (SepWin.smoothOp SepWin.bump K lam f j x)
  have hlim : ∀ x : ℝ, (⨆ j : ℕ, ‖SepWin.smoothOp SepWin.bump K lam f j x‖ₑ) ^ (2:ℝ)
      ≤ ⨆ N : ℕ, ⨅ i ≥ N,
          (⨆ j : ℕ, ‖SepWin.smoothOp SepWin.bump K lam (g i) j x‖ₑ) ^ (2:ℝ) := by
    intro x
    rw [iSup_rpow_two]
    refine iSup_le fun j => ?_
    have henorm : Tendsto (fun N : ℕ => ‖SepWin.smoothOp SepWin.bump K lam (g N) j x‖ₑ) atTop
        (𝓝 ‖SepWin.smoothOp SepWin.bump K lam f j x‖ₑ) := by
      simpa using ((hconv_op j x).norm).enorm
    have htj : Tendsto (fun N : ℕ => ‖SepWin.smoothOp SepWin.bump K lam (g N) j x‖ₑ ^ (2:ℝ))
        atTop (𝓝 (‖SepWin.smoothOp SepWin.bump K lam f j x‖ₑ ^ (2:ℝ))) :=
      (ENNReal.continuous_rpow_const (y := (2:ℝ))).tendsto
        (‖SepWin.smoothOp SepWin.bump K lam f j x‖ₑ) |>.comp henorm
    have h_a : ‖SepWin.smoothOp SepWin.bump K lam f j x‖ₑ ^ (2:ℝ)
        = ⨆ N : ℕ, ⨅ i ≥ N, ‖SepWin.smoothOp SepWin.bump K lam (g i) j x‖ₑ ^ (2:ℝ) := by
      rw [← htj.liminf_eq, Filter.liminf_eq_iSup_iInf_of_nat]
    rw [h_a]
    refine iSup_le (f := fun N : ℕ => (⨅ i : ℕ, ⨅ _hi : N ≤ i,
        ‖SepWin.smoothOp SepWin.bump K lam (g i) j x‖ₑ ^ (2:ℝ))) fun N => ?_
    refine le_trans ?_ (le_iSup (fun n : ℕ => (⨅ i : ℕ, ⨅ _hi : n ≤ i,
        (⨆ j' : ℕ, ‖SepWin.smoothOp SepWin.bump K lam (g i) j' x‖ₑ) ^ (2:ℝ))) N)
    exact iInf_mono fun R => iInf_mono fun hR =>
      ENNReal.rpow_le_rpow (le_iSup (fun j' => ‖SepWin.smoothOp SepWin.bump K lam (g R) j' x‖ₑ) j)
        (by norm_num)
  have hAEm : ∀ N : ℕ, AEMeasurable (fun x : ℝ =>
      (⨆ j : ℕ, ‖SepWin.smoothOp SepWin.bump K lam (g N) j x‖ₑ) ^ (2:ℝ)) (volume : Measure ℝ) := by
    intro N
    refine aemeasurable_rpow_two ?_
    refine AEMeasurable.iSup fun j => ?_
    exact ((aestronglyMeasurable_conv (hf := hg2 N) (measurable_innerSmooth K lam j)).aemeasurable.enorm)
  calc ∫⁻ x, (⨆ j : ℕ, ‖SepWin.smoothOp SepWin.bump K lam f j x‖ₑ) ^ (2:ℝ)
      ≤ ∫⁻ x, ⨆ N : ℕ, ⨅ i ≥ N,
          (⨆ j : ℕ, ‖SepWin.smoothOp SepWin.bump K lam (g i) j x‖ₑ) ^ (2:ℝ) :=
        lintegral_mono hlim
    _ = ⨆ N : ℕ, ∫⁻ x, ⨅ i ≥ N,
          (⨆ j : ℕ, ‖SepWin.smoothOp SepWin.bump K lam (g i) j x‖ₑ) ^ (2:ℝ) :=
        lintegral_iSup' (fun N => AEMeasurable.iInf fun i =>
            AEMeasurable.iInf fun _ : N ≤ i => hAEm i)
          (Filter.Eventually.of_forall fun x => fun N N' hNN' =>
            le_iInf fun i => le_iInf fun hi =>
              le_trans (iInf_le _ i) (iInf_le _ (le_trans hNN' hi)))
    _ ≤ ENNReal.ofReal ((C * (Real.log ((K:ℝ) + 2)) ^ 2) ^ 2) * (∫⁻ x, ‖f x‖ₑ ^ (2:ℝ)) :=
        iSup_le fun N => le_trans (lintegral_mono fun x =>
          le_trans (iInf_le _ N) (iInf_le _ le_rfl)) (hbnd N)

/-- **The fixed-window maximal estimate, uniform in `K` and `lam`.** -/
theorem FW_uniform' :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : ℕ) (lam : Fin K → ℝ)
      (hsep : ∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|),
      ∀ {f : ℝ → ℂ}, MemLp f 1 (volume : Measure ℝ) →
      MemLp f 2 (volume : Measure ℝ) →
      (∫⁻ x, (⨆ j : ℕ, ‖SepWin.smoothOp SepWin.bump K lam f j x‖ₑ) ^ (2:ℝ))
        ≤ ENNReal.ofReal ((C * (Real.log ((K:ℝ) + 2)) ^ 2) ^ 2)
            * (∫⁻ x, ‖f x‖ₑ ^ (2:ℝ)) := by
  have hth : 2 * (2 * Real.pi * (1 / (4 * Real.pi) + 3 / 100) * (9 / 10)) ^ 2 < 1 := by
    have h1 : 2 * Real.pi * (1 / (4 * Real.pi) + 3 / 100) * (9 / 10)
        = 9 / 20 + 27 * Real.pi / 500 := by
      field_simp
      ring
    rw [h1]
    nlinarith [Real.pi_pos, Real.pi_lt_four]
  obtain ⟨C, hCpos, hCbnd⟩ := bandMax_le_of_bandlimited' winSmooth winSmooth_bound
    (by positivity) hth
  refine ⟨Real.sqrt 2 * C, by positivity, fun K lam hsep {f} hf1 hf2 => ?_⟩
  have hw : 0 < (1:ℝ) / (4 * Real.pi) := by positivity
  have hw4 : 4 * Real.pi * (1 / (4 * Real.pi)) ≤ 1 := by
    rw [mul_one_div, div_self (by positivity : (4 * Real.pi) ≠ 0)]
  have hη : 0 < (3:ℝ) / 100 := by norm_num
  have hηw : (3:ℝ) / 100 < 1 / (4 * Real.pi) := by
    rw [lt_div_iff₀ (by positivity : (0:ℝ) < 4 * Real.pi)]
    nlinarith [Real.pi_lt_four]
  obtain ⟨ψ, κ, hψc, hψnn, hψle, hψone, hψzero, hκc, hκI, hκ2, hκtop, hκbd, hκF, hκsum⟩ :=
    exists_cellKernels lam hsep (1 / (4 * Real.pi)) (3 / 100) hw hw4 hη hηw
  have hκm : ∀ k : Fin K, Measurable (κ k) := fun k => (hκc k).measurable
  have hψm : ∀ k : Fin K, Measurable (ψ k) := fun k => (hψc k).continuous.measurable
  have hfI : Integrable f := memLp_one_iff_integrable.mp hf1
  set H : Fin K → ℝ → ℂ := fun k t => (∫ y : ℝ, f y * κ k (t - y))
      * Complex.exp (Complex.I * (lam k : ℂ) * (t : ℂ)) with hHdef
  -- membership in `L^p` of the slices
  have hconvL1 : ∀ k : Fin K, MemLp (fun t : ℝ => ∫ y, f y * κ k (t - y)) 1
      (volume : Measure ℝ) := by
    intro k
    refine memLp_one_iff_integrable.mpr ?_
    have h := hfI.integrable_convolution (L := ContinuousLinearMap.mul ℂ ℂ) (hκI k)
    have hfun : (MeasureTheory.convolution f (κ k) (ContinuousLinearMap.mul ℂ ℂ)
        (volume : Measure ℝ)) = fun t => ∫ y, f y * κ k (t - y) := by
      funext t
      rw [convolution_def]
      rfl
    rwa [hfun] at h
  have hconvL2 : ∀ k : Fin K, MemLp (fun t : ℝ => ∫ y, f y * κ k (t - y)) 2
      (volume : Measure ℝ) := fun k =>
    memLp_convolution_two_of_fourier_le_one hf2 (memLp_one_iff_integrable.mpr (hκI k)) (hκm k)
      (norm_fourier_le_one_of_eq (hκF k) (hψnn k) (hψle k))
  have hconvLtop : ∀ k : Fin K, MemLp (fun t : ℝ => ∫ y, f y * κ k (t - y)) ⊤
      (volume : Measure ℝ) := fun k =>
    memLp_convolution_top_of_bound hf1 hf2 (hκm k) (hκbd k).choose_spec
  have hunimod : ∀ k : Fin K, AEStronglyMeasurable
      (fun t : ℝ => Complex.exp (Complex.I * (lam k : ℂ) * (t : ℂ))) (volume : Measure ℝ) :=
    fun k => (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable
  have hunimod1 : ∀ k : Fin K, ∀ t : ℝ,
      ‖Complex.exp (Complex.I * (lam k : ℂ) * (t : ℂ))‖ = 1 := by
    intro k t
    rw [Complex.norm_exp]
    have hre : (Complex.I * (lam k : ℂ) * (t : ℂ)).re = 0 := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [hre, Real.exp_zero]
  -- admissibility of `H`
  have hAdm : AdmB (1 / (4 * Real.pi) + 3 / 100) H := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro k
      rw [hHdef]
      exact memLp_mul_unimodular (hconvL1 k) (hunimod k) (hunimod1 k)
    · intro k
      rw [hHdef]
      exact memLp_mul_unimodular (hconvL2 k) (hunimod k) (hunimod1 k)
    · intro k
      rw [hHdef]
      exact memLp_mul_unimodular (hconvLtop k) (hunimod k) (hunimod1 k)
    · intro k ξ hξ
      simp only [hHdef]
      rw [show (fun t : ℝ => (∫ y : ℝ, f y * κ k (t - y)) * Complex.exp (Complex.I * (lam k : ℂ) * (t : ℂ)))
          = fun t : ℝ => (∫ y : ℝ, f y * κ k (t - y))
              * Complex.exp ((↑(2 * Real.pi * (lam k / (2 * Real.pi)) * t) * Complex.I) : ℂ) from by
        funext t
        congr 2
        push_cast
        field_simp]
      rw [fourier_mul_exp_rule]
      rw [fourier_convolution f (κ k) hfI (hκI k) (ξ - lam k / (2 * Real.pi)),
        hκF k (ξ - lam k / (2 * Real.pi)),
        hψzero k (ξ - lam k / (2 * Real.pi)) (by
          have h : ξ - lam k / (2 * Real.pi) + lam k / (2 * Real.pi) = ξ := by ring
          rw [h]
          exact le_of_lt hξ)]
      simp
  -- the slice energy bound
  have hbandSq : bandSq H ≤ 2 * ∫⁻ x, ‖f x‖ₑ ^ (2:ℝ) := by
    have hbound : ∀ ξ : ℝ, ∑ k : Fin K, (ψ k ξ) ^ 2 ≤ 2 := by
      intro ξ
      refine le_trans (le_of_eq ?_) (hκsum ξ)
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hκF k ξ, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have hslice := slice_energy_le f κ ψ hf2 (fun k => memLp_one_iff_integrable.mpr (hκI k))
      hκm hκF hψm hψnn hbound
    have h1 : bandSq H
        = ∫⁻ x, ENNReal.ofReal (∑ k : Fin K, ‖∫ y : ℝ, f y * κ k (x - y)‖ ^ 2) := by
      rw [bandSq]
      refine lintegral_congr fun x => ?_
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [hHdef]
      rw [norm_mul, Complex.norm_exp]
      have hre : (Complex.I * (lam k : ℂ) * (x : ℂ)).re = 0 := by
        simp [Complex.mul_re, Complex.mul_im]
      rw [hre, Real.exp_zero, mul_one]
    rw [h1]
    refine le_trans hslice ?_
    rw [show (2 * ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2)) = 2 * ∫⁻ x, ‖f x‖ₑ ^ (2:ℝ) from by
      rw [show (∫⁻ x : ℝ, ENNReal.ofReal (‖f x‖ ^ 2)) = ∫⁻ x : ℝ, ‖f x‖ₑ ^ (2:ℝ) from
        lintegral_congr fun x => (enorm_rpow_two_eq_ofReal_sq (f x)).symm]]
  have hcrux := hCbnd K lam hsep (AdmB (1 / (4 * Real.pi) + 3 / 100))
    (fun H' h k => h.2.1 k) (fun H' h k => h.2.2.1 k)
    (fun H' h k => memLp_one_iff_integrable.mp (h.1 k)) (fun H' h k ξ hξ => h.2.2.2 k ξ hξ)
    (fun H' y h _ => admB_shiftH h y) H hAdm
  -- the two sides agree pointwise
  have hident : (∫⁻ x, (⨆ j : ℕ, ‖SepWin.smoothOp SepWin.bump K lam f j x‖ₑ) ^ (2:ℝ))
      = bandMax winSmooth lam H := by
    refine lintegral_congr fun x => ?_
    congr 1
    refine iSup_congr fun j => ?_
    rw [smoothOp_eq_bandOpD lam (fun k => memLp_one_iff_integrable.mpr (hκI k)) hκm hκF hψnn
      hψle (fun k ξ hξ => hψone k ξ hξ) hf1 hf2 j x]
  rw [hident]
  -- assemble
  have hsq : 2 * (C * Real.log ((K:ℝ) + 2) ^ 2) ^ 2
      = ((Real.sqrt 2 * C) * Real.log ((K:ℝ) + 2) ^ 2) ^ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  calc bandMax winSmooth lam H
      ≤ ENNReal.ofReal ((C * Real.log ((K:ℝ) + 2) ^ 2) ^ 2) * bandSq H := hcrux
    _ ≤ ENNReal.ofReal ((C * Real.log ((K:ℝ) + 2) ^ 2) ^ 2)
          * (2 * ∫⁻ x, ‖f x‖ₑ ^ (2:ℝ)) := by gcongr
    _ = ENNReal.ofReal (((Real.sqrt 2 * C) * Real.log ((K:ℝ) + 2) ^ 2) ^ 2)
          * ∫⁻ x, ‖f x‖ₑ ^ (2:ℝ) := by
        rw [show (2:ℝ≥0∞) = ENNReal.ofReal 2 from by norm_num, ← mul_assoc,
          mul_comm (ENNReal.ofReal ((C * Real.log ((K:ℝ) + 2) ^ 2) ^ 2)) (ENNReal.ofReal 2),
          ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2), hsq]

/-- **The fixed-window maximal estimate for `L²` functions, uniform in `K` and `lam`.** -/
theorem FW_L2_uniform' :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : ℕ) (lam : Fin K → ℝ)
      (hsep : ∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|),
      ∀ {f : ℝ → ℂ}, MemLp f 2 (volume : Measure ℝ) →
      (∫⁻ x, (⨆ j : ℕ, ‖SepWin.smoothOp SepWin.bump K lam f j x‖ₑ) ^ (2:ℝ))
        ≤ ENNReal.ofReal ((C * (Real.log ((K:ℝ) + 2)) ^ 2) ^ 2)
            * (∫⁻ x, ‖f x‖ₑ ^ (2:ℝ)) := by
  obtain ⟨C, hCpos, hC⟩ := FW_uniform'
  refine ⟨C, hCpos, fun K lam hsep {f} hf => ?_⟩
  obtain ⟨g, hg1, hg2, hgle, hgconv⟩ := exists_truncations hf
  have hbnd : ∀ N : ℕ, (∫⁻ x, (⨆ j : ℕ, ‖SepWin.smoothOp SepWin.bump K lam (g N) j x‖ₑ) ^ (2:ℝ))
      ≤ ENNReal.ofReal ((C * (Real.log ((K:ℝ) + 2)) ^ 2) ^ 2) * (∫⁻ x, ‖f x‖ₑ ^ (2:ℝ)) := by
    intro N
    refine le_trans (hC K lam hsep (hg1 N) (hg2 N)) (mul_le_mul_of_nonneg_left ?_ bot_le)
    refine lintegral_mono fun x => ENNReal.rpow_le_rpow ?_ (by norm_num)
    rw [← ofReal_norm, ← ofReal_norm, ENNReal.ofReal_le_ofReal_iff (norm_nonneg _)]
    exact hgle N x
  have hconv_op : ∀ j : ℕ, ∀ x : ℝ,
      Tendsto (fun N : ℕ => SepWin.smoothOp SepWin.bump K lam (g N) j x) atTop
        (𝓝 (SepWin.smoothOp SepWin.bump K lam f j x)) := by
    intro j x
    have hK2 : MemLp (fun y : ℝ => SepWin.innerSmooth SepWin.bump K lam j (x - y)) 2
        (volume : Measure ℝ) :=
      (memLp_innerSmooth K lam j).comp_measurePreserving (BoundaryLayer.mpSub x)
    have hdiff : ∀ N : ℕ, SepWin.smoothOp SepWin.bump K lam (g N) j x
          - SepWin.smoothOp SepWin.bump K lam f j x
        = ∫ y : ℝ, (g N y - f y) * SepWin.innerSmooth SepWin.bump K lam j (x - y) := by
      intro N
      rw [SepWin.smoothOp, SepWin.smoothOp, ← integral_sub]
      · refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        ring
      · exact (hg2 N).integrable_mul hK2
      · exact hf.integrable_mul hK2
    have hnorm : Tendsto (fun N : ℕ => ‖SepWin.smoothOp SepWin.bump K lam (g N) j x
        - SepWin.smoothOp SepWin.bump K lam f j x‖) atTop (𝓝 0) := by
      have h1 : Tendsto (fun N : ℕ => (eLpNorm (fun x : ℝ => g N x - f x) 2
            (volume : Measure ℝ)).toReal) atTop (𝓝 0) := by
        have h2 := (ENNReal.tendsto_toReal (by simp : (0:ℝ≥0∞) ≠ ⊤)).comp
          (tendsto_eLpNorm_two_sub_of_dominated hg2 hf hgle hgconv)
        simpa [Function.comp_def, ENNReal.toReal_zero] using h2
      have h3 := h1.mul_const (eLpNorm (SepWin.innerSmooth SepWin.bump K lam j) 2
        (volume : Measure ℝ)).toReal
      refine squeeze_zero (fun N => norm_nonneg _) (fun N => ?_) (by simpa using h3)
      rw [hdiff N]
      exact norm_convolution_le_eLpNorm ((hg2 N).sub hf) (memLp_innerSmooth K lam j) x
    have hzero := tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
    rw [show (fun N : ℕ => SepWin.smoothOp SepWin.bump K lam (g N) j x)
        = fun N : ℕ => (SepWin.smoothOp SepWin.bump K lam (g N) j x
            - SepWin.smoothOp SepWin.bump K lam f j x)
          + SepWin.smoothOp SepWin.bump K lam f j x from by
      funext N
      ring]
    simpa using hzero.add_const (SepWin.smoothOp SepWin.bump K lam f j x)
  have hlim : ∀ x : ℝ, (⨆ j : ℕ, ‖SepWin.smoothOp SepWin.bump K lam f j x‖ₑ) ^ (2:ℝ)
      ≤ ⨆ N : ℕ, ⨅ i ≥ N,
          (⨆ j : ℕ, ‖SepWin.smoothOp SepWin.bump K lam (g i) j x‖ₑ) ^ (2:ℝ) := by
    intro x
    rw [iSup_rpow_two]
    refine iSup_le fun j => ?_
    have henorm : Tendsto (fun N : ℕ => ‖SepWin.smoothOp SepWin.bump K lam (g N) j x‖ₑ) atTop
        (𝓝 ‖SepWin.smoothOp SepWin.bump K lam f j x‖ₑ) := by
      simpa using ((hconv_op j x).norm).enorm
    have htj : Tendsto (fun N : ℕ => ‖SepWin.smoothOp SepWin.bump K lam (g N) j x‖ₑ ^ (2:ℝ))
        atTop (𝓝 (‖SepWin.smoothOp SepWin.bump K lam f j x‖ₑ ^ (2:ℝ))) :=
      (ENNReal.continuous_rpow_const (y := (2:ℝ))).tendsto
        (‖SepWin.smoothOp SepWin.bump K lam f j x‖ₑ) |>.comp henorm
    have h_a : ‖SepWin.smoothOp SepWin.bump K lam f j x‖ₑ ^ (2:ℝ)
        = ⨆ N : ℕ, ⨅ i ≥ N, ‖SepWin.smoothOp SepWin.bump K lam (g i) j x‖ₑ ^ (2:ℝ) := by
      rw [← htj.liminf_eq, Filter.liminf_eq_iSup_iInf_of_nat]
    rw [h_a]
    refine iSup_le (f := fun N : ℕ => (⨅ i : ℕ, ⨅ _hi : N ≤ i,
        ‖SepWin.smoothOp SepWin.bump K lam (g i) j x‖ₑ ^ (2:ℝ))) fun N => ?_
    refine le_trans ?_ (le_iSup (fun n : ℕ => (⨅ i : ℕ, ⨅ _hi : n ≤ i,
        (⨆ j' : ℕ, ‖SepWin.smoothOp SepWin.bump K lam (g i) j' x‖ₑ) ^ (2:ℝ))) N)
    exact iInf_mono fun R => iInf_mono fun hR =>
      ENNReal.rpow_le_rpow (le_iSup (fun j' => ‖SepWin.smoothOp SepWin.bump K lam (g R) j' x‖ₑ) j)
        (by norm_num)
  have hAEm : ∀ N : ℕ, AEMeasurable (fun x : ℝ =>
      (⨆ j : ℕ, ‖SepWin.smoothOp SepWin.bump K lam (g N) j x‖ₑ) ^ (2:ℝ)) (volume : Measure ℝ) := by
    intro N
    refine aemeasurable_rpow_two ?_
    refine AEMeasurable.iSup fun j => ?_
    exact ((aestronglyMeasurable_conv (hf := hg2 N) (measurable_innerSmooth K lam j)).aemeasurable.enorm)
  calc ∫⁻ x, (⨆ j : ℕ, ‖SepWin.smoothOp SepWin.bump K lam f j x‖ₑ) ^ (2:ℝ)
      ≤ ∫⁻ x, ⨆ N : ℕ, ⨅ i ≥ N,
          (⨆ j : ℕ, ‖SepWin.smoothOp SepWin.bump K lam (g i) j x‖ₑ) ^ (2:ℝ) :=
        lintegral_mono hlim
    _ = ⨆ N : ℕ, ∫⁻ x, ⨅ i ≥ N,
          (⨆ j : ℕ, ‖SepWin.smoothOp SepWin.bump K lam (g i) j x‖ₑ) ^ (2:ℝ) :=
        lintegral_iSup' (fun N => AEMeasurable.iInf fun i =>
            AEMeasurable.iInf fun _ : N ≤ i => hAEm i)
          (Filter.Eventually.of_forall fun x => fun N N' hNN' =>
            le_iInf fun i => le_iInf fun hi =>
              le_trans (iInf_le _ i) (iInf_le _ (le_trans hNN' hi)))
    _ ≤ ENNReal.ofReal ((C * (Real.log ((K:ℝ) + 2)) ^ 2) ^ 2) * (∫⁻ x, ‖f x‖ₑ ^ (2:ℝ)) :=
        iSup_le fun N => le_trans (lintegral_mono fun x =>
          le_trans (iInf_le _ N) (iInf_le _ le_rfl)) (hbnd N)

end FixWin
end Commons.Analysis.Fourier


set_option maxHeartbeats 800000

namespace Commons.Analysis.Fourier

open _root_.MeasureTheory Finset Filter
open scoped BigOperators _root_.ENNReal _root_.Topology FourierTransform

noncomputable section

/-! ### The fixed bump used to split the window, and the annulus (remainder) estimate

These are the two ingredients of the reduction `φ = A + g` explained in
`Submission/Work/Analysis/Fourier/SINGLE_MULTIPLIER_REDUCTION.md`: the *fixed* bump `winA`
and the *annulus* window `g = φ - winA`, whose band-sum maximal function is bounded on `L²`
by `(8π)²` **uniformly in the annulus profile** — no dependence on the number `K` of
frequencies or on `φ`. -/


/-- The *fixed* `C^∞` bump `A` used to split a window `φ` of the target's class as `φ = A + g`:
`A = 1` on `[-1/2,1/2]`, `A = 0` off `[-1,1]`, `0 ≤ A ≤ 1`. -/
def winA (x : ℝ) : ℝ := Real.smoothTransition (2 - 2 * x) * Real.smoothTransition (2 + 2 * x)

lemma winA_contDiff (n : ℕ) : ContDiff ℝ n winA := by
  unfold winA
  exact ContDiff.mul
    ((Real.smoothTransition.contDiff (n := (n : ℕ∞))).comp (by fun_prop))
    ((Real.smoothTransition.contDiff (n := (n : ℕ∞))).comp (by fun_prop))

lemma winA_eq_one {x : ℝ} (hx : |x| ≤ 1 / 2) : winA x = 1 := by
  have h1 : (1 : ℝ) ≤ 2 - 2 * x := by
    have := (abs_le.mp hx).2; linarith
  have h2 : (1 : ℝ) ≤ 2 + 2 * x := by
    have := (abs_le.mp hx).1; linarith
  unfold winA
  rw [Real.smoothTransition.one_of_one_le h1, Real.smoothTransition.one_of_one_le h2, mul_one]

lemma winA_eq_zero {x : ℝ} (hx : 1 ≤ |x|) : winA x = 0 := by
  rcases le_total 0 x with h | h
  · have h1 : 2 - 2 * x ≤ 0 := by
      have := (abs_of_nonneg h) ▸ hx; linarith
    unfold winA
    rw [Real.smoothTransition.zero_of_nonpos h1, zero_mul]
  · have h2 : 2 + 2 * x ≤ 0 := by
      have hx' : 1 ≤ -x := by rw [abs_of_nonpos h] at hx; linarith
      linarith
    unfold winA
    rw [Real.smoothTransition.zero_of_nonpos h2, mul_zero]

lemma winA_nonneg (x : ℝ) : 0 ≤ winA x := by
  unfold winA
  exact mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

lemma winA_le_one (x : ℝ) : winA x ≤ 1 := by
  unfold winA
  exact mul_le_one₀ (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _)
    (Real.smoothTransition.le_one _)

/-- For a window `φ` of the target's class, the annulus profile `g = φ - A` vanishes on
`[-1/2,1/2]` and off `[-1,1]`, and is bounded by `2`. -/
lemma winA_sub_supp {φ : ℝ → ℝ} (h1 : ∀ x : ℝ, |x| ≤ 1 / 2 → φ x = 1)
    (h0 : ∀ x : ℝ, 1 ≤ |x| → φ x = 0) (hbd : ∀ x : ℝ, 0 ≤ φ x ∧ φ x ≤ 1) (x : ℝ) :
    ¬ ((1 : ℝ) / 2 < |x| ∧ |x| ≤ 1) → φ x - winA x = 0 := by
  intro hx
  rcases not_and_or.mp hx with h | h
  · have : |x| ≤ 1 / 2 := le_of_not_gt h
    rw [h1 x this, winA_eq_one this, sub_self]
  · have : 1 ≤ |x| := le_of_not_ge h
    rw [h0 x this, winA_eq_zero this, sub_self]

lemma winA_sub_bound {φ : ℝ → ℝ} (hbd : ∀ x : ℝ, 0 ≤ φ x ∧ φ x ≤ 1) (x : ℝ) :
    ‖φ x - winA x‖ ≤ 2 := by
  have h1 := hbd x
  have h2 := winA_nonneg x
  have h3 := winA_le_one x
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith [h1.1, h1.2]

/-- The dyadic scale `t_j = 2^{j+1}`. -/
def scaleT (j : ℕ) : ℝ := (2 : ℝ) ^ (j + 1)

lemma scaleT_pos (j : ℕ) : 0 < scaleT j := by
  rw [scaleT]; positivity

lemma scaleT_ge_two (j : ℕ) : 2 ≤ scaleT j := by
  rw [scaleT]
  calc (2:ℝ) = 2 ^ (1:ℕ) := by norm_num
    _ ≤ 2 ^ (j + 1) := by
        apply pow_le_pow_right₀ (by norm_num) (by omega)

/-- At most two `1`-separated points of `ℝ` can lie in an interval of length `≤ 1`. -/
lemma card_le_two_separated {K : ℕ} {lam : Fin K → ℝ}
    (hsep : ∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|)
    {c r : ℝ} (hr : 0 < r) (hr2 : 2 * r ≤ 1) :
    (Finset.univ.filter (fun k : Fin K => |lam k - c| ≤ r)).card ≤ 2 := by
  classical
  set S : Finset (Fin K) := Finset.univ.filter (fun k : Fin K => |lam k - c| ≤ r) with hS
  have hmem : ∀ k : Fin K, k ∈ S ↔ |lam k - c| ≤ r := by intro k; rw [hS]; simp
  have key : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → |lam x - c| = r := by
    intro x hx y hy hxy
    have h1 : 1 ≤ |lam x - lam y| := hsep x y hxy
    have h3 : |lam x - lam y| ≤ |lam x - c| + |lam y - c| := by
      calc |lam x - lam y| = |(lam x - c) - (lam y - c)| := by congr 1; ring
        _ ≤ |lam x - c| + |lam y - c| := by
            simpa only [sub_zero, zero_sub, abs_neg] using
              abs_sub_le (lam x - c) 0 (lam y - c)
    have h4 : |lam x - c| ≤ r := (hmem x).mp hx
    have h5 : |lam y - c| ≤ r := (hmem y).mp hy
    have h6 := abs_nonneg (lam x - c)
    have h7 := abs_nonneg (lam y - c)
    nlinarith [h1, h3, h4, h5, h6, h7]
  by_cases h : S.card ≤ 2
  · exact h
  · simp only [not_le] at h
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (show 1 < S.card by omega)
    have hall : ∀ x ∈ S, |lam x - c| = r := by
      intro x hx
      rcases eq_or_ne x a with h' | h'
      · rw [h']; exact key a ha b hb hab
      · exact key x hx a ha h'
    have hinj : Set.InjOn lam (↑S : Set (Fin K)) := by
      intro u hu v hv huv
      by_contra hne'
      have h1 : 1 ≤ |lam u - lam v| := hsep u v hne'
      rw [huv, sub_self, abs_zero] at h1
      linarith
    have himg : (S.image lam).card = S.card := Finset.card_image_of_injOn hinj
    have hsub : S.image lam ⊆ ({c - r, c + r} : Finset ℝ) := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      have := hall x hx
      rcases (abs_eq (le_of_lt hr)).mp this with h' | h'
      · simp [show lam x = c + r by linarith]
      · simp [show lam x = c - r by linarith]
    have hcard := Finset.card_le_card hsub
    have h2 : ({c - r, c + r} : Finset ℝ).card ≤ 2 := by
      rcases eq_or_ne (c - r) (c + r) with h' | h'
      · rw [h']; simp
      · rw [Finset.card_insert_of_notMem (by simp [h'])]; simp
    omega

/-- The annulus multiplier `M_j^g(η) = 2π ∑_k g(-t_j(η+λ_k))`. -/
def annulusMul {K : ℕ} (g : ℝ → ℂ) (lam : Fin K → ℝ) (j : ℕ) : ℝ → ℂ :=
  fun η => 2 * Real.pi * ∑ k : Fin K, g (-(scaleT j * (η + lam k)))

/-- Pointwise bound for the annulus multiplier. -/
lemma annulusMul_bound {K : ℕ} {lam : Fin K → ℝ}
    (hsep : ∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|) {g : ℝ → ℂ}
    (hg_supp : ∀ θ : ℝ, ¬ ((1:ℝ)/2 < |θ| ∧ |θ| ≤ 1) → g θ = 0)
    (hg_bd : ∀ θ : ℝ, ‖g θ‖ ≤ 2) (η : ℝ) (j : ℕ) :
    ‖annulusMul g lam j η‖ ≤ 8 * Real.pi := by
  rw [annulusMul]
  have hS : (Finset.univ.filter
      (fun k : Fin K => |lam k - (-η)| ≤ (scaleT j)⁻¹)).card ≤ 2 := by
    have hr : (0:ℝ) < (scaleT j)⁻¹ := inv_pos.mpr (scaleT_pos j)
    have hr2 : 2 * (scaleT j)⁻¹ ≤ 1 := by
      have h2 := scaleT_ge_two j
      have h3 : (1:ℝ) / scaleT j ≤ 1 / 2 :=
        one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 2) h2
      rw [inv_eq_one_div]
      linarith
    exact card_le_two_separated hsep hr hr2
  have hzero : ∀ k : Fin K, ¬ (|lam k - (-η)| ≤ (scaleT j)⁻¹) →
      g (-(scaleT j * (η + lam k))) = 0 := by
    intro k hk
    apply hg_supp
    intro hcon
    apply hk
    have h1 : scaleT j * |η + lam k| ≤ 1 := by
      have := hcon.2
      rw [abs_neg, abs_mul, abs_of_pos (scaleT_pos j)] at this
      exact this
    rw [sub_neg_eq_add, show lam k + η = η + lam k by ring, inv_eq_one_div,
      le_div_iff₀ (scaleT_pos j), mul_comm]
    exact h1
  have hsum : ‖∑ k : Fin K, g (-(scaleT j * (η + lam k)))‖ ≤ 4 := by
    calc ‖∑ k : Fin K, g (-(scaleT j * (η + lam k)))‖
        ≤ ∑ k : Fin K, ‖g (-(scaleT j * (η + lam k)))‖ := norm_sum_le _ _
      _ = ∑ k ∈ (Finset.univ.filter (fun k : Fin K => |lam k - (-η)| ≤ (scaleT j)⁻¹)),
            ‖g (-(scaleT j * (η + lam k)))‖ := by
          refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
          intro k _ hk
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
          rw [hzero k hk, norm_zero]
      _ ≤ ∑ k ∈ (Finset.univ.filter (fun k : Fin K => |lam k - (-η)| ≤ (scaleT j)⁻¹)),
            (2:ℝ) := by
          refine Finset.sum_le_sum (fun k _ => hg_bd _)
      _ = 2 * ((Finset.univ.filter
            (fun k : Fin K => |lam k - (-η)| ≤ (scaleT j)⁻¹)).card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          ring
      _ ≤ 2 * 2 := by
          have hcast : ((Finset.univ.filter
              (fun k : Fin K => |lam k - (-η)| ≤ (scaleT j)⁻¹)).card : ℝ) ≤ 2 := by
            exact_mod_cast hS
          linarith
      _ = 4 := by norm_num
  have hZ : (2:ℂ) * (Real.pi:ℂ) * (∑ k : Fin K, g (-(scaleT j * (η + lam k))))
      = ((2 * Real.pi : ℝ) : ℂ) * (∑ k : Fin K, g (-(scaleT j * (η + lam k)))) := by
    push_cast; ring
  calc ‖2 * Real.pi * ∑ k : Fin K, g (-(scaleT j * (η + lam k)))‖
      = 2 * Real.pi * ‖∑ k : Fin K, g (-(scaleT j * (η + lam k)))‖ := by
        rw [hZ, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    _ ≤ 2 * Real.pi * 4 := by
        have h2 : (0:ℝ) ≤ 2 * Real.pi := by positivity
        exact mul_le_mul_of_nonneg_left hsum h2
    _ = 8 * Real.pi := by ring



lemma scaleT_mono {j j' : ℕ} (h : j ≤ j') : scaleT j ≤ scaleT j' := by
  rw [scaleT, scaleT]
  exact pow_le_pow_right₀ (by norm_num) (by omega)

lemma scaleT_two_mul_le {j j' : ℕ} (h : j < j') : 2 * scaleT j ≤ scaleT j' := by
  have h2 : (2:ℝ) * 2 ^ (j+1) = 2 ^ (j+2) := by rw [pow_succ]; ring
  rw [scaleT, scaleT, h2]
  apply pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2)
  omega

lemma scaleT_inv_le_half (j : ℕ) : (scaleT j)⁻¹ ≤ 1/2 := by
  rw [inv_eq_one_div]
  exact one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 2) (scaleT_ge_two j)

/-- At most one dyadic scale `j` contributes to the annulus multiplier at a given frequency. -/
lemma at_most_one_scale {K : ℕ} {lam : Fin K → ℝ}
    (hsep : ∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|) {g : ℝ → ℂ}
    (hg_supp : ∀ θ : ℝ, ¬ ((1:ℝ)/2 < |θ| ∧ |θ| ≤ 1) → g θ = 0)
    (η : ℝ) {j j' : ℕ} (hj : ∃ k : Fin K, g (-(scaleT j * (η + lam k))) ≠ 0)
    (hj' : ∃ k : Fin K, g (-(scaleT j' * (η + lam k))) ≠ 0) : j = j' := by
  obtain ⟨k, hk⟩ := hj
  obtain ⟨k', hk'⟩ := hj'
  have hb : ∀ (m : ℕ) (l : Fin K), g (-(scaleT m * (η + lam l))) ≠ 0 →
      1/2 < scaleT m * |η + lam l| ∧ scaleT m * |η + lam l| ≤ 1 := by
    intro m l hl
    have hcon : 1/2 < |(-(scaleT m * (η + lam l)))| ∧
        |(-(scaleT m * (η + lam l)))| ≤ 1 := by
      by_contra hc
      exact hl (hg_supp _ hc)
    rw [abs_neg, abs_mul, abs_of_pos (scaleT_pos m)] at hcon
    exact hcon
  obtain ⟨hk1, hk2⟩ := hb j k hk
  obtain ⟨hk1', hk2'⟩ := hb j' k' hk'
  have htj : (0:ℝ) < scaleT j := scaleT_pos j
  have htj' : (0:ℝ) < scaleT j' := scaleT_pos j'
  -- one-sided bounds
  have hu2 : |η + lam k| ≤ (scaleT j)⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ htj, mul_comm]; exact hk2
  have hu2' : |η + lam k'| ≤ (scaleT j')⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ htj', mul_comm]; exact hk2'
  have hu1 : (scaleT j)⁻¹ / 2 < |η + lam k| := by
    have h := mul_lt_mul_of_pos_left hk1 (inv_pos.mpr htj)
    have h' : (scaleT j)⁻¹ * (scaleT j * |η + lam k|) = |η + lam k| := by
      rw [← mul_assoc, inv_mul_cancel₀ htj.ne', one_mul]
    rw [h'] at h
    calc (scaleT j)⁻¹ / 2 = (scaleT j)⁻¹ * (1/2) := by ring
      _ < |η + lam k| := h
  have hu1' : (scaleT j')⁻¹ / 2 < |η + lam k'| := by
    have h := mul_lt_mul_of_pos_left hk1' (inv_pos.mpr htj')
    have h' : (scaleT j')⁻¹ * (scaleT j' * |η + lam k'|) = |η + lam k'| := by
      rw [← mul_assoc, inv_mul_cancel₀ htj'.ne', one_mul]
    rw [h'] at h
    calc (scaleT j')⁻¹ / 2 = (scaleT j')⁻¹ * (1/2) := by ring
      _ < |η + lam k'| := h
  rcases eq_or_ne k k' with hkk | hkk
  · subst hkk
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have h2 : (scaleT j')⁻¹ ≤ (scaleT j)⁻¹ / 2 := by
        have hge := scaleT_two_mul_le hlt
        have h4 : (1:ℝ)/scaleT j' ≤ 1/(2*scaleT j) :=
          one_div_le_one_div_of_le (by positivity) hge
        rw [inv_eq_one_div]
        calc (1:ℝ)/scaleT j' ≤ 1/(2*scaleT j) := h4
          _ = (scaleT j)⁻¹/2 := by rw [inv_eq_one_div]; ring
      linarith [hu1, hu2']
    · have h2 : (scaleT j)⁻¹ ≤ (scaleT j')⁻¹ / 2 := by
        have hge := scaleT_two_mul_le hlt
        have h4 : (1:ℝ)/scaleT j ≤ 1/(2*scaleT j') :=
          one_div_le_one_div_of_le (by positivity) hge
        rw [inv_eq_one_div]
        calc (1:ℝ)/scaleT j ≤ 1/(2*scaleT j') := h4
          _ = (scaleT j')⁻¹/2 := by rw [inv_eq_one_div]; ring
      linarith [hu1', hu2]
  · -- different indices
    have h1 : (1:ℝ) ≤ |lam k - lam k'| := hsep k k' hkk
    have h2 : |lam k - lam k'| ≤ |η + lam k| + |η + lam k'| := by
      calc |lam k - lam k'| = |(η + lam k) - (η + lam k')| := by congr 1; ring
        _ ≤ |η + lam k| + |η + lam k'| := by
            simpa only [sub_zero, zero_sub, abs_neg] using
              abs_sub_le (η + lam k) 0 (η + lam k')
    have h3 : |η + lam k| + |η + lam k'| ≤ (scaleT j)⁻¹ + (scaleT j')⁻¹ := by linarith
    have h4 : (scaleT j)⁻¹ + (scaleT j')⁻¹ ≤ 1 := by
      linarith [scaleT_inv_le_half j, scaleT_inv_le_half j']
    have hsum1 : (scaleT j)⁻¹ + (scaleT j')⁻¹ = 1 := by linarith
    rcases lt_trichotomy j j' with hlt | heq | hgt
    · exfalso
      have hge := scaleT_two_mul_le hlt
      have h5 : (scaleT j')⁻¹ ≤ (scaleT j)⁻¹ / 2 := by
        have h6 : (1:ℝ)/scaleT j' ≤ 1/(2*scaleT j) :=
          one_div_le_one_div_of_le (by positivity) hge
        rw [inv_eq_one_div]
        calc (1:ℝ)/scaleT j' ≤ 1/(2*scaleT j) := h6
          _ = (scaleT j)⁻¹/2 := by rw [inv_eq_one_div]; ring
      have h7 : (scaleT j)⁻¹ ≤ 1/2 := scaleT_inv_le_half j
      linarith
    · exact heq
    · exfalso
      have hge := scaleT_two_mul_le hgt
      have h5 : (scaleT j)⁻¹ ≤ (scaleT j')⁻¹ / 2 := by
        have h6 : (1:ℝ)/scaleT j ≤ 1/(2*scaleT j') :=
          one_div_le_one_div_of_le (by positivity) hge
        rw [inv_eq_one_div]
        calc (1:ℝ)/scaleT j ≤ 1/(2*scaleT j') := h6
          _ = (scaleT j')⁻¹/2 := by rw [inv_eq_one_div]; ring
      have h7 : (scaleT j')⁻¹ ≤ 1/2 := scaleT_inv_le_half j'
      linarith



lemma annulusMul_ne_zero_imp {K : ℕ} {lam : Fin K → ℝ} {g : ℝ → ℂ} {j : ℕ} {η : ℝ}
    (h : annulusMul g lam j η ≠ 0) : ∃ k : Fin K, g (-(scaleT j * (η + lam k))) ≠ 0 := by
  by_contra hc
  push Not at hc
  exact h (by rw [annulusMul, Finset.sum_congr rfl (fun k _ => hc k), Finset.sum_const_zero,
    mul_zero])

lemma annulusMul_memLp {K : ℕ} {lam : Fin K → ℝ} {g : ℝ → ℂ} (hg : Measurable g)
    (hsep : ∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|)
    (hg_supp : ∀ θ : ℝ, ¬ ((1:ℝ)/2 < |θ| ∧ |θ| ≤ 1) → g θ = 0)
    (hg_bd : ∀ θ : ℝ, ‖g θ‖ ≤ 2) (j : ℕ) :
    MemLp (annulusMul g lam j) ⊤ (volume : Measure ℝ) := by
  refine memLp_top_of_bound ?_ (8 * Real.pi) ?_
  · exact (Measurable.const_mul (Finset.measurable_sum _ (fun k _ =>
      hg.comp (by fun_prop : Measurable (fun η : ℝ => -(scaleT j * (η + lam k)))))) _).aestronglyMeasurable
  · filter_upwards with η
    exact annulusMul_bound hsep hg_supp hg_bd η j

lemma annulusMul_tsum_le {K : ℕ} {lam : Fin K → ℝ} {g : ℝ → ℂ} (hg : Measurable g)
    (hsep : ∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|)
    (hg_supp : ∀ θ : ℝ, ¬ ((1:ℝ)/2 < |θ| ∧ |θ| ≤ 1) → g θ = 0)
    (hg_bd : ∀ θ : ℝ, ‖g θ‖ ≤ 2) (η : ℝ) :
    (∑' j : ℕ, ‖annulusMul g lam j η‖ₑ ^ (2:ℝ)) ≤ ENNReal.ofReal ((8 * Real.pi)^2) := by
  by_cases h : ∃ j : ℕ, annulusMul g lam j η ≠ 0
  · obtain ⟨j0, hj0⟩ := h
    have hzero : ∀ j : ℕ, j ≠ j0 → annulusMul g lam j η = 0 := by
      intro j hj
      by_contra hc
      exact hj (at_most_one_scale (j := j) (j' := j0) hsep hg_supp η
        (annulusMul_ne_zero_imp hc) (annulusMul_ne_zero_imp hj0))
    rw [tsum_eq_single j0 (fun j hj => by rw [hzero j hj]; simp)]
    have hb : ‖annulusMul g lam j0 η‖ₑ ^ (2:ℝ) ≤ ENNReal.ofReal ((8 * Real.pi)^2) := by
      have h1 : ‖annulusMul g lam j0 η‖ₑ ≤ ENNReal.ofReal (8 * Real.pi) := by
        rw [enorm_eq_nnnorm, ← ENNReal.ofReal_coe_nnreal, coe_nnnorm]
        exact ENNReal.ofReal_le_ofReal (annulusMul_bound hsep hg_supp hg_bd η j0)
      calc ‖annulusMul g lam j0 η‖ₑ ^ (2:ℝ)
          ≤ (ENNReal.ofReal (8 * Real.pi)) ^ (2:ℝ) := ENNReal.rpow_le_rpow h1 (by norm_num)
        _ = ENNReal.ofReal ((8 * Real.pi)^2) := by
            rw [ENNReal.rpow_two, ← ENNReal.ofReal_pow (by positivity)]
    exact hb
  · push Not at h
    simp [h]

/-- The annulus multiplier operator. -/
def annulusOp (K : ℕ) (lam : Fin K → ℝ) {g : ℝ → ℂ} (hg : Measurable g)
    (hsep : ∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|)
    (hg_supp : ∀ θ : ℝ, ¬ ((1:ℝ)/2 < |θ| ∧ |θ| ≤ 1) → g θ = 0)
    (hg_bd : ∀ θ : ℝ, ‖g θ‖ ≤ 2) (j : ℕ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    Lp ℂ 2 (volume : Measure ℝ) :=
  Commons.Analysis.Fourier.BoundaryLayer.multiplier (annulusMul g lam j)
    (annulusMul_memLp hg hsep hg_supp hg_bd j) f

/-- **The annulus part of the smooth window: the maximal band-sum is `L²`-bounded, uniformly
in the annulus profile `g`** (with `C = (8π)²`). -/
theorem annulus_multiplier_bandSum_maximal_l2 :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : ℕ) (lam : Fin K → ℝ)
      (hsep : ∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|),
      ∀ (g : ℝ → ℂ) (hg : Measurable g)
        (hg_supp : ∀ θ : ℝ, ¬ ((1:ℝ)/2 < |θ| ∧ |θ| ≤ 1) → g θ = 0)
        (hg_bd : ∀ θ : ℝ, ‖g θ‖ ≤ 2),
      ∀ (f : Lp ℂ 2 (volume : Measure ℝ)),
        ∫⁻ x, (⨆ j : ℕ, ‖(annulusOp K lam hg hsep hg_supp hg_bd j f
            : ℝ → ℂ) x‖ₑ) ^ (2:ℝ) ≤
          ENNReal.ofReal ((8 * Real.pi)^2) * ‖f‖ₑ ^ (2:ℝ) := by
  refine ⟨(8 * Real.pi)^2, by positivity, ?_⟩
  intro K lam hsep g hg hg_supp hg_bd f
  have hmemLp := fun j => annulusMul_memLp (K := K) hg hsep hg_supp hg_bd j
  have hmain := l2_multiplier_sum_square_function (ι := ℕ) (fun j => annulusMul g lam j)
    hmemLp f (8 * Real.pi) (fun η => annulusMul_tsum_le hg hsep hg_supp hg_bd η)
  have hfun : ∀ j : ℕ, annulusOp K lam hg hsep hg_supp hg_bd j f
      = Commons.Analysis.Fourier.BoundaryLayer.multiplier (annulusMul g lam j) (hmemLp j) f :=
    fun j => rfl
  calc ∫⁻ x, (⨆ j : ℕ, ‖(annulusOp K lam hg hsep hg_supp hg_bd j f
          : ℝ → ℂ) x‖ₑ) ^ (2:ℝ)
      = ∫⁻ x, (⨆ j : ℕ, ‖(Commons.Analysis.Fourier.BoundaryLayer.multiplier
          (annulusMul g lam j) (hmemLp j) f : ℝ → ℂ) x‖ₑ ^ (2:ℝ)) := by
        apply lintegral_congr; intro x
        rw [iSup_rpow_two]
        simp only [hfun]
    _ ≤ ∫⁻ x, ∑' j : ℕ, ‖(Commons.Analysis.Fourier.BoundaryLayer.multiplier
          (annulusMul g lam j) (hmemLp j) f : ℝ → ℂ) x‖ₑ ^ (2:ℝ) := by
        apply lintegral_mono; intro x
        exact iSup_le (fun j => ENNReal.le_tsum (f := fun j =>
          ‖(Commons.Analysis.Fourier.BoundaryLayer.multiplier
            (annulusMul g lam j) (hmemLp j) f : ℝ → ℂ) x‖ₑ ^ (2:ℝ)) j)
    _ ≤ ENNReal.ofReal ((8 * Real.pi)^2) * ‖f‖ₑ ^ (2:ℝ) := hmain


open SepWin

/-! ### The remainder term in the identification's frequency variable

`xiMul g lam j ξ = 2π ∑_k g(-t_j(2πξ+λ_k))` (with `t_j = 2^{j+1}`) is the annulus symbol in
the frequency variable `ξ` of `bandSum_eq_single_multiplier`.  For a profile `g` supported in the
annulus `{1/2 < |·| ≤ 1}` and bounded by `2`, at most one dyadic scale contributes at each `ξ`, so
`∑'_j ‖xiMul g lam j ξ‖² ≤ (8π)²` and the maximal multiplier is `L²`-bounded by `(8π)²`
**uniformly in `g`, `K` and the frequencies** — the elementary disjointness estimate that handles
the `φ - A` part of the window split, with no entropy input. -/

def xiMul {K : ℕ} (g : ℝ → ℂ) (lam : Fin K → ℝ) (j : ℕ) : ℝ → ℂ :=
  fun ξ => 2 * Real.pi * ∑ k : Fin K, g (-(scaleT j * (2 * Real.pi * ξ + lam k)))

lemma xiMul_bound {K : ℕ} {lam : Fin K → ℝ}
    (hsep : ∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|) {g : ℝ → ℂ}
    (hg_supp : ∀ θ : ℝ, ¬ ((1:ℝ)/2 < |θ| ∧ |θ| ≤ 1) → g θ = 0)
    (hg_bd : ∀ θ : ℝ, ‖g θ‖ ≤ 2) (ξ : ℝ) (j : ℕ) :
    ‖xiMul g lam j ξ‖ ≤ 8 * Real.pi := by
  rw [xiMul]
  have hS : (Finset.univ.filter
      (fun k : Fin K => |lam k - (-(2 * Real.pi * ξ))| ≤ (scaleT j)⁻¹)).card ≤ 2 := by
    have hr : (0:ℝ) < (scaleT j)⁻¹ := inv_pos.mpr (scaleT_pos j)
    have hr2 : 2 * (scaleT j)⁻¹ ≤ 1 := by
      have h2 := scaleT_ge_two j
      have h3 : (1:ℝ) / scaleT j ≤ 1 / 2 :=
        one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 2) h2
      rw [inv_eq_one_div]
      linarith
    exact card_le_two_separated hsep hr hr2
  have hzero : ∀ k : Fin K, ¬ (|lam k - (-(2 * Real.pi * ξ))| ≤ (scaleT j)⁻¹) →
      g (-(scaleT j * (2 * Real.pi * ξ + lam k))) = 0 := by
    intro k hk
    apply hg_supp
    intro hcon
    apply hk
    have h1 : scaleT j * |2 * Real.pi * ξ + lam k| ≤ 1 := by
      have := hcon.2
      rw [abs_neg, abs_mul, abs_of_pos (scaleT_pos j)] at this
      exact this
    rw [show lam k - (-(2 * Real.pi * ξ)) = 2 * Real.pi * ξ + lam k by ring,
      inv_eq_one_div, le_div_iff₀ (scaleT_pos j)]
    linarith [h1]
  have hsum : ‖∑ k : Fin K, g (-(scaleT j * (2 * Real.pi * ξ + lam k)))‖ ≤ 4 := by
    calc ‖∑ k : Fin K, g (-(scaleT j * (2 * Real.pi * ξ + lam k)))‖
        ≤ ∑ k : Fin K, ‖g (-(scaleT j * (2 * Real.pi * ξ + lam k)))‖ := norm_sum_le _ _
      _ = ∑ k ∈ (Finset.univ.filter (fun k : Fin K => |lam k - (-(2 * Real.pi * ξ))| ≤ (scaleT j)⁻¹)),
            ‖g (-(scaleT j * (2 * Real.pi * ξ + lam k)))‖ := by
          refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
          intro k _ hk
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
          rw [hzero k hk, norm_zero]
      _ ≤ ∑ k ∈ (Finset.univ.filter (fun k : Fin K => |lam k - (-(2 * Real.pi * ξ))| ≤ (scaleT j)⁻¹)),
            (2:ℝ) := by
          refine Finset.sum_le_sum (fun k _ => hg_bd _)
      _ = 2 * ((Finset.univ.filter
            (fun k : Fin K => |lam k - (-(2 * Real.pi * ξ))| ≤ (scaleT j)⁻¹)).card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ 2 * 2 := by
          have hcast : ((Finset.univ.filter
              (fun k : Fin K => |lam k - (-(2 * Real.pi * ξ))| ≤ (scaleT j)⁻¹)).card : ℝ) ≤ 2 := by
            exact_mod_cast hS
          linarith
      _ = 4 := by norm_num
  have hZ : (2:ℂ) * (Real.pi:ℂ) * (∑ k : Fin K, g (-(scaleT j * (2 * Real.pi * ξ + lam k))))
      = ((2 * Real.pi : ℝ) : ℂ) * (∑ k : Fin K, g (-(scaleT j * (2 * Real.pi * ξ + lam k)))) := by
    push_cast; ring
  calc ‖2 * Real.pi * ∑ k : Fin K, g (-(scaleT j * (2 * Real.pi * ξ + lam k)))‖
      = 2 * Real.pi * ‖∑ k : Fin K, g (-(scaleT j * (2 * Real.pi * ξ + lam k)))‖ := by
        rw [hZ, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ 2 * Real.pi)]
    _ ≤ 2 * Real.pi * 4 := by
        have h2 : (0:ℝ) ≤ 2 * Real.pi := by positivity
        exact mul_le_mul_of_nonneg_left hsum h2
    _ = 8 * Real.pi := by ring

lemma xiMul_memLp {K : ℕ} {lam : Fin K → ℝ} {g : ℝ → ℂ} (hg : Measurable g)
    (hsep : ∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|)
    (hg_supp : ∀ θ : ℝ, ¬ ((1:ℝ)/2 < |θ| ∧ |θ| ≤ 1) → g θ = 0)
    (hg_bd : ∀ θ : ℝ, ‖g θ‖ ≤ 2) (j : ℕ) :
    MemLp (xiMul g lam j) ⊤ (volume : Measure ℝ) := by
  refine memLp_top_of_bound ?_ (8 * Real.pi) ?_
  · exact (Measurable.const_mul (Finset.measurable_sum _ (fun k _ =>
      hg.comp (by fun_prop : Measurable (fun ξ : ℝ => -(scaleT j * (2 * Real.pi * ξ + lam k)))))) _).aestronglyMeasurable
  · filter_upwards with ξ
    exact xiMul_bound hsep hg_supp hg_bd ξ j

/-- At most one dyadic scale contributes at a given frequency `ξ`. -/
lemma xi_at_most_one_scale {K : ℕ} {lam : Fin K → ℝ}
    (hsep : ∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|) {g : ℝ → ℂ}
    (hg_supp : ∀ θ : ℝ, ¬ ((1:ℝ)/2 < |θ| ∧ |θ| ≤ 1) → g θ = 0)
    (ξ : ℝ) {j j' : ℕ}
    (hj : ∃ k : Fin K, g (-(scaleT j * (2 * Real.pi * ξ + lam k))) ≠ 0)
    (hj' : ∃ k : Fin K, g (-(scaleT j' * (2 * Real.pi * ξ + lam k))) ≠ 0) : j = j' := by
  have hsm : StrictMono (fun n : ℕ => (2:ℝ)^n) := by
    apply strictMono_nat_of_lt_succ
    intro n
    exact pow_lt_pow_right₀ (by norm_num) (Nat.lt_succ_self n)
  obtain ⟨k, hk⟩ := hj
  obtain ⟨k', hk'⟩ := hj'
  have hb : ∀ (m : ℕ) (l : Fin K), g (-(scaleT m * (2 * Real.pi * ξ + lam l))) ≠ 0 →
      1/2 < scaleT m * |2 * Real.pi * ξ + lam l| ∧ scaleT m * |2 * Real.pi * ξ + lam l| ≤ 1 := by
    intro m l hl
    have hcon : 1/2 < |(-(scaleT m * (2 * Real.pi * ξ + lam l)))| ∧
        |(-(scaleT m * (2 * Real.pi * ξ + lam l)))| ≤ 1 := by
      by_contra hc
      exact hl (hg_supp _ hc)
    rw [abs_neg, abs_mul, abs_of_pos (scaleT_pos m)] at hcon
    exact hcon
  obtain ⟨hk1, hk2⟩ := hb j k hk
  obtain ⟨hk1', hk2'⟩ := hb j' k' hk'
  have htj : (0:ℝ) < scaleT j := scaleT_pos j
  have htj' : (0:ℝ) < scaleT j' := scaleT_pos j'
  have hu2 : |2 * Real.pi * ξ + lam k| ≤ (scaleT j)⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ htj]; nlinarith [hk2]
  have hu2' : |2 * Real.pi * ξ + lam k'| ≤ (scaleT j')⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ htj']; nlinarith [hk2']
  have hu1 : (scaleT j)⁻¹ / 2 < |2 * Real.pi * ξ + lam k| := by
    have h := mul_lt_mul_of_pos_left hk1 (inv_pos.mpr htj)
    have h' : (scaleT j)⁻¹ * (scaleT j * |2 * Real.pi * ξ + lam k|) = |2 * Real.pi * ξ + lam k| := by
      rw [← mul_assoc, inv_mul_cancel₀ htj.ne', one_mul]
    rw [h'] at h
    calc (scaleT j)⁻¹ / 2 = (scaleT j)⁻¹ * (1/2) := by ring
      _ < |2 * Real.pi * ξ + lam k| := h
  have hu1' : (scaleT j')⁻¹ / 2 < |2 * Real.pi * ξ + lam k'| := by
    have h := mul_lt_mul_of_pos_left hk1' (inv_pos.mpr htj')
    have h' : (scaleT j')⁻¹ * (scaleT j' * |2 * Real.pi * ξ + lam k'|) = |2 * Real.pi * ξ + lam k'| := by
      rw [← mul_assoc, inv_mul_cancel₀ htj'.ne', one_mul]
    rw [h'] at h
    calc (scaleT j')⁻¹ / 2 = (scaleT j')⁻¹ * (1/2) := by ring
      _ < |2 * Real.pi * ξ + lam k'| := h
  rcases eq_or_ne k k' with hkk | hkk
  · -- same frequency: `t_j/2 < t_{j'} < 2 t_j`, and both are powers of `2` `≥ 2`
    subst hkk
    have hlt : (scaleT j)⁻¹ / 2 < (scaleT j')⁻¹ := by linarith [hu1, hu2']
    have hlt2 : (scaleT j')⁻¹ / 2 < (scaleT j)⁻¹ := by linarith [hu1', hu2]
    have hA : scaleT j' < 2 * scaleT j := by
      have h : (2 * scaleT j)⁻¹ < (scaleT j')⁻¹ := by
        rw [show (2 * scaleT j)⁻¹ = (scaleT j)⁻¹ / 2 by field_simp]
        exact hlt
      exact (inv_lt_inv₀ (a := 2 * scaleT j) (b := scaleT j') (by positivity) (scaleT_pos j')).mp h
    have hB : scaleT j < 2 * scaleT j' := by
      have h : (2 * scaleT j')⁻¹ < (scaleT j)⁻¹ := by
        rw [show (2 * scaleT j')⁻¹ = (scaleT j')⁻¹ / 2 by field_simp]
        exact hlt2
      exact (inv_lt_inv₀ (a := 2 * scaleT j') (b := scaleT j) (by positivity) (scaleT_pos j)).mp h
    have hA' : (2:ℝ)^(j'+1) < (2:ℝ)^(j+1+1) := by
      have h2 : (2:ℝ)^(j+1+1) = 2 * scaleT j := by rw [scaleT, pow_succ]; ring
      rw [h2]; exact hA
    have hB' : (2:ℝ)^(j+1) < (2:ℝ)^(j'+1+1) := by
      have h2 : (2:ℝ)^(j'+1+1) = 2 * scaleT j' := by rw [scaleT, pow_succ]; ring
      rw [h2]; exact hB
    have h1 : j' + 1 < j + 1 + 1 := hsm.lt_iff_lt.mp hA'
    have h2 : j + 1 < j' + 1 + 1 := hsm.lt_iff_lt.mp hB'
    omega
  · -- different frequencies: `t_j = t_{j'} = 2`
    have h1 : (1:ℝ) ≤ |lam k - lam k'| := hsep k k' hkk
    have h2 : |lam k - lam k'| ≤ |2 * Real.pi * ξ + lam k| + |2 * Real.pi * ξ + lam k'| := by
      have h := abs_sub_le (2 * Real.pi * ξ + lam k) 0 (2 * Real.pi * ξ + lam k')
      simp only [sub_zero, zero_sub, abs_neg] at h
      have heq : (2 * Real.pi * ξ + lam k) - (2 * Real.pi * ξ + lam k') = lam k - lam k' := by ring
      rw [heq] at h
      exact h
    have h4 : (scaleT j)⁻¹ ≤ 1/2 := scaleT_inv_le_half j
    have h5 : (scaleT j')⁻¹ ≤ 1/2 := scaleT_inv_le_half j'
    have h3 : (scaleT j)⁻¹ + (scaleT j')⁻¹ ≤ 1 := by linarith
    have h6 : (1:ℝ) ≤ (scaleT j)⁻¹ + (scaleT j')⁻¹ := by linarith [h1, h2, hu2, hu2']
    have h7 : (scaleT j)⁻¹ = 1/2 := by linarith
    have h8 : (scaleT j')⁻¹ = 1/2 := by linarith
    have hj2 : scaleT j = 2 := by
      rw [← inv_inv (scaleT j), h7]; norm_num
    have hj'2 : scaleT j' = 2 := by
      rw [← inv_inv (scaleT j'), h8]; norm_num
    have : j + 1 = j' + 1 := hsm.injective (by rw [← scaleT, ← scaleT]; rw [hj2, hj'2])
    omega

lemma xiMul_tsum_le {K : ℕ} {lam : Fin K → ℝ}
    (hsep : ∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|) {g : ℝ → ℂ} (hg : Measurable g)
    (hg_supp : ∀ θ : ℝ, ¬ ((1:ℝ)/2 < |θ| ∧ |θ| ≤ 1) → g θ = 0)
    (hg_bd : ∀ θ : ℝ, ‖g θ‖ ≤ 2) (ξ : ℝ) :
    (∑' j : ℕ, ‖xiMul g lam j ξ‖ₑ ^ (2:ℝ)) ≤ ENNReal.ofReal ((8 * Real.pi)^2) := by
  by_cases h : ∃ j : ℕ, xiMul g lam j ξ ≠ 0
  · obtain ⟨j0, hj0⟩ := h
    have hne : ∃ k : Fin K, g (-(scaleT j0 * (2 * Real.pi * ξ + lam k))) ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hj0 (by rw [xiMul, Finset.sum_congr rfl (fun k _ => hc k), Finset.sum_const_zero, mul_zero])
    have hzero : ∀ j : ℕ, j ≠ j0 → xiMul g lam j ξ = 0 := by
      intro j hj
      by_contra hc
      have hk : ∃ k : Fin K, g (-(scaleT j * (2 * Real.pi * ξ + lam k))) ≠ 0 := by
        by_contra hcc
        push Not at hcc
        exact hc (by rw [xiMul, Finset.sum_congr rfl (fun k _ => hcc k), Finset.sum_const_zero, mul_zero])
      exact hj (xi_at_most_one_scale hsep hg_supp ξ hk hne)
    rw [tsum_eq_single j0 (fun j hj => by rw [hzero j hj]; simp)]
    have hb : ‖xiMul g lam j0 ξ‖ₑ ^ (2:ℝ) ≤ ENNReal.ofReal ((8 * Real.pi)^2) := by
      have h1 : ‖xiMul g lam j0 ξ‖ₑ ≤ ENNReal.ofReal (8 * Real.pi) := by
        rw [enorm_eq_nnnorm, ← ENNReal.ofReal_coe_nnreal, coe_nnnorm]
        exact ENNReal.ofReal_le_ofReal (xiMul_bound hsep hg_supp hg_bd ξ j0)
      calc ‖xiMul g lam j0 ξ‖ₑ ^ (2:ℝ)
          ≤ (ENNReal.ofReal (8 * Real.pi)) ^ (2:ℝ) := ENNReal.rpow_le_rpow h1 (by norm_num)
        _ = ENNReal.ofReal ((8 * Real.pi)^2) := by
            rw [ENNReal.rpow_two, ← ENNReal.ofReal_pow (by positivity)]
    exact hb
  · push Not at h
    simp [h]

/-- The annulus (remainder) part of the smooth-window maximal estimate, in the identification's
frequency variable: the maximal band-sum is `L²`-bounded with the absolute constant `(8π)²`,
uniformly in the annulus profile `g`, the number `K` and the frequencies. -/
theorem xi_multiplier_maximal_l2 {K : ℕ} {lam : Fin K → ℝ}
    (hsep : ∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|)
    {g : ℝ → ℂ} (hg : Measurable g)
    (hg_supp : ∀ θ : ℝ, ¬ ((1:ℝ)/2 < |θ| ∧ |θ| ≤ 1) → g θ = 0)
    (hg_bd : ∀ θ : ℝ, ‖g θ‖ ≤ 2) :
    ∀ (f : Lp ℂ 2 (volume : Measure ℝ)),
      ∫⁻ x, (⨆ j : ℕ, ‖(BoundaryLayer.multiplier (xiMul g lam j)
          (xiMul_memLp hg hsep hg_supp hg_bd j) f : ℝ → ℂ) x‖ₑ) ^ (2:ℝ) ≤
        ENNReal.ofReal ((8 * Real.pi)^2) * ‖f‖ₑ ^ (2:ℝ) := by
  intro f
  have hmain := l2_multiplier_sum_square_function (ι := ℕ) (fun j => xiMul g lam j)
    (fun j => xiMul_memLp hg hsep hg_supp hg_bd j) f (8 * Real.pi)
    (fun ξ => xiMul_tsum_le hsep hg hg_supp hg_bd ξ)
  calc ∫⁻ x, (⨆ j : ℕ, ‖(BoundaryLayer.multiplier (xiMul g lam j)
          (xiMul_memLp hg hsep hg_supp hg_bd j) f : ℝ → ℂ) x‖ₑ) ^ (2:ℝ)
      = ∫⁻ x, (⨆ j : ℕ, ‖(BoundaryLayer.multiplier (xiMul g lam j)
          (xiMul_memLp hg hsep hg_supp hg_bd j) f : ℝ → ℂ) x‖ₑ ^ (2:ℝ)) := by
        apply lintegral_congr; intro x
        rw [iSup_rpow_two]
    _ ≤ ∫⁻ x, ∑' j : ℕ, ‖(BoundaryLayer.multiplier (xiMul g lam j)
          (xiMul_memLp hg hsep hg_supp hg_bd j) f : ℝ → ℂ) x‖ₑ ^ (2:ℝ) := by
        apply lintegral_mono; intro x
        exact iSup_le (fun j => ENNReal.le_tsum (f := fun j =>
          ‖(BoundaryLayer.multiplier (xiMul g lam j)
            (xiMul_memLp hg hsep hg_supp hg_bd j) f : ℝ → ℂ) x‖ₑ ^ (2:ℝ)) j)
    _ ≤ ENNReal.ofReal ((8 * Real.pi)^2) * ‖f‖ₑ ^ (2:ℝ) := hmain


/-- Integrability of `y ↦ f y · k (x - y)` for `f, k ∈ L²` (Cauchy–Schwarz). -/
lemma integrable_mul_comp_sub {f k : ℝ → ℂ} (hf : MemLp f 2 (volume : Measure ℝ))
    (hk : MemLp k 2 (volume : Measure ℝ)) (x : ℝ) :
    Integrable (fun y : ℝ => f y * k (x - y)) (volume : Measure ℝ) := by
  have hk' : MemLp (fun y : ℝ => k (x - y)) 2 (volume : Measure ℝ) :=
    hk.comp_measurePreserving (BoundaryLayer.mpSub x)
  exact hf.integrable_mul hk'

/-- Kernel splitting: `innerSmooth φ = innerSmooth A + innerBound A - innerBound φ`. -/
lemma innerSmooth_split {K : ℕ} (lam : Fin K → ℝ) (A φ : ℝ → ℝ)
    (hφ : Continuous φ) (hA : Continuous A) (j : ℕ) (z : ℝ) :
    innerSmooth φ K lam j z
      = innerSmooth A K lam j z + innerBound A K lam j z - innerBound φ K lam j z := by
  have hk : ∀ k : Fin K, (∫ θ in (lam k - hJ j)..(lam k + hJ j),
        (φ ((θ - lam k) / hJ j) : ℂ) * Complex.exp (-(Complex.I * (z : ℂ) * (θ : ℂ))))
      = (∫ θ in (lam k - hJ j)..(lam k + hJ j),
        (A ((θ - lam k) / hJ j) : ℂ) * Complex.exp (-(Complex.I * (z : ℂ) * (θ : ℂ))))
      + (∫ θ in (lam k - hJ j)..(lam k + hJ j),
        ((1 - A ((θ - lam k) / hJ j)) : ℂ) * Complex.exp (-(Complex.I * (z : ℂ) * (θ : ℂ))))
      - (∫ θ in (lam k - hJ j)..(lam k + hJ j),
        ((1 - φ ((θ - lam k) / hJ j)) : ℂ) * Complex.exp (-(Complex.I * (z : ℂ) * (θ : ℂ)))) := by
    intro k
    rw [← intervalIntegral.integral_add, ← intervalIntegral.integral_sub]
    · refine intervalIntegral.integral_congr (fun θ _ => ?_)
      push_cast; ring
    · exact Continuous.intervalIntegrable (by fun_prop) _ _
    · exact Continuous.intervalIntegrable (by fun_prop) _ _
    · exact Continuous.intervalIntegrable (by fun_prop) _ _
    · exact Continuous.intervalIntegrable (by fun_prop) _ _
  simp only [innerSmooth, innerBound]
  trans (∑ k : Fin K, ((∫ θ in (lam k - hJ j)..(lam k + hJ j),
        (A ((θ - lam k) / hJ j) : ℂ) * Complex.exp (-(Complex.I * (z : ℂ) * (θ : ℂ))))
      + (∫ θ in (lam k - hJ j)..(lam k + hJ j),
        ((1 - A ((θ - lam k) / hJ j)) : ℂ) * Complex.exp (-(Complex.I * (z : ℂ) * (θ : ℂ))))
      - (∫ θ in (lam k - hJ j)..(lam k + hJ j),
        ((1 - φ ((θ - lam k) / hJ j)) : ℂ) * Complex.exp (-(Complex.I * (z : ℂ) * (θ : ℂ))))))
  · exact Finset.sum_congr rfl (fun k _ => hk k)
  · rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]

/-- Operator splitting: `smoothOp φ f = smoothOp A f + boundOp A f - boundOp φ f`. -/
lemma smoothOp_split {K : ℕ} (lam : Fin K → ℝ) (A φ : ℝ → ℝ)
    (hφ : Continuous φ) (hA : Continuous A) (hφbd : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    (hAbd : ∀ x, 0 ≤ A x ∧ A x ≤ 1)
    (hφm : Measurable φ) (hAm : Measurable A)
    {f : ℝ → ℂ} (hf : MemLp f 2 (volume : Measure ℝ)) (j : ℕ) (x : ℝ) :
    smoothOp φ K lam f j x
      = smoothOp A K lam f j x + boundOp A K lam f j x - boundOp φ K lam f j x := by
  have h1 := integrable_mul_comp_sub hf (memLp_innerSmooth A hAm hAbd K lam j) x
  have h2 := integrable_mul_comp_sub hf (memLp_innerBound A hAm hAbd K lam j) x
  have h3 := integrable_mul_comp_sub hf (memLp_innerBound φ hφm hφbd K lam j) x
  have hfun : (fun y : ℝ => f y * innerSmooth φ K lam j (x - y))
      = (fun a : ℝ => ((fun y : ℝ => f y * innerSmooth A K lam j (x - y))
          + (fun y : ℝ => f y * innerBound A K lam j (x - y))) a
            - (fun y : ℝ => f y * innerBound φ K lam j (x - y)) a) := by
    funext y
    simp only [Pi.add_apply, Pi.sub_apply]
    rw [innerSmooth_split lam A φ hφ hA j (x - y)]
    ring
  simp only [smoothOp, boundOp]
  rw [hfun, integral_sub (h1.add h2) h3]
  simp only [Pi.add_apply]
  rw [integral_add h1 h2]

/-- `smoothOp` is the target's double integral. -/
lemma smoothOp_eq_target (φ : ℝ → ℝ) (K : ℕ) (lam : Fin K → ℝ) (f : ℝ → ℂ) (j : ℕ) (x : ℝ) :
    smoothOp φ K lam f j x = ∫ y : ℝ, f y * (∑ k : Fin K,
      ∫ θ in (lam k - (2:ℝ)^(-(j:ℝ)-1))..(lam k + (2:ℝ)^(-(j:ℝ)-1)),
        (φ ((θ - lam k) / (2:ℝ)^(-(j:ℝ)-1)) : ℂ) *
          Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ)))) := rfl

/-- A.e. measurability of the maximal function of `smoothOp`. -/
lemma aemeasurable_iSup_smoothOp (φ : ℝ → ℝ) (K : ℕ) (lam : Fin K → ℝ) (hφm : Measurable φ)
    (hbd : ∀ x : ℝ, 0 ≤ φ x ∧ φ x ≤ 1) {f : ℝ → ℂ} (hf : MemLp f 2 (volume : Measure ℝ)) :
    AEMeasurable (fun x : ℝ => (⨆ j : ℕ, ‖smoothOp φ K lam f j x‖ₑ) ^ (2:ℝ)) volume := by
  refine AEMeasurable.pow_const ?_ 2
  refine AEMeasurable.iSup (fun j => ?_)
  exact (aestronglyMeasurable_conv hf (measurable_innerSmooth φ hφm hbd K lam j)).aemeasurable.enorm

/-- A.e. measurability of the maximal function of `boundOp`. -/
lemma aemeasurable_iSup_boundOp (φ : ℝ → ℝ) (K : ℕ) (lam : Fin K → ℝ) (hφm : Measurable φ)
    (hbd : ∀ x : ℝ, 0 ≤ φ x ∧ φ x ≤ 1) {f : ℝ → ℂ} (hf : MemLp f 2 (volume : Measure ℝ)) :
    AEMeasurable (fun x : ℝ => (⨆ j : ℕ, ‖boundOp φ K lam f j x‖ₑ) ^ (2:ℝ)) volume := by
  refine AEMeasurable.pow_const ?_ 2
  refine AEMeasurable.iSup (fun j => ?_)
  exact (aestronglyMeasurable_conv hf (measurable_innerBound φ hφm hbd K lam j)).aemeasurable.enorm

/-! ### The `K = 1` case of the fixed-window maximal estimate

The simplest instance of the crux: for a *single* function the maximal band-pass operator is
bounded by an absolute constant, because the family `h_j Ψ(h_j ·)` is a sub-family of the full
dilation family `t⁻¹ • Ψ(·/t)`, `t > 0`, whose maximal function is the published
`maximal_dilation_convolution_l2`.  (This is the `K = 1` piece of Bourgain's Lemma 4.13; the
`K`-dependence is the genuine content.) -/

noncomputable def winKc (Ψ : SchwartzMap ℝ ℂ) (j : ℕ) : ℝ → ℂ :=
  fun u => (((2:ℝ)^(-(j:ℝ)-1) : ℝ) : ℂ) * (Ψ ((2:ℝ)^(-(j:ℝ)-1) * u))
theorem crux_K1 (Ψ : SchwartzMap ℝ ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (H : ℝ → ℂ), MemLp H 2 (volume : Measure ℝ) →
      (∫⁻ x, (⨆ j : ℕ, ‖∫ y : ℝ, H y * winKc Ψ j (x - y)‖ₑ) ^ (2:ℝ))
        ≤ ENNReal.ofReal C * (∫⁻ x, ‖H x‖ₑ ^ (2:ℝ)) := by
  obtain ⟨C, hCpos, hC⟩ := maximal_dilation_convolution_l2 Ψ
  refine ⟨C, hCpos, fun H hH => ?_⟩
  refine le_trans ?_ (hC H hH)
  apply lintegral_mono; intro x
  refine ENNReal.rpow_le_rpow ?_ (by norm_num)
  refine iSup_le (fun j => ?_)
  have ht : (0:ℝ) < ((2:ℝ)^(-(j:ℝ)-1))⁻¹ := inv_pos.mpr (Real.rpow_pos_of_pos (by norm_num) _)
  have heq : (∫ y : ℝ, H y * winKc Ψ j (x - y))
      = ∫ y : ℝ, H y * ((((2:ℝ)^(-(j:ℝ)-1))⁻¹ : ℝ)⁻¹ • (Ψ : ℝ → ℂ)
          ((x - y) / ((2:ℝ)^(-(j:ℝ)-1))⁻¹)) := by
    apply integral_congr_ae
    filter_upwards with y
    simp only [winKc, Complex.real_smul, div_eq_mul_inv]
    congr 1
    rw [inv_inv]
    ring
  rw [heq]
  exact le_iSup (fun t : {t : ℝ // 0 < t} => ‖∫ y : ℝ, H y *
      ((t : ℝ)⁻¹ • (Ψ : ℝ → ℂ) ((x - y) / (t : ℝ)))‖ₑ) ⟨((2:ℝ)^(-(j:ℝ)-1))⁻¹, ht⟩

/-! ### Bourgain's geometric bootstrap (the iteration half of the crux)

`iterate_bound` is the iteration engine of the fixed-window maximal estimate: given
* the **one-step** inequality `bandMax H ≤ A · bandSq H + bandMax (H - T_y H)` (a fixed shift `y`),
* the **contraction** `bandSq (H - T_y H) ≤ ρ · bandSq H` for that same `y`,
* the **a priori bound** `bandMax H ≤ CK · bandSq H`,
the maximal estimate follows with the geometric constant `A/(1-ρ)`.  Everything in this lemma is
elementary `ℝ≥0∞` arithmetic; the content of the crux is the *one-step* inequality, whose two
inputs are the published entropy chain and the published translation contraction. -/

/-- **Geometric iteration (Bourgain's bootstrap).**  If
`M n ≤ A · S n + M (n+1)`, `S (n+1) ≤ ρ · S n`, `M n ≤ CK · S n` and `S 0 < ∞`, then
`M 0 ≤ A/(1-ρ) · S 0`. -/
theorem iterate_bound {M S : ℕ → ℝ≥0∞} {A ρ CK : ℝ}
    (hA : 0 ≤ A) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hCK : 0 ≤ CK) (hfin : S 0 < ⊤)
    (hrec : ∀ n, M n ≤ ENNReal.ofReal A * S n + M (n+1))
    (hSdec : ∀ n, S (n+1) ≤ ENNReal.ofReal ρ * S n)
    (htail : ∀ n, M n ≤ ENNReal.ofReal CK * S n) :
    M 0 ≤ ENNReal.ofReal (A / (1 - ρ)) * S 0 := by
  have hpow_le_one : ∀ n, (ENNReal.ofReal ρ) ^ n ≤ 1 := fun n =>
    pow_le_one₀ (by simp) (by rw [ENNReal.ofReal_le_one]; linarith)
  have hSpow : ∀ n, S n ≤ (ENNReal.ofReal ρ) ^ n * S 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        calc S (n+1) ≤ ENNReal.ofReal ρ * S n := hSdec n
          _ ≤ ENNReal.ofReal ρ * ((ENNReal.ofReal ρ) ^ n * S 0) := mul_le_mul_right ih _
          _ = (ENNReal.ofReal ρ) ^ (n+1) * S 0 := by ring
  have hSn_fin : ∀ n, S n < ⊤ := fun n =>
    lt_of_le_of_lt (le_trans (hSpow n) (by
      simpa using mul_le_mul_left (hpow_le_one n) (S 0))) hfin
  have hsum : ∀ n, M 0 ≤ (∑ i ∈ Finset.range n, ENNReal.ofReal A * S i) + M n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        calc M 0 ≤ (∑ i ∈ Finset.range n, ENNReal.ofReal A * S i) + M n := ih
          _ ≤ (∑ i ∈ Finset.range n, ENNReal.ofReal A * S i)
                + (ENNReal.ofReal A * S n + M (n+1)) := add_le_add_right (hrec n) _
          _ = (∑ i ∈ Finset.range n, ENNReal.ofReal A * S i) + ENNReal.ofReal A * S n + M (n+1) := by
              ring
          _ = (∑ i ∈ Finset.range (n+1), ENNReal.ofReal A * S i) + M (n+1) := by
              rw [Finset.sum_range_succ]
  have hcast : ∀ n, (∑ i ∈ Finset.range n, ENNReal.ofReal A * S i) + M n
      ≤ ENNReal.ofReal (A * (∑ i ∈ Finset.range n, ρ ^ i) + CK * ρ ^ n) * S 0 := by
    intro n
    have h1 : (∑ i ∈ Finset.range n, ENNReal.ofReal A * S i)
        ≤ ENNReal.ofReal (A * (∑ i ∈ Finset.range n, ρ ^ i)) * S 0 := by
      calc (∑ i ∈ Finset.range n, ENNReal.ofReal A * S i)
          = ENNReal.ofReal A * (∑ i ∈ Finset.range n, S i) := (Finset.mul_sum _ _ _).symm
        _ ≤ ENNReal.ofReal A * (∑ i ∈ Finset.range n, (ENNReal.ofReal ρ) ^ i * S 0) :=
            mul_le_mul_right (Finset.sum_le_sum (fun i _ => hSpow i)) _
        _ = ENNReal.ofReal A * ((∑ i ∈ Finset.range n, (ENNReal.ofReal ρ) ^ i) * S 0) := by
            rw [Finset.sum_mul]
        _ = ENNReal.ofReal A * (ENNReal.ofReal (∑ i ∈ Finset.range n, ρ ^ i) * S 0) := by
            rw [show (∑ i ∈ Finset.range n, (ENNReal.ofReal ρ) ^ i)
                = ENNReal.ofReal (∑ i ∈ Finset.range n, ρ ^ i) from by
              rw [show (∑ i ∈ Finset.range n, (ENNReal.ofReal ρ) ^ i)
                  = ∑ i ∈ Finset.range n, ENNReal.ofReal (ρ ^ i) from
                Finset.sum_congr rfl (fun i _ => (ENNReal.ofReal_pow hρ0 i).symm),
                ← ENNReal.ofReal_sum_of_nonneg (fun i _ => pow_nonneg hρ0 i)]]
        _ = ENNReal.ofReal (A * (∑ i ∈ Finset.range n, ρ ^ i)) * S 0 := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul hA]
    have h2 : M n ≤ ENNReal.ofReal (CK * ρ ^ n) * S 0 := by
      calc M n ≤ ENNReal.ofReal CK * S n := htail n
        _ ≤ ENNReal.ofReal CK * ((ENNReal.ofReal ρ) ^ n * S 0) := mul_le_mul_right (hSpow n) _
        _ = ENNReal.ofReal CK * (ENNReal.ofReal (ρ ^ n) * S 0) := by
            rw [ENNReal.ofReal_pow hρ0 n]
        _ = ENNReal.ofReal (CK * ρ ^ n) * S 0 := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul hCK]
    calc (∑ i ∈ Finset.range n, ENNReal.ofReal A * S i) + M n
        ≤ ENNReal.ofReal (A * (∑ i ∈ Finset.range n, ρ ^ i)) * S 0
          + ENNReal.ofReal (CK * ρ ^ n) * S 0 := add_le_add h1 h2
      _ = (ENNReal.ofReal (A * (∑ i ∈ Finset.range n, ρ ^ i)) + ENNReal.ofReal (CK * ρ ^ n)) * S 0 := by
          ring
      _ = ENNReal.ofReal (A * (∑ i ∈ Finset.range n, ρ ^ i) + CK * ρ ^ n) * S 0 := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity)]
  -- the real sequence converges to `A/(1-ρ)`
  have hgeosum : Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, ρ ^ i) atTop (𝓝 ((1 - ρ)⁻¹)) :=
    (hasSum_geometric_of_lt_one hρ0 hρ1).tendsto_sum_nat
  have hlim : Tendsto (fun n : ℕ => A * (∑ i ∈ Finset.range n, ρ ^ i) + CK * ρ ^ n) atTop
      (𝓝 (A / (1 - ρ))) := by
    have h1 := hgeosum.const_mul A
    have h2 : Tendsto (fun n : ℕ => CK * ρ ^ n) atTop (𝓝 (CK * 0)) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).const_mul CK
    simpa only [mul_zero, add_zero, div_eq_mul_inv] using h1.add h2
  -- conclude
  refine ENNReal.le_of_forall_pos_le_add (fun ε hε _ => ?_)
  by_cases hS0zero : S 0 = 0
  · have h := le_trans (hsum 0) (hcast 0)
    simp only [Finset.range_zero, Finset.sum_empty, zero_add] at h
    rw [hS0zero, mul_zero] at h
    exact le_trans h (by simp)
  · have hS0pos : 0 < (S 0).toReal := ENNReal.toReal_pos_iff.mpr ⟨bot_lt_iff_ne_bot.mpr hS0zero, hfin⟩
    set δ : ℝ := ε.toReal / (S 0).toReal with hδ
    have hεpos : 0 < (ε : ℝ≥0∞).toReal := ENNReal.toReal_pos_iff.mpr
      ⟨bot_lt_iff_ne_bot.mpr (by simp [hε.ne']), ENNReal.coe_lt_top (r := ε)⟩
    have hδpos : 0 < δ := div_pos hεpos hS0pos
    have hδε : ENNReal.ofReal δ * S 0 ≤ ε := by
      have h1 : ENNReal.ofReal δ * S 0 = ENNReal.ofReal (δ * (S 0).toReal) := by
        conv_lhs => rw [← ENNReal.ofReal_toReal hfin.ne]
        rw [← ENNReal.ofReal_mul hδpos.le]
      rw [h1, show δ * (S 0).toReal = ε.toReal by rw [hδ]; field_simp]
      rw [show ε.toReal = (ε : ℝ) by simp]
      exact le_of_eq ENNReal.ofReal_coe_nnreal
    have hev : ∀ᶠ n : ℕ in atTop,
        A * (∑ i ∈ Finset.range n, ρ ^ i) + CK * ρ ^ n ≤ A / (1 - ρ) + δ :=
      (hlim.eventually (eventually_lt_nhds (by linarith))).mono (fun n hn => le_of_lt hn)
    obtain ⟨n, hn⟩ := hev.exists
    refine le_trans (le_iInf (fun m => le_trans (hsum m) (hcast m)) : M 0 ≤ _) ?_
    calc (⨅ m, ENNReal.ofReal (A * (∑ i ∈ Finset.range m, ρ ^ i) + CK * ρ ^ m) * S 0)
        ≤ ENNReal.ofReal (A * (∑ i ∈ Finset.range n, ρ ^ i) + CK * ρ ^ n) * S 0 := iInf_le _ n
      _ ≤ ENNReal.ofReal (A / (1 - ρ) + δ) * S 0 := mul_le_mul_left (ENNReal.ofReal_le_ofReal hn) _
      _ ≤ (ENNReal.ofReal (A / (1 - ρ)) + ENNReal.ofReal δ) * S 0 := by
          refine mul_le_mul_left ?_ _
          rw [ENNReal.ofReal_add (by positivity) hδpos.le]
      _ = ENNReal.ofReal (A / (1 - ρ)) * S 0 + ENNReal.ofReal δ * S 0 := by ring
      _ ≤ ENNReal.ofReal (A / (1 - ρ)) * S 0 + ε := add_le_add_right hδε _

/-- **The target reduces to the fixed-window (`A = bump`) estimate plus the boundary layer.**
Split `φ = A + (1-A) - (1-φ)` at the level of the convolution kernels; use the fixed-window
estimate for the `A`-part and the published `boundary_layer_l2` for the two boundary layers. -/
theorem smooth_window_of_fixed_bump
    (hcrux : ∃ CA : ℝ, 0 < CA ∧ ∀ (K : ℕ) (lam : Fin K → ℝ),
      (∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|) →
      ∀ (f : ℝ → ℂ), MemLp f 2 (volume : Measure ℝ) →
      (∫⁻ x, (⨆ j : ℕ, ‖smoothOp bump K lam f j x‖ₑ) ^ (2:ℝ))
        ≤ ENNReal.ofReal ((CA * (Real.log ((K:ℝ)+2))^2)^2) * (∫⁻ x, ‖f x‖ₑ^(2:ℝ))) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : ℕ) (lam : Fin K → ℝ),
      (∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|) →
      ∀ (φ : ℝ → ℝ), (∀ n : ℕ, ContDiff ℝ n φ) →
        (∀ x : ℝ, |x| ≤ 1 / 2 → φ x = 1) →
        (∀ x : ℝ, 1 ≤ |x| → φ x = 0) → (∀ x : ℝ, 0 ≤ φ x ∧ φ x ≤ 1) →
      ∀ (f : ℝ → ℂ), MemLp f 2 (volume : Measure ℝ) →
        (∫⁻ x, (⨆ j : ℕ, ‖∫ y : ℝ, f y * (∑ k : Fin K,
            ∫ θ in (lam k - (2:ℝ)^(-(j:ℝ)-1))..(lam k + (2:ℝ)^(-(j:ℝ)-1)),
              (φ ((θ - lam k) / (2:ℝ)^(-(j:ℝ)-1)) : ℂ) *
                Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ))))‖ₑ) ^ (2:ℝ))
          ≤ ENNReal.ofReal ((C * (Real.log ((K:ℝ)+2))^2)^2) * (∫⁻ x, ‖f x‖ₑ^(2:ℝ)) := by
  obtain ⟨CA, hCApos, hcrux⟩ := hcrux
  obtain ⟨Cb, hCbpos, hbl⟩ := boundary_layer_l2
  refine ⟨Real.sqrt (16 * CA^2 + 20 * Cb^2 / ((Real.log 2)^2)^2) + 1, by positivity, ?_⟩
  intro K lam hsep φ hφφ h1 h0 hbd f hf
  have hφc : Continuous φ := (hφφ 1).continuous
  have hφm : Measurable φ := hφc.measurable
  have hbc : Continuous bump := (bump_contDiff 1).continuous
  have hbm : Measurable bump := hbc.measurable
  -- pointwise bound
  have hpt : ∀ x : ℝ, (⨆ j : ℕ, ‖smoothOp φ K lam f j x‖ₑ) ^ (2:ℝ)
      ≤ 16 * ((⨆ j : ℕ, ‖smoothOp bump K lam f j x‖ₑ) ^ (2:ℝ))
        + 16 * ((⨆ j : ℕ, ‖boundOp bump K lam f j x‖ₑ) ^ (2:ℝ))
        + 4 * ((⨆ j : ℕ, ‖boundOp φ K lam f j x‖ₑ) ^ (2:ℝ)) := by
    intro x
    set A := ⨆ j : ℕ, ‖smoothOp bump K lam f j x‖ₑ with hA
    set B := ⨆ j : ℕ, ‖boundOp bump K lam f j x‖ₑ with hB
    set Cc := ⨆ j : ℕ, ‖boundOp φ K lam f j x‖ₑ with hC
    have hle : (⨆ j : ℕ, ‖smoothOp φ K lam f j x‖ₑ) ≤ A + B + Cc := by
      refine iSup_le (fun j => ?_)
      rw [smoothOp_split lam bump φ hφc hbc hbd bump_bounds hφm hbm hf j x]
      calc ‖smoothOp bump K lam f j x + boundOp bump K lam f j x - boundOp φ K lam f j x‖ₑ
          ≤ ‖smoothOp bump K lam f j x + boundOp bump K lam f j x‖ₑ
            + ‖boundOp φ K lam f j x‖ₑ := enorm_sub_le
        _ ≤ (‖smoothOp bump K lam f j x‖ₑ + ‖boundOp bump K lam f j x‖ₑ)
            + ‖boundOp φ K lam f j x‖ₑ := add_le_add_left (enorm_add_le _ _) _
        _ ≤ A + B + Cc :=
            add_le_add (add_le_add
              (le_iSup (fun j => ‖smoothOp bump K lam f j x‖ₑ) j)
              (le_iSup (fun j => ‖boundOp bump K lam f j x‖ₑ) j))
              (le_iSup (fun j => ‖boundOp φ K lam f j x‖ₑ) j)
    calc (⨆ j : ℕ, ‖smoothOp φ K lam f j x‖ₑ) ^ (2:ℝ)
        ≤ (A + B + Cc) ^ (2:ℝ) := ENNReal.rpow_le_rpow hle (by norm_num)
      _ ≤ 16 * A ^ (2:ℝ) + 16 * B ^ (2:ℝ) + 4 * Cc ^ (2:ℝ) := by
          refine le_trans (add_rpow_two_le (A + B) Cc) ?_
          refine le_trans (mul_le_mul_right (add_le_add_left
            (add_rpow_two_le A B) (Cc ^ (2:ℝ))) 4) ?_
          exact le_of_eq (by ring)
  -- integrate
  have hInt : (∫⁻ x, (⨆ j : ℕ, ‖smoothOp φ K lam f j x‖ₑ) ^ (2:ℝ))
      ≤ (16 * (∫⁻ x, (⨆ j : ℕ, ‖smoothOp bump K lam f j x‖ₑ) ^ (2:ℝ)))
        + (16 * (∫⁻ x, (⨆ j : ℕ, ‖boundOp bump K lam f j x‖ₑ) ^ (2:ℝ)))
        + (4 * (∫⁻ x, (⨆ j : ℕ, ‖boundOp φ K lam f j x‖ₑ) ^ (2:ℝ))) := by
    have ha := aemeasurable_iSup_smoothOp bump K lam hbm bump_bounds hf
    have hb := aemeasurable_iSup_boundOp bump K lam hbm bump_bounds hf
    have hc := aemeasurable_iSup_boundOp φ K lam hφm hbd hf
    calc ∫⁻ x, (⨆ j : ℕ, ‖smoothOp φ K lam f j x‖ₑ) ^ (2:ℝ)
        ≤ ∫⁻ x, (16 * ((⨆ j : ℕ, ‖smoothOp bump K lam f j x‖ₑ) ^ (2:ℝ))
            + 16 * ((⨆ j : ℕ, ‖boundOp bump K lam f j x‖ₑ) ^ (2:ℝ))
            + 4 * ((⨆ j : ℕ, ‖boundOp φ K lam f j x‖ₑ) ^ (2:ℝ))) := lintegral_mono hpt
      _ = (16 * (∫⁻ x, (⨆ j : ℕ, ‖smoothOp bump K lam f j x‖ₑ) ^ (2:ℝ)))
            + (16 * (∫⁻ x, (⨆ j : ℕ, ‖boundOp bump K lam f j x‖ₑ) ^ (2:ℝ)))
            + (4 * (∫⁻ x, (⨆ j : ℕ, ‖boundOp φ K lam f j x‖ₑ) ^ (2:ℝ))) := by
          rw [show (fun x : ℝ => 16 * ((⨆ j : ℕ, ‖smoothOp bump K lam f j x‖ₑ) ^ (2:ℝ))
                + 16 * ((⨆ j : ℕ, ‖boundOp bump K lam f j x‖ₑ) ^ (2:ℝ))
                + 4 * ((⨆ j : ℕ, ‖boundOp φ K lam f j x‖ₑ) ^ (2:ℝ)))
              = (fun a : ℝ =>
                  ((fun x : ℝ => 16 * ((⨆ j : ℕ, ‖smoothOp bump K lam f j x‖ₑ) ^ (2:ℝ))
                      + 16 * ((⨆ j : ℕ, ‖boundOp bump K lam f j x‖ₑ) ^ (2:ℝ))) a)
                  + ((fun x : ℝ => 4 * ((⨆ j : ℕ, ‖boundOp φ K lam f j x‖ₑ) ^ (2:ℝ))) a))
              from by funext a; rfl]
          rw [lintegral_add_left' (show AEMeasurable (fun x : ℝ =>
                16 * ((⨆ j : ℕ, ‖smoothOp bump K lam f j x‖ₑ) ^ (2:ℝ))
                + 16 * ((⨆ j : ℕ, ‖boundOp bump K lam f j x‖ₑ) ^ (2:ℝ))) volume from
              (ha.const_mul 16).add (hb.const_mul 16))]
          rw [show (fun x : ℝ => 16 * ((⨆ j : ℕ, ‖smoothOp bump K lam f j x‖ₑ) ^ (2:ℝ))
                  + 16 * ((⨆ j : ℕ, ‖boundOp bump K lam f j x‖ₑ) ^ (2:ℝ)))
              = (fun a : ℝ =>
                  ((fun x : ℝ => 16 * ((⨆ j : ℕ, ‖smoothOp bump K lam f j x‖ₑ) ^ (2:ℝ))) a)
                  + ((fun x : ℝ => 16 * ((⨆ j : ℕ, ‖boundOp bump K lam f j x‖ₑ) ^ (2:ℝ))) a))
              from by funext a; rfl]
          rw [lintegral_add_left' (show AEMeasurable (fun x : ℝ =>
                16 * ((⨆ j : ℕ, ‖smoothOp bump K lam f j x‖ₑ) ^ (2:ℝ))) volume from ha.const_mul 16)]
          rw [lintegral_const_mul'' 16 ha, lintegral_const_mul'' 16 hb, lintegral_const_mul'' 4 hc]
  have hcruxK := hcrux K lam hsep f hf
  -- the boundary layer bounds
  have hbnd : ∀ (ψ : ℝ → ℝ), (∀ x : ℝ, |x| ≤ 1 / 2 → ψ x = 1) →
      (∀ x : ℝ, 1 ≤ |x| → ψ x = 0) → (∀ x : ℝ, 0 ≤ ψ x ∧ ψ x ≤ 1) → Measurable ψ →
      (∫⁻ x, (⨆ j : ℕ, ‖boundOp ψ K lam f j x‖ₑ) ^ (2:ℝ))
        ≤ ENNReal.ofReal (Cb^2) * (∫⁻ x, ‖f x‖ₑ^(2:ℝ)) := by
    intro ψ hψ1 hψ0 hψbd hψm
    have hψ := hbl K lam hsep ψ hψ1 hψ0 hψbd f hf
    calc ∫⁻ x, (⨆ j : ℕ, ‖boundOp ψ K lam f j x‖ₑ) ^ (2:ℝ)
        ≤ ∫⁻ x, ∑' j : ℕ, ‖boundOp ψ K lam f j x‖ₑ ^ (2:ℝ) := by
            apply lintegral_mono; intro x
            show (⨆ j : ℕ, ‖boundOp ψ K lam f j x‖ₑ) ^ (2:ℝ)
              ≤ ∑' j : ℕ, ‖boundOp ψ K lam f j x‖ₑ ^ (2:ℝ)
            rw [iSup_rpow_two]
            exact iSup_le (fun j => ENNReal.le_tsum
              (f := fun j => ‖boundOp ψ K lam f j x‖ₑ ^ (2:ℝ)) j)
      _ = ∫⁻ x, ∑' j : ℕ, ENNReal.ofReal ‖boundOp ψ K lam f j x‖ ^ (2:ℝ) := by
            apply lintegral_congr; intro x
            exact tsum_congr (fun j => by rw [BoundaryLayer.enorm_eq_ofReal_norm])
      _ ≤ ENNReal.ofReal (Cb^2) * (∫⁻ x, ‖f x‖ₑ^(2:ℝ)) := by
            refine le_trans hψ (mul_le_mul_right ?_ (ENNReal.ofReal (Cb^2)))
            rw [show (∫⁻ x, ENNReal.ofReal ‖f x‖ ^ (2:ℝ)) = ∫⁻ x, ‖f x‖ₑ ^ (2:ℝ) from
              lintegral_congr (fun x => by rw [BoundaryLayer.enorm_eq_ofReal_norm])]
  have hLhs_eq : (∫⁻ x, (⨆ j : ℕ, ‖∫ y : ℝ, f y * (∑ k : Fin K,
            ∫ θ in (lam k - (2:ℝ)^(-(j:ℝ)-1))..(lam k + (2:ℝ)^(-(j:ℝ)-1)),
              (φ ((θ - lam k) / (2:ℝ)^(-(j:ℝ)-1)) : ℂ) *
                Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ))))‖ₑ) ^ (2:ℝ))
      = (∫⁻ x, (⨆ j : ℕ, ‖smoothOp φ K lam f j x‖ₑ) ^ (2:ℝ)) := rfl
  rw [hLhs_eq]
  have hLpos : (0:ℝ) < Real.log ((K:ℝ) + 2) :=
    Real.log_pos (by linarith [(show (0:ℝ) ≤ (K:ℝ) by positivity)])
  have h2pos : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hLge : Real.log 2 ≤ Real.log ((K:ℝ) + 2) :=
    Real.log_le_log (by norm_num) (by linarith [(show (0:ℝ) ≤ (K:ℝ) by positivity)])
  have hsq : ((Real.log 2)^2)^2 ≤ ((Real.log ((K:ℝ)+2))^2)^2 := by
    apply pow_le_pow_left₀ (by positivity)
    exact pow_le_pow_left₀ h2pos.le hLge 2
  set C0 := Real.sqrt (16 * CA^2 + 20 * Cb^2 / ((Real.log 2)^2)^2) with hC0
  have hC0nonneg : 0 ≤ C0 := Real.sqrt_nonneg _
  have hC0sq : (16 * CA^2 + 20 * Cb^2 / ((Real.log 2)^2)^2) ≤ C0^2 := by
    rw [hC0, Real.sq_sqrt (by positivity)]
  have hCsq : (16 * CA^2 + 20 * Cb^2 / ((Real.log ((K:ℝ)+2))^2)^2) ≤ (C0 + 1)^2 := by
    have h1' : 20 * Cb^2 / ((Real.log ((K:ℝ)+2))^2)^2 ≤ 20 * Cb^2 / ((Real.log 2)^2)^2 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hsq
    nlinarith [hC0sq, h1']
  calc (∫⁻ x, (⨆ j : ℕ, ‖smoothOp φ K lam f j x‖ₑ) ^ (2:ℝ))
      ≤ (16 * (∫⁻ x, (⨆ j : ℕ, ‖smoothOp bump K lam f j x‖ₑ) ^ (2:ℝ)))
        + (16 * (∫⁻ x, (⨆ j : ℕ, ‖boundOp bump K lam f j x‖ₑ) ^ (2:ℝ)))
        + (4 * (∫⁻ x, (⨆ j : ℕ, ‖boundOp φ K lam f j x‖ₑ) ^ (2:ℝ))) := hInt
    _ ≤ (16 * (ENNReal.ofReal ((CA * (Real.log ((K:ℝ)+2))^2)^2) * (∫⁻ x, ‖f x‖ₑ^(2:ℝ))))
        + (16 * (ENNReal.ofReal (Cb^2) * (∫⁻ x, ‖f x‖ₑ^(2:ℝ))))
        + (4 * (ENNReal.ofReal (Cb^2) * (∫⁻ x, ‖f x‖ₑ^(2:ℝ)))) := by
          refine add_le_add (add_le_add ?_ ?_) ?_
          · exact mul_le_mul_right hcruxK 16
          · exact mul_le_mul_right (hbnd bump bump_one bump_zero bump_bounds hbm) 16
          · exact mul_le_mul_right (hbnd φ h1 h0 hbd hφm) 4
    _ = ((16:ℝ≥0∞) * ENNReal.ofReal ((CA * (Real.log ((K:ℝ)+2))^2)^2)
          + 16 * ENNReal.ofReal (Cb^2) + 4 * ENNReal.ofReal (Cb^2))
        * (∫⁻ x, ‖f x‖ₑ^(2:ℝ)) := by
          rw [← mul_assoc, ← mul_assoc, ← mul_assoc, ← add_mul, ← add_mul]
    _ ≤ ENNReal.ofReal (((C0 + 1) * (Real.log ((K:ℝ)+2))^2)^2)
          * (∫⁻ x, ‖f x‖ₑ^(2:ℝ)) := by
          refine mul_le_mul_left ?_ (∫⁻ x, ‖f x‖ₑ^(2:ℝ))
          rw [show ((16:ℝ≥0∞) * ENNReal.ofReal ((CA * (Real.log ((K:ℝ)+2))^2)^2)
                + 16 * ENNReal.ofReal (Cb^2) + 4 * ENNReal.ofReal (Cb^2))
              = ENNReal.ofReal (16 * (CA * (Real.log ((K:ℝ)+2))^2)^2 + 16 * Cb^2 + 4 * Cb^2) from ?_]
          · apply ENNReal.ofReal_le_ofReal
            have hgoal : 16 * (CA * (Real.log ((K:ℝ)+2))^2)^2 + 16 * Cb^2 + 4 * Cb^2
                ≤ ((C0 + 1) * (Real.log ((K:ℝ)+2))^2)^2 := by
              have hL4 : (0:ℝ) < ((Real.log ((K:ℝ)+2))^2)^2 := by positivity
              have hkey := mul_le_mul_of_nonneg_right hCsq hL4.le
              have eI : (16 * CA^2 + 20 * Cb^2 / ((Real.log ((K:ℝ)+2))^2)^2)
                    * ((Real.log ((K:ℝ)+2))^2)^2 = 16 * CA^2 * ((Real.log ((K:ℝ)+2))^2)^2 + 20 * Cb^2 := by
                field_simp
              rw [eI] at hkey
              nlinarith [hkey]
            exact hgoal
          · rw [show (16:ℝ≥0∞) = ENNReal.ofReal 16 from by norm_num,
                show (4:ℝ≥0∞) = ENNReal.ofReal 4 from by norm_num]
            rw [← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 16),
                ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 16),
                ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4),
                ← ENNReal.ofReal_add (by positivity) (by positivity),
                ← ENNReal.ofReal_add (by positivity) (by positivity)]


/-- **Bourgain's smooth-window maximal estimate** (his §4, Lemma 4.13).  For `1`-separated
frequencies `lam : Fin K → ℝ` and a `C^∞` bump `φ` equal to `1` on `[-1/2,1/2]` and vanishing off
`[-1,1]`, the maximal function over the dyadic scales `2^{-j-1}` of the band-pass operators whose
symbols are the smooth bumps around the frequencies is bounded on `L²(ℝ)` by `C (log (K+2))²`. -/
theorem bourgain_smooth_window_maximal_l2 :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : ℕ) (lam : Fin K → ℝ),
      (∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|) →
      ∀ (φ : ℝ → ℝ), (∀ n : ℕ, ContDiff ℝ n φ) →
        (∀ x : ℝ, |x| ≤ 1 / 2 → φ x = 1) →
        (∀ x : ℝ, 1 ≤ |x| → φ x = 0) → (∀ x : ℝ, 0 ≤ φ x ∧ φ x ≤ 1) →
      ∀ (f : ℝ → ℂ), MeasureTheory.MemLp f 2 (MeasureTheory.volume : MeasureTheory.Measure ℝ) →
        ∫⁻ x, (⨆ j : ℕ, ‖∫ y : ℝ, f y *
            (∑ k : Fin K,
              ∫ θ in (lam k - (2 : ℝ) ^ (-(j : ℝ) - 1))..(lam k + (2 : ℝ) ^ (-(j : ℝ) - 1)),
                (φ ((θ - lam k) / (2 : ℝ) ^ (-(j : ℝ) - 1)) : ℂ) *
                  Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ))))‖ₑ) ^ (2 : ℝ)
          ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)
        ≤ ENNReal.ofReal ((C * (Real.log ((K : ℝ) + 2)) ^ 2) ^ 2)
          * ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
  obtain ⟨C, hCpos, hC⟩ := FixWin.FW_L2_uniform'
  exact smooth_window_of_fixed_bump ⟨C, hCpos, fun K lam hsep f hf => hC K lam hsep hf⟩

end

end Commons.Analysis.Fourier

