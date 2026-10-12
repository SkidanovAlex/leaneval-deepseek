import Mathlib.Analysis.Convolution
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.BoseB7AK.W1low.chat_sub_le
import Submission.Work.BoseBoxFock.PCFU.ChDKernelDefs
import Submission.Work.BoseBoxFock.chat_eq_kinFT_of_even
import Submission.Work.BoseBoxFock.kinRow_lattice_tauPhi
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section
open MeasureTheory
open scoped BigOperators

set_option maxHeartbeats 1000000

namespace Work.PCFU

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-!
# `Work.PCFU.chDpoisson_E` — the Poisson summation of the truncation kernel `E`

The `(D)`-channel kernel `chDkerE fu ℓ N = uvSmear fu (uvRad ℓ N) (W1fun v h ℓ) − W1fun v h ℓ`
has Fourier transform `(uvCut fu (uvRad ℓ N) − 1)·chat (W1fun v h ℓ)`, which is *compactly
supported in momentum*; its `χ_ℓ`-smearing `χ_ℓ ⋆ E` is therefore smooth and rapidly decreasing,
with a compactly supported rapidly decreasing Fourier transform.  The decay-based Poisson summation
`Work.BoseBoxFock.latSampling_decay` applied to `χ_ℓ ⋆ E` gives the asserted identity at once: the
left-hand side is the periodisation of `χ_ℓ ⋆ E` and the right-hand side is its Fourier series,
whose coefficients are `ℓ³·χ̂(ℓk)·(ζ_Λ(k) − 1)·Ŵ₁(k)`.
-/

/-! ## 0. Elementary lattice algebra -/

/-- `Work.BoseB4.vec m = 2π • latVec m`. -/
private lemma vec_eq_two_pi_smul_latVec (m : Fin 3 → ℤ) :
    Work.BoseB4.vec m = (2 * Real.pi) • Work.BoseBoxFock.latVec m := by
  refine PiLp.ext fun i => ?_
  simp only [Work.BoseB4.vec, Work.BoseBoxFock.latVec, WithLp.ofLp_smul, WithLp.ofLp_toLp,
    Pi.smul_apply, smul_eq_mul]

/-- `kmomInt ℓ m = (2π/ℓ) • latVec m`. -/
private lemma kmomInt_eq_smul (ℓ : ℝ) (m : Fin 3 → ℤ) :
    Work.BoseBoxFock.kmomInt ℓ m = (2 * Real.pi / ℓ) • Work.BoseBoxFock.latVec m := by
  rw [Work.BoseBoxFock.kmomInt, vec_eq_two_pi_smul_latVec, smul_smul]
  congr 1
  rw [div_eq_mul_inv]
  ring

/-- `x ^ (-(n : ℤ)) = (x ^ n)⁻¹`. -/
private lemma zpow_neg_nat (n : ℕ) (x : ℝ) : x ^ (-(n : ℤ)) = (x ^ n)⁻¹ := by
  rw [zpow_neg, zpow_natCast]

/-! ## 1. Analytic helpers -/

/-- The exponential phase is unimodular. -/
private lemma norm_exp_phase (p y : E3) :
    ‖Complex.exp (-(Complex.I * (inner ℝ p y : ℂ)))‖ = 1 := by
  rw [show -(Complex.I * ((inner ℝ p y : ℝ) : ℂ)) = ((-(inner ℝ p y) : ℝ) : ℂ) * Complex.I by
    push_cast; ring, Complex.norm_exp_ofReal_mul_I]

/-- Multiplying an `L¹` real function by the unimodular phase `e^{-i⟪p,·⟫}` preserves
integrability. -/
private lemma integrable_exp_mul_ofReal {f : E3 → ℝ} (hf : Integrable f) (p : E3) :
    Integrable (fun y : E3 => Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * (f y : ℂ)) := by
  refine (hf.ofReal).bdd_mul (c := 1) ?_ ?_
  · exact (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable
  · filter_upwards with y
    exact le_of_eq (norm_exp_phase p y)

/-- Linearity of `chat` in a difference. -/
private lemma chat_sub' {f g : E3 → ℝ} (hf : Integrable f) (hg : Integrable g) (p : E3) :
    Work.BoseFixR.chat (f - g) p = Work.BoseFixR.chat f p - Work.BoseFixR.chat g p := by
  simp only [Work.BoseFixR.chat, Submission.BoseGases.kinFT]
  have hfun : (fun y : E3 => Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * ((f - g) y : ℂ))
      = fun y : E3 => Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * (f y : ℂ)
          - Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * (g y : ℂ) := by
    funext y
    simp only [Pi.sub_apply]
    push_cast
    ring
  rw [hfun, integral_sub (integrable_exp_mul_ofReal hf p) (integrable_exp_mul_ofReal hg p),
    Complex.sub_re]

/-- `|chat W p| ≤ ∫|W|`. -/
private lemma abs_chat_le_integral_abs {W : E3 → ℝ} (hW : Integrable W) (p : E3) :
    |Work.BoseFixR.chat W p| ≤ ∫ x : E3, |W x| := by
  refine (Complex.abs_re_le_norm _).trans ?_
  calc ‖Submission.BoseGases.kinFT (fun y : E3 => ((W y : ℝ) : ℂ)) p‖
      ≤ ∫ y : E3, ‖Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * (W y : ℂ)‖ := by
        rw [Submission.BoseGases.kinFT]
        exact norm_integral_le_integral_norm _
    _ = ∫ y : E3, |W y| := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        show ‖Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * ((W y : ℝ) : ℂ)‖ = |W y|
        rw [norm_mul, norm_exp_phase, one_mul, Complex.norm_real, Real.norm_eq_abs]

/-- The norm of the complexification of a windowed convolution integral is the absolute value of
the real convolution integral. -/
private lemma norm_integral_ofReal_conv (χ g : E3 → ℝ) (u : E3) :
    ‖∫ x : E3, (χ x : ℂ) * ((g (u - x) : ℝ) : ℂ)‖ = |∫ x : E3, χ x * g (u - x)| := by
  rw [show (fun x : E3 => (χ x : ℂ) * ((g (u - x) : ℝ) : ℂ))
      = (fun x : E3 => ((χ x * g (u - x) : ℝ) : ℂ)) by
    funext x; push_cast; ring]
  rw [show (∫ x : E3, ((χ x * g (u - x) : ℝ) : ℂ)) = ((∫ x : E3, χ x * g (u - x) : ℝ) : ℂ)
      from integral_ofReal]
  rw [Complex.norm_real, Real.norm_eq_abs]

/-- Rapid decay of a continuous function with compact support. -/
private lemma abs_le_of_continuous_hasCompactSupport {f : E3 → ℝ} (hc : Continuous f)
    (hs : HasCompactSupport f) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : E3, ‖f x‖ ≤ C * (1 + ‖x‖) ^ (-(n : ℤ)) := by
  obtain ⟨R₀, hR₀⟩ := (Metric.isBounded_iff_subset_closedBall (0 : E3)).mp hs.isCompact.isBounded
  set R : ℝ := max R₀ 0 with hRdef
  have hRnn : 0 ≤ R := le_max_right _ _
  have hR : tsupport f ⊆ Metric.closedBall (0 : E3) R := by
    intro x hx
    have h := hR₀ hx
    rw [Metric.mem_closedBall, dist_zero_right] at h ⊢
    exact h.trans (le_max_left _ _)
  obtain ⟨M, hM⟩ := hs.isCompact.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max M 0 * (1 + R) ^ n, by positivity, fun x => ?_⟩
  by_cases hx : x ∈ tsupport f
  · have hxR : ‖x‖ ≤ R := by
      have h := hR hx
      rwa [Metric.mem_closedBall, dist_zero_right] at h
    have hb : ‖f x‖ ≤ max M 0 := (hM x hx).trans (le_max_left _ _)
    have h1 : (1 : ℝ) ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
    have h2 : (1 : ℝ) ≤ 1 + R := by linarith
    have key : ‖f x‖ * (1 + ‖x‖) ^ n ≤ max M 0 * (1 + R) ^ n :=
      mul_le_mul hb (pow_le_pow_left₀ (by linarith) (by linarith) n)
        (by positivity) (by positivity)
    calc ‖f x‖ = ‖f x‖ * (1 + ‖x‖) ^ n * ((1 + ‖x‖) ^ n)⁻¹ := by
          rw [mul_assoc, mul_inv_cancel₀ (by positivity), mul_one]
      _ ≤ (max M 0 * (1 + R) ^ n) * ((1 + ‖x‖) ^ n)⁻¹ :=
          mul_le_mul_of_nonneg_right key (by positivity)
      _ = max M 0 * (1 + R) ^ n * (1 + ‖x‖) ^ (-(n : ℤ)) := by
          rw [zpow_neg_nat n (1 + ‖x‖)]
  · rw [image_eq_zero_of_notMem_tsupport hx, norm_zero]
    exact mul_nonneg (by positivity) (by positivity)

/-- The function `x ↦ C·(1+‖x‖)^{-8}` is integrable on `ℝ³`. -/
private lemma integrable_const_mul_zpow8 (C : ℝ) :
    Integrable (fun x : E3 => C * (1 + ‖x‖) ^ (-(8 : ℤ))) := by
  have h1 : Integrable (fun x : E3 => (1 + ‖x‖) ^ (-(8 : ℝ))) :=
    integrable_one_add_norm (μ := volume) (E := E3) (r := 8) (by
      rw [finrank_euclideanSpace_fin]; norm_num)
  refine (h1.const_mul C).congr ?_
  filter_upwards with x
  congr 1
  rw [← Real.rpow_intCast (1 + ‖x‖) (-(8 : ℤ))]
  norm_num

/-! ## 2. The decay of a compactly windowed convolution

This is the one genuinely analytic input of the proof (the sibling statement
`Work.PCFU.conv_le_of_rapidDecay`), reproduced here as a local helper so that the assembly below
is self-contained. -/

/-- **Windowed decay.**  Convolving a compactly supported continuous `χ` with a rapidly decreasing
`f` produces a rapidly decreasing function. -/
private theorem conv_le_of_rapidDecay_aux {χ : E3 → ℝ} {f : E3 → ℂ} (hχc : Continuous χ)
    (hχs : HasCompactSupport χ) (hfm : AEStronglyMeasurable f volume)
    (hf : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x : E3, ‖f x‖ ≤ C * (1 + ‖x‖) ^ (-(n : ℤ))) :
    ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ u : E3,
      ‖∫ x : E3, (χ x : ℂ) * f (u - x)‖ ≤ C * (1 + ‖u‖) ^ (-(n : ℤ)) := by
  intro n
  obtain ⟨R₀, hR₀⟩ := (Metric.isBounded_iff_subset_closedBall (0 : E3)).mp hχs.isCompact.isBounded
  set R : ℝ := max R₀ 0 with hRdef
  have hRnn : 0 ≤ R := le_max_right _ _
  have hR : tsupport χ ⊆ Metric.closedBall (0 : E3) R := by
    intro x hx
    have h := hR₀ hx
    rw [Metric.mem_closedBall, dist_zero_right] at h ⊢
    exact h.trans (le_max_left _ _)
  obtain ⟨C, hC0, hC⟩ := hf n
  refine ⟨C * (1 + R) ^ n * (∫ x : E3, |χ x|), by positivity, fun u => ?_⟩
  have hpt : ∀ x : E3, |χ x| * ‖f (u - x)‖
      ≤ |χ x| * ((C * (1 + R) ^ n) * (1 + ‖u‖) ^ (-(n : ℤ))) := by
    intro x
    by_cases hx : x ∈ tsupport χ
    · have hxR : ‖x‖ ≤ R := by
        have h := hR hx
        rwa [Metric.mem_closedBall, dist_zero_right] at h
      have h1 : 1 + ‖u‖ ≤ (1 + ‖u - x‖) * (1 + R) := by
        have h2 : ‖u‖ ≤ ‖u - x‖ + ‖x‖ := by
          have h3 := norm_add_le (u - x) x
          rwa [sub_add_cancel] at h3
        nlinarith [hxR, norm_nonneg (u - x), norm_nonneg u]
      have h4 : (1 + ‖u‖) / (1 + R) ≤ 1 + ‖u - x‖ := (div_le_iff₀ (by linarith)).mpr h1
      have h3 : (1 + ‖u - x‖)⁻¹ ≤ (1 + R) / (1 + ‖u‖) := by
        have hpos : 0 < (1 + ‖u‖) / (1 + R) := by
          apply div_pos <;> linarith [norm_nonneg u, hRnn]
        have h5 : (1 + ‖u - x‖)⁻¹ ≤ ((1 + ‖u‖) / (1 + R))⁻¹ :=
          (inv_le_inv₀ (by linarith) hpos).mpr h4
        rwa [inv_div] at h5
      have h6 : (1 + ‖u - x‖) ^ (-(n : ℤ)) ≤ (1 + R) ^ n * (1 + ‖u‖) ^ (-(n : ℤ)) := by
        have hstep : ((1 + ‖u - x‖)⁻¹) ^ n ≤ ((1 + R) / (1 + ‖u‖)) ^ n :=
          pow_le_pow_left₀ (by positivity) h3 n
        rw [div_pow, div_eq_mul_inv, inv_pow] at hstep
        rw [zpow_neg_nat, zpow_neg_nat]
        exact hstep
      have hfbound : ‖f (u - x)‖ ≤ (C * (1 + R) ^ n) * (1 + ‖u‖) ^ (-(n : ℤ)) := by
        calc ‖f (u - x)‖ ≤ C * (1 + ‖u - x‖) ^ (-(n : ℤ)) := hC (u - x)
          _ ≤ C * ((1 + R) ^ n * (1 + ‖u‖) ^ (-(n : ℤ))) :=
              mul_le_mul_of_nonneg_left h6 hC0
          _ = (C * (1 + R) ^ n) * (1 + ‖u‖) ^ (-(n : ℤ)) := by ring
      exact mul_le_mul_of_nonneg_left hfbound (abs_nonneg _)
    · rw [image_eq_zero_of_notMem_tsupport hx]
      simp
  calc ‖∫ x : E3, (χ x : ℂ) * f (u - x)‖
      ≤ ∫ x : E3, ‖(χ x : ℂ) * f (u - x)‖ := norm_integral_le_integral_norm _
    _ = ∫ x : E3, |χ x| * ‖f (u - x)‖ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        show ‖(χ x : ℂ) * f (u - x)‖ = |χ x| * ‖f (u - x)‖
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ ∫ x : E3, |χ x| * ((C * (1 + R) ^ n) * (1 + ‖u‖) ^ (-(n : ℤ))) := by
        have hInt : Integrable
            (fun x : E3 => |χ x| * ((C * (1 + R) ^ n) * (1 + ‖u‖) ^ (-(n : ℤ)))) :=
          (hχc.integrable_of_hasCompactSupport hχs).abs.mul_const _
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => by positivity) hInt ?_
        filter_upwards with x
        exact hpt x
    _ = (∫ x : E3, |χ x|) * ((C * (1 + R) ^ n) * (1 + ‖u‖) ^ (-(n : ℤ))) := by
        rw [integral_mul_const]
    _ = (C * (1 + R) ^ n * (∫ x : E3, |χ x|)) * (1 + ‖u‖) ^ (-(n : ℤ)) := by ring

/-! ## 3. The target -/

theorem chDpoisson_E {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {fu : Work.BoseBoxFix.LowCut} {ℓ : ℝ} (hℓ : 0 < ℓ) {N : ℕ} (hN : 1 ≤ N)
    (hI : MeasureTheory.Integrable (Work.BoseFixR.W1fun v h ℓ))
    (hcs : HasCompactSupport (Work.BoseFixR.W1fun v h ℓ))
    (hev : ∀ x, Work.BoseFixR.W1fun v h ℓ (-x) = Work.BoseFixR.W1fun v h ℓ x)
    (z : EuclideanSpace ℝ (Fin 3)) :
    (∑' d : Fin 3 → ℤ, Work.BoseBoxFock.PCFU.chDconv ℓ
        (fun u => ((Work.BoseBoxFock.PCFU.chDkerE (h := h) fu ℓ N u : ℝ) : ℂ))
        (z + ℓ • Work.BoseBoxFock.latVec d))
      = ∑' m : Fin 3 → ℤ,
          (((Work.BoseBoxFock.uvCut fu (Work.BoseBoxFock.uvRad ℓ N)
              (Work.BoseBoxFock.kmomInt ℓ m) - 1 : ℝ)) : ℂ)
            * (((Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ)
                  (Work.BoseBoxFock.kmomInt ℓ m)) : ℝ) : ℂ)
            * (((Work.BoseK15.corpusBox.hatChi (ℓ • Work.BoseBoxFock.kmomInt ℓ m)) : ℝ) : ℂ)
            * Complex.exp (Complex.I * (inner ℝ (Work.BoseBoxFock.kmomInt ℓ m) z : ℂ)) := by
  classical
  -- ## abbreviations
  set W : E3 → ℝ := Work.BoseFixR.W1fun v h ℓ with hW
  set Λ : ℝ := Work.BoseBoxFock.uvRad ℓ N with hΛ
  set χ : E3 → ℝ := Work.BoseK15.corpusBox.chiLam ℓ with hχ
  set S : E3 → ℝ := Work.BoseBoxFock.uvSmear fu Λ W with hS
  set GS : E3 → ℝ := fun u => ∫ x, χ x * S (u - x) with hGS
  set GW : E3 → ℝ := fun u => ∫ x, χ x * W (u - x) with hGW
  set F : E3 → ℂ := fun u => ((GS u : ℝ) : ℂ) - ((GW u : ℝ) : ℂ) with hF
  -- ## basic facts
  have hΛpos : 0 < Λ := by
    rw [hΛ, Work.BoseBoxFock.uvRad]
    have hN' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    positivity
  have hWint : Integrable W := by rw [hW]; exact hI
  have hWcs : HasCompactSupport W := by rw [hW]; exact hcs
  have hWev : ∀ x, W (-x) = W x := by intro x; rw [hW]; exact hev x
  have hWloc : LocallyIntegrable W volume := hWint.locallyIntegrable
  have hχcont : Continuous χ := by rw [hχ]; exact Work.BoseK15.corpusBox.chiLam_cont ℓ
  have hχcs : HasCompactSupport χ := by
    rw [hχ]; exact Work.BoseBoxFock.chiLam_hasCompactSupport_tauPhi hℓ
  have hχint : Integrable χ := hχcont.integrable_of_hasCompactSupport hχcs
  have hχev : ∀ x, χ (-x) = χ x := by
    intro x; rw [hχ]; exact Work.BoseK15.corpusBox.chiLam_even ℓ x
  have hScont : Continuous S := by
    rw [hS]; exact Work.BoseBoxFock.uvSmear_continuous fu hΛpos hWint
  have hSdec : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x : E3, |S x| ≤ C * (1 + ‖x‖) ^ (-(n : ℤ)) := by
    intro n
    obtain ⟨C, hC0, hC⟩ := Work.BoseBoxFock.uvSmear_rapidDecay fu hΛpos hWint hWcs n
    exact ⟨C, hC0, fun x => by rw [hS]; exact hC x⟩
  have hSi : Integrable S := by
    obtain ⟨C, hC0, hC⟩ := hSdec 8
    exact (integrable_const_mul_zpow8 C).mono' hScont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]
        exact hC x)
  have hSev : ∀ x, S (-x) = S x := by
    intro x
    have hconv : S = MeasureTheory.convolution (Work.BoseBoxFock.uvKernel fu Λ) W
        (ContinuousLinearMap.mul ℝ ℝ) volume := by
      rw [hS]
      funext u
      rw [Work.BoseBoxFock.uvSmear, MeasureTheory.convolution_mul_swap]
    rw [hconv]
    exact MeasureTheory.convolution_neg_of_neg_eq (μ := volume) (ContinuousLinearMap.mul ℝ ℝ)
      (Filter.Eventually.of_forall (Work.BoseBoxFock.uvKernel_even fu Λ))
      (Filter.Eventually.of_forall hWev)
  -- ## continuity and integrability of the two windowed convolutions
  have hGSint : Integrable GS := by
    rw [hGS]
    exact Work.BoseRowsL.Row2.chat_conv_integrable hχint hSi
  have hGWint : Integrable GW := by
    rw [hGW]
    exact Work.BoseRowsL.Row2.chat_conv_integrable hχint hWint
  have hGSc : Continuous GS := by
    rw [hGS]
    have h := HasCompactSupport.continuous_convolution_left (f := χ) (g := S)
      (L := ContinuousLinearMap.lsmul ℝ ℝ) (μ := volume) hχcs hχcont hScont.locallyIntegrable
    convert h using 1
    funext u
    rw [MeasureTheory.convolution_lsmul]
    rfl
  have hGWc : Continuous GW := by
    rw [hGW]
    have h := HasCompactSupport.continuous_convolution_left (f := χ) (g := W)
      (L := ContinuousLinearMap.lsmul ℝ ℝ) (μ := volume) hχcs hχcont hWloc
    convert h using 1
    funext u
    rw [MeasureTheory.convolution_lsmul]
    rfl
  have hGWcs : HasCompactSupport GW := by
    obtain ⟨Rχ, hRχ⟩ :=
      (Metric.isBounded_iff_subset_closedBall (0 : E3)).mp hχcs.isCompact.isBounded
    obtain ⟨RW, hRW⟩ :=
      (Metric.isBounded_iff_subset_closedBall (0 : E3)).mp hWcs.isCompact.isBounded
    have hχR : tsupport χ ⊆ Metric.closedBall (0 : E3) (max Rχ RW) := fun x hx => by
      have h := hRχ hx
      rw [Metric.mem_closedBall, dist_zero_right] at h ⊢
      exact h.trans (le_max_left _ _)
    have hWR : tsupport W ⊆ Metric.closedBall (0 : E3) (max Rχ RW) := fun x hx => by
      have h := hRW hx
      rw [Metric.mem_closedBall, dist_zero_right] at h ⊢
      exact h.trans (le_max_right _ _)
    have hsub := Work.BoseRowsL.Row2.tsupport_conv_subset (f := χ) (g := W)
      (R := max Rχ RW) hχR hWR
    rw [hGW]
    exact (isCompact_closedBall (0 : E3) (2 * max Rχ RW)).of_isClosed_subset
      (isClosed_tsupport _) hsub
  -- ## the closed form of the Fourier transform
  have hchatχ : ∀ p : E3, Work.BoseFixR.chat χ p
      = ℓ ^ 3 * Work.BoseK15.corpusBox.hatChi (ℓ • p) := by
    intro p
    rw [Work.BoseB7AK.W1low.chat_eq_integral_cos hχint p]
    rw [hχ]
    exact Work.BoseB4.BoxData.integral_chiLam_mul_cos Work.BoseK15.corpusBox hℓ p
  have hchatS : ∀ p : E3, Work.BoseFixR.chat S p
      = Work.BoseBoxFock.uvCut fu Λ p * Work.BoseFixR.chat W p := by
    intro p
    rw [hS]
    exact Work.BoseBoxFock.chat_uvSmear fu hΛpos hWint p
  have hkinFTχ : ∀ p : E3,
      Submission.BoseGases.kinFT (fun x : E3 => ((χ x : ℝ) : ℂ)) p
        = ((ℓ ^ 3 * Work.BoseK15.corpusBox.hatChi (ℓ • p) : ℝ) : ℂ) := by
    intro p
    rw [← Work.BoseBoxFock.chat_eq_kinFT_of_even hχev p, hchatχ p]
  have hkinFTS : ∀ p : E3,
      (∫ y : E3, Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * ((GS y : ℝ) : ℂ))
        = ((ℓ ^ 3 * Work.BoseK15.corpusBox.hatChi (ℓ • p) * Work.BoseBoxFock.uvCut fu Λ p
            * Work.BoseFixR.chat W p : ℝ) : ℂ) := by
    intro p
    have h1 : (∫ y : E3, Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * ((GS y : ℝ) : ℂ))
        = ∫ y : E3, Complex.exp (-(Complex.I * (inner ℝ p y : ℂ)))
            * ((∫ x : E3, χ x * S (y - x) : ℝ) : ℂ) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      show Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * ((GS y : ℝ) : ℂ)
          = Complex.exp (-(Complex.I * (inner ℝ p y : ℂ)))
            * ((∫ x : E3, χ x * S (y - x) : ℝ) : ℂ)
      rw [hGS]
    rw [h1, show (∫ y : E3, Complex.exp (-(Complex.I * (inner ℝ p y : ℂ)))
            * ((∫ x : E3, χ x * S (y - x) : ℝ) : ℂ))
          = Submission.BoseGases.kinFT (fun y : E3 => ((∫ x : E3, χ x * S (y - x) : ℝ) : ℂ)) p
        from rfl,
      Work.BoseRowsL.Row2.kinFT_ofReal_convolution hχint hSi p, hkinFTχ p,
      ← Work.BoseBoxFock.chat_eq_kinFT_of_even hSev p, hchatS p]
    push_cast
    ring
  have hkinFTW : ∀ p : E3,
      (∫ y : E3, Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * ((GW y : ℝ) : ℂ))
        = ((ℓ ^ 3 * Work.BoseK15.corpusBox.hatChi (ℓ • p)
            * Work.BoseFixR.chat W p : ℝ) : ℂ) := by
    intro p
    have h1 : (∫ y : E3, Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * ((GW y : ℝ) : ℂ))
        = ∫ y : E3, Complex.exp (-(Complex.I * (inner ℝ p y : ℂ)))
            * ((∫ x : E3, χ x * W (y - x) : ℝ) : ℂ) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      show Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * ((GW y : ℝ) : ℂ)
          = Complex.exp (-(Complex.I * (inner ℝ p y : ℂ)))
            * ((∫ x : E3, χ x * W (y - x) : ℝ) : ℂ)
      rw [hGW]
    rw [h1, show (∫ y : E3, Complex.exp (-(Complex.I * (inner ℝ p y : ℂ)))
            * ((∫ x : E3, χ x * W (y - x) : ℝ) : ℂ))
          = Submission.BoseGases.kinFT (fun y : E3 => ((∫ x : E3, χ x * W (y - x) : ℝ) : ℂ)) p
        from rfl,
      Work.BoseRowsL.Row2.kinFT_ofReal_convolution hχint hWint p, hkinFTχ p,
      ← Work.BoseBoxFock.chat_eq_kinFT_of_even hWev p]
    push_cast
    ring
  have hFT_F : ∀ p : E3, (∫ y : E3, Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * F y)
      = ((ℓ ^ 3 * (Work.BoseK15.corpusBox.hatChi (ℓ • p)
          * ((Work.BoseBoxFock.uvCut fu Λ p - 1) * Work.BoseFixR.chat W p)) : ℝ) : ℂ) := by
    intro p
    have hsplit : (∫ y : E3, Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * F y)
        = (∫ y : E3, Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * ((GS y : ℝ) : ℂ))
          - (∫ y : E3, Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * ((GW y : ℝ) : ℂ)) := by
      rw [hF]
      rw [show (fun y : E3 => Complex.exp (-(Complex.I * (inner ℝ p y : ℂ)))
            * (((fun u : E3 => ((GS u : ℝ) : ℂ) - ((GW u : ℝ) : ℂ)) y)))
          = (fun y : E3 => Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * ((GS y : ℝ) : ℂ)
              - Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * ((GW y : ℝ) : ℂ)) from by
        funext y
        show Complex.exp (-(Complex.I * (inner ℝ p y : ℂ)))
              * (((GS y : ℝ) : ℂ) - ((GW y : ℝ) : ℂ))
            = Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * ((GS y : ℝ) : ℂ)
              - Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * ((GW y : ℝ) : ℂ)
        ring]
      rw [integral_sub (integrable_exp_mul_ofReal hGSint p) (integrable_exp_mul_ofReal hGWint p)]
    rw [hsplit, hkinFTS p, hkinFTW p]
    push_cast
    ring
  -- ## the three Poisson hypotheses
  have hFc : Continuous F := by
    rw [hF]
    exact (Complex.continuous_ofReal.comp hGSc).sub (Complex.continuous_ofReal.comp hGWc)
  have hFdec : ∀ n : ℕ, ∃ C : ℝ, ∀ u : E3, ‖F u‖ ≤ C * (1 + ‖u‖) ^ (-(n : ℤ)) := by
    intro n
    obtain ⟨C₁, _hC₁0, hC₁⟩ := conv_le_of_rapidDecay_aux hχcont hχcs
      (Complex.continuous_ofReal.comp hScont).aestronglyMeasurable
      (by
        intro k
        obtain ⟨C, hC0, hC⟩ := hSdec k
        exact ⟨C, hC0, fun x => by
          show ‖((S x : ℝ) : ℂ)‖ ≤ C * (1 + ‖x‖) ^ (-(k : ℤ))
          rw [Complex.norm_real, Real.norm_eq_abs]
          exact hC x⟩) n
    obtain ⟨C₂, _hC₂0, hC₂⟩ := abs_le_of_continuous_hasCompactSupport hGWc hGWcs n
    refine ⟨C₁ + C₂, fun u => ?_⟩
    have h1 : ‖F u‖ ≤ |GS u| + |GW u| := by
      rw [hF]
      show ‖((GS u : ℝ) : ℂ) - ((GW u : ℝ) : ℂ)‖ ≤ |GS u| + |GW u|
      rw [show ((GS u : ℝ) : ℂ) - ((GW u : ℝ) : ℂ) = (((GS u - GW u : ℝ)) : ℂ) by
        push_cast; ring]
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact abs_sub _ _
    have h2 : |GS u| ≤ C₁ * (1 + ‖u‖) ^ (-(n : ℤ)) := by
      rw [hGS, ← norm_integral_ofReal_conv χ S u]
      exact hC₁ u
    calc ‖F u‖ ≤ |GS u| + |GW u| := h1
      _ ≤ C₁ * (1 + ‖u‖) ^ (-(n : ℤ)) + C₂ * (1 + ‖u‖) ^ (-(n : ℤ)) :=
          add_le_add h2 (hC₂ u)
      _ = (C₁ + C₂) * (1 + ‖u‖) ^ (-(n : ℤ)) := by ring
  have hFTdec : ∀ n : ℕ, ∃ C : ℝ, ∀ p : E3,
      ‖∫ y : E3, Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * F y‖
        ≤ C * (1 + ‖p‖) ^ (-(n : ℤ)) := by
    intro n
    have hcd : ContDiff ℝ (⊤ : ℕ∞) (fun x : E3 => ((χ x : ℝ) : ℂ)) := by
      rw [hχ]
      exact Complex.ofRealCLM.contDiff.comp (Work.BoseBoxFock.chiLam_contDiff hℓ)
    have hcs' : HasCompactSupport (fun x : E3 => ((χ x : ℝ) : ℂ)) := by
      rw [hχ]
      exact HasCompactSupport.comp_left (g := fun r : ℝ => ((r : ℝ) : ℂ))
        (Work.BoseBoxFock.chiLam_hasCompactSupport_tauPhi hℓ) Complex.ofReal_zero
    obtain ⟨C₁, hC₁0, hC₁⟩ := Work.OneBodyKin.kinFT_decay_le n hcd hcs'
    have hC₁' : ∀ p : E3, ‖Submission.BoseGases.kinFT (fun x : E3 => ((χ x : ℝ) : ℂ)) p‖
        ≤ C₁ * (1 + ‖p‖) ^ (-(n : ℤ)) := by
      intro p
      have h := hC₁ p
      rwa [div_eq_mul_inv, ← zpow_neg_nat n (1 + ‖p‖)] at h
    refine ⟨2 * (∫ x : E3, |W x|) * C₁, fun p => ?_⟩
    rw [hFT_F p, Complex.norm_real, Real.norm_eq_abs]
    have hmain : |ℓ ^ 3 * (Work.BoseK15.corpusBox.hatChi (ℓ • p)
          * ((Work.BoseBoxFock.uvCut fu Λ p - 1) * Work.BoseFixR.chat W p))|
        = |Work.BoseFixR.chat χ p| * |Work.BoseBoxFock.uvCut fu Λ p - 1|
            * |Work.BoseFixR.chat W p| := by
      rw [show ℓ ^ 3 * (Work.BoseK15.corpusBox.hatChi (ℓ • p)
            * ((Work.BoseBoxFock.uvCut fu Λ p - 1) * Work.BoseFixR.chat W p))
          = Work.BoseFixR.chat χ p
            * ((Work.BoseBoxFock.uvCut fu Λ p - 1) * Work.BoseFixR.chat W p) by
        rw [hchatχ p]; ring]
      rw [abs_mul, abs_mul]
      ring
    rw [hmain]
    have hχd : |Work.BoseFixR.chat χ p| ≤ C₁ * (1 + ‖p‖) ^ (-(n : ℤ)) :=
      (Complex.abs_re_le_norm _).trans (hC₁' p)
    have huc : |Work.BoseBoxFock.uvCut fu Λ p - 1| ≤ 2 := by
      have h3 : |Work.BoseBoxFock.uvCut fu Λ p| ≤ 1 := by
        rw [Work.BoseBoxFock.uvCut, abs_le]
        exact ⟨by linarith [fu.nonneg (‖p‖ / Λ)], fu.le_one _⟩
      calc |Work.BoseBoxFock.uvCut fu Λ p - 1|
          ≤ |Work.BoseBoxFock.uvCut fu Λ p| + |(1 : ℝ)| := abs_sub _ _
        _ = |Work.BoseBoxFock.uvCut fu Λ p| + 1 := by rw [abs_one]
        _ ≤ 1 + 1 := by linarith
        _ = 2 := by norm_num
    have hWd : |Work.BoseFixR.chat W p| ≤ ∫ x : E3, |W x| := abs_chat_le_integral_abs hWint p
    calc |Work.BoseFixR.chat χ p| * |Work.BoseBoxFock.uvCut fu Λ p - 1|
          * |Work.BoseFixR.chat W p|
        ≤ (C₁ * (1 + ‖p‖) ^ (-(n : ℤ))) * 2 * (∫ x : E3, |W x|) := by
          refine mul_le_mul (mul_le_mul hχd huc (abs_nonneg _) (by positivity))
            hWd (abs_nonneg _) (by positivity)
      _ = (2 * (∫ x : E3, |W x|) * C₁) * (1 + ‖p‖) ^ (-(n : ℤ)) := by ring
  -- ## Poisson summation
  have hPois := Work.BoseBoxFock.latSampling_decay (ℓ := ℓ) hℓ (F := F) hFc hFdec hFTdec z
  -- ## the LHS summand, identified with `F`
  have hconvF : ∀ u : E3, Work.BoseBoxFock.PCFU.chDconv ℓ
      (fun u => ((Work.BoseBoxFock.PCFU.chDkerE (h := h) fu ℓ N u : ℝ) : ℂ)) u = F u := by
    intro u
    rw [Work.BoseBoxFock.PCFU.chDconv, ← hχ]
    rw [show (fun w : E3 => (χ w : ℂ)
          * ((Work.BoseBoxFock.PCFU.chDkerE (h := h) fu ℓ N (u - w) : ℝ) : ℂ))
        = (fun w : E3 => ((χ w * Work.BoseBoxFock.PCFU.chDkerE (h := h) fu ℓ N (u - w) : ℝ) : ℂ))
        from by
      funext w; push_cast; ring]
    rw [show (∫ w : E3, ((χ w * Work.BoseBoxFock.PCFU.chDkerE (h := h) fu ℓ N (u - w) : ℝ) : ℂ))
        = ((∫ w : E3, χ w * Work.BoseBoxFock.PCFU.chDkerE (h := h) fu ℓ N (u - w) : ℝ) : ℂ)
        from integral_ofReal]
    have hE : (fun w : E3 => χ w * Work.BoseBoxFock.PCFU.chDkerE (h := h) fu ℓ N (u - w))
        = fun w : E3 => χ w * S (u - w) - χ w * W (u - w) := by
      funext w
      rw [show Work.BoseBoxFock.PCFU.chDkerE (h := h) fu ℓ N (u - w) = S (u - w) - W (u - w) by
        simp only [Work.BoseBoxFock.PCFU.chDkerE, ← hΛ, ← hW, ← hS]]
      ring
    have hIntS : Integrable (fun w : E3 => χ w * S (u - w)) := by
      obtain ⟨C, _hC0, hC⟩ := hSdec 0
      exact hχint.mul_bdd (c := C)
        ((hScont.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun w => by
          show ‖S (u - w)‖ ≤ C
          rw [Real.norm_eq_abs]
          simpa using hC (u - w))
    have hIntW : Integrable (fun w : E3 => χ w * W (u - w)) := by
      obtain ⟨C, _hC0, hC⟩ := abs_le_of_continuous_hasCompactSupport hχcont hχcs 0
      exact (hWint.comp_sub_left u).bdd_mul (c := C) hχcont.aestronglyMeasurable
        (Filter.Eventually.of_forall fun w => by
          show ‖χ w‖ ≤ C
          rw [Real.norm_eq_abs]
          simpa using hC w)
    rw [hE, integral_sub hIntS hIntW]
    have hGSu : (∫ a : E3, χ a * S (u - a)) = GS u := by rw [hGS]
    have hGWu : (∫ a : E3, χ a * W (u - a)) = GW u := by rw [hGW]
    rw [hGSu, hGWu]
    push_cast
    ring
  -- ## assembling the summands
  have hpt : ∀ m : Fin 3 → ℤ,
      (∫ x : E3, Complex.exp (-(Complex.I * (inner ℝ ((2 * Real.pi / ℓ)
            • Work.BoseBoxFock.latVec m) x : ℂ))) * F x)
          * Complex.exp (Complex.I * (inner ℝ ((2 * Real.pi / ℓ)
            • Work.BoseBoxFock.latVec m) z : ℂ))
        = ((ℓ : ℂ) ^ 3) * ((((Work.BoseBoxFock.uvCut fu Λ
              (Work.BoseBoxFock.kmomInt ℓ m) - 1 : ℝ)) : ℂ)
            * (((Work.BoseFixR.chat W (Work.BoseBoxFock.kmomInt ℓ m)) : ℝ) : ℂ)
            * (((Work.BoseK15.corpusBox.hatChi (ℓ • Work.BoseBoxFock.kmomInt ℓ m)) : ℝ) : ℂ)
            * Complex.exp (Complex.I * (inner ℝ (Work.BoseBoxFock.kmomInt ℓ m) z : ℂ))) := by
    intro m
    rw [hFT_F ((2 * Real.pi / ℓ) • Work.BoseBoxFock.latVec m), kmomInt_eq_smul ℓ m]
    push_cast
    ring
  have hsum : ((ℓ : ℂ) ^ 3) * (∑' m : Fin 3 → ℤ,
        (((Work.BoseBoxFock.uvCut fu Λ (Work.BoseBoxFock.kmomInt ℓ m) - 1 : ℝ)) : ℂ)
          * (((Work.BoseFixR.chat W (Work.BoseBoxFock.kmomInt ℓ m)) : ℝ) : ℂ)
          * (((Work.BoseK15.corpusBox.hatChi (ℓ • Work.BoseBoxFock.kmomInt ℓ m)) : ℝ) : ℂ)
          * Complex.exp (Complex.I * (inner ℝ (Work.BoseBoxFock.kmomInt ℓ m) z : ℂ)))
      = ∑' m : Fin 3 → ℤ,
          (∫ x : E3, Complex.exp (-(Complex.I * (inner ℝ ((2 * Real.pi / ℓ)
              • Work.BoseBoxFock.latVec m) x : ℂ))) * F x)
            * Complex.exp (Complex.I * (inner ℝ ((2 * Real.pi / ℓ)
              • Work.BoseBoxFock.latVec m) z : ℂ)) := by
    rw [← tsum_mul_left]
    exact tsum_congr fun m => (hpt m).symm
  have hresult : (∑' m : Fin 3 → ℤ,
        (((Work.BoseBoxFock.uvCut fu Λ (Work.BoseBoxFock.kmomInt ℓ m) - 1 : ℝ)) : ℂ)
          * (((Work.BoseFixR.chat W (Work.BoseBoxFock.kmomInt ℓ m)) : ℝ) : ℂ)
          * (((Work.BoseK15.corpusBox.hatChi (ℓ • Work.BoseBoxFock.kmomInt ℓ m)) : ℝ) : ℂ)
          * Complex.exp (Complex.I * (inner ℝ (Work.BoseBoxFock.kmomInt ℓ m) z : ℂ)))
      = ∑' d : Fin 3 → ℤ, F (z + ℓ • Work.BoseBoxFock.latVec d) :=
    mul_left_cancel₀ (pow_ne_zero 3 (Complex.ofReal_ne_zero.mpr (ne_of_gt hℓ)))
      (hsum.trans hPois)
  -- ## conclusion
  have hLHSconv : (∑' d : Fin 3 → ℤ, Work.BoseBoxFock.PCFU.chDconv ℓ
        (fun u => ((Work.BoseBoxFock.PCFU.chDkerE (h := h) fu ℓ N u : ℝ) : ℂ))
        (z + ℓ • Work.BoseBoxFock.latVec d))
      = ∑' d : Fin 3 → ℤ, F (z + ℓ • Work.BoseBoxFock.latVec d) :=
    tsum_congr fun d => hconvF (z + ℓ • Work.BoseBoxFock.latVec d)
  rw [hLHSconv]
  exact hresult.symm

end Work.PCFU
