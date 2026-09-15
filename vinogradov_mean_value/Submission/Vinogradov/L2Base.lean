/-
Copyright: the formalization team of the Vinogradov mean value theorem project.
-/
import Submission.Vinogradov.DecouplingClass
import Submission.Commons.Analysis.Fourier.fourierIntegral_mul_measure_eq_zero
import Submission.Commons.Analysis.Fourier.fourierInv_toLp_ae_eq_fourierInv
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# The `k = 1` base case of the §4 bootstrap: `L²` Fourier analysis

The base case `etaLin 1 ≤ 0` of the strong induction of GLYZ §4 is the statement that the
linear `ℓ²`-decoupling for the *line* holds with no loss.  For `k = 1` the plates of the pieces
are intervals and the pieces have essentially disjoint frequency supports, so the content is the
`L²` orthogonality of frequency-disjoint functions.

This module builds it from scratch on Mathlib's Fourier transform:

* `star_chat`, `integrable_fourier_schwartz`, `integrable_fourierInv_schwartz`;
* **`integral_chat_mul_star_fourierInv`** — the pointwise Fourier inversion identity
  `∫ x, e(⟪x,ξ⟫)·conj (𝓕⁻ψ x) = conj (ψ ξ)` for a Schwartz test function `ψ`;
* **`IsFourierRep.inner_fourier_eq_integral`** — the pairing identity
  `⟪𝓕 f, ψ⟫ = ∫ u, φ u · conj (ψ (Γ u)) ∂ν` for `f ∈ 𝒞(U)`;
* **`IsFourierRep.fourier_eq_zero_off`** — the frequency support of an `L²` class member is
  contained in `U`;
* the orthogonality and the `k = 1` decoupling.
-/

noncomputable section
open MeasureTheory FourierTransform Complex Classical Filter
open scoped FourierTransform RealInnerProductSpace BigOperators ENNReal NNReal

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.style.emptyLine false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000

namespace Submission.Vinogradov

/-! ## 1. The character and its conjugate -/

/-- `conj (e(⟪x,ξ⟫)) = e(⟪x,-ξ⟫)`. -/
lemma star_chat (k : ℕ) (x ξ : E k) : star (chat k x ξ) = chat k x (-ξ) := by
  rw [chat, chat, inner_neg_right]
  rw [Complex.star_def, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.conj_ofNat, ofReal_neg]
  ring

/-! ## 2. Fourier inversion against a Schwartz test function -/

lemma integrable_fourier_schwartz {k : ℕ} (ψ : SchwartzMap (E k) ℂ) :
    Integrable (𝓕 (ψ : E k → ℂ)) volume := by
  rw [← SchwartzMap.fourier_coe (f := ψ)]
  exact (𝓕 ψ).integrable

lemma integrable_fourierInv_schwartz {k : ℕ} (ψ : SchwartzMap (E k) ℂ) :
    Integrable (𝓕⁻ (ψ : E k → ℂ)) volume := by
  rw [← SchwartzMap.fourierInv_coe (f := ψ)]
  exact (𝓕⁻ ψ).integrable

/-- **Fourier inversion, pointwise, in the form used by the pairing identity.** -/
lemma integral_chat_mul_star_fourierInv {k : ℕ} (ξ : E k) (ψ : SchwartzMap (E k) ℂ) :
    (∫ x, chat k x ξ * star (𝓕⁻ (ψ : E k → ℂ) x)) = star (ψ ξ) := by
  have hψ1 : Integrable (ψ : E k → ℂ) volume := ψ.integrable
  have hFψ : Integrable (𝓕 (ψ : E k → ℂ)) volume := integrable_fourier_schwartz ψ
  have hinv : ∀ v : E k, 𝓕 (𝓕⁻ (ψ : E k → ℂ)) v = ψ v := fun v =>
    hψ1.fourier_fourierInv_eq hFψ ψ.continuous.continuousAt
  have hpair : (∫ x, chat k x ξ * star (𝓕⁻ (ψ : E k → ℂ) x))
      = star (∫ x, star (chat k x ξ) * (𝓕⁻ (ψ : E k → ℂ) x)) := by
    have h1 : (∫ x, chat k x ξ * star (𝓕⁻ (ψ : E k → ℂ) x))
        = ∫ x, star (star (chat k x ξ) * (𝓕⁻ (ψ : E k → ℂ) x)) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      show chat k x ξ * star (𝓕⁻ (ψ : E k → ℂ) x)
        = star (star (chat k x ξ) * (𝓕⁻ (ψ : E k → ℂ) x))
      rw [star_mul, star_star]
      ring
    rw [h1]
    simp only [Complex.star_def]
    rw [integral_conj]
  rw [hpair,
    show (∫ x, star (chat k x ξ) * (𝓕⁻ (ψ : E k → ℂ) x)) = 𝓕 (𝓕⁻ (ψ : E k → ℂ)) ξ from ?_,
    hinv ξ]
  · rw [Real.fourier_eq]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show star (chat k x ξ) * (𝓕⁻ (ψ : E k → ℂ) x) = 𝐞 (-⟪x, ξ⟫) • (𝓕⁻ (ψ : E k → ℂ) x)
    rw [star_chat, chat, Circle.smul_def, smul_eq_mul,
      Commons.Analysis.Fourier.exp_two_pi_I_eq_fourierChar]
    congr 1
    rw [inner_neg_right]

/-! ## 3. The pairing identity for a representing function -/

/-- Integrability of the Fubini kernel of the pairing identity. -/
lemma integrable_chat_mul_conj {k : ℕ} {ι : Type*} [MeasurableSpace ι] {Γ : ι → E k}
    {ν : Measure ι} [SigmaFinite ν] {φ : ι → ℂ} (hφ : Integrable φ ν) (hΓ : Measurable Γ)
    {ψ : E k → ℂ} (hψ : Integrable ψ) :
    Integrable (Function.uncurry (fun x (u : ι) => chat k x (Γ u) * φ u * star (ψ x)))
      (volume.prod ν) := by
  have hb : Integrable (fun p : E k × ι => ‖ψ p.1‖ * ‖φ p.2‖) (volume.prod ν) :=
    hψ.norm.mul_prod hφ.norm
  refine hb.mono ?_ ?_
  · refine (((continuous_chat_uncurry k).measurable.comp
      (measurable_fst.prodMk (hΓ.comp measurable_snd))).aestronglyMeasurable.mul
      (hφ.aestronglyMeasurable.comp_snd)).mul (hψ.aestronglyMeasurable.star.comp_fst)
  · filter_upwards with p
    rw [Function.uncurry_apply_pair, norm_mul, norm_mul, norm_star, chat_norm, one_mul,
      Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)), mul_comm]


/-! ## 4. The `L²` inner product as an integral, and the pairing identity -/

/-- The `L²` inner product of scalar-valued `L²` classes as an integral with the conjugation
on the first factor (`RCLike.inner_apply` orientation). -/
lemma inner_Lp_eq_integral {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (u v : Lp ℂ 2 μ) :
    inner ℂ u v = ∫ x, (v : α → ℂ) x * star ((u : α → ℂ) x) ∂μ := by
  rw [MeasureTheory.L2.inner_def]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => by
    simp only [Complex.star_def, RCLike.inner_apply])

set_option maxHeartbeats 16000000 in
/-- **The pairing identity.**  For a representing function `f = repFun k Γ ν φ` which is `L²`,
the `L²` Fourier transform of `f` pairs against a Schwartz test function `ψ` through the
representation:
  `∫ ξ, (𝓕 f) ξ · conj (ψ ξ) = ∫ u, φ u · conj (ψ (Γ u)) ∂ν`. -/
theorem repFun_integral_fourier_mul_conj {k : ℕ} {ι : Type*} [MeasurableSpace ι]
    {Γ : ι → E k} {ν : Measure ι} [IsFiniteMeasure ν] {φ : ι → ℂ}
    (hφ : Integrable φ ν) (hΓ : Measurable Γ)
    (hf2 : MemLp (repFun k Γ ν φ) 2 (volume : Measure (E k))) (ψ : SchwartzMap (E k) ℂ) :
    (∫ ξ, ((𝓕 (hf2.toLp (repFun k Γ ν φ)) : Lp ℂ 2 (volume : Measure (E k))) : E k → ℂ) ξ
        * star (ψ ξ)) = ∫ u, φ u * star (ψ (Γ u)) ∂ν := by
  set f : E k → ℂ := repFun k Γ ν φ with hfdef
  set fL : Lp ℂ 2 (volume : Measure (E k)) := hf2.toLp f with hfL
  have hψ2 : MemLp (ψ : E k → ℂ) 2 (volume : Measure (E k)) := ψ.memLp 2 volume
  have hψ1 : MemLp (ψ : E k → ℂ) 1 (volume : Measure (E k)) := ψ.memLp 1 volume
  set ψL : Lp ℂ 2 (volume : Measure (E k)) := hψ2.toLp ψ with hψL
  -- (A) the integral is the `L²` pairing
  have hA : (∫ ξ, ((𝓕 fL : Lp ℂ 2 (volume : Measure (E k))) : E k → ℂ) ξ * star (ψ ξ))
      = inner ℂ ψL (𝓕 fL) := by
    rw [inner_Lp_eq_integral]
    refine integral_congr_ae ?_
    filter_upwards [MeasureTheory.MemLp.coeFn_toLp hψ2] with ξ hξ
    rw [hξ]
  -- (B) the Plancherel isometry
  have hB : inner ℂ ψL (𝓕 fL) = inner ℂ (𝓕⁻ ψL) fL := by
    have h1 : 𝓕 (𝓕⁻ ψL) = ψL := fourier_fourierInv_eq ψL
    conv_lhs => rw [← h1]
    exact Lp.inner_fourier_eq (𝓕⁻ ψL) fL
  -- (C) the `L²` pairing against `f` and `𝓕⁻ψ`
  have hC : inner ℂ (𝓕⁻ ψL) fL = ∫ x, f x * star (𝓕⁻ (ψ : E k → ℂ) x) := by
    rw [inner_Lp_eq_integral]
    refine integral_congr_ae ?_
    filter_upwards [MeasureTheory.MemLp.coeFn_toLp hf2,
      Commons.Analysis.Fourier.fourierInv_toLp_ae_eq_fourierInv hψ1 hψ2] with x hf hfi
    rw [hf, hfi]
  -- (D) Fubini
  have hD : (∫ x, f x * star (𝓕⁻ (ψ : E k → ℂ) x))
      = ∫ u, φ u * star (ψ (Γ u)) ∂ν := by
    have hInt0 : Integrable (𝓕⁻ (ψ : E k → ℂ)) volume := integrable_fourierInv_schwartz ψ
    have hInt : Integrable (Function.uncurry
        (fun x (u : ι) => chat k x (Γ u) * φ u * star (𝓕⁻ (ψ : E k → ℂ) x)))
        (volume.prod ν) :=
      integrable_chat_mul_conj hφ hΓ hInt0
    have hsym : (∫ x, (∫ u, chat k x (Γ u) * φ u * star (𝓕⁻ (ψ : E k → ℂ) x) ∂ν))
        = ∫ u, ∫ x, chat k x (Γ u) * φ u * star (𝓕⁻ (ψ : E k → ℂ) x) ∂volume ∂ν :=
      integral_integral_swap hInt
    simp only [hfdef, repFun]
    rw [show (fun x => (∫ u, chat k x (Γ u) * φ u ∂ν) * star (𝓕⁻ (ψ : E k → ℂ) x))
        = fun x => ∫ u, chat k x (Γ u) * φ u * star (𝓕⁻ (ψ : E k → ℂ) x) ∂ν from by
      funext x; rw [MeasureTheory.integral_mul_const]]
    rw [hsym]
    have hinner : ∀ u : ι, (∫ x, chat k x (Γ u) * φ u * star (𝓕⁻ (ψ : E k → ℂ) x)) =
        φ u * star (ψ (Γ u)) := by
      intro u
      rw [show (fun x => chat k x (Γ u) * φ u * star (𝓕⁻ (ψ : E k → ℂ) x))
          = fun x => φ u * (chat k x (Γ u) * star (𝓕⁻ (ψ : E k → ℂ) x)) from by
        funext x; ring]
      rw [MeasureTheory.integral_const_mul, integral_chat_mul_star_fourierInv]
    exact integral_congr_ae (Filter.Eventually.of_forall fun u => hinner u)
  rw [hA, hB, hC, hD]

/-- **The immediate corollary of the pairing identity**: a Schwartz test function vanishing on the
frequency support `U` of the class `𝒞(U)` has vanishing pairing with `𝓕 f`.  This is the input of
the frequency-support lemma (step 2 of the base case). -/
theorem repFun_integral_fourier_mul_conj_of_vanishing {k : ℕ} {ι : Type*} [MeasurableSpace ι]
    {Γ : ι → E k} {ν : Measure ι} [IsFiniteMeasure ν] {φ : ι → ℂ} {U : Set (E k)}
    (hφ : Integrable φ ν) (hΓ : Measurable Γ) (hU : ∀ u, φ u ≠ 0 → Γ u ∈ U)
    (hf2 : MemLp (repFun k Γ ν φ) 2 (volume : Measure (E k))) {ψ : SchwartzMap (E k) ℂ}
    (hvan : ∀ ξ ∈ U, ψ ξ = 0) :
    (∫ ξ, ((𝓕 (hf2.toLp (repFun k Γ ν φ)) : Lp ℂ 2 (volume : Measure (E k))) : E k → ℂ) ξ
        * star (ψ ξ)) = 0 := by
  rw [repFun_integral_fourier_mul_conj hφ hΓ hf2 ψ,
    show (∫ u, φ u * star (ψ (Γ u)) ∂ν) = ∫ u, (0 : ℂ) ∂ν from
      integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)]
  · simp
  · show φ u * star (ψ (Γ u)) = 0
    by_cases h : φ u = 0
    · rw [h, zero_mul]
    · rw [hvan (Γ u) (hU u h), star_zero, mul_zero]

end Submission.Vinogradov
