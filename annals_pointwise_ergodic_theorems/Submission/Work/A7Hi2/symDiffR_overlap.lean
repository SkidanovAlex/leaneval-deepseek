import Mathlib
import Submission.Work.A7Hi2.RealScaleDefs
import Submission.Work.KMTAreas.A7LoLin.lacDevNearIntK
import Submission.Work.A7Hi2.lacSumMinSq
import Submission.Work.KMTAreas.tsum_inv_sq_shift_le

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace Work.A7Hi2

open MeasureTheory Finset
open scoped ENNReal NNReal BigOperators FourierTransform

noncomputable section

/-!
# The uniform overlap bound for the real-scale difference symbols `symDiffR`

`RealScaleDefs` introduces the difference symbol `symDiffR K σ ρ θ = ∑_j diffKernR K σ ρ j · e^{2πijθ}`
of two *comparable* real dilations `ρ ≤ σ ≤ 2ρ`, and the real-scale Poisson-summation form
`bumpSymR K σ θ = ∑_k 𝓕K (σ (k - θ))`.

This file proves `symDiffR_overlap`: for a fixed frequency `θ` and a `2`-lacunary family of scale
pairs (`2 σₙ ≤ σₙ₊₁`, `ρₙ ≤ σₙ ≤ 2ρₙ`), the sum `∑_{n ∈ U} ‖symDiffR K σₙ ρₙ θ‖` is bounded
uniformly in `U` and in `θ`.

The proof has three ingredients:

* **Modulated Poisson summation at a real scale** (`poissonReal`): the Fourier series of the real
  scale bump kernel `bumpKernR K σ` is the Poisson form `bumpSymR K σ`; the real-scale analogue of
  `Work.KMTAreas.ADev.bumpSym_eq_tsum`.

* **The single-scale decay estimate** (`symDiffBound`): for `1 ≤ ρ ≤ σ ≤ 2ρ`,
  `‖bumpSymR K σ θ − bumpSymR K ρ θ‖ ≤ A ρ⁻² + A min (ρ d) (ρ d)⁻²`, `d = nearDist θ`.  Only the
  single Poisson node nearest to `θ` contributes at scale `ρ d`; every other node decays with the
  Schwartz tails at rate `ρ⁻²`.

* **The lacunary absorption** (`lacSumReal`): `∑_{n ∈ U} min (aₙ d) (aₙ d)⁻² ≤ 8` and
  `∑_{n ∈ U} aₙ⁻² ≤ 2` for a `2`-lacunary real family with `1 ≤ aₙ`.
-/

/-! ## 1. Modulated Poisson summation at a real scale -/

/-- **Modulated Poisson summation at a real scale.**
For a Schwartz kernel `K`, a real scale `σ ≥ 1` and a frequency `θ`, the Fourier series
`∑_j (1/σ) K (j/σ) e^{2πijθ}` of the sampled dilation kernel equals the Poisson form
`∑_k 𝓕K (σ (k - θ))`.

The proof is that of `Work.KMTAreas.ADev.bumpSym_eq_tsum` with the natural number `m` replaced by
the real number `σ`: modulated Poisson summation `poisson_modulated` applied to the dilated
Schwartz function `x ↦ K (x/σ)`, together with the scaling rule
`Commons.Analysis.Fourier.fourier_comp_div`. -/
lemma poissonReal (K : SchwartzMap ℝ ℂ) {σ : ℝ} (hσ : 1 ≤ σ) (θ : ℝ) :
    (∑' j : ℤ, bumpKernR K σ j * Work.KMTAreas.ADev.chr j θ) = bumpSymR K σ θ := by
  have hσ0 : (0 : ℝ) < σ := lt_of_lt_of_le one_pos hσ
  have hσne : σ ≠ 0 := ne_of_gt hσ0
  let u : ℝˣ := Units.mk0 (σ⁻¹) (inv_ne_zero hσne)
  let e : ℝ ≃L[ℝ] ℝ := ContinuousLinearEquiv.unitsEquivAut ℝ u
  let g : SchwartzMap ℝ ℂ := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e K
  have hg : ∀ x : ℝ, g x = K (x / σ) := by
    intro x
    simp only [g, e, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
      ContinuousLinearEquiv.unitsEquivAut_apply, u, Units.val_mk0, div_eq_mul_inv]
  have hgf : ∀ y : ℝ, (𝓕 g) y
      = ((σ : ℝ) : ℂ) * FourierTransform.fourier (K : ℝ → ℂ) (y * σ) := by
    intro y
    rw [SchwartzMap.fourier_coe g]
    have hgfun : (⇑g : ℝ → ℂ) = fun x : ℝ => K (x / σ) := funext fun x => hg x
    rw [hgfun, Commons.Analysis.Fourier.fourier_comp_div (K : ℝ → ℂ) hσ0]
  have hp := Work.KMTAreas.ADev.poisson_modulated g (-θ)
  have hL : (∑' n : ℤ, g (n : ℝ)
        * Complex.exp (-(2 * Real.pi * Complex.I * (n : ℂ) * ((-θ : ℝ) : ℂ))))
      = ∑' n : ℤ, K ((n : ℝ) / σ) * Work.KMTAreas.ADev.chr n θ := by
    refine tsum_congr fun n => ?_
    simp only [hg n]
    rw [Work.KMTAreas.ADev.chr]
    congr 1
    push_cast
    ring
  have hR : (∑' k : ℤ, (𝓕 g) ((-θ) + (k : ℝ))) = ((σ : ℝ) : ℂ) * bumpSymR K σ θ := by
    rw [bumpSymR, ← tsum_mul_left]
    refine tsum_congr fun k => ?_
    rw [hgf ((-θ) + (k : ℝ))]
    congr 2
    ring
  have hmain : (∑' n : ℤ, K ((n : ℝ) / σ) * Work.KMTAreas.ADev.chr n θ)
      = ((σ : ℝ) : ℂ) * bumpSymR K σ θ := by
    rw [← hL, hp, hR]
  have hcoef : (((1 / σ : ℝ)) : ℂ) * (((σ : ℝ)) : ℂ) = 1 := by
    rw [show ((1 / σ : ℝ)) = ((σ : ℝ))⁻¹ by rw [one_div]]
    rw [Complex.ofReal_inv]
    exact inv_mul_cancel₀ (by exact_mod_cast hσne)
  have hsplit : (∑' z : ℤ, bumpKernR K σ z * Work.KMTAreas.ADev.chr z θ)
      = (((1 / σ : ℝ)) : ℂ)
          * (∑' n : ℤ, K ((n : ℝ) / σ) * Work.KMTAreas.ADev.chr n θ) := by
    rw [← tsum_mul_left]
    refine tsum_congr fun z => ?_
    rw [bumpKernR]
    push_cast
    ring
  rw [hsplit, hmain, ← mul_assoc, hcoef, one_mul]

/-! ## 2. Schwartz decay -/

/-- Schwartz decay of a Schwartz map in the form `‖L x‖ ≤ B (1 + |x|)⁻²`. -/
lemma schwartz_decay_sq (L : SchwartzMap ℝ ℂ) :
    ∃ B : ℝ, 0 < B ∧ ∀ x : ℝ, ‖L x‖ ≤ B * ((1 + |x|) ^ 2)⁻¹ := by
  obtain ⟨B, hBpos, hB⟩ := Commons.Analysis.Fourier.schwartz_decay_real L 2
  refine ⟨B, hBpos, fun x => ?_⟩
  have hx : (0 : ℝ) ≤ 1 + |x| := by positivity
  have he : (1 + |x|) ^ (-((2 : ℕ) : ℝ)) = ((1 + |x|) ^ 2)⁻¹ := by
    rw [show (-((2 : ℕ) : ℝ)) = -(2 : ℝ) by norm_num, Real.rpow_neg hx, Real.rpow_two]
  simpa only [he] using hB x

/-- Schwartz decay of `𝓕K` in the form `‖𝓕K x‖ ≤ B (1 + |x|)⁻²`. -/
lemma fourier_decay_sq' (K : SchwartzMap ℝ ℂ) :
    ∃ B : ℝ, 0 < B ∧ ∀ x : ℝ, ‖(𝓕 K) x‖ ≤ B * ((1 + |x|) ^ 2)⁻¹ :=
  schwartz_decay_sq (𝓕 K)

/-! ## 3. Summability and the symbol identity for the difference -/

/-- The Poisson side of the symbol at a real scale is summable. -/
lemma summable_symDiff_side (K : SchwartzMap ℝ ℂ) {s : ℝ} (hs : 1 ≤ s) (θ : ℝ) :
    Summable (fun k : ℤ => (𝓕 K) (s * ((k : ℝ) - θ))) := by
  obtain ⟨B, hBpos, hB⟩ := fourier_decay_sq' K
  obtain ⟨B₀, hB₀nn, hB₀⟩ := Work.KMTAreas.tsum_inv_sq_shift_le
  have hs0 : 0 < s := lt_of_lt_of_le one_pos hs
  have hsum0 : Summable (fun k : ℤ => (1 : ℝ) / (1 + (-θ + (k : ℝ)) ^ 2)) := (hB₀ (-θ)).1
  have hsum : Summable (fun k : ℤ => (1 : ℝ) / (1 + |(k : ℝ) - θ| ^ 2)) := by
    refine hsum0.congr fun k => ?_
    congr 1
    rw [sq_abs]
    ring
  refine Summable.of_norm_bounded (Summable.mul_left B hsum) fun k => ?_
  have h1 := hB (s * ((k : ℝ) - θ))
  rw [abs_mul, abs_of_nonneg hs0.le] at h1
  have h2 : (1 : ℝ) + |(k : ℝ) - θ| ≤ 1 + s * |(k : ℝ) - θ| := by
    nlinarith [abs_nonneg ((k : ℝ) - θ)]
  have h3 : ((1 + s * |(k : ℝ) - θ|) ^ 2)⁻¹ ≤ ((1 + |(k : ℝ) - θ|) ^ 2)⁻¹ :=
    (inv_le_inv₀ (by positivity) (by positivity)).mpr
      (by nlinarith [h2, abs_nonneg ((k : ℝ) - θ), hs])
  have h4 : ((1 + |(k : ℝ) - θ|) ^ 2)⁻¹ ≤ 1 / (1 + |(k : ℝ) - θ| ^ 2) := by
    rw [one_div]
    exact (inv_le_inv₀ (by positivity) (by positivity)).mpr
      (by nlinarith [abs_nonneg ((k : ℝ) - θ), sq_abs ((k : ℝ) - θ)])
  calc ‖(𝓕 K) (s * ((k : ℝ) - θ))‖
      ≤ B * ((1 + s * |(k : ℝ) - θ|) ^ 2)⁻¹ := h1
    _ ≤ B * ((1 + |(k : ℝ) - θ|) ^ 2)⁻¹ := mul_le_mul_of_nonneg_left h3 hBpos.le
    _ ≤ B * (1 / (1 + |(k : ℝ) - θ| ^ 2)) := mul_le_mul_of_nonneg_left h4 hBpos.le

/-- `bumpSymR` written with the Fourier transform of the Schwartz kernel. -/
lemma bumpSymR_eq_fourier (K : SchwartzMap ℝ ℂ) (s θ : ℝ) :
    bumpSymR K s θ = ∑' k : ℤ, (𝓕 K) (s * ((k : ℝ) - θ)) := by
  rw [bumpSymR]
  exact tsum_congr fun k => congrFun (SchwartzMap.fourier_coe K).symm _

/-- **The symbol difference is the Poisson difference.**  For `1 ≤ ρ ≤ σ` the difference of the two
symbols is the series of the differences `𝓕K (σ (k-θ)) − 𝓕K (ρ (k-θ))`. -/
lemma bumpSymR_diff_eq (K : SchwartzMap ℝ ℂ) {σ ρ : ℝ} (hσ : 1 ≤ σ) (hρ : 1 ≤ ρ) (θ : ℝ) :
    bumpSymR K σ θ - bumpSymR K ρ θ
      = ∑' k : ℤ, ((𝓕 K) (σ * ((k : ℝ) - θ)) - (𝓕 K) (ρ * ((k : ℝ) - θ))) := by
  rw [bumpSymR_eq_fourier K σ θ, bumpSymR_eq_fourier K ρ θ]
  exact (Summable.tsum_sub (summable_symDiff_side K hσ θ) (summable_symDiff_side K hρ θ)).symm

/-! ## 4. The single-scale decay estimate -/

/-- **The single-scale symbol difference bound.**  There is a constant `A`, depending only on `K`,
such that for `1 ≤ ρ ≤ σ ≤ 2ρ` and every frequency `θ`,
`‖bumpSymR K σ θ − bumpSymR K ρ θ‖ ≤ A ρ⁻² + A min (ρ d) (ρ d)⁻²` with `d = nearDist θ`.

The single Poisson node `k = nearInt θ` is the only one that can be of size `ρ d`; all other nodes
contribute at rate `ρ⁻²` because the distances `|k - θ| ≥ |k - nearInt θ|/2` grow with `k`. -/
theorem symDiffBound (K : SchwartzMap ℝ ℂ) :
    ∃ A : ℝ, 0 < A ∧ ∀ (σ ρ : ℝ) (θ : ℝ), 1 ≤ ρ → ρ ≤ σ → σ ≤ 2 * ρ →
      ‖bumpSymR K σ θ - bumpSymR K ρ θ‖
        ≤ A * (ρ ^ 2)⁻¹ + A * min (ρ * Work.KMTAreas.A7.nearDist θ)
            ((ρ * Work.KMTAreas.A7.nearDist θ) ^ 2)⁻¹ := by
  obtain ⟨B, hBpos, hB⟩ := fourier_decay_sq' K
  obtain ⟨B₀, hB₀nn, hB₀⟩ := Work.KMTAreas.tsum_inv_sq_shift_le
  set L : ℝ := |(SchwartzMap.seminorm ℂ 0 1) (𝓕 K)| + 1 with hL
  have hLpos : 0 < L := by rw [hL]; positivity
  have hderiv : ∀ x : ℝ, ‖iteratedDeriv 1 (fun y : ℝ => (𝓕 K) y) x‖ ≤ L := by
    intro x
    have h := SchwartzMap.le_seminorm' ℂ 0 1 (𝓕 K) x
    rw [pow_zero, one_mul] at h
    rw [hL]
    have h2 := le_abs_self ((SchwartzMap.seminorm ℂ 0 1) (𝓕 K))
    linarith
  have hLip : ∀ x y : ℝ, ‖(𝓕 K) x - (𝓕 K) y‖ ≤ L * |x - y| := by
    intro x y
    have hseg := norm_image_sub_le_of_norm_deriv_le_segment' (f := fun z : ℝ => (𝓕 K) z)
      (f' := deriv (fun z : ℝ => (𝓕 K) z)) (a := min x y) (b := max x y) (C := L)
      (fun z _ => (((SchwartzMap.differentiable (𝓕 K)).differentiableAt).hasFDerivAt.hasDerivAt).hasDerivWithinAt)
      (fun z _ => by
        have h := hderiv z
        rwa [iteratedDeriv_one] at h)
      (max x y) (Set.mem_Icc.mpr ⟨min_le_max, le_rfl⟩)
    rw [max_sub_min_eq_abs] at hseg
    rcases le_total x y with h | h
    · rw [max_eq_right h, min_eq_left h, abs_sub_comm] at hseg
      rwa [norm_sub_rev]
    · rw [max_eq_left h, min_eq_right h, abs_sub_comm] at hseg
      exact hseg
  have hApos : 0 < max L (2 * B) + 32 * B * B₀ + 1 := by
    have h1 : 0 < max L (2 * B) := lt_of_lt_of_le hLpos (le_max_left _ _)
    have h2 : 0 ≤ 32 * B * B₀ := by positivity
    linarith
  refine ⟨max L (2 * B) + 32 * B * B₀ + 1, hApos, ?_⟩
  intro σ ρ θ hρ hρσ hσ2ρ
  have hρ0 : 0 < ρ := lt_of_lt_of_le one_pos hρ
  have hσ1 : 1 ≤ σ := le_trans hρ hρσ
  have hσ0 : 0 < σ := lt_of_lt_of_le one_pos hσ1
  set k₀ : ℤ := Work.KMTAreas.A7.nearInt θ with hk₀
  set d : ℝ := Work.KMTAreas.A7.nearDist θ with hd
  have hdnn : 0 ≤ d := by rw [hd, Work.KMTAreas.A7.nearDist]; positivity
  have hdabs : d = |θ - (k₀ : ℝ)| := by rw [hd, hk₀, Work.KMTAreas.A7.nearDist]
  have hsum_σ := summable_symDiff_side K hσ1 θ
  have hsum_ρ := summable_symDiff_side K hρ θ
  have hJsum : Summable (fun k : ℤ =>
      ((𝓕 K) (σ * ((k : ℝ) - θ)) - (𝓕 K) (ρ * ((k : ℝ) - θ)))) := hsum_σ.sub hsum_ρ
  have hmin_nn : 0 ≤ min (ρ * d) ((ρ * d) ^ 2)⁻¹ := le_min (by positivity) (by positivity)
  have hdρ_nn : 0 ≤ ρ * d := mul_nonneg hρ0.le hdnn
  -- ### the nearest Poisson node
  have hnear : ‖(𝓕 K) (σ * ((k₀ : ℝ) - θ)) - (𝓕 K) (ρ * ((k₀ : ℝ) - θ))‖
      ≤ max L (2 * B) * min (ρ * d) ((ρ * d) ^ 2)⁻¹ := by
    have hk₀d : |(k₀ : ℝ) - θ| = d := by rw [hdabs, abs_sub_comm]
    have hσarg : |σ * ((k₀ : ℝ) - θ)| = σ * d := by
      rw [abs_mul, abs_of_nonneg hσ0.le, hk₀d]
    have hρarg : |ρ * ((k₀ : ℝ) - θ)| = ρ * d := by
      rw [abs_mul, abs_of_nonneg hρ0.le, hk₀d]
    have hdec1 : ‖(𝓕 K) (σ * ((k₀ : ℝ) - θ))‖ ≤ B * ((1 + σ * d) ^ 2)⁻¹ := by
      have h := hB (σ * ((k₀ : ℝ) - θ))
      rwa [hσarg] at h
    have hdec2 : ‖(𝓕 K) (ρ * ((k₀ : ℝ) - θ))‖ ≤ B * ((1 + ρ * d) ^ 2)⁻¹ := by
      have h := hB (ρ * ((k₀ : ℝ) - θ))
      rwa [hρarg] at h
    have hmono : ((1 + σ * d) ^ 2)⁻¹ ≤ ((1 + ρ * d) ^ 2)⁻¹ := by
      apply (inv_le_inv₀ (by positivity) (by positivity)).mpr
      have h : ρ * d ≤ σ * d := mul_le_mul_of_nonneg_right hρσ hdnn
      nlinarith [h, hdρ_nn, mul_nonneg hσ0.le hdnn]
    have hdec : ‖(𝓕 K) (σ * ((k₀ : ℝ) - θ)) - (𝓕 K) (ρ * ((k₀ : ℝ) - θ))‖
        ≤ 2 * B * ((1 + ρ * d) ^ 2)⁻¹ := by
      calc ‖(𝓕 K) (σ * ((k₀ : ℝ) - θ)) - (𝓕 K) (ρ * ((k₀ : ℝ) - θ))‖
          ≤ ‖(𝓕 K) (σ * ((k₀ : ℝ) - θ))‖ + ‖(𝓕 K) (ρ * ((k₀ : ℝ) - θ))‖ := norm_sub_le _ _
        _ ≤ B * ((1 + σ * d) ^ 2)⁻¹ + B * ((1 + ρ * d) ^ 2)⁻¹ := add_le_add hdec1 hdec2
        _ ≤ B * ((1 + ρ * d) ^ 2)⁻¹ + B * ((1 + ρ * d) ^ 2)⁻¹ :=
            add_le_add (mul_le_mul_of_nonneg_left hmono hBpos.le) le_rfl
        _ = 2 * B * ((1 + ρ * d) ^ 2)⁻¹ := by ring
    have hlip : ‖(𝓕 K) (σ * ((k₀ : ℝ) - θ)) - (𝓕 K) (ρ * ((k₀ : ℝ) - θ))‖ ≤ L * (ρ * d) := by
      have h := hLip (σ * ((k₀ : ℝ) - θ)) (ρ * ((k₀ : ℝ) - θ))
      have harg : |σ * ((k₀ : ℝ) - θ) - ρ * ((k₀ : ℝ) - θ)| = (σ - ρ) * d := by
        rw [show σ * ((k₀ : ℝ) - θ) - ρ * ((k₀ : ℝ) - θ) = (σ - ρ) * ((k₀ : ℝ) - θ) by ring,
          abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ σ - ρ), hk₀d]
      rw [harg] at h
      calc ‖(𝓕 K) (σ * ((k₀ : ℝ) - θ)) - (𝓕 K) (ρ * ((k₀ : ℝ) - θ))‖
          ≤ L * ((σ - ρ) * d) := h
        _ ≤ L * (ρ * d) := by
            apply mul_le_mul_of_nonneg_left _ hLpos.le
            nlinarith [hσ2ρ, hdnn]
    rcases lt_or_ge (ρ * d) 1 with hlt | hge
    · have hmin : min (ρ * d) ((ρ * d) ^ 2)⁻¹ = ρ * d := by
        apply min_eq_left
        rcases eq_or_lt_of_le hdρ_nn with h0 | h0
        · rw [← h0]; norm_num
        · have h1 : 1 ≤ (ρ * d)⁻¹ := (one_le_inv₀ h0).mpr (le_of_lt hlt)
          have h2 : (0 : ℝ) ≤ (ρ * d)⁻¹ := le_of_lt (inv_pos.mpr h0)
          rw [← inv_pow]
          nlinarith [h1, h2, sq_nonneg ((ρ * d)⁻¹)]
      rw [hmin]
      calc ‖(𝓕 K) (σ * ((k₀ : ℝ) - θ)) - (𝓕 K) (ρ * ((k₀ : ℝ) - θ))‖
          ≤ L * (ρ * d) := hlip
        _ ≤ max L (2 * B) * (ρ * d) := mul_le_mul_of_nonneg_right (le_max_left _ _) hdρ_nn
    · have h1 : (1 : ℝ) ≤ ρ * d := hge
      have hmin : min (ρ * d) ((ρ * d) ^ 2)⁻¹ = ((ρ * d) ^ 2)⁻¹ := by
        apply min_eq_right
        have h2 : (ρ * d)⁻¹ ≤ 1 := (inv_le_one₀ (by linarith)).mpr h1
        have h3 : (0 : ℝ) ≤ (ρ * d)⁻¹ := le_of_lt (inv_pos.mpr (by linarith))
        rw [← inv_pow]
        nlinarith [h2, h3, sq_nonneg ((ρ * d)⁻¹)]
      rw [hmin]
      have hdec' : ‖(𝓕 K) (σ * ((k₀ : ℝ) - θ)) - (𝓕 K) (ρ * ((k₀ : ℝ) - θ))‖
          ≤ 2 * B * ((ρ * d) ^ 2)⁻¹ := by
        have h2 : ((1 + ρ * d) ^ 2)⁻¹ ≤ ((ρ * d) ^ 2)⁻¹ := by
          apply (inv_le_inv₀ (by positivity) (by positivity)).mpr
          nlinarith [h1]
        calc ‖(𝓕 K) (σ * ((k₀ : ℝ) - θ)) - (𝓕 K) (ρ * ((k₀ : ℝ) - θ))‖
            ≤ 2 * B * ((1 + ρ * d) ^ 2)⁻¹ := hdec
          _ ≤ 2 * B * ((ρ * d) ^ 2)⁻¹ := mul_le_mul_of_nonneg_left h2 (by positivity)
      calc ‖(𝓕 K) (σ * ((k₀ : ℝ) - θ)) - (𝓕 K) (ρ * ((k₀ : ℝ) - θ))‖
          ≤ 2 * B * ((ρ * d) ^ 2)⁻¹ := hdec'
        _ ≤ max L (2 * B) * ((ρ * d) ^ 2)⁻¹ :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  -- ### the far tail
  have hfar : ‖∑' k : ℤ, (if k = k₀ then (0 : ℂ) else
        ((𝓕 K) (σ * ((k : ℝ) - θ)) - (𝓕 K) (ρ * ((k : ℝ) - θ))))‖
      ≤ 32 * B * B₀ * (ρ ^ 2)⁻¹ := by
    have hmaj : Summable (fun k : ℤ =>
        32 * B * (ρ ^ 2)⁻¹ * (1 + ((k : ℝ) - (k₀ : ℝ)) ^ 2)⁻¹) :=
      Summable.mul_left (32 * B * (ρ ^ 2)⁻¹) (by
        refine ((hB₀ (-(k₀ : ℝ))).1).congr fun k => ?_
        congr 1
        ring)
    have hpoint_if : ∀ k : ℤ, (if k = k₀ then (0 : ℝ) else
          ‖(𝓕 K) (σ * ((k : ℝ) - θ)) - (𝓕 K) (ρ * ((k : ℝ) - θ))‖)
        ≤ 32 * B * (ρ ^ 2)⁻¹ * (1 + ((k : ℝ) - (k₀ : ℝ)) ^ 2)⁻¹ := by
      intro k
      by_cases hk : k = k₀
      · rw [if_pos hk]; positivity
      · rw [if_neg hk]
        have hj : 1 ≤ |(k : ℝ) - (k₀ : ℝ)| := by
          have h1 : (1 : ℤ) ≤ |k - k₀| := Int.one_le_abs (sub_ne_zero.mpr hk)
          have h2 : (1 : ℝ) ≤ ((|k - k₀| : ℤ) : ℝ) := by exact_mod_cast h1
          rwa [Int.cast_abs, Int.cast_sub] at h2
        have hX : (1 : ℝ) ≤ ((k : ℝ) - (k₀ : ℝ)) ^ 2 := by
          nlinarith [hj, abs_nonneg ((k : ℝ) - (k₀ : ℝ)), sq_abs ((k : ℝ) - (k₀ : ℝ))]
        have harm : |(k : ℝ) - (k₀ : ℝ)| / 2 ≤ |(k : ℝ) - θ| := by
          have h := Work.KMTAreas.A7LoLin.abs_sub_nearInt_le_two_mul_abs_sub θ
            (k := k) (by simpa [hk₀] using hk)
          rw [← hk₀, abs_sub_comm θ] at h
          linarith
        have hkθ : 0 < |(k : ℝ) - θ| := by linarith [hj, harm]
        have hu : 0 < ρ * |(k : ℝ) - θ| := by
          have h := mul_pos hρ0 hkθ
          linarith
        have hkk : 0 < |(k : ℝ) - (k₀ : ℝ)| := by linarith
        have ha : |σ * ((k : ℝ) - θ)| = σ * |(k : ℝ) - θ| := by
          rw [abs_mul, abs_of_nonneg hσ0.le]
        have hb : |ρ * ((k : ℝ) - θ)| = ρ * |(k : ℝ) - θ| := by
          rw [abs_mul, abs_of_nonneg hρ0.le]
        have h1 : ‖(𝓕 K) (σ * ((k : ℝ) - θ))‖ ≤ B * ((1 + σ * |(k : ℝ) - θ|) ^ 2)⁻¹ := by
          have h := hB (σ * ((k : ℝ) - θ))
          rwa [ha] at h
        have h2 : ‖(𝓕 K) (ρ * ((k : ℝ) - θ))‖ ≤ B * ((1 + ρ * |(k : ℝ) - θ|) ^ 2)⁻¹ := by
          have h := hB (ρ * ((k : ℝ) - θ))
          rwa [hb] at h
        have h3 : ((1 + σ * |(k : ℝ) - θ|) ^ 2)⁻¹ ≤ ((1 + ρ * |(k : ℝ) - θ|) ^ 2)⁻¹ := by
          apply (inv_le_inv₀ (by positivity) (by positivity)).mpr
          have : ρ * |(k : ℝ) - θ| ≤ σ * |(k : ℝ) - θ| :=
            mul_le_mul_of_nonneg_right hρσ (abs_nonneg _)
          nlinarith
        have hdec : ‖(𝓕 K) (σ * ((k : ℝ) - θ)) - (𝓕 K) (ρ * ((k : ℝ) - θ))‖
            ≤ 2 * B * ((1 + ρ * |(k : ℝ) - θ|) ^ 2)⁻¹ := by
          calc ‖(𝓕 K) (σ * ((k : ℝ) - θ)) - (𝓕 K) (ρ * ((k : ℝ) - θ))‖
              ≤ ‖(𝓕 K) (σ * ((k : ℝ) - θ))‖ + ‖(𝓕 K) (ρ * ((k : ℝ) - θ))‖ := norm_sub_le _ _
            _ ≤ B * ((1 + σ * |(k : ℝ) - θ|) ^ 2)⁻¹ + B * ((1 + ρ * |(k : ℝ) - θ|) ^ 2)⁻¹ :=
                add_le_add h1 h2
            _ ≤ B * ((1 + ρ * |(k : ℝ) - θ|) ^ 2)⁻¹ + B * ((1 + ρ * |(k : ℝ) - θ|) ^ 2)⁻¹ :=
                add_le_add (mul_le_mul_of_nonneg_left h3 hBpos.le) le_rfl
            _ = 2 * B * ((1 + ρ * |(k : ℝ) - θ|) ^ 2)⁻¹ := by ring
        have hstep1 : 2 * B * ((1 + ρ * |(k : ℝ) - θ|) ^ 2)⁻¹
            ≤ 2 * B * ((ρ * |(k : ℝ) - θ|) ^ 2)⁻¹ := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply (inv_le_inv₀ (by positivity) (by positivity)).mpr
          nlinarith [hu.le]
        have hstep2 : 2 * B * ((ρ * |(k : ℝ) - θ|) ^ 2)⁻¹
            ≤ 2 * B * (4 * (ρ ^ 2)⁻¹ * ((|(k : ℝ) - (k₀ : ℝ)|) ^ 2)⁻¹) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have hmid : ρ * |(k : ℝ) - (k₀ : ℝ)| / 2 ≤ ρ * |(k : ℝ) - θ| := by
            have h := mul_le_mul_of_nonneg_left harm hρ0.le
            linarith
          have hmidpos : 0 < ρ * |(k : ℝ) - (k₀ : ℝ)| / 2 := by
            have h := mul_pos hρ0 hkk
            linarith
          have h6 : ((ρ * |(k : ℝ) - θ|) ^ 2)⁻¹
              ≤ ((ρ * |(k : ℝ) - (k₀ : ℝ)| / 2) ^ 2)⁻¹ := by
            apply (inv_le_inv₀ (by positivity) (by positivity)).mpr
            exact pow_le_pow_left₀ hmidpos.le hmid 2
          have h7 : ((ρ * |(k : ℝ) - (k₀ : ℝ)| / 2) ^ 2)⁻¹
              = 4 * (ρ ^ 2)⁻¹ * ((|(k : ℝ) - (k₀ : ℝ)|) ^ 2)⁻¹ := by
            rw [div_pow, mul_pow, inv_div, div_eq_mul_inv, mul_inv]
            ring
          rw [← h7]
          exact h6
        have hstep3 : 2 * B * (4 * (ρ ^ 2)⁻¹ * ((|(k : ℝ) - (k₀ : ℝ)|) ^ 2)⁻¹)
            ≤ 2 * B * (16 * (ρ ^ 2)⁻¹ * (1 + ((k : ℝ) - (k₀ : ℝ)) ^ 2)⁻¹) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [sq_abs]
          have hkey : 4 * (((k : ℝ) - (k₀ : ℝ)) ^ 2)⁻¹
              ≤ 16 * (1 + ((k : ℝ) - (k₀ : ℝ)) ^ 2)⁻¹ := by
            have h8 : 4 * (((k : ℝ) - (k₀ : ℝ)) ^ 2)⁻¹
                = ((((k : ℝ) - (k₀ : ℝ)) ^ 2) / 4)⁻¹ := by
              rw [inv_div, div_eq_mul_inv]
            have h9 : 16 * (1 + ((k : ℝ) - (k₀ : ℝ)) ^ 2)⁻¹
                = ((1 + ((k : ℝ) - (k₀ : ℝ)) ^ 2) / 16)⁻¹ := by
              rw [inv_div, div_eq_mul_inv]
            rw [h8, h9]
            apply (inv_le_inv₀ (by positivity) (by positivity)).mpr
            nlinarith [hX]
          calc 4 * (ρ ^ 2)⁻¹ * (((k : ℝ) - (k₀ : ℝ)) ^ 2)⁻¹
              = (ρ ^ 2)⁻¹ * (4 * (((k : ℝ) - (k₀ : ℝ)) ^ 2)⁻¹) := by ring
            _ ≤ (ρ ^ 2)⁻¹ * (16 * (1 + ((k : ℝ) - (k₀ : ℝ)) ^ 2)⁻¹) :=
                mul_le_mul_of_nonneg_left hkey (by positivity)
            _ = 16 * (ρ ^ 2)⁻¹ * (1 + ((k : ℝ) - (k₀ : ℝ)) ^ 2)⁻¹ := by ring
        calc ‖(𝓕 K) (σ * ((k : ℝ) - θ)) - (𝓕 K) (ρ * ((k : ℝ) - θ))‖
            ≤ 2 * B * ((1 + ρ * |(k : ℝ) - θ|) ^ 2)⁻¹ := hdec
          _ ≤ 2 * B * ((ρ * |(k : ℝ) - θ|) ^ 2)⁻¹ := hstep1
          _ ≤ 2 * B * (4 * (ρ ^ 2)⁻¹ * ((|(k : ℝ) - (k₀ : ℝ)|) ^ 2)⁻¹) := hstep2
          _ ≤ 2 * B * (16 * (ρ ^ 2)⁻¹ * (1 + ((k : ℝ) - (k₀ : ℝ)) ^ 2)⁻¹) := hstep3
          _ = 32 * B * (ρ ^ 2)⁻¹ * (1 + ((k : ℝ) - (k₀ : ℝ)) ^ 2)⁻¹ := by ring
    have hnorm_eq : (fun k : ℤ => ‖(if k = k₀ then (0 : ℂ) else
          ((𝓕 K) (σ * ((k : ℝ) - θ)) - (𝓕 K) (ρ * ((k : ℝ) - θ))))‖)
        = (fun k : ℤ => (if k = k₀ then (0 : ℝ) else
          ‖((𝓕 K) (σ * ((k : ℝ) - θ)) - (𝓕 K) (ρ * ((k : ℝ) - θ)))‖)) := by
      funext k
      by_cases h : k = k₀ <;> simp [h]
    have hpoint : ∀ k : ℤ, ‖(if k = k₀ then (0 : ℂ) else
          ((𝓕 K) (σ * ((k : ℝ) - θ)) - (𝓕 K) (ρ * ((k : ℝ) - θ))))‖
        ≤ 32 * B * (ρ ^ 2)⁻¹ * (1 + ((k : ℝ) - (k₀ : ℝ)) ^ 2)⁻¹ := fun k => by
      rw [congrFun hnorm_eq k]
      exact hpoint_if k
    have hinorm : Summable (fun k : ℤ => ‖(if k = k₀ then (0 : ℂ) else
          ((𝓕 K) (σ * ((k : ℝ) - θ)) - (𝓕 K) (ρ * ((k : ℝ) - θ))))‖) :=
      Summable.of_nonneg_of_le (fun k => by positivity) (fun k => hpoint k) hmaj
    have hinorm' : Summable (fun k : ℤ => (if k = k₀ then (0 : ℝ) else
          ‖((𝓕 K) (σ * ((k : ℝ) - θ)) - (𝓕 K) (ρ * ((k : ℝ) - θ)))‖)) := by
      rw [← hnorm_eq]
      exact hinorm
    calc ‖∑' k : ℤ, (if k = k₀ then (0 : ℂ) else
            ((𝓕 K) (σ * ((k : ℝ) - θ)) - (𝓕 K) (ρ * ((k : ℝ) - θ))))‖
        ≤ ∑' k : ℤ, ‖(if k = k₀ then (0 : ℂ) else
            ((𝓕 K) (σ * ((k : ℝ) - θ)) - (𝓕 K) (ρ * ((k : ℝ) - θ))))‖ :=
          norm_tsum_le_tsum_norm hinorm
      _ = ∑' k : ℤ, (if k = k₀ then (0 : ℝ) else
            ‖((𝓕 K) (σ * ((k : ℝ) - θ)) - (𝓕 K) (ρ * ((k : ℝ) - θ)))‖) := by rw [hnorm_eq]
      _ ≤ ∑' k : ℤ, 32 * B * (ρ ^ 2)⁻¹ * (1 + ((k : ℝ) - (k₀ : ℝ)) ^ 2)⁻¹ := by
          refine Summable.tsum_le_tsum (fun k => ?_) hinorm' hmaj
          exact hpoint_if k
      _ = 32 * B * (ρ ^ 2)⁻¹ * ∑' k : ℤ, (1 + ((k : ℝ) - (k₀ : ℝ)) ^ 2)⁻¹ :=
          tsum_mul_left
      _ ≤ 32 * B * (ρ ^ 2)⁻¹ * B₀ := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          refine le_trans (le_of_eq (tsum_congr fun k => ?_)) (hB₀ (-(k₀ : ℝ))).2
          congr 1
          ring
      _ = 32 * B * B₀ * (ρ ^ 2)⁻¹ := by ring
  -- ### assembly
  rw [bumpSymR_diff_eq K hσ1 hρ θ, hJsum.tsum_eq_add_tsum_ite k₀]
  refine le_trans (norm_add_le _ _) ?_
  have hA1 : max L (2 * B) ≤ max L (2 * B) + 32 * B * B₀ + 1 := by
    have h : (0 : ℝ) ≤ 32 * B * B₀ + 1 := by positivity
    linarith
  have hA2 : 32 * B * B₀ ≤ max L (2 * B) + 32 * B * B₀ + 1 := by
    linarith [le_max_left L (2 * B)]
  have hmul1 : max L (2 * B) * min (ρ * d) ((ρ * d) ^ 2)⁻¹
      ≤ (max L (2 * B) + 32 * B * B₀ + 1) * min (ρ * d) ((ρ * d) ^ 2)⁻¹ :=
    mul_le_mul_of_nonneg_right hA1 hmin_nn
  have hmul2 : 32 * B * B₀ * (ρ ^ 2)⁻¹
      ≤ (max L (2 * B) + 32 * B * B₀ + 1) * (ρ ^ 2)⁻¹ :=
    mul_le_mul_of_nonneg_right hA2 (by positivity)
  calc ‖(𝓕 K) (σ * ((k₀ : ℝ) - θ)) - (𝓕 K) (ρ * ((k₀ : ℝ) - θ))‖
        + ‖∑' k : ℤ, (if k = k₀ then (0 : ℂ) else
          ((𝓕 K) (σ * ((k : ℝ) - θ)) - (𝓕 K) (ρ * ((k : ℝ) - θ))))‖
      ≤ max L (2 * B) * min (ρ * d) ((ρ * d) ^ 2)⁻¹ + 32 * B * B₀ * (ρ ^ 2)⁻¹ :=
        add_le_add hnear hfar
    _ ≤ (max L (2 * B) + 32 * B * B₀ + 1) * min (ρ * d) ((ρ * d) ^ 2)⁻¹
        + (max L (2 * B) + 32 * B * B₀ + 1) * (ρ ^ 2)⁻¹ := add_le_add hmul1 hmul2
    _ = (max L (2 * B) + 32 * B * B₀ + 1) * (ρ ^ 2)⁻¹
        + (max L (2 * B) + 32 * B * B₀ + 1) * min (ρ * d) ((ρ * d) ^ 2)⁻¹ := by ring

/-! ## 5. The lacunary absorption -/

/-- For `0 ≤ v ≤ u ≤ 2v` one has `(u²)⁻¹ ≤ 2 (v²)⁻¹` (with `x⁻¹ = 0` at `x = 0`). -/
lemma inv_sq_le_two_inv_sq {u v : ℝ} (hv : 0 ≤ v) (h1 : v ≤ u) (h2 : u ≤ 2 * v) :
    (u ^ 2)⁻¹ ≤ 2 * (v ^ 2)⁻¹ := by
  rcases eq_or_lt_of_le hv with h0 | h0
  · have h3 : u = 0 := by linarith
    rw [← h0, h3]
    norm_num
  · have hu : 0 < u := lt_of_lt_of_le h0 h1
    have h4 : (u ^ 2)⁻¹ ≤ (v ^ 2)⁻¹ :=
      (inv_le_inv₀ (by positivity) (by positivity)).mpr (by nlinarith)
    have h5 : 0 ≤ (v ^ 2)⁻¹ := by positivity
    linarith

/-- **Lacunary absorption.**  For a `2`-lacunary real family `a` with `1 ≤ aₙ`, every `d ≥ 0`,
every `C ≥ 0` and every finite `U`,
`∑_{n ∈ U} (C (aₙ²)⁻¹ + C min (aₙ d) (aₙ d)⁻²) ≤ 12 C`.

The first part is `∑ (aₙ²)⁻¹ ≤ ∑ 4^{-n} = 4/3 ≤ 2`; the second part is the floor reduction to
`Work.A7Hi2.lacSumMinSq` (which gives `≤ 4` for integer scales, hence `≤ 8` here). -/
theorem lacSumReal {a : ℕ → ℝ} (ha1 : ∀ n, 1 ≤ a n) (ha2 : ∀ n, 2 * a n ≤ a (n + 1))
    (C : ℝ) (hC : 0 ≤ C) (d : ℝ) (hd : 0 ≤ d) (U : Finset ℕ) :
    ∑ n ∈ U, (C * (a n ^ 2)⁻¹ + C * min (a n * d) ((a n * d) ^ 2)⁻¹) ≤ 12 * C := by
  have hpow : ∀ n : ℕ, (2 : ℝ) ^ n ≤ a n := by
    intro n
    induction n with
    | zero => simpa using ha1 0
    | succ k ih =>
        rw [pow_succ]
        linarith [ha2 k, ih]
  have hpart1 : ∑ n ∈ U, (a n ^ 2)⁻¹ ≤ 2 := by
    have hpt : ∀ n ∈ U, (a n ^ 2)⁻¹ ≤ ((4 : ℝ)⁻¹) ^ n := by
      intro n _
      have h1 : (2 : ℝ) ^ n ≤ a n := hpow n
      have h2 : (2 : ℝ) ^ n * (2 : ℝ) ^ n ≤ a n * a n :=
        mul_le_mul h1 h1 (by positivity) (by linarith [ha1 n])
      have h3 : (2 : ℝ) ^ n * (2 : ℝ) ^ n = (4 : ℝ) ^ n := by
        rw [← mul_pow]
        norm_num
      have h4 : (a n * a n)⁻¹ ≤ ((4 : ℝ) ^ n)⁻¹ := by
        refine (inv_le_inv₀ (by nlinarith [ha1 n]) (by positivity)).mpr ?_
        rw [← h3]
        exact h2
      calc (a n ^ 2)⁻¹ = (a n * a n)⁻¹ := by rw [pow_two]
        _ ≤ ((4 : ℝ) ^ n)⁻¹ := h4
        _ = ((4 : ℝ)⁻¹) ^ n := by rw [← inv_pow]
    calc ∑ n ∈ U, (a n ^ 2)⁻¹ ≤ ∑ n ∈ U, ((4 : ℝ)⁻¹) ^ n := Finset.sum_le_sum hpt
      _ ≤ ∑' n : ℕ, ((4 : ℝ)⁻¹) ^ n :=
          Summable.sum_le_tsum U (fun n _ => by positivity)
            (summable_geometric_of_norm_lt_one (by norm_num : ‖((4 : ℝ)⁻¹)‖ < 1))
      _ = (1 - (4 : ℝ)⁻¹)⁻¹ := tsum_geometric_of_norm_lt_one (by norm_num : ‖((4 : ℝ)⁻¹)‖ < 1)
      _ ≤ 2 := by norm_num
  have hpart2 : ∑ n ∈ U, min (a n * d) ((a n * d) ^ 2)⁻¹ ≤ 8 := by
    set b : ℕ → ℕ := fun n => ⌊a n⌋₊ with hb
    have hb1 : ∀ n, 1 ≤ b n := by
      intro n
      rw [hb]
      exact Nat.le_floor (by exact_mod_cast ha1 n)
    have hb2 : ∀ n, 2 * b n ≤ b (n + 1) := by
      intro n
      rw [hb]
      apply Nat.le_floor
      have hle : ((⌊a n⌋₊ : ℕ) : ℝ) ≤ a n := Nat.floor_le (by linarith [ha1 n])
      push_cast
      linarith [ha2 n, hle]
    have hint := Work.A7Hi2.lacSumMinSq hb1 hb2 d hd U
    have hpt : ∀ n ∈ U, min (a n * d) ((a n * d) ^ 2)⁻¹
        ≤ 2 * min (((b n : ℕ) : ℝ) * d) (((((b n : ℕ) : ℝ) * d) ^ 2)⁻¹) := by
      intro n _
      have hbn : ((b n : ℕ) : ℝ) ≤ a n := by
        rw [hb]; exact Nat.floor_le (by linarith [ha1 n])
      have hbn1 : (1 : ℝ) ≤ ((b n : ℕ) : ℝ) := by
        rw [hb]; exact_mod_cast (hb1 n)
      have han : a n ≤ 2 * ((b n : ℕ) : ℝ) := by
        have hlt : a n < ((b n : ℕ) : ℝ) + 1 := by
          rw [hb]; exact Nat.lt_floor_add_one (a n)
        linarith
      have hv : 0 ≤ ((b n : ℕ) : ℝ) * d := mul_nonneg (by linarith) hd
      have hvu : ((b n : ℕ) : ℝ) * d ≤ a n * d := mul_le_mul_of_nonneg_right hbn hd
      have huv : a n * d ≤ 2 * (((b n : ℕ) : ℝ) * d) := by
        have h := mul_le_mul_of_nonneg_right han hd
        linarith
      have hAB : ((a n * d) ^ 2)⁻¹ ≤ 2 * (((((b n : ℕ) : ℝ) * d) ^ 2)⁻¹) :=
        inv_sq_le_two_inv_sq hv hvu huv
      calc min (a n * d) ((a n * d) ^ 2)⁻¹
          ≤ min (2 * (((b n : ℕ) : ℝ) * d)) (2 * (((((b n : ℕ) : ℝ) * d) ^ 2)⁻¹)) :=
            le_min (le_trans (min_le_left _ _) huv) (le_trans (min_le_right _ _) hAB)
        _ = 2 * min (((b n : ℕ) : ℝ) * d) (((((b n : ℕ) : ℝ) * d) ^ 2)⁻¹) :=
            (mul_min_of_nonneg (a := 2) (((b n : ℕ) : ℝ) * d) (((((b n : ℕ) : ℝ) * d) ^ 2)⁻¹)
              (by norm_num)).symm
    calc ∑ n ∈ U, min (a n * d) ((a n * d) ^ 2)⁻¹
        ≤ ∑ n ∈ U, 2 * min (((b n : ℕ) : ℝ) * d) (((((b n : ℕ) : ℝ) * d) ^ 2)⁻¹) :=
          Finset.sum_le_sum hpt
      _ = 2 * ∑ n ∈ U, min (((b n : ℕ) : ℝ) * d) (((((b n : ℕ) : ℝ) * d) ^ 2)⁻¹) := by
          rw [Finset.mul_sum]
      _ ≤ 2 * 4 := by linarith [hint]
      _ = 8 := by norm_num
  calc ∑ n ∈ U, (C * (a n ^ 2)⁻¹ + C * min (a n * d) ((a n * d) ^ 2)⁻¹)
      = C * (∑ n ∈ U, (a n ^ 2)⁻¹) + C * (∑ n ∈ U, min (a n * d) ((a n * d) ^ 2)⁻¹) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ C * 2 + C * 8 := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hpart1 hC
        · exact mul_le_mul_of_nonneg_left hpart2 hC
    _ ≤ 12 * C := by linarith

/-! ## 6. The symbol identity for `symDiffR` -/

/-- The Fourier series of the real-scale bump kernel converges absolutely. -/
lemma summable_bumpKernR_chr (K : SchwartzMap ℝ ℂ) {σ : ℝ} (hσ : 1 ≤ σ) (θ : ℝ) :
    Summable (fun j : ℤ => bumpKernR K σ j * Work.KMTAreas.ADev.chr j θ) := by
  obtain ⟨B, hBpos, hB⟩ := schwartz_decay_sq K
  obtain ⟨B₀, hB₀nn, hB₀⟩ := Work.KMTAreas.tsum_inv_sq_shift_le
  have hσ0 : 0 < σ := lt_of_lt_of_le one_pos hσ
  have hσne : σ ≠ 0 := ne_of_gt hσ0
  have hsum : Summable (fun j : ℤ => (1 + ((j : ℝ)) ^ 2)⁻¹) := by
    have h := (hB₀ 0).1
    refine h.congr fun j => ?_
    rw [one_div]
    congr 1
    ring
  refine Summable.of_norm_bounded (Summable.mul_left (B * σ) hsum) fun j => ?_
  rw [bumpKernR, norm_mul, norm_mul, Work.KMTAreas.ADev.norm_chr, mul_one]
  have hcoe1 : ((1 : ℂ) / ((σ : ℝ) : ℂ)) = (((1 : ℝ) / σ : ℝ) : ℂ) := by push_cast; ring
  rw [hcoe1]
  have hfac : ‖(((1 : ℝ) / σ : ℝ) : ℂ)‖ = 1 / σ := by
    have h : ‖(((1 : ℝ) / σ : ℝ) : ℂ)‖ = |(1 : ℝ) / σ| := RCLike.norm_ofReal _
    rw [h, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / σ)]
  rw [hfac]
  have h := hB ((j : ℝ) / σ)
  rw [abs_div, abs_of_nonneg hσ0.le] at h
  have h1 : (1 / σ) * ‖K ((j : ℝ) / σ)‖
      ≤ (1 / σ) * (B * ((1 + |(j : ℝ)| / σ) ^ 2)⁻¹) :=
    mul_le_mul_of_nonneg_left h (by positivity)
  have hkey : ((1 + |(j : ℝ)| / σ) ^ 2)⁻¹ ≤ σ ^ 2 * (1 + (j : ℝ) ^ 2)⁻¹ := by
    have h3 : 1 + |(j : ℝ)| / σ = (σ + |(j : ℝ)|) / σ := by
      rw [add_div, div_self hσne]
    have h4 : (1 : ℝ) + (j : ℝ) ^ 2 ≤ (σ + |(j : ℝ)|) ^ 2 := by
      have h5 : (1 : ℝ) ≤ σ ^ 2 := by nlinarith
      nlinarith [abs_nonneg (j : ℝ), sq_abs (j : ℝ), sq_nonneg (σ + |(j : ℝ)|)]
    rw [h3, div_pow, inv_div, div_eq_mul_inv]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact (inv_le_inv₀ (by positivity) (by positivity)).mpr h4
  calc (1 / σ) * ‖K ((j : ℝ) / σ)‖
      ≤ (1 / σ) * (B * ((1 + |(j : ℝ)| / σ) ^ 2)⁻¹) := h1
    _ ≤ (1 / σ) * (B * (σ ^ 2 * (1 + (j : ℝ) ^ 2)⁻¹)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hkey hBpos.le) (by positivity)
    _ = (B * σ) * (1 + (j : ℝ) ^ 2)⁻¹ := by
        field_simp

/-- **`symDiffR` is the difference of the two Poisson symbols.** -/
lemma symDiffR_eq (K : SchwartzMap ℝ ℂ) {σ ρ : ℝ} (hσ : 1 ≤ σ) (hρ : 1 ≤ ρ) (θ : ℝ) :
    symDiffR K σ ρ θ = bumpSymR K σ θ - bumpSymR K ρ θ := by
  have h1 : Summable (fun j : ℤ => bumpKernR K σ j * Work.KMTAreas.ADev.chr j θ) :=
    summable_bumpKernR_chr K hσ θ
  have h2 : Summable (fun j : ℤ => bumpKernR K ρ j * Work.KMTAreas.ADev.chr j θ) :=
    summable_bumpKernR_chr K hρ θ
  rw [symDiffR, ← poissonReal K hσ θ, ← poissonReal K hρ θ, ← h1.tsum_sub h2]
  refine tsum_congr fun j => ?_
  simp only [diffKernR]
  ring

/-! ## 7. The overlap bound -/

theorem symDiffR_overlap (K : SchwartzMap ℝ ℂ) :
    ∃ A : ℝ, 0 < A ∧ ∀ (σ ρ : ℕ → ℝ), (∀ n, 1 ≤ σ n) → (∀ n, 2 * σ n ≤ σ (n + 1)) →
      (∀ n, 1 ≤ ρ n) → (∀ n, 2 * ρ n ≤ ρ (n + 1)) →
      (∀ n, ρ n ≤ σ n ∧ σ n ≤ 2 * ρ n) → ∀ (U : Finset ℕ) (θ : ℝ),
      ∑ n ∈ U, ‖symDiffR K (σ n) (ρ n) θ‖ ≤ A := by
  obtain ⟨A₁, hA₁pos, hA₁⟩ := symDiffBound K
  refine ⟨12 * A₁, by positivity, ?_⟩
  intro σ ρ hσ1 hσ2 hρ1 hρ2 hcomp U θ
  have hterm : ∀ n ∈ U, ‖symDiffR K (σ n) (ρ n) θ‖
      ≤ A₁ * ((ρ n) ^ 2)⁻¹
        + A₁ * min (ρ n * Work.KMTAreas.A7.nearDist θ)
            (((ρ n) * Work.KMTAreas.A7.nearDist θ) ^ 2)⁻¹ := by
    intro n _
    have h1 : 1 ≤ ρ n := hρ1 n
    have h3 : ρ n ≤ σ n := (hcomp n).1
    have h4 : σ n ≤ 2 * ρ n := (hcomp n).2
    rw [symDiffR_eq K (le_trans h1 h3) h1 θ]
    exact hA₁ (σ n) (ρ n) θ h1 h3 h4
  have hdnn : 0 ≤ Work.KMTAreas.A7.nearDist θ := by
    rw [Work.KMTAreas.A7.nearDist]
    positivity
  calc ∑ n ∈ U, ‖symDiffR K (σ n) (ρ n) θ‖
      ≤ ∑ n ∈ U, (A₁ * ((ρ n) ^ 2)⁻¹
          + A₁ * min (ρ n * Work.KMTAreas.A7.nearDist θ)
              (((ρ n) * Work.KMTAreas.A7.nearDist θ) ^ 2)⁻¹) := Finset.sum_le_sum hterm
    _ ≤ 12 * A₁ := lacSumReal hρ1 hρ2 A₁ hA₁pos.le (Work.KMTAreas.A7.nearDist θ) hdnn U

end

end Work.A7Hi2
