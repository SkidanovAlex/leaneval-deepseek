/-
# The multiplier bound for the `g`-side bump at `k₂ ≥ 1`

Entry point requested by the large-scale (`Large/`) area of A7: for every polynomial
`P : ℤ[X]`, every `d` with `P.natDegree ≤ d`, every `1 < p` and every lacunarity threshold
`Λ > 1` there is `C > 0` such that for every `k₂ ≥ 1`, every `t ∈ [1/2,1]`, every `Λ`-lacunary
sequence `a ≥ 1`, every finite `U` and every family of coefficients `ε` with `‖ε n‖ ≤ 1`,

  `‖ T_{∑_{n ∈ U} ε_n φ̃_{N_n,t,k₂}} ‖_{L^p → L^p} ≤ C (1 + d k₂)`,

with `N_n = ⌊a n⌋` and `φ̃_{N,t,k₂}(ξ) = φ̃_N(ξ) e(P(Nt) ξ)` the modulated `g`-side bump of §6.

## The proof (the paper's `k₂ ≥ 1` scale split)

For the fixed (`k₂`-independent, because `k₂ ≥ 1`) profile `G = gProfile d 1 = η - η(2^d ·)`:

* `G` is `C²`, compactly supported in `[-1,1]`, real-valued and even, so `𝓕⁻G` is real-valued:
  we set `Ψ := Re (𝓕⁻G)`, and `Ψ` is a Calderón–Zygmund seed for `G`
  (`gProfile_one_cz`, via `isCZSeed_of_fourierInv_explicit` and the uniform bounds
  `gProfile_deriv_bounds`); the mean value theorem (from the bound on `deriv G`) gives
  `‖G ξ‖ ≤ C · min 1 |ξ|`, so `G` is mean zero and its kernel is a wavelet;
* the scale of the `n`-th term is `gScale d ⌊a n⌋ k₂` and the shift is
  `PevalR P (⌊a n⌋ t) / gScale d ⌊a n⌋ k₂`, with
  `|PevalR P (N t)| / gScale d N k₂ ≤ (S+1) 3^d (1 + 2^{d k₂}) ≤ 2^{n₀ + d k₂}`
  (`abs_PevalR_div_gScale_le`), where `S` is the coefficient `ℓ¹`-norm of `P`;
* the family of scales is `2`-lacunary on every residue class mod `M`, where `M` is the
  decimation modulus of `lacBumpDecimation` (`gScale d N k₂ = (lacσ N k₂)^d`, so the `d`-th power
  of a `2`-lacunary family is again `2`-lacunary — `lacunaryFam_pow`);
* splitting the symbol into its fibres mod `M` (`sum_fiberwise_of_maps_to`), each fibre is a
  `czOp` of shifted CZ kernels (`gBump_kernel` + the linearity of `contMulOp`), so `cz_shift_lp`
  bounds it by `C₀ (B (1 + K) + 1)` with `K = n₀ + d k₂`, and the `M` fibres give
  `M C₀ (B (1+K) + 1) ≤ C (1 + d k₂)`.

For `d = 0` the profile is `G = η - η(1 ·) = 0`, so the symbol vanishes identically and the
bound is trivial.

The proof below is the one of `Work.KMTAreas.A7.lacunaryBumpG_mult_bound_k2pos`, re-elaborated
against the current Mathlib (that file no longer compiles because of API drift: `Eventually.of_forall`,
`le_or_lt`, `Nat.one_le_mul`, and two coercion normalisations).
-/
import Mathlib
import Submission.Work.KMTAreas.A7.lacunaryBump_mult_bound_k1pos
import Submission.Work.KMTAreas.A7.varphitildeNt_eq_profile
import Submission.Work.KMTAreas.A7.gProfile_deriv_bounds
import Submission.Work.KMTAreas.A7.abs_PevalR_div_gScale_le
import Submission.Work.A7.varphitildeN_integrable_measurable

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.KMTAreas.A7

open MeasureTheory
open scoped ENNReal NNReal BigOperators FourierTransform


noncomputable section

/-! ## 1.  The frequency scale `gScale d N k₂` as a power of `lacσ N k₂` -/

/-- `gScale d N k₂ = (lacσ N k₂)^d`: the `d`-fold rescaled frequency scale is the `d`-th power of
the `k₁`-side scale taken at the same continuous level `k₂`. -/
private lemma gScale_eq_lacσ_pow (d N k₂ : ℕ) :
    gScale d N k₂ = (lacσ N k₂) ^ d := by
  rw [gScale, lacσ]
  rw [← zpow_natCast ((2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℤ) - (k₂ : ℤ))) d,
    ← zpow_mul]
  congr 1
  ring

/-- The `g`-side frequency scale is positive. -/
private lemma gScale_pos_g (d N k₂ : ℕ) : 0 < gScale d N k₂ := by
  rw [gScale]
  exact zpow_pos (by norm_num) _

/-- The `d`-th power of a `2`-lacunary scale family is again `2`-lacunary when `d ≥ 1`. -/
private lemma lacunaryFam_pow {ι : Type*} {d : ℕ} (hd : 1 ≤ d) {D : Finset ι} {σ : ι → ℝ}
    (h : Work.Analysis.CzShift.LacunaryFam 2 D σ) :
    Work.Analysis.CzShift.LacunaryFam 2 D (fun i => (σ i) ^ d) := by
  refine ⟨fun i hi => pow_pos (h.1 i hi) d, ?_⟩
  intro i hi j hj hij
  have hi0 : 0 < σ i := h.1 i hi
  have hj0 : 0 < σ j := h.1 j hj
  have h2 := h.2 i hi j hj hij
  have hmin : min ((σ i) ^ d) ((σ j) ^ d) = (min (σ i) (σ j)) ^ d := by
    rcases le_total (σ i) (σ j) with hle | hle
    · rw [min_eq_left hle, min_eq_left (pow_le_pow_left₀ hi0.le hle d)]
    · rw [min_eq_right hle, min_eq_right (pow_le_pow_left₀ hj0.le hle d)]
  have hmax : max ((σ i) ^ d) ((σ j) ^ d) = (max (σ i) (σ j)) ^ d := by
    rcases le_total (σ i) (σ j) with hle | hle
    · rw [max_eq_right hle, max_eq_right (pow_le_pow_left₀ hi0.le hle d)]
    · rw [max_eq_left hle, max_eq_left (pow_le_pow_left₀ hj0.le hle d)]
  rw [hmin, hmax]
  calc 2 * (min (σ i) (σ j)) ^ d ≤ 2 ^ d * (min (σ i) (σ j)) ^ d := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hd
    _ = (2 * min (σ i) (σ j)) ^ d := by rw [mul_pow]
    _ ≤ (max (σ i) (σ j)) ^ d := pow_le_pow_left₀ (by positivity) h2 d

/-! ## 2.  The fixed profile `G = gProfile d 1`, its seed and its symbol bounds -/

/-- For `k₂ ≥ 1` the profile `gProfile d k₂` is the fixed function `η - η(2^d ·) = gProfile d 1`. -/
private lemma gProfile_eq_gProfile_one {d k₂ : ℕ} (hk₂ : 1 ≤ k₂) :
    gProfile d k₂ = gProfile d 1 := by
  rw [gProfile, gProfile, if_neg (by omega), if_neg (by norm_num)]

/-- **Dilation + modulation.**  If `(Ψ u : ℂ) = 𝓕⁻ψ u` then the inverse Fourier transform of
`ξ ↦ ψ (σ ξ) e (a ξ)` is `x ↦ σ⁻¹ Ψ((x + a)/σ)`. -/
private lemma fourierInv_shift_form (ψ : ℝ → ℂ) (Ψ : ℝ → ℝ)
    (hΨ : ∀ u : ℝ, (Ψ u : ℂ) = FourierTransformInv.fourierInv ψ u)
    {σ a : ℝ} (hσ : 0 < σ) (x : ℝ) :
    FourierTransformInv.fourierInv (fun ξ : ℝ => ψ (σ * ξ) * ee (a * ξ)) x
      = (σ : ℂ)⁻¹ * (Ψ ((x + a) / σ) : ℂ) := by
  rw [fourierInv_mul_ee (g := fun ξ : ℝ => ψ (σ * ξ)) a x]
  rw [congrFun (fourierInv_comp_mul ψ hσ) (x + a)]
  rw [← hΨ]

/-- **The kernel of the modulated `g`-bump.**  The inverse Fourier transform of
`varphitildeNt P d N k₂ t` (`k₂ ≥ 1`) is the shifted Calderón–Zygmund kernel with seed `Ψ`,
scale `gScale d N k₂` and shift `-PevalR P (N t) / gScale d N k₂`. -/
private lemma gBump_kernel (P : Polynomial ℤ) (d : ℕ) (Ψ : ℝ → ℝ)
    (hΨ : ∀ u : ℝ, (Ψ u : ℂ) = FourierTransformInv.fourierInv (gProfile d 1) u)
    (N : ℕ) {k₂ : ℕ} (hk₂ : 1 ≤ k₂) (t : ℝ) :
    (fun x : ℝ => FourierTransformInv.fourierInv (varphitildeNt P d N k₂ t) x)
      = fun x : ℝ => Work.Analysis.CzShift.shiftKernel Ψ (gScale d N k₂)
          (-(PevalR P ((N : ℝ) * t)) / gScale d N k₂) x := by
  funext x
  rw [varphitildeNt_eq_profile P d N k₂ t, gProfile_eq_gProfile_one hk₂]
  rw [fourierInv_shift_form (gProfile d 1) Ψ hΨ (gScale_pos_g d N k₂) x]
  rw [Work.Analysis.CzShift.shiftKernel, Complex.ofReal_mul, Complex.ofReal_inv]
  congr 1
  have hσnz : gScale d N k₂ ≠ 0 := (gScale_pos_g d N k₂).ne'
  have harg : (-(PevalR P ((N : ℝ) * t)) / gScale d N k₂) * gScale d N k₂
      = -(PevalR P ((N : ℝ) * t)) := by
    field_simp
  rw [show (x + PevalR P ((N : ℝ) * t)) / gScale d N k₂
      = (x - (-(PevalR P ((N : ℝ) * t)) / gScale d N k₂) * gScale d N k₂)
          / gScale d N k₂ from by
    rw [harg]; ring]

/-- The modulated `g`-bump is integrable (the modulation is unimodular). -/
private lemma integrable_varphitildeNt_k2 (P : Polynomial ℤ) (d N k₂ : ℕ) (t : ℝ) :
    Integrable (varphitildeNt P d N k₂ t) (volume : Measure ℝ) := by
  have h2 : AEStronglyMeasurable (fun ξ : ℝ => ee (PevalR P ((N : ℝ) * t) * ξ)) volume :=
    (Work.KMTPlan.A6.continuous_ee.comp (by fun_prop)).aestronglyMeasurable
  have h3 : ∀ᵐ ξ : ℝ ∂(volume : Measure ℝ),
      ‖ee (PevalR P ((N : ℝ) * t) * ξ)‖ ≤ 1 :=
    Filter.Eventually.of_forall (fun ξ => le_of_eq (Work.KMTPlan.A6.norm_ee _))
  show Integrable (fun ξ : ℝ => varphitildeN d N k₂ ξ * ee (PevalR P ((N : ℝ) * t) * ξ))
    (volume : Measure ℝ)
  exact Integrable.mul_bdd (Work.A7.varphitildeN_integrable_measurable d N k₂).1 h2 h3

/-! ### The Fourier transform of a real, even, integrable function is real -/

/-- Conjugation commutes with the Bochner integral. -/
private lemma integral_star_eq (g : ℝ → ℂ) (hg : Integrable g) :
    ∫ x, (starRingEnd ℂ) (g x) = (starRingEnd ℂ) (∫ x, g x) := by
  have h := ContinuousLinearMap.integral_comp_comm (Complex.conjCLE : ℂ →L[ℝ] ℂ) hg
  have h1 : (fun x => (starRingEnd ℂ) (g x)) = fun x => (Complex.conjCLE : ℂ → ℂ) (g x) := by
    funext x; rw [Complex.conjCLE_apply]
  have h2 : (starRingEnd ℂ) (∫ x, g x) = (Complex.conjCLE : ℂ → ℂ) (∫ x, g x) := by
    rw [Complex.conjCLE_apply]
  rw [h1, h2]
  exact h

/-- `𝓕 (conj ∘ f) (-w) = conj (𝓕 f w)` for integrable `f`. -/
private lemma conj_fourier (f : ℝ → ℂ) (hf : Integrable f) (w : ℝ) :
    (starRingEnd ℂ) (𝓕 f w) = 𝓕 (fun x => (starRingEnd ℂ) (f x)) (-w) := by
  have hint : Integrable (fun v : ℝ => Complex.exp (↑(-2 * Real.pi * v * w) * Complex.I) • f v) := by
    have h : Integrable (fun v : ℝ => 𝐞 (-(v * w)) • f v) := by
      simpa [mul_comm] using (Real.fourierIntegral_convergent_iff (μ := volume) (f := f) w).2 hf
    refine h.congr (Filter.Eventually.of_forall fun v => ?_)
    show 𝐞 (-(v * w)) • f v = Complex.exp (↑(-2 * Real.pi * v * w) * Complex.I) • f v
    rw [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul, smul_eq_mul]
    congr 1
    push_cast
    ring_nf
  rw [Real.fourier_real_eq_integral_exp_smul]
  rw [← integral_star_eq _ hint]
  rw [Real.fourier_real_eq_integral_exp_smul]
  congr 1 with v
  rw [smul_eq_mul, smul_eq_mul, map_mul, ← Complex.exp_conj]
  congr 1
  rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring_nf

/-- The Fourier transform of an even function is even. -/
private lemma fourier_eq_of_even {f : ℝ → ℂ} (heven : ∀ x, f (-x) = f x) (ξ : ℝ) :
    𝓕 f (-ξ) = 𝓕 f ξ := by
  have h2 : (fun x : ℝ => f (-x)) = f := funext heven
  have h3 : 𝓕⁻ f = 𝓕 f := by rw [Real.fourierInv_eq_fourier_comp_neg, h2]
  rw [← Real.fourierInv_eq_fourier_neg f ξ]
  exact congrFun h3 ξ

/-- The Fourier transform of a real-valued, even, integrable function is real-valued. -/
private lemma star_fourier_eq_of_real_even {f : ℝ → ℂ} (hf : Integrable f)
    (hreal : ∀ x, (starRingEnd ℂ) (f x) = f x) (heven : ∀ x, f (-x) = f x) (ξ : ℝ) :
    (starRingEnd ℂ) (𝓕 f ξ) = 𝓕 f ξ := by
  rw [conj_fourier f hf ξ]
  rw [show (fun x : ℝ => (starRingEnd ℂ) (f x)) = f from funext hreal]
  exact fourier_eq_of_even heven ξ

/-! ### The elementary properties of `G = gProfile d 1` -/

private lemma gProfile_one_even (d : ℕ) (u : ℝ) : gProfile d 1 (-u) = gProfile d 1 u := by
  have hg : gProfile d 1 = fun u : ℝ =>
      Work.KMTContract.kmtEta u - Work.KMTContract.kmtEta ((2 : ℝ) ^ d * u) := by
    rw [gProfile, if_neg (by norm_num)]
  simp only [hg]
  rw [Work.KMTContract.kmtEta_neg,
    show (2 : ℝ) ^ d * -u = -((2 : ℝ) ^ d * u) by ring, Work.KMTContract.kmtEta_neg]

private lemma gProfile_one_star (d : ℕ) (u : ℝ) :
    (starRingEnd ℂ) (gProfile d 1 u) = gProfile d 1 u := by
  have hg : gProfile d 1 = fun u : ℝ =>
      Work.KMTContract.kmtEta u - Work.KMTContract.kmtEta ((2 : ℝ) ^ d * u) := by
    rw [gProfile, if_neg (by norm_num)]
  rw [hg]
  simp only [Work.KMTContract.kmtEta]
  rw [map_sub, Complex.conj_ofReal, Complex.conj_ofReal]

private lemma gProfile_one_contDiff (d : ℕ) : ContDiff ℝ (↑(⊤ : ℕ∞)) (gProfile d 1) := by
  have h1 : ContDiff ℝ (↑(⊤ : ℕ∞)) Work.KMTContract.kmtEta :=
    (ContinuousLinearMap.contDiff (n := (↑(⊤ : ℕ∞))) (Complex.ofRealCLM : ℝ →L[ℝ] ℂ)).comp
      (ContDiffBump.contDiff Work.KMTContract.kmtBump (n := ⊤))
  have hg : gProfile d 1 = fun u : ℝ =>
      Work.KMTContract.kmtEta u - Work.KMTContract.kmtEta ((2 : ℝ) ^ d * u) := by
    rw [gProfile, if_neg (by norm_num)]
  rw [hg]
  exact h1.sub (h1.comp (by fun_prop))

private lemma gProfile_one_hasCompactSupport (d : ℕ) : HasCompactSupport (gProfile d 1) :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : ℝ) 1) (by
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
    by_contra h
    exact hx ((gProfile_facts d 1).2.1 x (le_of_lt (not_le.mp h))))

private lemma gProfile_one_integrable (d : ℕ) : Integrable (gProfile d 1) :=
  (gProfile_one_contDiff d).continuous.integrable_of_hasCompactSupport
    (gProfile_one_hasCompactSupport d)

/-- The real seed attached to `G = gProfile d 1`: the real part of `𝓕⁻G`. -/
private noncomputable def gProfileSeed (d : ℕ) : ℝ → ℝ :=
  fun u => (FourierTransformInv.fourierInv (gProfile d 1) u).re

private lemma gProfileSeed_spec (d : ℕ) (u : ℝ) :
    (gProfileSeed d u : ℂ) = FourierTransformInv.fourierInv (gProfile d 1) u := by
  rw [gProfileSeed, Real.fourierInv_eq_fourier_neg]
  exact Complex.conj_eq_iff_re.mp (star_fourier_eq_of_real_even (gProfile_one_integrable d)
    (gProfile_one_star d) (gProfile_one_even d) (-u))

private noncomputable def gProfileS (d : ℕ) : SchwartzMap ℝ ℂ :=
  (gProfile_one_hasCompactSupport d).toSchwartzMap (gProfile_one_contDiff d)

private lemma gProfileS_coe (d : ℕ) : ⇑(gProfileS d) = gProfile d 1 :=
  funext fun x => HasCompactSupport.toSchwartzMap_toFun _ _ x

private noncomputable def gKernelS (d : ℕ) : SchwartzMap ℝ ℂ :=
  FourierTransformInv.fourierInv (gProfileS d)

private lemma gKernelS_coe (d : ℕ) :
    (⇑(gKernelS d) : ℝ → ℂ) = FourierTransformInv.fourierInv (gProfile d 1) := by
  rw [show ⇑(gKernelS d) = FourierTransformInv.fourierInv (⇑(gProfileS d)) from
    SchwartzMap.fourierInv_coe (gProfileS d)]
  exact congrArg FourierTransformInv.fourierInv (gProfileS_coe d)

/-- Fourier inversion for the seed: `𝓕 (gProfileSeed d) = gProfile d 1`. -/
private lemma gProfileSeed_fourier (d : ℕ) (ξ : ℝ) :
    𝓕 (fun u : ℝ => (gProfileSeed d u : ℂ)) ξ = gProfile d 1 ξ := by
  have hfun : (fun u : ℝ => (gProfileSeed d u : ℂ)) = ⇑(gKernelS d) := by
    rw [gKernelS_coe]
    exact funext (fun u => gProfileSeed_spec d u)
  rw [hfun, ← SchwartzMap.fourier_coe (gKernelS d)]
  rw [show 𝓕 (gKernelS d) = gProfileS d from FourierInvPair.fourier_fourierInv_eq (gProfileS d)]
  exact congrFun (gProfileS_coe d) ξ

/-- **The seed and the symbol bounds of `G = gProfile d 1`.**  There are a real seed `Ψ` (the real
part of `𝓕⁻G`), a derivative `Ψ'`, a size parameter `B ≥ 1` and a constant `C > 0` such that
`Ψ` is a Calderón–Zygmund seed for `G`, `𝓕Ψ = G`, and `G` is supported in `[-C,C]` with
`‖G ξ‖ ≤ C min 1 |ξ|`. -/
private lemma gProfile_one_cz (d : ℕ) :
    ∃ (Ψ : ℝ → ℝ) (Ψ' : ℝ → ℝ) (B C : ℝ), 1 ≤ B ∧ 0 < C ∧
      Work.Analysis.CzShift.IsCZSeed Ψ Ψ' B ∧
      (∀ u : ℝ, (Ψ u : ℂ) = FourierTransformInv.fourierInv (gProfile d 1) u) ∧
      (∀ ξ : ℝ, FourierTransform.fourier (fun u : ℝ => (Ψ u : ℂ)) ξ = gProfile d 1 ξ) ∧
      (∀ ξ : ℝ, C < |ξ| → gProfile d 1 ξ = 0) ∧
      (∀ ξ : ℝ, ‖gProfile d 1 ξ‖ ≤ C * min 1 |ξ|) := by
  obtain ⟨M0, M1, M2, hM0nn, hM1nn, hM2nn, hb⟩ := gProfile_deriv_bounds d
  obtain ⟨hbcd, hb0, hb1, hb2, hbZ0, hbZ1, hbZ2, hbD1, hbD2⟩ := hb 1
  set C : ℝ := max 1 (max M0 (max M1 M2)) with hCdef
  have hC1 : 1 ≤ C := le_max_left _ _
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC1
  have hCM0 : M0 ≤ C := le_trans (le_max_left _ _) (le_max_right _ _)
  have hCM1 : M1 ≤ C := le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
    (le_max_right _ _)
  have hCM2 : M2 ≤ C := le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
    (le_max_right _ _)
  have hsupp : ∀ ξ : ℝ, C < |ξ| → gProfile d 1 ξ = 0 :=
    fun ξ hξ => hbZ0 ξ (le_trans hC1 (le_of_lt hξ))
  have hbd0 : ∀ ξ : ℝ, ‖gProfile d 1 ξ‖ ≤ C := fun ξ => le_trans (hb0 ξ) hCM0
  have hbd1' : ∀ ξ : ℝ, ‖deriv (gProfile d 1) ξ‖ ≤ C := fun ξ => le_trans (hb1 ξ) hCM1
  have hbd2' : ∀ ξ : ℝ, ‖iteratedDeriv 2 (gProfile d 1) ξ‖ ≤ C := fun ξ => le_trans (hb2 ξ) hCM2
  have hseed := Work.Analysis.CzShift.isCZSeed_of_fourierInv_explicit (gProfile d 1)
    (deriv (gProfile d 1)) (iteratedDeriv 2 (gProfile d 1)) (gProfileSeed d) C hCpos
    (gProfileSeed_spec d) hsupp hbd0 hbD1 hbd1' hbD2 hbd2'
  refine ⟨gProfileSeed d, Classical.choose hseed,
    max 1 (4 * C * (C + 2 * Real.pi * (2 * C + C ^ 2))), C,
    Work.Analysis.CzShift.one_le_max_C C hCpos, hCpos, Classical.choose_spec hseed,
    gProfileSeed_spec d, gProfileSeed_fourier d, hsupp, ?_⟩
  -- the mean value bound `‖G ξ‖ ≤ C min 1 |ξ|`
  intro ξ
  by_cases hle : |ξ| ≤ 1
  · have hG0 : gProfile d 1 0 = 0 := by
      simpa using (gProfile_facts d 1).2.2.1
    have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le (f := gProfile d 1)
      (s := Set.Icc (-1 : ℝ) 1) (x := 0) (y := ξ) (C := C)
      (fun x _ => (hbD1 x).differentiableAt) (fun x _ => hbd1' x) (convex_Icc _ _)
      (by simp) (by rw [Set.mem_Icc]; exact abs_le.mp hle)
    rw [hG0, sub_zero, Real.norm_eq_abs, sub_zero] at hmvt
    rw [min_eq_right hle]
    exact hmvt
  · have hlt : (1 : ℝ) < |ξ| := lt_of_not_ge hle
    have hz : gProfile d 1 ξ = 0 := hbZ0 ξ (le_of_lt hlt)
    rw [hz, min_eq_left (le_of_lt hlt), norm_zero]
    exact mul_nonneg (le_of_lt hCpos) zero_le_one

/-! ## 3.  The operator of a fibre is the `czOp` of the shifted kernels -/

/-- Linearity of `contMulOp` over a finite sum, combined with the kernel identity: the multiplier
with the symbol `∑_{n ∈ D} ε n * Φ n` is the `czOp` of the kernels `κ n = 𝓕⁻(Φ n)`. -/
private lemma contMulOp_finset_eq_czOp {ι : Type*} (D : Finset ι) (Φ : ι → ℝ → ℂ)
    (κ : ι → ℝ → ℂ) (ε : ι → ℂ) (hInt : ∀ n ∈ D, Integrable (Φ n))
    (hker : ∀ n ∈ D, ∀ z : ℝ, FourierTransformInv.fourierInv (Φ n) z = κ n z)
    (f : SchwartzMap ℝ ℂ) :
    Work.Analysis.IWMultiplier.contMulOp (fun ξ : ℝ => ∑ n ∈ D, ε n * Φ n ξ)
        (f : ℝ → ℂ)
      = Work.Analysis.CzShift.czOp D κ ε (f : ℝ → ℂ) := by
  rw [lacBump_contMulOp_finsetSum D (fun n ξ => ε n * Φ n ξ) f
    (fun n hn => (hInt n hn).const_mul (ε n))]
  unfold Work.Analysis.CzShift.czOp
  funext x
  simp only [Finset.sum_apply]
  refine Finset.sum_congr rfl (fun n hn => ?_)
  have h1 : FourierTransformInv.fourierInv (fun ξ : ℝ => ε n * Φ n ξ)
      = fun z : ℝ => ε n * κ n z := by
    funext z
    rw [lacBump_fourierInv_const_mul (ε n) _ z, hker n hn z]
  rw [lacBump_contMulOp_eq_integral _ _ ((hInt n hn).const_mul (ε n)) f.integrable x, h1,
    smul_eq_mul, ← MeasureTheory.integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
  ring

/-! ## 4.  The main theorem -/

theorem varphitildeNt_mult_bound_k2pos_hi (P : Polynomial ℤ) (d : ℕ) (hd : P.natDegree ≤ d)
    (p : ℝ) (hp : 1 < p) (Λ : NNReal) (hΛ : 1 < Λ) :
    ∃ C : NNReal, 0 < C ∧
      ∀ (k₂ : ℕ) (hk₂ : 1 ≤ k₂) (t : ℝ) (ht : t ∈ Set.Icc (1/2 : ℝ) 1) (a : ℕ → NNReal)
        (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n)
        (U : Finset ℕ) (ε : ℕ → ℂ) (hε : ∀ n, ‖ε n‖ ≤ 1),
        Work.Analysis.IWMultiplier.IsLqMultiplierBound (ENNReal.ofReal p)
          (fun ξ : ℝ => ∑ n ∈ U, ε n *
            Work.KMTAreas.A7.varphitildeNt P d (Nat.floor (a n)) k₂ t ξ)
          (C * (1 + d * k₂)) := by
  classical
  by_cases hd1 : 1 ≤ d
  · -- ## the case `d ≥ 1`
    obtain ⟨M, hMpos, hMlac⟩ := lacBumpDecimation Λ hΛ
    obtain ⟨Ψ, Ψ', B, Cψ, hB1, hCψpos, hseed, hΨform, hΨfourier, hψsupp0, hψbd0⟩ :=
      gProfile_one_cz d
    obtain ⟨C₀, hC₀pos, hC₀⟩ :=
      Work.Analysis.CzShift.cz_shift_lp 2 B Cψ (by norm_num) hB1 hCψpos hp
    -- the coefficient `ℓ¹`-norm of `P` and the exponent offset `n₀`
    set S : ℝ := ∑ i ∈ Finset.range (P.natDegree + 1), |(P.coeff i : ℝ)| with hSdef
    have hSnn : 0 ≤ S := by rw [hSdef]; exact Finset.sum_nonneg (fun i _ => abs_nonneg _)
    obtain ⟨n₀, hn₀⟩ := pow_unbounded_of_one_lt ((S + 1) * 3 ^ d * 2)
      (by norm_num : (1 : ℝ) < 2)
    -- the constant
    set CR : ℝ := (M : ℝ) * C₀ * (B + 1) * ((n₀ : ℝ) + 1) with hCRdef
    have hCRpos : 0 < CR := by
      rw [hCRdef]
      have hMpos' : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hMpos
      have hBpos : (0 : ℝ) < B + 1 := by linarith
      have hn₀pos : (0 : ℝ) < (n₀ : ℝ) + 1 := by positivity
      positivity
    refine ⟨NNReal.mk CR (le_of_lt hCRpos), NNReal.coe_pos.mp hCRpos, ?_⟩
    intro k₂ hk₂ t ht a ha ha1 U ε hε
    -- the shift and the exponent
    set lam : ℕ → ℝ := fun n =>
      -(PevalR P ((Nat.floor (a n) : ℝ) * t)) / gScale d (Nat.floor (a n)) k₂
      with hlamdef
    have hlam_apply : ∀ n : ℕ, lam n
        = -(PevalR P ((Nat.floor (a n) : ℝ) * t)) / gScale d (Nat.floor (a n)) k₂ := by
      intro n; rw [hlamdef]
    set K : ℝ := (n₀ : ℝ) + ((d * k₂ : ℕ) : ℝ) with hKdef
    have hK1 : 1 ≤ K := by
      have hdk : (1 : ℝ) ≤ ((d * k₂ : ℕ) : ℝ) := by
        have h : 1 ≤ d * k₂ := by simpa using Nat.mul_le_mul hd1 hk₂
        exact_mod_cast h
      have hn : (0 : ℝ) ≤ (n₀ : ℝ) := Nat.cast_nonneg _
      rw [hKdef]; linarith
    -- the shift bound
    have h2K : (S + 1) * 3 ^ d * (1 + (2 : ℝ) ^ (d * k₂)) ≤ (2 : ℝ) ^ K := by
      have h1 : (1 : ℝ) + (2 : ℝ) ^ (d * k₂) ≤ 2 * (2 : ℝ) ^ (d * k₂) := by
        have hge1 : (1 : ℝ) ≤ (2 : ℝ) ^ (d * k₂) := one_le_pow₀ (by norm_num)
        linarith
      have hn₀' : (S + 1) * 3 ^ d * 2 ≤ (2 : ℝ) ^ n₀ := le_of_lt hn₀
      calc (S + 1) * 3 ^ d * (1 + (2 : ℝ) ^ (d * k₂))
          ≤ (S + 1) * 3 ^ d * (2 * (2 : ℝ) ^ (d * k₂)) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = ((S + 1) * 3 ^ d * 2) * (2 : ℝ) ^ (d * k₂) := by ring
        _ ≤ (2 : ℝ) ^ n₀ * (2 : ℝ) ^ (d * k₂) :=
            mul_le_mul_of_nonneg_right hn₀' (by positivity)
        _ = (2 : ℝ) ^ K := by
            rw [hKdef, Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_natCast,
              Real.rpow_natCast]
    -- the lacunarity of the scaled family on each fibre
    have hLac : ∀ r : ℕ, Work.Analysis.CzShift.LacunaryFam 2 (U.filter (fun n => n % M = r))
        (fun n => gScale d (Nat.floor (a n)) k₂) := by
      intro r
      have h0 := hMlac k₂ a ha ha1 U r
      have h1 : Work.Analysis.CzShift.LacunaryFam 2 (U.filter (fun n => n % M = r))
          (fun n => (lacσ (Nat.floor (a n)) k₂) ^ d) :=
        lacunaryFam_pow hd1 h0
      simpa only [gScale_eq_lacσ_pow] using h1
    -- the symbol hypotheses of the CZ theorem
    have hψsuppF : ∀ ξ : ℝ, Cψ < |ξ| → 𝓕 (fun u : ℝ => (Ψ u : ℂ)) ξ = 0 := by
      intro ξ hξ
      rw [hΨfourier ξ]
      exact hψsupp0 ξ hξ
    have hψbdF : ∀ ξ : ℝ, ‖𝓕 (fun u : ℝ => (Ψ u : ℂ)) ξ‖ ≤ Cψ * min 1 |ξ| := by
      intro ξ
      rw [hΨfourier ξ]
      exact hψbd0 ξ
    -- the bound for one fibre
    have hfiber : ∀ (r : ℕ) (f : SchwartzMap ℝ ℂ),
        eLpNorm (Work.Analysis.IWMultiplier.contMulOp
            (fun ξ : ℝ => ∑ n ∈ U.filter (fun n => n % M = r),
              ε n * varphitildeNt P d (Nat.floor (a n)) k₂ t ξ) (f : ℝ → ℂ))
          (ENNReal.ofReal p) (volume : Measure ℝ)
        ≤ ENNReal.ofReal (C₀ * (B * (1 + K) + 1))
            * eLpNorm (f : ℝ → ℂ) (ENNReal.ofReal p) (volume : Measure ℝ) := by
      intro r f
      have hInt : ∀ n ∈ U.filter (fun n => n % M = r),
          Integrable (fun ξ : ℝ => varphitildeNt P d (Nat.floor (a n)) k₂ t ξ) :=
        fun n _ => integrable_varphitildeNt_k2 P d _ k₂ t
      have hker : ∀ n ∈ U.filter (fun n => n % M = r), ∀ z : ℝ,
          FourierTransformInv.fourierInv
              (fun ξ : ℝ => varphitildeNt P d (Nat.floor (a n)) k₂ t ξ) z
            = Work.Analysis.CzShift.shiftKernel Ψ (gScale d (Nat.floor (a n)) k₂) (lam n) z := by
        intro n _ z
        rw [hlam_apply n]
        exact congrFun (gBump_kernel P d Ψ hΨform (Nat.floor (a n)) hk₂ t) z
      have hsh : ∀ n ∈ U.filter (fun n => n % M = r), |lam n| ≤ (2 : ℝ) ^ K := by
        intro n _
        have htabs : |t| ≤ 1 := by
          rw [abs_of_nonneg (by linarith [ht.1])]
          exact ht.2
        have hb := abs_PevalR_div_gScale_le P d (Nat.floor (a n)) k₂ hd htabs
        rw [← hSdef] at hb
        rw [hlam_apply n, abs_div, abs_neg, abs_of_pos (gScale_pos_g d _ k₂)]
        exact le_trans hb h2K
      have hcz := hC₀ (U.filter (fun n => n % M = r))
        (fun n => gScale d (Nat.floor (a n)) k₂) lam Ψ Ψ' K
        (hLac r) hseed hK1 hsh hψsuppF hψbdF (fun n => ε n) (fun n _ => hε n)
        (f : ℝ → ℂ) f.integrable (SchwartzMap.memLp f (ENNReal.ofReal p) (volume : Measure ℝ))
      rw [contMulOp_finset_eq_czOp (U.filter (fun n => n % M = r))
        (fun n ξ => varphitildeNt P d (Nat.floor (a n)) k₂ t ξ)
        (fun n => Work.Analysis.CzShift.shiftKernel Ψ (gScale d (Nat.floor (a n)) k₂) (lam n))
        (fun n => ε n) hInt hker f]
      exact hcz
    -- the constant comparison
    have hrealineq : (M : ℝ) * (C₀ * (B * (1 + K) + 1)) ≤ CR * (1 + (d * k₂ : ℕ) : ℝ) := by
      have hC₀nn : 0 ≤ C₀ := le_of_lt hC₀pos
      have hK0 : 0 ≤ K := by rw [hKdef]; positivity
      have hKle : 1 + K ≤ ((n₀ : ℝ) + 1) * (1 + (d * k₂ : ℕ) : ℝ) := by
        have hdk : (0 : ℝ) ≤ ((d * k₂ : ℕ) : ℝ) := by positivity
        have hn : (0 : ℝ) ≤ (n₀ : ℝ) := by positivity
        rw [hKdef]
        nlinarith [hdk, hn, mul_nonneg hn hdk]
      have hstep1 : B * (1 + K) + 1 ≤ (B + 1) * (1 + K) := by
        have h1 : (1 : ℝ) ≤ 1 + K := by linarith
        nlinarith [h1, hB1]
      have hinner : C₀ * (B * (1 + K) + 1)
          ≤ C₀ * ((B + 1) * ((n₀ : ℝ) + 1) * (1 + (d * k₂ : ℕ) : ℝ)) := by
        refine mul_le_mul_of_nonneg_left ?_ hC₀nn
        calc B * (1 + K) + 1 ≤ (B + 1) * (1 + K) := hstep1
          _ ≤ (B + 1) * (((n₀ : ℝ) + 1) * (1 + (d * k₂ : ℕ) : ℝ)) :=
              mul_le_mul_of_nonneg_left hKle (by linarith)
          _ = (B + 1) * ((n₀ : ℝ) + 1) * (1 + (d * k₂ : ℕ) : ℝ) := by ring
      have hMnn : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg _
      calc (M : ℝ) * (C₀ * (B * (1 + K) + 1))
          ≤ (M : ℝ) * (C₀ * ((B + 1) * ((n₀ : ℝ) + 1) * (1 + (d * k₂ : ℕ) : ℝ))) :=
            mul_le_mul_of_nonneg_left hinner hMnn
        _ = CR * (1 + (d * k₂ : ℕ) : ℝ) := by rw [hCRdef]; ring
    have hCe : ((NNReal.mk CR (le_of_lt hCRpos) * (1 + (d : NNReal) * (k₂ : NNReal)) : NNReal) : ℝ)
        = CR * (1 + (d * k₂ : ℕ) : ℝ) := by
      push_cast
      ring
    intro f
    have hFtop : MemLp (fun ξ : ℝ => 𝓕 (f : ℝ → ℂ) ξ) ⊤ (volume : Measure ℝ) := by
      simpa only [SchwartzMap.fourier_coe] using
        (SchwartzMap.memLp (𝓕 f) ⊤ (volume : Measure ℝ))
    -- the symbol is the sum of its fibres
    have hsymb : (fun ξ : ℝ => ∑ n ∈ U, ε n * varphitildeNt P d (Nat.floor (a n)) k₂ t ξ)
        = fun ξ : ℝ => ∑ r ∈ Finset.range M,
            ∑ n ∈ U.filter (fun n => n % M = r),
              ε n * varphitildeNt P d (Nat.floor (a n)) k₂ t ξ := by
      funext ξ
      exact (Finset.sum_fiberwise_of_maps_to (s := U) (t := Finset.range M)
        (g := fun n => n % M) (fun n _ => Finset.mem_range.mpr (Nat.mod_lt n hMpos))
        (fun n => ε n * varphitildeNt P d (Nat.floor (a n)) k₂ t ξ)).symm
    rw [hsymb]
    rw [lacBump_contMulOp_finsetSum (Finset.range M)
      (fun r ξ => ∑ n ∈ U.filter (fun n => n % M = r),
        ε n * varphitildeNt P d (Nat.floor (a n)) k₂ t ξ) f
      (fun r _ => integrable_finsetSum _ (fun n _ =>
        (integrable_varphitildeNt_k2 P d _ k₂ t).const_mul (ε n)))]
    refine (eLpNorm_sum_le ?_).trans ?_
    · exact ENNReal.one_le_ofReal.mpr (le_of_lt hp)
    · refine (Finset.sum_le_sum (fun r _ => hfiber r f)).trans ?_
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc]
      refine mul_le_mul_of_nonneg_right ?_ zero_le
      rw [← ENNReal.ofReal_natCast M,
        ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (M : ℝ))]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [hCe]
      exact hrealineq
  · -- ## the case `d = 0`
    have hd0 : d = 0 := by omega
    subst hd0
    refine ⟨1, one_pos, ?_⟩
    intro k₂ hk₂ t ht a ha ha1 U ε hε
    have hg0 : gProfile 0 k₂ = 0 := by
      rw [gProfile, if_neg (by omega)]
      funext u
      simp
    have hsymb0 : (fun ξ : ℝ => ∑ n ∈ U,
        ε n * varphitildeNt P 0 (Nat.floor (a n)) k₂ t ξ) = 0 := by
      funext ξ
      refine Finset.sum_eq_zero (fun n _ => ?_)
      rw [varphitildeNt_eq_profile P 0 (Nat.floor (a n)) k₂ t, hg0]
      simp
    intro f
    rw [hsymb0]
    have hzero : Work.Analysis.IWMultiplier.contMulOp (0 : ℝ → ℂ) (f : ℝ → ℂ) = 0 := by
      funext x
      rw [Work.Analysis.IWMultiplier.contMulOp, lacBump_fourierInv_eq_integral_mul]
      simp
    rw [hzero]
    simp

end

end Work.KMTAreas.A7

