import Mathlib
import Submission.Work.Asymptotics.funnelTailBasic
import Submission.Work.Asymptotics.ThetaQExp
import Submission.Work.Asymptotics.CuspL_eq
import Submission.Work.Asymptotics.KhatE1.E1LS_eq_log
import Submission.Work.Kernels.KernelFacts.psi2_T2
import Submission.Work.Kernels.KernelFacts.psi4_T2
import Submission.Work.Residues.LamSExpansion
import Submission.Work.Residues.ThetaAux

/-!
# First-order cusp expansion of `ψ₂` and `ψ₄` individually

CKMRV (Cohn--Kumar--Miller--Radchenko--Viazovska, Ann. of Math. 196 (2022)) use the
functions `ψ₂ = ξ₂𝓛 + (ξ₂|₂S)𝓛_S` and `ψ₄ = ξ₄𝓛 + (ξ₄|₄S)𝓛_S` of Proposition 4.3, where
`ξ₂ = U + W`, `ξ₄ = U² + W² - 2V²` and `U = θ₀₀⁴`, `W = θ₀₁⁴`, `V = θ₁₀⁴`.  Near the cusp
`i∞` the two functions have the same first-order behaviour

  `ψ₂(τ) = 2(πiτ + c) + O(scale(τ)^N ‖q(τ)‖)`,  `ψ₄(τ) = 2(πiτ + c) + O(scale(τ)^N ‖q(τ)‖)`,

with `c = cuspC ℓ` and `q(τ) = e^{2πiτ}`.

Writing `e = e^{πiτ}` (so that `‖e‖² = ‖q‖`) the relevant expansions are

* `𝓛 = πiτ + c - 8e + 12e² + O(‖e‖³)`   (`Compact.cuspC_spec`),
* `𝓛_S = -16e + O(‖e‖³)`   (`Residues.LamSExpansion`),
* `U = 1 + 8e + 24e² + 32e³ + 24e⁴ + O(‖e‖⁵)`, `W = 1 - 8e + 24e² - 32e³ + 24e⁴ + O(‖e‖⁵)`,
  `V = 16e + 64e³ + O(‖e‖⁵)`   (`ThetaQExp`).

Hence `ξ₂ = 2 + O(‖e‖²)` and `(ξ₂|₂S) = -(U+V) = -1 + O(‖e‖)`, while `ξ₄ = 2 + O(‖e‖²)` and
`(ξ₄|₄S) = U² + V² - 2W² = -1 + O(‖e‖)`.  In both cases the `O(‖e‖)` terms of
`ξ(𝓛 - πiτ - c)` and of `(ξ|S)𝓛_S` cancel:

  `2(-8e) + (-1)(-16e) = 0`,

which is why the first-order expansion of `ψ₂` and `ψ₄` is accurate to order `q`.
-/

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle

namespace Work.Asymptotics.KhatE1Core

noncomputable section

/-! ## Elementary funnel facts -/

/-- On the funnel, `‖e^{πiτ}‖ ≤ 1/2`. -/
private lemma nomeE_norm_le_half {τ : ℍ} (hτ : Work.Asymptotics.Funnel τ) :
    ‖Work.Asymptotics.nomeE τ‖ ≤ 1 / 2 := by
  rw [Work.Asymptotics.norm_nomeE]
  have h6 : (6 : ℝ) ≤ Real.pi * τ.im := by nlinarith [Real.pi_gt_three, hτ.2]
  have h1 : Real.exp (-(Real.pi * τ.im)) ≤ Real.exp (-6) := Real.exp_le_exp.mpr (by linarith)
  have h2 : (2 : ℝ) ≤ Real.exp 6 :=
    (le_of_lt Real.exp_one_gt_two).trans (Real.exp_le_exp.mpr (by norm_num))
  calc Real.exp (-(Real.pi * τ.im)) ≤ Real.exp (-6) := h1
    _ = (Real.exp 6)⁻¹ := Real.exp_neg 6
    _ ≤ (2 : ℝ)⁻¹ := by
        rw [inv_le_inv₀ (Real.exp_pos 6) (by norm_num)]
        exact h2
    _ = 1 / 2 := by norm_num

/-- On the funnel, `‖e^{πiτ}‖ ≤ 1`. -/
private lemma nomeE_norm_le_one {τ : ℍ} (hτ : Work.Asymptotics.Funnel τ) :
    ‖Work.Asymptotics.nomeE τ‖ ≤ 1 :=
  le_trans (nomeE_norm_le_half hτ) (by norm_num)

/-- The cusp constant term `πiτ + c` is bounded by `(π + 4)` times the scale. -/
private lemma cuspC_add_bound (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) :
    ‖(Real.pi : ℂ) * Complex.I * (τ : ℂ) + Work.Asymptotics.Compact.cuspC ℓ‖
      ≤ (Real.pi + 4) * Work.Kernels.scale τ := by
  have hc : Work.Asymptotics.Compact.cuspC ℓ = 4 * (Real.log 2 : ℂ) :=
    Work.Asymptotics.CuspL_eq ℓ
  have hlog0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog1 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hlog : ‖(4 : ℂ) * (Real.log 2 : ℂ)‖ ≤ 4 := by
    rw [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hlog0]
    linarith
  have hπ : ‖(Real.pi : ℂ) * Complex.I * (τ : ℂ)‖ ≤ Real.pi * Work.Kernels.scale τ := by
    rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
    have h := Work.Kernels.coe_norm_le_scale τ
    nlinarith [Real.pi_pos]
  rw [hc]
  calc ‖(Real.pi : ℂ) * Complex.I * (τ : ℂ) + 4 * (Real.log 2 : ℂ)‖
      ≤ ‖(Real.pi : ℂ) * Complex.I * (τ : ℂ)‖ + ‖(4 : ℂ) * (Real.log 2 : ℂ)‖ :=
        norm_add_le _ _
    _ ≤ Real.pi * Work.Kernels.scale τ + 4 := add_le_add hπ hlog
    _ ≤ (Real.pi + 4) * Work.Kernels.scale τ := by
        have := Work.Kernels.one_le_scale τ
        nlinarith

/-! ## Elementary norm bounds for sums and squares -/

/-- Norm bound for a four-term sum. -/
private lemma norm_chain4 (a b c d : ℂ) :
    ‖a + b + c + d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by
  have h1 := norm_add_le (a + b + c) d
  have h2 := norm_add_le (a + b) c
  have h3 := norm_add_le a b
  linarith

/-- Norm bound for an eight-term sum. -/
private lemma norm_chain8 (a b c d e f g h : ℂ) :
    ‖a + b + c + d + e + f + g + h‖
      ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖ + ‖f‖ + ‖g‖ + ‖h‖ := by
  have h1 := norm_add_le (a + b + c + d + e + f + g) h
  have h2 := norm_add_le (a + b + c + d + e + f) g
  have h3 := norm_add_le (a + b + c + d + e) f
  have h4 := norm_add_le (a + b + c + d) e
  have h5 := norm_add_le (a + b + c) d
  have h6 := norm_add_le (a + b) c
  have h7 := norm_add_le a b
  linarith

/-- If `P` is a small polynomial truncation and `U - P = O(r⁵)`, then
`U + P = O(1)` on the funnel. -/
private lemma norm_add_poly_bound {U P : ℂ} {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (h1 : ‖U - P‖ ≤ 10000 * r ^ 5) (h2 : ‖P‖ ≤ 90) : ‖U + P‖ ≤ 100000 := by
  have hk5 : r ^ 5 ≤ 1 := pow_le_one₀ hr0 hr1
  have hUn : ‖U‖ ≤ 90 + 10000 := by
    have h := norm_add_le (U - P) P
    rw [sub_add_cancel] at h
    nlinarith [h, h1, h2, hk5]
  have h2' := norm_add_le U P
  linarith [h2', hUn, h2]

/-- `U² - P² = O(r²)` when `U - P = O(r⁵)` and `P = O(1)`. -/
private lemma sq_sub_sq_bound {U P : ℂ} {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (h1 : ‖U - P‖ ≤ 10000 * r ^ 5) (h2 : ‖P‖ ≤ 90) :
    ‖U ^ 2 - P ^ 2‖ ≤ 10000000000 * r ^ 2 := by
  have h5 : r ^ 5 ≤ r ^ 2 := pow_le_pow_of_le_one hr0 hr1 (by norm_num)
  have h2' : ‖U + P‖ ≤ 100000 := norm_add_poly_bound hr0 hr1 h1 h2
  have hfact : U ^ 2 - P ^ 2 = (U - P) * (U + P) := by ring
  rw [hfact, norm_mul]
  calc ‖U - P‖ * ‖U + P‖ ≤ (10000 * r ^ 5) * 100000 :=
        mul_le_mul h1 h2' (norm_nonneg _) (by positivity)
    _ = 1000000000 * r ^ 5 := by ring
    _ ≤ 10000000000 * r ^ 2 := by nlinarith [h5]

/-! ## The two `ξ`-bounds for `ψ₂` -/

/-- `ξ₂ = U + W = 2 + O(‖e‖²)`. -/
private lemma xi2Fun_sub_two_bound (τ : ℍ) (hτ : Work.Asymptotics.Funnel τ) :
    ‖Work.Kernels.xi2Fun τ - 2‖ ≤ 30000 * ‖Work.Asymptotics.nomeE τ‖ ^ 2 := by
  have hτ2 : (2 : ℝ) ≤ τ.im := hτ.2
  have hU := Work.Asymptotics.UFun_qexp τ hτ2
  have hW := Work.Asymptotics.WFun_qexp τ hτ2
  set e : ℂ := Work.Asymptotics.nomeE τ with he
  have hU' : ‖Work.Kernels.UFun τ - (1 + 8 * e + 24 * e ^ 2 + 32 * e ^ 3 + 24 * e ^ 4)‖
      ≤ 10000 * ‖e‖ ^ 5 := by rw [he]; exact hU
  have hW' : ‖Work.Kernels.WFun τ - (1 - 8 * e + 24 * e ^ 2 - 32 * e ^ 3 + 24 * e ^ 4)‖
      ≤ 10000 * ‖e‖ ^ 5 := by rw [he]; exact hW
  have he1 : ‖e‖ ≤ 1 := by rw [he]; exact nomeE_norm_le_one hτ
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = ‖e‖ := ⟨_, rfl⟩
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have hr1 : r ≤ 1 := by rw [hr]; exact he1
  have h4 : r ^ 4 ≤ r ^ 2 := pow_le_pow_of_le_one hr0 hr1 (by norm_num)
  have h5 : r ^ 5 ≤ r ^ 2 := pow_le_pow_of_le_one hr0 hr1 (by norm_num)
  have hU'' : ‖Work.Kernels.UFun τ - (1 + 8 * e + 24 * e ^ 2 + 32 * e ^ 3 + 24 * e ^ 4)‖
      ≤ 10000 * r ^ 5 := by simpa only [← hr] using hU'
  have hW'' : ‖Work.Kernels.WFun τ - (1 - 8 * e + 24 * e ^ 2 - 32 * e ^ 3 + 24 * e ^ 4)‖
      ≤ 10000 * r ^ 5 := by simpa only [← hr] using hW'
  have hid : Work.Kernels.xi2Fun τ - 2
      = (48 * e ^ 2 + 48 * e ^ 4)
        + ((Work.Kernels.UFun τ - (1 + 8 * e + 24 * e ^ 2 + 32 * e ^ 3 + 24 * e ^ 4))
          + (Work.Kernels.WFun τ - (1 - 8 * e + 24 * e ^ 2 - 32 * e ^ 3 + 24 * e ^ 4))) := by
    rw [Work.Kernels.xi2Fun]; ring
  have hA : ‖(48 : ℂ) * e ^ 2 + 48 * e ^ 4‖ ≤ 48 * r ^ 2 + 48 * r ^ 2 := by
    have h1 : ‖(48 : ℂ) * e ^ 2‖ = 48 * r ^ 2 := by
      rw [norm_mul, norm_pow, Complex.norm_ofNat, ← hr]
    have h2 : ‖(48 : ℂ) * e ^ 4‖ = 48 * r ^ 4 := by
      rw [norm_mul, norm_pow, Complex.norm_ofNat, ← hr]
    have h3 := norm_add_le ((48 : ℂ) * e ^ 2) ((48 : ℂ) * e ^ 4)
    rw [h1, h2] at h3
    linarith [h3, h4]
  have hB : ‖(Work.Kernels.UFun τ - (1 + 8 * e + 24 * e ^ 2 + 32 * e ^ 3 + 24 * e ^ 4))
      + (Work.Kernels.WFun τ - (1 - 8 * e + 24 * e ^ 2 - 32 * e ^ 3 + 24 * e ^ 4))‖
      ≤ 10000 * r ^ 5 + 10000 * r ^ 5 := by
    have h3 := norm_add_le
      (Work.Kernels.UFun τ - (1 + 8 * e + 24 * e ^ 2 + 32 * e ^ 3 + 24 * e ^ 4))
      (Work.Kernels.WFun τ - (1 - 8 * e + 24 * e ^ 2 - 32 * e ^ 3 + 24 * e ^ 4))
    linarith [h3, hU'', hW'']
  have hmain : ‖Work.Kernels.xi2Fun τ - 2‖ ≤ 30000 * r ^ 2 := by
    rw [hid]
    have h3 := norm_add_le (48 * e ^ 2 + 48 * e ^ 4)
      ((Work.Kernels.UFun τ - (1 + 8 * e + 24 * e ^ 2 + 32 * e ^ 3 + 24 * e ^ 4))
        + (Work.Kernels.WFun τ - (1 - 8 * e + 24 * e ^ 2 - 32 * e ^ 3 + 24 * e ^ 4)))
    linarith [h3, hA, hB, h5, pow_nonneg hr0 2]
  simpa only [← hr] using hmain

/-- `(ξ₂|₂S) = -(U+V) = -1 + O(‖e‖)`. -/
private lemma xi2S_add_one_bound (τ : ℍ) (hτ : Work.Asymptotics.Funnel τ) :
    ‖(Work.Kernels.xi2Fun ∣[(2 : ℤ)] ModularGroup.S) τ + 1‖
      ≤ 30000 * ‖Work.Asymptotics.nomeE τ‖ := by
  have hτ2 : (2 : ℝ) ≤ τ.im := hτ.2
  have hU := Work.Asymptotics.UFun_qexp τ hτ2
  have hV := Work.Asymptotics.VFun_qexp τ hτ2
  set e : ℂ := Work.Asymptotics.nomeE τ with he
  have hU' : ‖Work.Kernels.UFun τ - (1 + 8 * e + 24 * e ^ 2 + 32 * e ^ 3 + 24 * e ^ 4)‖
      ≤ 10000 * ‖e‖ ^ 5 := by rw [he]; exact hU
  have hV' : ‖Work.Kernels.VFun τ - (16 * e + 64 * e ^ 3)‖ ≤ 10000 * ‖e‖ ^ 5 := by
    rw [he]; exact hV
  have he1 : ‖e‖ ≤ 1 := by rw [he]; exact nomeE_norm_le_one hτ
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = ‖e‖ := ⟨_, rfl⟩
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have hr1 : r ≤ 1 := by rw [hr]; exact he1
  have h2 : r ^ 2 ≤ r := by
    have := pow_le_pow_of_le_one (a := r) hr0 hr1 (show (1 : ℕ) ≤ 2 by norm_num)
    simpa using this
  have h3 : r ^ 3 ≤ r := by
    have := pow_le_pow_of_le_one (a := r) hr0 hr1 (show (1 : ℕ) ≤ 3 by norm_num)
    simpa using this
  have h4 : r ^ 4 ≤ r := by
    have := pow_le_pow_of_le_one (a := r) hr0 hr1 (show (1 : ℕ) ≤ 4 by norm_num)
    simpa using this
  have h5 : r ^ 5 ≤ r := by
    have := pow_le_pow_of_le_one (a := r) hr0 hr1 (show (1 : ℕ) ≤ 5 by norm_num)
    simpa using this
  have hU'' : ‖Work.Kernels.UFun τ - (1 + 8 * e + 24 * e ^ 2 + 32 * e ^ 3 + 24 * e ^ 4)‖
      ≤ 10000 * r ^ 5 := by simpa only [← hr] using hU'
  have hV'' : ‖Work.Kernels.VFun τ - (16 * e + 64 * e ^ 3)‖ ≤ 10000 * r ^ 5 := by
    simpa only [← hr] using hV'
  have hid : -(Work.Kernels.UFun τ + Work.Kernels.VFun τ) + 1
      = -(((Work.Kernels.UFun τ - (1 + 8 * e + 24 * e ^ 2 + 32 * e ^ 3 + 24 * e ^ 4))
          + (Work.Kernels.VFun τ - (16 * e + 64 * e ^ 3))
          + (24 * e + 24 * e ^ 2 + 96 * e ^ 3 + 24 * e ^ 4))) := by ring
  have hpoly : ‖(24 : ℂ) * e + 24 * e ^ 2 + 96 * e ^ 3 + 24 * e ^ 4‖ ≤ 168 * r := by
    have hN1 : ‖(24 : ℂ) * e‖ = 24 * r := by rw [norm_mul, Complex.norm_ofNat, ← hr]
    have hN2 : ‖(24 : ℂ) * e ^ 2‖ = 24 * r ^ 2 := by
      rw [norm_mul, norm_pow, Complex.norm_ofNat, ← hr]
    have hN3 : ‖(96 : ℂ) * e ^ 3‖ = 96 * r ^ 3 := by
      rw [norm_mul, norm_pow, Complex.norm_ofNat, ← hr]
    have hN4 : ‖(24 : ℂ) * e ^ 4‖ = 24 * r ^ 4 := by
      rw [norm_mul, norm_pow, Complex.norm_ofNat, ← hr]
    have h12 := norm_add_le ((24 : ℂ) * e) ((24 : ℂ) * e ^ 2)
    have h13 := norm_add_le ((24 : ℂ) * e + (24 : ℂ) * e ^ 2) ((96 : ℂ) * e ^ 3)
    have h14 := norm_add_le ((24 : ℂ) * e + (24 : ℂ) * e ^ 2 + (96 : ℂ) * e ^ 3)
      ((24 : ℂ) * e ^ 4)
    linarith [h12, h13, h14, hN1, hN2, hN3, hN4, h2, h3, h4]
  have hrest : ‖(Work.Kernels.UFun τ - (1 + 8 * e + 24 * e ^ 2 + 32 * e ^ 3 + 24 * e ^ 4))
      + (Work.Kernels.VFun τ - (16 * e + 64 * e ^ 3))‖ ≤ 10000 * r ^ 5 + 10000 * r ^ 5 := by
    have h3' := norm_add_le
      (Work.Kernels.UFun τ - (1 + 8 * e + 24 * e ^ 2 + 32 * e ^ 3 + 24 * e ^ 4))
      (Work.Kernels.VFun τ - (16 * e + 64 * e ^ 3))
    linarith [h3', hU'', hV'']
  rw [Work.Kernels.KernelFacts.xi2Fun_slash_S τ]
  have hmain : ‖-(Work.Kernels.UFun τ + Work.Kernels.VFun τ) + 1‖ ≤ 30000 * r := by
    rw [hid, norm_neg]
    have h3' := norm_add_le
      ((Work.Kernels.UFun τ - (1 + 8 * e + 24 * e ^ 2 + 32 * e ^ 3 + 24 * e ^ 4))
        + (Work.Kernels.VFun τ - (16 * e + 64 * e ^ 3)))
      ((24 : ℂ) * e + 24 * e ^ 2 + 96 * e ^ 3 + 24 * e ^ 4)
    linarith [h3', hrest, hpoly, h5, hr0]
  simpa only [← hr] using hmain

/-! ## The two `ξ`-bounds for `ψ₄` -/

/-- `ξ₄ = U² + W² - 2V² = 2 + O(‖e‖²)`. -/
private lemma xi4Fun_sub_two_bound (τ : ℍ) (hτ : Work.Asymptotics.Funnel τ) :
    ‖Work.Kernels.xi4Fun τ - 2‖ ≤ 100000000000 * ‖Work.Asymptotics.nomeE τ‖ ^ 2 := by
  have hτ2 : (2 : ℝ) ≤ τ.im := hτ.2
  have hU := Work.Asymptotics.UFun_qexp τ hτ2
  have hW := Work.Asymptotics.WFun_qexp τ hτ2
  have hV := Work.Asymptotics.VFun_qexp τ hτ2
  set e : ℂ := Work.Asymptotics.nomeE τ with he
  set PU : ℂ := 1 + 8 * e + 24 * e ^ 2 + 32 * e ^ 3 + 24 * e ^ 4 with hPU
  set PW : ℂ := 1 - 8 * e + 24 * e ^ 2 - 32 * e ^ 3 + 24 * e ^ 4 with hPW
  set PV : ℂ := 16 * e + 64 * e ^ 3 with hPV
  have hUp : ‖Work.Kernels.UFun τ - PU‖ ≤ 10000 * ‖e‖ ^ 5 := by rw [hPU, he]; exact hU
  have hWp : ‖Work.Kernels.WFun τ - PW‖ ≤ 10000 * ‖e‖ ^ 5 := by rw [hPW, he]; exact hW
  have hVp : ‖Work.Kernels.VFun τ - PV‖ ≤ 10000 * ‖e‖ ^ 5 := by rw [hPV, he]; exact hV
  have he1 : ‖e‖ ≤ 1 := by rw [he]; exact nomeE_norm_le_one hτ
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = ‖e‖ := ⟨_, rfl⟩
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have hr1 : r ≤ 1 := by rw [hr]; exact he1
  have hk2 : r ^ 2 ≤ 1 := pow_le_one₀ hr0 hr1
  have hk3 : r ^ 3 ≤ 1 := pow_le_one₀ hr0 hr1
  have hk4 : r ^ 4 ≤ 1 := pow_le_one₀ hr0 hr1
  have hr2r : r ^ 2 ≤ r := by
    have := pow_le_pow_of_le_one (a := r) hr0 hr1 (show (1 : ℕ) ≤ 2 by norm_num)
    simpa using this
  have hUp' : ‖Work.Kernels.UFun τ - PU‖ ≤ 10000 * r ^ 5 := by simpa only [← hr] using hUp
  have hWp' : ‖Work.Kernels.WFun τ - PW‖ ≤ 10000 * r ^ 5 := by simpa only [← hr] using hWp
  have hVp' : ‖Work.Kernels.VFun τ - PV‖ ≤ 10000 * r ^ 5 := by simpa only [← hr] using hVp
  have hPUb : ‖PU‖ ≤ 90 := by
    have hsum : ‖PU‖ ≤ ‖(1 : ℂ)‖ + ‖(8 : ℂ) * e‖ + ‖(24 : ℂ) * e ^ 2‖ + ‖(32 : ℂ) * e ^ 3‖
        + ‖(24 : ℂ) * e ^ 4‖ := by
      rw [hPU]
      have hA := norm_add_le (((1 : ℂ) + 8 * e) + 24 * e ^ 2 + 32 * e ^ 3) ((24 : ℂ) * e ^ 4)
      have hB := norm_chain4 (1 : ℂ) ((8 : ℂ) * e) ((24 : ℂ) * e ^ 2) ((32 : ℂ) * e ^ 3)
      linarith
    have h1 : ‖(8 : ℂ) * e‖ = 8 * r := by rw [norm_mul, Complex.norm_ofNat, ← hr]
    have h2 : ‖(24 : ℂ) * e ^ 2‖ = 24 * r ^ 2 := by
      rw [norm_mul, norm_pow, Complex.norm_ofNat, ← hr]
    have h3 : ‖(32 : ℂ) * e ^ 3‖ = 32 * r ^ 3 := by
      rw [norm_mul, norm_pow, Complex.norm_ofNat, ← hr]
    have h4 : ‖(24 : ℂ) * e ^ 4‖ = 24 * r ^ 4 := by
      rw [norm_mul, norm_pow, Complex.norm_ofNat, ← hr]
    rw [h1, h2, h3, h4, norm_one] at hsum
    nlinarith [hsum, hr1, hk2, hk3, hk4]
  have hPWb : ‖PW‖ ≤ 90 := by
    have hsum : ‖PW‖ ≤ ‖(1 : ℂ)‖ + ‖(8 : ℂ) * e‖ + ‖(24 : ℂ) * e ^ 2‖ + ‖(32 : ℂ) * e ^ 3‖
        + ‖(24 : ℂ) * e ^ 4‖ := by
      rw [hPW]
      have hA := norm_add_le (((1 - 8 * e) + 24 * e ^ 2) - 32 * e ^ 3) ((24 : ℂ) * e ^ 4)
      have hB := norm_sub_le ((1 - 8 * e) + 24 * e ^ 2) ((32 : ℂ) * e ^ 3)
      have hC := norm_add_le (1 - (8 : ℂ) * e) ((24 : ℂ) * e ^ 2)
      have hD := norm_sub_le (1 : ℂ) ((8 : ℂ) * e)
      linarith
    have h1 : ‖(8 : ℂ) * e‖ = 8 * r := by rw [norm_mul, Complex.norm_ofNat, ← hr]
    have h2 : ‖(24 : ℂ) * e ^ 2‖ = 24 * r ^ 2 := by
      rw [norm_mul, norm_pow, Complex.norm_ofNat, ← hr]
    have h3 : ‖(32 : ℂ) * e ^ 3‖ = 32 * r ^ 3 := by
      rw [norm_mul, norm_pow, Complex.norm_ofNat, ← hr]
    have h4 : ‖(24 : ℂ) * e ^ 4‖ = 24 * r ^ 4 := by
      rw [norm_mul, norm_pow, Complex.norm_ofNat, ← hr]
    rw [h1, h2, h3, h4, norm_one] at hsum
    nlinarith [hsum, hr1, hk2, hk3, hk4]
  have hPVb : ‖PV‖ ≤ 90 := by
    have hsum : ‖PV‖ ≤ ‖(16 : ℂ) * e‖ + ‖(64 : ℂ) * e ^ 3‖ := by
      rw [hPV]
      exact norm_add_le _ _
    have h1 : ‖(16 : ℂ) * e‖ = 16 * r := by rw [norm_mul, Complex.norm_ofNat, ← hr]
    have h2 : ‖(64 : ℂ) * e ^ 3‖ = 64 * r ^ 3 := by
      rw [norm_mul, norm_pow, Complex.norm_ofNat, ← hr]
    rw [h1, h2] at hsum
    nlinarith [hsum, hr1, hk3]
  have hδU := sq_sub_sq_bound (U := Work.Kernels.UFun τ) (P := PU) hr0 hr1 hUp' hPUb
  have hδW := sq_sub_sq_bound (U := Work.Kernels.WFun τ) (P := PW) hr0 hr1 hWp' hPWb
  have hδV := sq_sub_sq_bound (U := Work.Kernels.VFun τ) (P := PV) hr0 hr1 hVp' hPVb
  have hpolyb : ‖288 * e ^ 2 + 1824 * e ^ 4 + 3840 * e ^ 6 - 1152 * e ^ 8‖ ≤ 10000 * r ^ 2 := by
    have h1 : ‖(288 : ℂ) * e ^ 2‖ = 288 * r ^ 2 := by
      rw [norm_mul, norm_pow, Complex.norm_ofNat, ← hr]
    have h2 : ‖(1824 : ℂ) * e ^ 4‖ = 1824 * r ^ 4 := by
      rw [norm_mul, norm_pow, Complex.norm_ofNat, ← hr]
    have h3 : ‖(3840 : ℂ) * e ^ 6‖ = 3840 * r ^ 6 := by
      rw [norm_mul, norm_pow, Complex.norm_ofNat, ← hr]
    have h4 : ‖(1152 : ℂ) * e ^ 8‖ = 1152 * r ^ 8 := by
      rw [norm_mul, norm_pow, Complex.norm_ofNat, ← hr]
    have hs1 := norm_sub_le ((288 : ℂ) * e ^ 2 + 1824 * e ^ 4 + 3840 * e ^ 6)
      ((1152 : ℂ) * e ^ 8)
    have hs2 := norm_add_le ((288 : ℂ) * e ^ 2 + 1824 * e ^ 4) ((3840 : ℂ) * e ^ 6)
    have hs3 := norm_add_le ((288 : ℂ) * e ^ 2) ((1824 : ℂ) * e ^ 4)
    have h4r : r ^ 4 ≤ r ^ 2 := pow_le_pow_of_le_one hr0 hr1 (by norm_num)
    have h6r : r ^ 6 ≤ r ^ 2 := pow_le_pow_of_le_one hr0 hr1 (by norm_num)
    have h8r : r ^ 8 ≤ r ^ 2 := pow_le_pow_of_le_one hr0 hr1 (by norm_num)
    linarith [hs1, hs2, hs3, h1, h2, h3, h4, h4r, h6r, h8r, pow_nonneg hr0 2]
  have hid : Work.Kernels.xi4Fun τ - 2
      = (PU ^ 2 + PW ^ 2 - 2 * PV ^ 2 - 2)
        + ((Work.Kernels.UFun τ ^ 2 - PU ^ 2) + (Work.Kernels.WFun τ ^ 2 - PW ^ 2)
            - 2 * (Work.Kernels.VFun τ ^ 2 - PV ^ 2)) := by
    rw [Work.Kernels.xi4Fun]; ring
  have hpoly : PU ^ 2 + PW ^ 2 - 2 * PV ^ 2 - 2
      = -(288 * e ^ 2 + 1824 * e ^ 4 + 3840 * e ^ 6 - 1152 * e ^ 8) := by
    rw [hPU, hPW, hPV]; ring
  have hmain : ‖Work.Kernels.xi4Fun τ - 2‖ ≤ 100000000000 * r ^ 2 := by
    rw [hid, hpoly]
    have hsplit := norm_add_le (-(288 * e ^ 2 + 1824 * e ^ 4 + 3840 * e ^ 6 - 1152 * e ^ 8))
      ((Work.Kernels.UFun τ ^ 2 - PU ^ 2) + (Work.Kernels.WFun τ ^ 2 - PW ^ 2)
        - 2 * (Work.Kernels.VFun τ ^ 2 - PV ^ 2))
    have hsplit2 := norm_sub_le
      ((Work.Kernels.UFun τ ^ 2 - PU ^ 2) + (Work.Kernels.WFun τ ^ 2 - PW ^ 2))
      (2 * (Work.Kernels.VFun τ ^ 2 - PV ^ 2))
    have hsplit3 := norm_add_le (Work.Kernels.UFun τ ^ 2 - PU ^ 2)
      (Work.Kernels.WFun τ ^ 2 - PW ^ 2)
    have hV2 : ‖2 * (Work.Kernels.VFun τ ^ 2 - PV ^ 2)‖ ≤ 2 * (10000000000 * r ^ 2) := by
      rw [norm_mul, Complex.norm_ofNat]
      linarith [hδV]
    have hp' : ‖-(288 * e ^ 2 + 1824 * e ^ 4 + 3840 * e ^ 6 - 1152 * e ^ 8)‖ ≤ 10000 * r ^ 2 := by
      rw [norm_neg]; exact hpolyb
    linarith [hsplit, hsplit2, hsplit3, hp', hδU, hδW, hV2, pow_nonneg hr0 2]
  simpa only [← hr] using hmain

/-- `(ξ₄|₄S) = U² + V² - 2W² = -1 + O(‖e‖)`. -/
private lemma xi4S_add_one_bound (τ : ℍ) (hτ : Work.Asymptotics.Funnel τ) :
    ‖(Work.Kernels.xi4Fun ∣[(4 : ℤ)] ModularGroup.S) τ + 1‖
      ≤ 100000000000 * ‖Work.Asymptotics.nomeE τ‖ := by
  have hτ2 : (2 : ℝ) ≤ τ.im := hτ.2
  have hU := Work.Asymptotics.UFun_qexp τ hτ2
  have hW := Work.Asymptotics.WFun_qexp τ hτ2
  have hV := Work.Asymptotics.VFun_qexp τ hτ2
  set e : ℂ := Work.Asymptotics.nomeE τ with he
  set PU : ℂ := 1 + 8 * e + 24 * e ^ 2 + 32 * e ^ 3 + 24 * e ^ 4 with hPU
  set PW : ℂ := 1 - 8 * e + 24 * e ^ 2 - 32 * e ^ 3 + 24 * e ^ 4 with hPW
  set PV : ℂ := 16 * e + 64 * e ^ 3 with hPV
  have hUp : ‖Work.Kernels.UFun τ - PU‖ ≤ 10000 * ‖e‖ ^ 5 := by rw [hPU, he]; exact hU
  have hWp : ‖Work.Kernels.WFun τ - PW‖ ≤ 10000 * ‖e‖ ^ 5 := by rw [hPW, he]; exact hW
  have hVp : ‖Work.Kernels.VFun τ - PV‖ ≤ 10000 * ‖e‖ ^ 5 := by rw [hPV, he]; exact hV
  have he1 : ‖e‖ ≤ 1 := by rw [he]; exact nomeE_norm_le_one hτ
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = ‖e‖ := ⟨_, rfl⟩
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have hr1 : r ≤ 1 := by rw [hr]; exact he1
  have hk2 : r ^ 2 ≤ 1 := pow_le_one₀ hr0 hr1
  have hk3 : r ^ 3 ≤ 1 := pow_le_one₀ hr0 hr1
  have hk4 : r ^ 4 ≤ 1 := pow_le_one₀ hr0 hr1
  have hr2r : r ^ 2 ≤ r := by
    have := pow_le_pow_of_le_one (a := r) hr0 hr1 (show (1 : ℕ) ≤ 2 by norm_num)
    simpa using this
  have hUp' : ‖Work.Kernels.UFun τ - PU‖ ≤ 10000 * r ^ 5 := by simpa only [← hr] using hUp
  have hWp' : ‖Work.Kernels.WFun τ - PW‖ ≤ 10000 * r ^ 5 := by simpa only [← hr] using hWp
  have hVp' : ‖Work.Kernels.VFun τ - PV‖ ≤ 10000 * r ^ 5 := by simpa only [← hr] using hVp
  have hPUb : ‖PU‖ ≤ 90 := by
    have hsum : ‖PU‖ ≤ ‖(1 : ℂ)‖ + ‖(8 : ℂ) * e‖ + ‖(24 : ℂ) * e ^ 2‖ + ‖(32 : ℂ) * e ^ 3‖
        + ‖(24 : ℂ) * e ^ 4‖ := by
      rw [hPU]
      have hA := norm_add_le (((1 : ℂ) + 8 * e) + 24 * e ^ 2 + 32 * e ^ 3) ((24 : ℂ) * e ^ 4)
      have hB := norm_chain4 (1 : ℂ) ((8 : ℂ) * e) ((24 : ℂ) * e ^ 2) ((32 : ℂ) * e ^ 3)
      linarith
    have h1 : ‖(8 : ℂ) * e‖ = 8 * r := by rw [norm_mul, Complex.norm_ofNat, ← hr]
    have h2 : ‖(24 : ℂ) * e ^ 2‖ = 24 * r ^ 2 := by
      rw [norm_mul, norm_pow, Complex.norm_ofNat, ← hr]
    have h3 : ‖(32 : ℂ) * e ^ 3‖ = 32 * r ^ 3 := by
      rw [norm_mul, norm_pow, Complex.norm_ofNat, ← hr]
    have h4 : ‖(24 : ℂ) * e ^ 4‖ = 24 * r ^ 4 := by
      rw [norm_mul, norm_pow, Complex.norm_ofNat, ← hr]
    rw [h1, h2, h3, h4, norm_one] at hsum
    nlinarith [hsum, hr1, hk2, hk3, hk4]
  have hPWb : ‖PW‖ ≤ 90 := by
    have hsum : ‖PW‖ ≤ ‖(1 : ℂ)‖ + ‖(8 : ℂ) * e‖ + ‖(24 : ℂ) * e ^ 2‖ + ‖(32 : ℂ) * e ^ 3‖
        + ‖(24 : ℂ) * e ^ 4‖ := by
      rw [hPW]
      have hA := norm_add_le (((1 - 8 * e) + 24 * e ^ 2) - 32 * e ^ 3) ((24 : ℂ) * e ^ 4)
      have hB := norm_sub_le ((1 - 8 * e) + 24 * e ^ 2) ((32 : ℂ) * e ^ 3)
      have hC := norm_add_le (1 - (8 : ℂ) * e) ((24 : ℂ) * e ^ 2)
      have hD := norm_sub_le (1 : ℂ) ((8 : ℂ) * e)
      linarith
    have h1 : ‖(8 : ℂ) * e‖ = 8 * r := by rw [norm_mul, Complex.norm_ofNat, ← hr]
    have h2 : ‖(24 : ℂ) * e ^ 2‖ = 24 * r ^ 2 := by
      rw [norm_mul, norm_pow, Complex.norm_ofNat, ← hr]
    have h3 : ‖(32 : ℂ) * e ^ 3‖ = 32 * r ^ 3 := by
      rw [norm_mul, norm_pow, Complex.norm_ofNat, ← hr]
    have h4 : ‖(24 : ℂ) * e ^ 4‖ = 24 * r ^ 4 := by
      rw [norm_mul, norm_pow, Complex.norm_ofNat, ← hr]
    rw [h1, h2, h3, h4, norm_one] at hsum
    nlinarith [hsum, hr1, hk2, hk3, hk4]
  have hPVb : ‖PV‖ ≤ 90 := by
    have hsum : ‖PV‖ ≤ ‖(16 : ℂ) * e‖ + ‖(64 : ℂ) * e ^ 3‖ := by
      rw [hPV]
      exact norm_add_le _ _
    have h1 : ‖(16 : ℂ) * e‖ = 16 * r := by rw [norm_mul, Complex.norm_ofNat, ← hr]
    have h2 : ‖(64 : ℂ) * e ^ 3‖ = 64 * r ^ 3 := by
      rw [norm_mul, norm_pow, Complex.norm_ofNat, ← hr]
    rw [h1, h2] at hsum
    nlinarith [hsum, hr1, hk3]
  have hδU := sq_sub_sq_bound (U := Work.Kernels.UFun τ) (P := PU) hr0 hr1 hUp' hPUb
  have hδV := sq_sub_sq_bound (U := Work.Kernels.VFun τ) (P := PV) hr0 hr1 hVp' hPVb
  have hδW := sq_sub_sq_bound (U := Work.Kernels.WFun τ) (P := PW) hr0 hr1 hWp' hPWb
  have hpolyb : ‖48 * e + 144 * e ^ 2 + 1344 * e ^ 3 + 912 * e ^ 4 + 5760 * e ^ 5
      + 1920 * e ^ 6 + 4608 * e ^ 7 - 576 * e ^ 8‖ ≤ 20000 * r := by
    have h1 : ‖(48 : ℂ) * e‖ = 48 * r := by rw [norm_mul, Complex.norm_ofNat, ← hr]
    have h2 : ‖(144 : ℂ) * e ^ 2‖ = 144 * r ^ 2 := by
      rw [norm_mul, norm_pow, Complex.norm_ofNat, ← hr]
    have h3 : ‖(1344 : ℂ) * e ^ 3‖ = 1344 * r ^ 3 := by
      rw [norm_mul, norm_pow, Complex.norm_ofNat, ← hr]
    have h4 : ‖(912 : ℂ) * e ^ 4‖ = 912 * r ^ 4 := by
      rw [norm_mul, norm_pow, Complex.norm_ofNat, ← hr]
    have h5 : ‖(5760 : ℂ) * e ^ 5‖ = 5760 * r ^ 5 := by
      rw [norm_mul, norm_pow, Complex.norm_ofNat, ← hr]
    have h6 : ‖(1920 : ℂ) * e ^ 6‖ = 1920 * r ^ 6 := by
      rw [norm_mul, norm_pow, Complex.norm_ofNat, ← hr]
    have h7 : ‖(4608 : ℂ) * e ^ 7‖ = 4608 * r ^ 7 := by
      rw [norm_mul, norm_pow, Complex.norm_ofNat, ← hr]
    have h8 : ‖-((576 : ℂ) * e ^ 8)‖ = 576 * r ^ 8 := by
      rw [norm_neg, norm_mul, norm_pow, Complex.norm_ofNat, ← hr]
    have hs := norm_chain8 ((48 : ℂ) * e) ((144 : ℂ) * e ^ 2) ((1344 : ℂ) * e ^ 3)
      ((912 : ℂ) * e ^ 4) ((5760 : ℂ) * e ^ 5) ((1920 : ℂ) * e ^ 6) ((4608 : ℂ) * e ^ 7)
      (-((576 : ℂ) * e ^ 8))
    rw [h1, h2, h3, h4, h5, h6, h7, h8] at hs
    have h2r : r ^ 2 ≤ r := hr2r
    have h3r : r ^ 3 ≤ r := by
      have := pow_le_pow_of_le_one (a := r) hr0 hr1 (show (1 : ℕ) ≤ 3 by norm_num)
      simpa using this
    have h4r : r ^ 4 ≤ r := by
      have := pow_le_pow_of_le_one (a := r) hr0 hr1 (show (1 : ℕ) ≤ 4 by norm_num)
      simpa using this
    have h5r : r ^ 5 ≤ r := by
      have := pow_le_pow_of_le_one (a := r) hr0 hr1 (show (1 : ℕ) ≤ 5 by norm_num)
      simpa using this
    have h6r : r ^ 6 ≤ r := by
      have := pow_le_pow_of_le_one (a := r) hr0 hr1 (show (1 : ℕ) ≤ 6 by norm_num)
      simpa using this
    have h7r : r ^ 7 ≤ r := by
      have := pow_le_pow_of_le_one (a := r) hr0 hr1 (show (1 : ℕ) ≤ 7 by norm_num)
      simpa using this
    have h8r : r ^ 8 ≤ r := by
      have := pow_le_pow_of_le_one (a := r) hr0 hr1 (show (1 : ℕ) ≤ 8 by norm_num)
      simpa using this
    have hmain : ‖48 * e + 144 * e ^ 2 + 1344 * e ^ 3 + 912 * e ^ 4 + 5760 * e ^ 5
        + 1920 * e ^ 6 + 4608 * e ^ 7 + -((576 : ℂ) * e ^ 8)‖ ≤ 20000 * r := by
      linarith [hs, h2r, h3r, h4r, h5r, h6r, h7r, h8r, hr0]
    simpa only [sub_eq_add_neg] using hmain
  have hid : Work.Kernels.UFun τ ^ 2 + Work.Kernels.VFun τ ^ 2 - 2 * Work.Kernels.WFun τ ^ 2 + 1
      = (PU ^ 2 + PV ^ 2 - 2 * PW ^ 2 + 1)
        + ((Work.Kernels.UFun τ ^ 2 - PU ^ 2) + (Work.Kernels.VFun τ ^ 2 - PV ^ 2)
            - 2 * (Work.Kernels.WFun τ ^ 2 - PW ^ 2)) := by ring
  have hpoly : PU ^ 2 + PV ^ 2 - 2 * PW ^ 2 + 1
      = 48 * e + 144 * e ^ 2 + 1344 * e ^ 3 + 912 * e ^ 4 + 5760 * e ^ 5
        + 1920 * e ^ 6 + 4608 * e ^ 7 - 576 * e ^ 8 := by
    rw [hPU, hPW, hPV]; ring
  rw [Work.Kernels.KernelFacts.xi4S_apply τ]
  have hmain : ‖Work.Kernels.UFun τ ^ 2 + Work.Kernels.VFun τ ^ 2
      - 2 * Work.Kernels.WFun τ ^ 2 + 1‖ ≤ 100000000000 * r := by
    rw [hid, hpoly]
    have hsplit := norm_add_le (48 * e + 144 * e ^ 2 + 1344 * e ^ 3 + 912 * e ^ 4 + 5760 * e ^ 5
        + 1920 * e ^ 6 + 4608 * e ^ 7 - 576 * e ^ 8)
      ((Work.Kernels.UFun τ ^ 2 - PU ^ 2) + (Work.Kernels.VFun τ ^ 2 - PV ^ 2)
        - 2 * (Work.Kernels.WFun τ ^ 2 - PW ^ 2))
    have hsplit2 := norm_sub_le
      ((Work.Kernels.UFun τ ^ 2 - PU ^ 2) + (Work.Kernels.VFun τ ^ 2 - PV ^ 2))
      (2 * (Work.Kernels.WFun τ ^ 2 - PW ^ 2))
    have hsplit3 := norm_add_le (Work.Kernels.UFun τ ^ 2 - PU ^ 2)
      (Work.Kernels.VFun τ ^ 2 - PV ^ 2)
    have hW2 : ‖2 * (Work.Kernels.WFun τ ^ 2 - PW ^ 2)‖ ≤ 2 * (10000000000 * r ^ 2) := by
      rw [norm_mul, Complex.norm_ofNat]
      linarith [hδW]
    linarith [hsplit, hsplit2, hsplit3, hpolyb, hδU, hδV, hW2, pow_nonneg hr0 2, hr2r, hr0]
  simpa only [← hr] using hmain

/-! ## The slash transforms of `ξ₂`, `ξ₄` -/

/-- `(ξ₂|₂S) = -(U + V)`. -/
private def xi2SlashFun : ℍ → ℂ := fun τ => -(Work.Kernels.UFun τ + Work.Kernels.VFun τ)

/-- `(ξ₄|₄S) = U² + V² - 2W²`. -/
private def xi4SlashFun : ℍ → ℂ :=
  fun τ => Work.Kernels.UFun τ ^ 2 + Work.Kernels.VFun τ ^ 2 - 2 * Work.Kernels.WFun τ ^ 2

/-! ## The abstract first-order statement -/

/-- If `A = 2 + O(‖e‖²)` and `B = -1 + O(‖e‖)`, then
`A𝓛 + B𝓛_S = 2(πiτ + c) + O(scale · ‖q‖)` on the funnel. -/
private theorem psi_shift_bound (ℓ : Work.Kernels.LogLambdaData) (A B : ℍ → ℂ) (Ca Cb : ℝ)
    (hA : ∀ τ, Work.Asymptotics.Funnel τ → ‖A τ - 2‖ ≤ Ca * ‖Work.Asymptotics.nomeE τ‖ ^ 2)
    (hB : ∀ τ, Work.Asymptotics.Funnel τ → ‖B τ + 1‖ ≤ Cb * ‖Work.Asymptotics.nomeE τ‖)
    (hCa : 0 ≤ Ca) (hCb : 0 ≤ Cb) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, Work.Asymptotics.Funnel τ →
      ‖A τ * ℓ.L τ + B τ * ℓ.L_S τ
          - 2 * ((Real.pi : ℂ) * Complex.I * (τ : ℂ) + Work.Asymptotics.Compact.cuspC ℓ)‖
        ≤ C * (Work.Kernels.scale τ) ^ (1 : ℝ) * ‖Work.Kernels.qParamFun τ‖ := by
  obtain ⟨CL, hCLpos, hLb⟩ := Work.Asymptotics.Compact.cuspC_spec ℓ
  obtain ⟨CS, hCSpos, hSb⟩ := Work.Residues.LamSExpansion
  refine ⟨(Real.pi + 4) * Ca
      + (24 + 16 * Cb + (20 + CL) * Ca + 2 * CL + CS + Cb * CS) + 1, ?_, fun τ hτ => ?_⟩
  · have h1 : (0 : ℝ) ≤ (Real.pi + 4) * Ca := by
      have h2 : (0 : ℝ) ≤ Real.pi + 4 := by linarith [Real.pi_pos]
      positivity
    have h2 : (0 : ℝ) ≤ 24 + 16 * Cb + (20 + CL) * Ca + 2 * CL + CS + Cb * CS := by
      have h3 : (0 : ℝ) ≤ CL := hCLpos.le
      have h4 : (0 : ℝ) ≤ CS := hCSpos.le
      positivity
    linarith
  have hτ1 : (1 : ℝ) ≤ τ.im := Work.Asymptotics.Funnel.im_one hτ
  set e : ℂ := Work.Asymptotics.nomeE τ with he
  have hEpt : Work.Residues.Ept τ = e := by rw [he]; rfl
  have he1 : ‖e‖ ≤ 1 := by rw [he]; exact nomeE_norm_le_one hτ
  have hAτ : ‖A τ - 2‖ ≤ Ca * ‖e‖ ^ 2 := by rw [he]; exact hA τ hτ
  have hBτ : ‖B τ + 1‖ ≤ Cb * ‖e‖ := by rw [he]; exact hB τ hτ
  have hLbτ : ‖ℓ.L τ - ((Real.pi : ℂ) * Complex.I * (τ : ℂ) + Work.Asymptotics.Compact.cuspC ℓ
        - 8 * e + 12 * e ^ 2)‖ ≤ CL * ‖e‖ ^ 3 := by
    have h := hLb τ hτ1
    rw [hEpt] at h
    exact h
  have hLSbτ : ‖ℓ.L_S τ + 16 * e‖ ≤ CS * ‖e‖ ^ 3 := by
    have h1 : ℓ.L_S τ = Work.Kernels.LogLambda.LamS (τ : ℂ) :=
      Work.Residues.LogLambdaData_LS_eq_LamS ℓ τ (by linarith)
    rw [h1]
    have h := hSb τ hτ1
    rw [hEpt] at h
    exact h
  set Λ : ℂ := (Real.pi : ℂ) * Complex.I * (τ : ℂ) + Work.Asymptotics.Compact.cuspC ℓ with hΛ
  set ER : ℂ := ℓ.L τ - (Λ - 8 * e + 12 * e ^ 2) with hER
  set ES : ℂ := ℓ.L_S τ + 16 * e with hES
  have hERb : ‖ER‖ ≤ CL * ‖e‖ ^ 3 := by rw [hER, hΛ]; exact hLbτ
  have hESb : ‖ES‖ ≤ CS * ‖e‖ ^ 3 := by rw [hES]; exact hLSbτ
  have hL : ℓ.L τ = Λ - 8 * e + 12 * e ^ 2 + ER := by rw [hER]; ring
  have hLS : ℓ.L_S τ = ES - 16 * e := by rw [hES]; ring
  have hkey : A τ * ℓ.L τ + B τ * ℓ.L_S τ - 2 * Λ
      = (A τ - 2) * Λ + (24 * e ^ 2 + 2 * ER - ES)
        + (A τ - 2) * (-8 * e + 12 * e ^ 2 + ER) + (B τ + 1) * (-16 * e + ES) := by
    rw [hL, hLS]; ring
  have hΛb : ‖Λ‖ ≤ (Real.pi + 4) * Work.Kernels.scale τ := by rw [hΛ]; exact cuspC_add_bound ℓ τ
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = ‖e‖ := ⟨_, rfl⟩
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have hr1 : r ≤ 1 := by rw [hr]; exact he1
  have h32 : r ^ 3 ≤ r ^ 2 := pow_le_pow_of_le_one hr0 hr1 (by norm_num)
  have hr2r : r ^ 2 ≤ r := by
    have := pow_le_pow_of_le_one (a := r) hr0 hr1 (show (1 : ℕ) ≤ 2 by norm_num)
    simpa using this
  have hAτ' : ‖A τ - 2‖ ≤ Ca * r ^ 2 := by simpa only [← hr] using hAτ
  have hBτ' : ‖B τ + 1‖ ≤ Cb * r := by simpa only [← hr] using hBτ
  have hERb' : ‖ER‖ ≤ CL * r ^ 3 := by simpa only [← hr] using hERb
  have hESb' : ‖ES‖ ≤ CS * r ^ 3 := by simpa only [← hr] using hESb
  have hCLr : CL * r ^ 3 ≤ CL * r ^ 2 := mul_le_mul_of_nonneg_left h32 hCLpos.le
  have hCSr : CS * r ^ 3 ≤ CS * r ^ 2 := mul_le_mul_of_nonneg_left h32 hCSpos.le
  have hCLr1 : CL * r ^ 3 ≤ CL * r :=
    le_trans hCLr (mul_le_mul_of_nonneg_left hr2r hCLpos.le)
  have hCSr1 : CS * r ^ 3 ≤ CS * r :=
    le_trans hCSr (mul_le_mul_of_nonneg_left hr2r hCSpos.le)
  have hscale1 : (1 : ℝ) ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ
  have t1 : ‖(A τ - 2) * Λ‖ ≤ (Real.pi + 4) * Ca * Work.Kernels.scale τ * r ^ 2 := by
    rw [norm_mul]
    calc ‖A τ - 2‖ * ‖Λ‖ ≤ (Ca * r ^ 2) * ((Real.pi + 4) * Work.Kernels.scale τ) :=
          mul_le_mul hAτ' hΛb (norm_nonneg _) (mul_nonneg hCa (sq_nonneg r))
      _ = (Real.pi + 4) * Ca * Work.Kernels.scale τ * r ^ 2 := by ring
  have t2 : ‖24 * e ^ 2 + 2 * ER - ES‖ ≤ (24 + 2 * CL + CS) * r ^ 2 := by
    have h24 : ‖(24 : ℂ) * e ^ 2‖ = 24 * r ^ 2 := by
      rw [norm_mul, norm_pow, Complex.norm_ofNat, ← hr]
    have h2E : ‖(2 : ℂ) * ER‖ ≤ 2 * (CL * r ^ 3) := by
      rw [norm_mul, Complex.norm_ofNat]
      linarith [hERb']
    have hsum1 := norm_add_le ((24 : ℂ) * e ^ 2) ((2 : ℂ) * ER)
    have hsum2 := norm_sub_le ((24 : ℂ) * e ^ 2 + (2 : ℂ) * ER) ES
    have hlin : 24 * r ^ 2 + 2 * (CL * r ^ 3) + CS * r ^ 3 ≤ (24 + 2 * CL + CS) * r ^ 2 := by
      nlinarith [hCLr, hCSr]
    linarith [hsum1, hsum2, h24, h2E, hESb', hlin]
  have t3 : ‖(A τ - 2) * (-8 * e + 12 * e ^ 2 + ER)‖ ≤ Ca * (20 + CL) * r ^ 2 := by
    rw [norm_mul]
    have hv : ‖-8 * e + 12 * e ^ 2 + ER‖ ≤ (20 + CL) * r := by
      have h8 : ‖(-8 : ℂ) * e‖ = 8 * r := by
        have heq : (-8 : ℂ) * e = -((8 : ℂ) * e) := by ring
        rw [heq, norm_neg, norm_mul, Complex.norm_ofNat, ← hr]
      have h12 : ‖(12 : ℂ) * e ^ 2‖ = 12 * r ^ 2 := by
        rw [norm_mul, norm_pow, Complex.norm_ofNat, ← hr]
      have hsum1 := norm_add_le ((-8 : ℂ) * e) ((12 : ℂ) * e ^ 2)
      have hsum2 := norm_add_le ((-8 : ℂ) * e + (12 : ℂ) * e ^ 2) ER
      have h12r : 12 * r ^ 2 ≤ 12 * r := by linarith [hr2r]
      linarith [hsum1, hsum2, h8, h12, h12r, hCLr1, hERb']
    calc ‖A τ - 2‖ * ‖-8 * e + 12 * e ^ 2 + ER‖ ≤ (Ca * r ^ 2) * ((20 + CL) * r) :=
          mul_le_mul hAτ' hv (norm_nonneg _) (mul_nonneg hCa (sq_nonneg r))
      _ = Ca * (20 + CL) * r ^ 3 := by ring
      _ ≤ Ca * (20 + CL) * r ^ 2 :=
          mul_le_mul_of_nonneg_left h32 (mul_nonneg hCa (by linarith [hCLpos.le]))
  have t4 : ‖(B τ + 1) * (-16 * e + ES)‖ ≤ Cb * (16 + CS) * r ^ 2 := by
    rw [norm_mul]
    have hv : ‖-16 * e + ES‖ ≤ (16 + CS) * r := by
      have h16 : ‖(-16 : ℂ) * e‖ = 16 * r := by
        have heq : (-16 : ℂ) * e = -((16 : ℂ) * e) := by ring
        rw [heq, norm_neg, norm_mul, Complex.norm_ofNat, ← hr]
      have hsum1 := norm_add_le ((-16 : ℂ) * e) ES
      linarith [hsum1, h16, hCSr1, hESb']
    calc ‖B τ + 1‖ * ‖-16 * e + ES‖ ≤ (Cb * r) * ((16 + CS) * r) :=
          mul_le_mul hBτ' hv (norm_nonneg _) (mul_nonneg hCb hr0)
      _ = Cb * (16 + CS) * r ^ 2 := by ring
  have hmain : ‖A τ * ℓ.L τ + B τ * ℓ.L_S τ - 2 * Λ‖
      ≤ ((Real.pi + 4) * Ca * Work.Kernels.scale τ
          + (24 + 16 * Cb + (20 + CL) * Ca + 2 * CL + CS + Cb * CS)) * r ^ 2 := by
    rw [hkey]
    have h1 := norm_add_le ((A τ - 2) * Λ + (24 * e ^ 2 + 2 * ER - ES)
        + (A τ - 2) * (-8 * e + 12 * e ^ 2 + ER)) ((B τ + 1) * (-16 * e + ES))
    have h2 := norm_add_le ((A τ - 2) * Λ + (24 * e ^ 2 + 2 * ER - ES))
        ((A τ - 2) * (-8 * e + 12 * e ^ 2 + ER))
    have h3 := norm_add_le ((A τ - 2) * Λ) ((24 * e ^ 2 + 2 * ER - ES))
    linarith [h1, h2, h3, t1, t2, t3, t4]
  have hqn : ‖Work.Kernels.qParamFun τ‖ = r ^ 2 := by
    rw [show Work.Kernels.qParamFun τ = Work.Asymptotics.nomeE τ ^ 2 from
        Work.Asymptotics.nomeE_sq τ, norm_pow, hr]
  rw [hqn]
  have hKS : (Real.pi + 4) * Ca * Work.Kernels.scale τ
        + (24 + 16 * Cb + (20 + CL) * Ca + 2 * CL + CS + Cb * CS)
      ≤ ((Real.pi + 4) * Ca + (24 + 16 * Cb + (20 + CL) * Ca + 2 * CL + CS + Cb * CS) + 1)
        * Work.Kernels.scale τ := by
    have hK' : (0 : ℝ) ≤ 24 + 16 * Cb + (20 + CL) * Ca + 2 * CL + CS + Cb * CS := by
      have h3 : (0 : ℝ) ≤ CL := hCLpos.le
      have h4 : (0 : ℝ) ≤ CS := hCSpos.le
      positivity
    have hmul : (24 + 16 * Cb + (20 + CL) * Ca + 2 * CL + CS + Cb * CS)
        ≤ (24 + 16 * Cb + (20 + CL) * Ca + 2 * CL + CS + Cb * CS) * Work.Kernels.scale τ := by
      have := mul_le_mul_of_nonneg_left hscale1 hK'
      simpa using this
    nlinarith [hmul, hscale1]
  calc ‖A τ * ℓ.L τ + B τ * ℓ.L_S τ - 2 * Λ‖
      ≤ ((Real.pi + 4) * Ca * Work.Kernels.scale τ
          + (24 + 16 * Cb + (20 + CL) * Ca + 2 * CL + CS + Cb * CS)) * r ^ 2 := hmain
    _ ≤ (((Real.pi + 4) * Ca + (24 + 16 * Cb + (20 + CL) * Ca + 2 * CL + CS + Cb * CS) + 1)
          * Work.Kernels.scale τ) * r ^ 2 :=
        mul_le_mul_of_nonneg_right hKS (sq_nonneg r)
    _ = ((Real.pi + 4) * Ca + (24 + 16 * Cb + (20 + CL) * Ca + 2 * CL + CS + Cb * CS) + 1)
          * (Work.Kernels.scale τ) ^ (1 : ℝ) * r ^ 2 := by rw [Real.rpow_one]

/-! ## The individual first-order statements -/

theorem psi_individual_first_order (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ τ : UpperHalfPlane, Work.Asymptotics.Funnel τ →
      ‖Work.Kernels.psi2 ℓ τ - 2 * ((Real.pi : ℂ) * Complex.I * (τ : ℂ)
          + Work.Asymptotics.Compact.cuspC ℓ)‖
        ≤ C * (Work.Kernels.scale τ) ^ N * ‖Work.Kernels.qParamFun τ‖ ∧
      ‖Work.Kernels.psi4 ℓ τ - 2 * ((Real.pi : ℂ) * Complex.I * (τ : ℂ)
          + Work.Asymptotics.Compact.cuspC ℓ)‖
        ≤ C * (Work.Kernels.scale τ) ^ N * ‖Work.Kernels.qParamFun τ‖ := by
  obtain ⟨C1, hC1, h1⟩ := psi_shift_bound ℓ Work.Kernels.xi2Fun
    xi2SlashFun 30000 30000
    xi2Fun_sub_two_bound
    (fun τ hτ => by
      rw [show xi2SlashFun τ = -(Work.Kernels.UFun τ + Work.Kernels.VFun τ) from rfl,
        ← Work.Kernels.KernelFacts.xi2Fun_slash_S τ]
      exact xi2S_add_one_bound τ hτ)
    (by norm_num) (by norm_num)
  obtain ⟨C2, hC2, h2⟩ := psi_shift_bound ℓ Work.Kernels.xi4Fun
    xi4SlashFun 100000000000 100000000000
    xi4Fun_sub_two_bound
    (fun τ hτ => by
      rw [show xi4SlashFun τ
          = Work.Kernels.UFun τ ^ 2 + Work.Kernels.VFun τ ^ 2 - 2 * Work.Kernels.WFun τ ^ 2
        from rfl,
        ← Work.Kernels.KernelFacts.xi4S_apply τ]
      exact xi4S_add_one_bound τ hτ)
    (by norm_num) (by norm_num)
  refine ⟨max C1 C2 + 1, 1, by positivity, by norm_num, fun τ hτ => ?_⟩
  set Λ : ℂ := (Real.pi : ℂ) * Complex.I * (τ : ℂ) + Work.Asymptotics.Compact.cuspC ℓ with hΛ
  set q : ℂ := Work.Kernels.qParamFun τ with hq
  have hC1le : C1 ≤ max C1 C2 + 1 := by linarith [le_max_left C1 C2]
  have hC2le : C2 ≤ max C1 C2 + 1 := by linarith [le_max_right C1 C2]
  constructor
  · have h := h1 τ hτ
    rw [← hΛ, ← hq] at h
    have heq : Work.Kernels.psi2 ℓ τ
        = Work.Kernels.xi2Fun τ * ℓ.L τ + xi2SlashFun τ * ℓ.L_S τ := by
      show Work.Kernels.psi2 ℓ τ = Work.Kernels.xi2Fun τ * ℓ.L τ
        + (-(Work.Kernels.UFun τ + Work.Kernels.VFun τ)) * ℓ.L_S τ
      rw [Work.Kernels.psi2, Work.Kernels.KernelFacts.xi2Fun_slash_S τ]
    have h3 : (0 : ℝ) ≤ (Work.Kernels.scale τ) ^ (1 : ℝ) :=
      Real.rpow_nonneg (le_of_lt (Work.Kernels.scale_pos τ)) 1
    have h4 : (0 : ℝ) ≤ ‖q‖ := norm_nonneg q
    have h6 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC1le h3) h4
    calc ‖Work.Kernels.psi2 ℓ τ - 2 * Λ‖
        ≤ C1 * (Work.Kernels.scale τ) ^ (1 : ℝ) * ‖q‖ := by rw [heq]; exact h
      _ ≤ (max C1 C2 + 1) * (Work.Kernels.scale τ) ^ (1 : ℝ) * ‖q‖ := by linarith [h6]
  · have h := h2 τ hτ
    rw [← hΛ, ← hq] at h
    have heq : Work.Kernels.psi4 ℓ τ
        = Work.Kernels.xi4Fun τ * ℓ.L τ + xi4SlashFun τ * ℓ.L_S τ := by
      show Work.Kernels.psi4 ℓ τ = Work.Kernels.xi4Fun τ * ℓ.L τ
        + (Work.Kernels.UFun τ ^ 2 + Work.Kernels.VFun τ ^ 2 - 2 * Work.Kernels.WFun τ ^ 2)
            * ℓ.L_S τ
      rw [Work.Kernels.psi4, Work.Kernels.KernelFacts.xi4S_apply τ]
    have h3 : (0 : ℝ) ≤ (Work.Kernels.scale τ) ^ (1 : ℝ) :=
      Real.rpow_nonneg (le_of_lt (Work.Kernels.scale_pos τ)) 1
    have h4 : (0 : ℝ) ≤ ‖q‖ := norm_nonneg q
    have h6 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC2le h3) h4
    calc ‖Work.Kernels.psi4 ℓ τ - 2 * Λ‖
        ≤ C2 * (Work.Kernels.scale τ) ^ (1 : ℝ) * ‖q‖ := by rw [heq]; exact h
      _ ≤ (max C1 C2 + 1) * (Work.Kernels.scale τ) ^ (1 : ℝ) * ‖q‖ := by linarith [h6]

end

end Work.Asymptotics.KhatE1Core
