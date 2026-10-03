/-
Copyright (c) 2026 The AnnalsChallenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AnnalsChallenge team
-/
import Mathlib
import Submission.Work.Analysis.IWMultiplier.iwConv_eq_iwOpSet

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators ENNReal NNReal FourierTransform

open MeasureTheory

namespace Work.KMTAreas.A4

open Work.Analysis.IonescuWainger

/-! ## Two elementary identities about the Fourier transform on `ℤ`

The multiplier `T_σ` on `ℓ²(ℤ)` is, by definition, the conjugate of the multiplication operator
with the symbol under the Fourier isomorphism `𝓕_ℤ : ℓ²(ℤ) ≃ L²(ℝ/ℤ)`.  To compute its action we
use the two identities below:

* `fourierZ_symm_apply_inner` — the `n`-th value of `𝓕_ℤ⁻¹ g` is the `L²` scalar product
  `⟪e_n, g⟫` with the `n`-th character `e_n`;
* `inner_fourierLp_lpSMul` — `⟪e_n, m · e_k⟫ = m̂(n - k)` for a bounded symbol `m`. -/

/-- The `n`-th value of the (inverse) Fourier transform on `ℤ` is the `L²` inner product
against the `n`-th character: `(𝓕_ℤ⁻¹ g) n = ⟪e_n, g⟫`. -/
theorem fourierZ_symm_apply_inner (g : Lp ℂ 2 circleMeasure) (n : ℤ) :
    (fourierZ.symm g) n = inner ℂ (fourierLp (T := 1) 2 n) g := by
  have h : fourierZ.symm = (fourierBasis (T := 1)).repr := rfl
  rw [h, HilbertBasis.repr_apply_apply, coe_fourierBasis]

/-- The `L²` scalar product of the `n`-th character with the product of an `L^∞` symbol `m` and
the `k`-th character is the `(n - k)`-th Fourier coefficient of `m`: `⟪e_n, m · e_k⟫ = m̂(n-k)`. -/
theorem inner_fourierLp_lpSMul {m : Work.Analysis.IonescuWainger.Circle → ℂ} (hm : MemLp m ⊤ circleMeasure) (n k : ℤ) :
    inner ℂ (fourierLp (T := 1) 2 n) (hm.toLp m • fourierLp (T := 1) 2 k)
      = fourierCoeff m (n - k) := by
  rw [MeasureTheory.L2.inner_def]
  rw [fourierCoeff]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_fourierLp (T := 1) 2 n,
    Lp.coeFn_lpSMul (p := ⊤) (q := 2) (r := 2) (hm.toLp m) (fourierLp (T := 1) 2 k),
    MemLp.coeFn_toLp hm, coeFn_fourierLp (T := 1) 2 k] with ξ h1 h2 h3 h4
  simp only [h1, h2, RCLike.inner_apply']
  simp only [Pi.mul_apply, h3, h4, smul_eq_mul]
  rw [← fourier_neg (T := 1) (n := n) (x := ξ)]
  rw [show (fourier (T := 1) (-n)) ξ * (m ξ * (fourier (T := 1) k) ξ)
    = ((fourier (T := 1) (-n)) ξ * (fourier (T := 1) k) ξ) * m ξ by ring,
  ← fourier_add (T := 1) (m := -n) (n := k) (x := ξ),
  show -n + k = -(n - k) by ring]

/-- **The Ionescu–Wainger Fourier multiplier on `ℓ²(ℤ)` acts by convolution with the
Fourier coefficients of its symbol.**  For a bounded measurable symbol `σ` on the circle and any
`ℓ²` sequence `F`, the `n`-th value of the multiplier `T_σ` is the convolution
`∑_j (fourierCoeff σ j) · F(n - j)`.  (`iwKernel σ j` is by definition `fourierCoeff σ j`.)
The case of finitely supported `F` is `Work.Analysis.IWMultiplier.iwConv_eq_iwOpSet` (applied
with the singleton family `{0}`, for which `iwSymbolSet {0} σ = σ`). -/
theorem multiplierConv {σ : Work.Analysis.IonescuWainger.Circle → ℂ}
    (hσ : MeasureTheory.MemLp σ ⊤ Work.Analysis.IonescuWainger.circleMeasure)
    (F : Work.Analysis.IonescuWainger.L2Z) (n : ℤ) :
    Work.Analysis.IonescuWainger.multiplierOf σ hσ F n
      = ∑' j : ℤ, Work.Analysis.IWMultiplier.iwKernel σ j * F (n - j) := by
  -- On the Fourier side the multiplier is multiplication by `σ`, so the `n`-th value is the
  -- `L²` inner product `⟪e_n, σ · 𝓕_ℤ F⟫`.
  have hLHS : multiplierOf σ hσ F n
      = inner ℂ (fourierLp (T := 1) 2 n) (hσ.toLp σ • fourierZ F) := by
    rw [show multiplierOf σ hσ F = fourierZ.symm (hσ.toLp σ • fourierZ F) from rfl]
    exact fourierZ_symm_apply_inner _ n
  -- `𝓕_ℤ F = ∑_k F k • e_k` in `L²`, and multiplication by `σ` is continuous linear, so
  -- `σ · 𝓕_ℤ F = ∑_k F k • (σ · e_k)`.
  have hmul : HasSum (fun k : ℤ => F k • (hσ.toLp σ • fourierLp (T := 1) 2 k))
      (hσ.toLp σ • fourierZ F) := by
    have h := ContinuousLinearMap.hasSum (circleMulOp (hσ.toLp σ)) (fourierZ_hasSum F)
    simpa [circleMulOp_apply] using h
  have hs := ContinuousLinearMap.hasSum (innerSL ℂ (fourierLp (T := 1) 2 n)) hmul
  rw [hLHS]
  change (innerSL ℂ (fourierLp (T := 1) 2 n)) (hσ.toLp σ • fourierZ F) = _
  rw [hs.tsum_eq.symm]
  -- each summand is `F k` times the `(n - k)`-th Fourier coefficient of `σ`
  have hterm : ∀ k : ℤ, (innerSL ℂ (fourierLp (T := 1) 2 n))
      (F k • (hσ.toLp σ • fourierLp (T := 1) 2 k)) = F k * fourierCoeff σ (n - k) := by
    intro k
    rw [ContinuousLinearMap.map_smul, innerSL_apply_apply, inner_fourierLp_lpSMul hσ n k,
      smul_eq_mul]
  rw [tsum_congr hterm]
  -- reindex `k ↦ n - k` (an involution of `ℤ`)
  have hreindex : (∑' j : ℤ, (F (n - j) : ℂ) * fourierCoeff σ j)
      = ∑' k : ℤ, (F k : ℂ) * fourierCoeff σ (n - k) := by
    have hbij : Function.Bijective (fun k : ℤ => n - k) :=
      Function.Involutive.bijective (fun k => by ring)
    have he := Equiv.tsum_eq (Equiv.ofBijective (fun k : ℤ => n - k) hbij)
      (fun j : ℤ => (F (n - j) : ℂ) * fourierCoeff σ j)
    simpa [Equiv.coe_ofBijective] using he.symm
  rw [← hreindex]
  exact tsum_congr (fun j => by rw [Work.Analysis.IWMultiplier.iwKernel, mul_comm])

end Work.KMTAreas.A4
