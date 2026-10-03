/-
# The Ionescu–Wainger multiplier acts by convolution on *all* of `ℓ²(ℤ)`

`Work.Analysis.IWMultiplier.iwConv_eq_iwOpSet` identifies the two definitions of the
Ionescu–Wainger multiplier — the convolution `iwConv A Φ f` with the Fourier coefficients of the
symbol and the `L²` Fourier multiplier `iwOpSet A Φ h` — but only on *finitely supported*
sequences `f`.  The present file removes that restriction: for every `F ∈ ℓ²(ℤ)`, the sequence
`n ↦ iwConv A Φ (⇑F) n` is (equal to) the `ℓ²` function `⇑(iwOpSet A Φ h F)`.

The mathematical content is the elementary Fourier-analysis fact underlying the whole
identification: the Fourier coefficients of the product of an `L^∞` function with an `L²`
function are the convolution of the two sequences of Fourier coefficients.  Concretely, for a
bounded symbol `m` on the circle,

`fourierCoeff (⇑(m · 𝓕_ℤ F)) n = ∑'_j fourierCoeff m j · F(n - j)`,

which is proved by expanding `𝓕_ℤ F = ∑_k F(k) e_k` (a `HasSum` in `L²`), multiplying by `m`
(continuous, hence preserving `HasSum`) and applying the continuous linear functional
`g ↦ ⟪e_n, g⟫` — which is `fourierCoeff · n` — termwise.

## Main results

* `Work.KMTPlan.A6.fourierCoeff_lpSMul_fourierLp` — the Fourier coefficients of `m · e_k`;
* `Work.KMTPlan.A6.fourierCoeff_lpSMul_fourierZ_l2` — the convolution formula for the Fourier
  coefficients of `m · 𝓕_ℤ F`, for arbitrary `F ∈ ℓ²(ℤ)`;
* `Work.KMTPlan.A6.iwConvEqIwOpSetMemlp` — the identification of `iwConv` with `iwOpSet` on all
  of `ℓ²(ℤ)`.
-/
import Mathlib
import Submission.Work.Analysis.IWMultiplier.Basic

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators ENNReal NNReal FourierTransform
open MeasureTheory

namespace Work.KMTPlan.A6

open Work.Analysis.IonescuWainger

/-! ## Elementary facts about Fourier coefficients on the circle -/

/-- The `n`-th Fourier coefficient of `g ∈ L²(ℝ/ℤ)` is the inner product with the character
`e_n`; equivalently `fourierCoeff (⇑g) n = (innerSL ℂ e_n) g`, a continuous linear functional of
`g`. -/
theorem fourierCoeff_eq_innerSL (g : Lp ℂ 2 circleMeasure) (n : ℤ) :
    fourierCoeff (⇑g) n = (innerSL ℂ (fourierLp (T := 1) 2 n)) g := by
  rw [← fourierBasis_repr g n, HilbertBasis.repr_apply_apply, innerSL_apply_apply,
    congr_fun (coe_fourierBasis (T := 1)) n]

/-- **The Fourier coefficients of `m · e_k`.**  For a bounded symbol `m` on the circle, the
`n`-th Fourier coefficient of the product of `m` with the character `e_k` is the `n - k`-th
Fourier coefficient of `m`. -/
theorem fourierCoeff_lpSMul_fourierLp (M : Lp ℂ ⊤ circleMeasure) (k n : ℤ) :
    fourierCoeff (⇑(M • fourierLp (T := 1) 2 k)) n = fourierCoeff (⇑M) (n - k) := by
  have hcoe : ⇑(M • fourierLp (T := 1) 2 k) =ᵐ[circleMeasure]
      fun ξ => ⇑M ξ * fourier (T := 1) k ξ := by
    filter_upwards [Lp.coeFn_lpSMul (p := ⊤) (q := 2) (r := 2) M (fourierLp (T := 1) 2 k),
      coeFn_fourierLp (T := 1) 2 k] with ξ h1 h2
    rw [h1, Pi.smul_apply', h2, smul_eq_mul]
  rw [congrFun (fourierCoeff_congr_ae hcoe) n]
  rw [fourierCoeff, fourierCoeff]
  apply integral_congr_ae
  filter_upwards with t
  rw [smul_eq_mul, smul_eq_mul]
  have hf : fourier (T := 1) (-(n - k)) t = fourier (T := 1) (-n) t * fourier (T := 1) k t := by
    rw [show -(n - k) = -n + k by ring, fourier_add]
  rw [hf]; ring

/-- The reflection `j ↦ n - j` of the integers. -/
def reindexSub (n : ℤ) : ℤ ≃ ℤ where
  toFun j := n - j
  invFun k := n - k
  left_inv j := by ring
  right_inv k := by ring

/-- Reindexing an unconditionally convergent series over `ℤ` by the reflection `j ↦ n - j`: the
convolution `∑_j a_j · F(n - j)` equals `∑_k F(k) · a(n - k)`. -/
theorem tsum_mul_conv (a F : ℤ → ℂ) (n : ℤ) :
    ∑' j : ℤ, a j * F (n - j) = ∑' k : ℤ, F k * a (n - k) := by
  rw [← Equiv.tsum_eq (reindexSub n) (fun k => F k * a (n - k))]
  refine tsum_congr fun j => ?_
  show a j * F (n - j) = F (n - j) * a (n - (n - j))
  rw [show n - (n - j) = j by ring]
  exact mul_comm _ _

/-! ## The Fourier coefficients of `m · 𝓕_ℤ F` for arbitrary `F ∈ ℓ²(ℤ)` -/

/-- **The Fourier coefficients of a bounded symbol times the Fourier transform of an `ℓ²`
sequence.**  For `m ∈ L^∞(ℝ/ℤ)` and `F ∈ ℓ²(ℤ)`, the `n`-th Fourier coefficient of the product
`m · 𝓕_ℤ F` is the convolution `∑_j m̂(j) · F(n - j)` of the Fourier coefficients of `m` with
the sequence `F`. -/
theorem fourierCoeff_lpSMul_fourierZ_l2 {m : Work.Analysis.IonescuWainger.Circle → ℂ}
    (hm : MemLp m ⊤ circleMeasure) (F : L2Z) (n : ℤ) :
    fourierCoeff (⇑(hm.toLp m • fourierZ F)) n
      = ∑' j : ℤ, fourierCoeff m j * ⇑F (n - j) := by
  -- `𝓕_ℤ F = ∑_k F(k) e_k` as a `HasSum` in `L²`; multiplying by `m` preserves it.
  have hs1 : HasSum (fun k : ℤ => ⇑F k • (hm.toLp m • fourierLp (T := 1) 2 k))
      (hm.toLp m • fourierZ F) := by
    have h := ContinuousLinearMap.hasSum (circleMulOp (hm.toLp m)) (fourierZ_hasSum F)
    simpa only [circleMulOp_apply, Lp.smul_comm] using h
  -- apply the continuous linear functional `g ↦ ⟪e_n, g⟫` = `fourierCoeff · n`.
  have hs2 := ContinuousLinearMap.hasSum (innerSL ℂ (fourierLp (T := 1) 2 n)) hs1
  have hterm : ∀ k : ℤ, (innerSL ℂ (fourierLp (T := 1) 2 n))
        (⇑F k • (hm.toLp m • fourierLp (T := 1) 2 k))
      = ⇑F k * fourierCoeff m (n - k) := by
    intro k
    rw [innerSL_apply_apply, inner_smul_right]
    congr 1
    rw [← innerSL_apply_apply,
      ← fourierCoeff_eq_innerSL (hm.toLp m • fourierLp (T := 1) 2 k) n,
      fourierCoeff_lpSMul_fourierLp (hm.toLp m) k n,
      congrFun (fourierCoeff_congr_ae (MemLp.coeFn_toLp hm)) (n - k)]
  have hs3 : HasSum (fun k : ℤ => ⇑F k * fourierCoeff m (n - k))
      ((innerSL ℂ (fourierLp (T := 1) 2 n)) (hm.toLp m • fourierZ F)) := by
    simpa only [hterm] using hs2
  -- identify the sum with `fourierCoeff (⇑(m • 𝓕_ℤ F)) n` and reindex.
  exact (fourierCoeff_eq_innerSL (hm.toLp m • fourierZ F) n).trans
    (hs3.tsum_eq.symm.trans (tsum_mul_conv (fourierCoeff m) (⇑F) n).symm)

/-! ## The identification `iwConv = iwOpSet` on `ℓ²(ℤ)` -/

/-- The `n`-th value of the `L²` Ionescu–Wainger multiplier `iwOpSet A Φ h` is the `n`-th Fourier
coefficient of `iwSymbolSet A Φ · 𝓕_ℤ F`. -/
theorem iwOpSet_apply_eq (A : Finset Work.Analysis.IonescuWainger.Circle)
    (Φ : Work.Analysis.IonescuWainger.Circle → ℂ)
    (h : MemLp (iwSymbolSet A Φ) ⊤ circleMeasure) (F : L2Z) (n : ℤ) :
    ⇑(iwOpSet A Φ h F) n = fourierCoeff (⇑(h.toLp (iwSymbolSet A Φ) • fourierZ F)) n := by
  have hsymm : fourierZ.symm = (fourierBasis (T := 1)).repr := rfl
  have h1 : ⇑(iwOpSet A Φ h F) n
      = (fourierZ.symm (h.toLp (iwSymbolSet A Φ) • fourierZ F)) n := rfl
  rw [h1, hsymm]
  exact fourierBasis_repr _ n

/-- **The Ionescu–Wainger multiplier acts by convolution on all of `ℓ²(ℤ)`.**  For a finite set
`A` of frequencies on the circle and a symbol `Φ` whose IW symbol `iwSymbolSet A Φ` is bounded,
the IW multiplier `iwOpSet A Φ h` agrees with the convolution `iwConv A Φ` on every `F ∈ ℓ²(ℤ)`
(not only on finitely supported sequences, as in
`Work.Analysis.IWMultiplier.iwConv_eq_iwOpSet`). -/
theorem iwConvEqIwOpSetMemlp {A : Finset Work.Analysis.IonescuWainger.Circle} {Φ : Work.Analysis.IonescuWainger.Circle → ℂ} (h : MeasureTheory.MemLp (Work.Analysis.IonescuWainger.iwSymbolSet A Φ) ⊤ Work.Analysis.IonescuWainger.circleMeasure) (F : Work.Analysis.IonescuWainger.L2Z) : Work.Analysis.IWMultiplier.iwConv A Φ ⇑F = ⇑(Work.Analysis.IonescuWainger.iwOpSet A Φ h F) := by
  funext n
  have hL : Work.Analysis.IWMultiplier.iwConv A Φ (⇑F) n
      = ∑' j : ℤ, fourierCoeff (iwSymbolSet A Φ) j * ⇑F (n - j) := by
    rw [Work.Analysis.IWMultiplier.iwConv_apply]
    refine tsum_congr fun j => ?_
    rw [Work.Analysis.IWMultiplier.iwKernel, smul_eq_mul]
  rw [hL, iwOpSet_apply_eq A Φ h F n, fourierCoeff_lpSMul_fourierZ_l2 h F n]

end Work.KMTPlan.A6
