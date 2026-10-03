import Mathlib
import Submission.Work.Analysis.IWMultiplier.Defs

/-!
# The Ionescu–Wainger multiplier on finitely supported sequences

The Ionescu–Wainger multiplier on `ℓ²(ℤ)` with symbol `m = iwSymbolSet A Φ` is, by definition,
the Fourier multiplier `iwOpSet A Φ h` (`iwOpSet`), i.e. the conjugate under the Fourier
transform `𝓕_ℤ : ℓ²(ℤ) ≃ L²(ℝ/ℤ)` of multiplication by `m`.  On the other hand `iwConv A Φ f`
is the convolution of a sequence `f` with the Fourier coefficients of `m`.  The present file
identifies the two on finitely supported sequences:

`⇑(iwOpSet A Φ h F) = fun n => iwConv A Φ f n`   whenever   `⇑F = f`   is finitely supported.

The proof is the computation of the Fourier coefficients of the product `m · 𝓕_ℤ F`: since `f`
is finitely supported, `𝓕_ℤ F = ∑_{k ∈ supp f} f k • e_k` is a trigonometric polynomial, so

`(m · 𝓕_ℤ F)̂(n) = ∑_{k ∈ supp f} f k · m̂(n - k)`,

which is exactly the convolution `iwConv A Φ f n = ∑'_j m̂(j) f(n - j)`.

## Main results

* `Work.Analysis.IWMultiplier.iwConv_eq_iwOpSet` — the identification.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators ENNReal NNReal FourierTransform
open MeasureTheory

namespace Work.Analysis.IWMultiplier

open Work.Analysis.IonescuWainger

/-- The `n`-th value of the inverse Fourier transform `𝓕_ℤ⁻¹ : L²(ℝ/ℤ) → ℓ²(ℤ)` is the `n`-th
Fourier coefficient of the `L²` function: `(𝓕_ℤ⁻¹ g) n = ∫ g(ξ) e(-nξ) dξ`. -/
private lemma fourierZ_symm_apply (g : Lp ℂ 2 circleMeasure) (n : ℤ) :
    (fourierZ.symm g) n = fourierCoeff (⇑g) n := by
  have h : fourierZ.symm = (fourierBasis (T := 1)).repr := rfl
  rw [h]
  exact fourierBasis_repr g n

/-- For a finitely supported `f : ℤ → ℂ`, the convolution against the Fourier coefficients of a
symbol `m` on the circle is the finite sum `∑_{k ∈ supp f} f k · m̂(n - k)`. -/
private lemma iwConv_tsum_eq_sum (m : Circle → ℂ) (f : ℤ → ℂ)
    (hf : (Function.support f).Finite) (n : ℤ) :
    (∑' j : ℤ, fourierCoeff m j • f (n - j))
      = ∑ k ∈ hf.toFinset, f k * fourierCoeff m (n - k) := by
  rw [tsum_eq_sum (L := SummationFilter.unconditional ℤ)
    (s := hf.toFinset.image (fun k => n - k)) ?_]
  · rw [Finset.sum_image (sub_right_injective (b := n)).injOn]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [show n - (n - k) = k by ring, smul_eq_mul, mul_comm]
  · intro j hj
    have hz : f (n - j) = 0 := by
      by_contra hne
      refine hj (Finset.mem_image.mpr ⟨n - j, hf.mem_toFinset.mpr hne, ?_⟩)
      ring
    rw [hz, smul_zero]

/-- **The Fourier coefficients of the IW multiplier applied to a finitely supported sequence.**
For a bounded symbol `m ∈ L^∞(ℝ/ℤ)`, a finitely supported `f : ℤ → ℂ` realised as `F ∈ ℓ²(ℤ)`,
the `n`-th Fourier coefficient of `m · 𝓕_ℤ F` is the finite convolution
`∑_{k ∈ supp f} f k · m̂(n - k)`. -/
private lemma fourierCoeff_lpSMul_fourierZ (m : Circle → ℂ) (hm : MemLp m ⊤ circleMeasure)
    (f : ℤ → ℂ) (hf : (Function.support f).Finite) (F : L2Z) (hF : ⇑F = f) (n : ℤ) :
    fourierCoeff (⇑(hm.toLp m • fourierZ F)) n
      = ∑ k ∈ hf.toFinset, f k * fourierCoeff m (n - k) := by
  -- `𝓕_ℤ F` is the finitely supported combination `∑_{k ∈ supp f} f k • e_k`.
  have hG : fourierZ F = ∑ k ∈ hf.toFinset, f k • fourierLp (T := 1) 2 k := by
    have hg0 : ∀ k ∉ hf.toFinset, F k • fourierLp (T := 1) 2 k = 0 := by
      intro k hk
      have hk0 : f k = 0 := by
        by_contra hne
        exact hk (hf.mem_toFinset.mpr hne)
      rw [congrFun hF k, hk0, zero_smul]
    have htsum := tsum_eq_sum (L := SummationFilter.unconditional ℤ) (s := hf.toFinset) hg0
    rw [← (fourierZ_hasSum F).tsum_eq, htsum]
    exact Finset.sum_congr rfl (fun k _ => by rw [congrFun hF k])
  -- As a function, `𝓕_ℤ F` is the trigonometric polynomial `∑_k f k · e_k`.
  have hGcoe : ⇑(fourierZ F) =ᵐ[circleMeasure]
      fun ξ => ∑ k ∈ hf.toFinset, f k * fourier (T := 1) k ξ := by
    rw [hG]
    have hterm : ∀ᵐ ξ ∂circleMeasure, ∀ k ∈ hf.toFinset,
        (f k • fourierLp (T := 1) 2 k : Lp ℂ 2 circleMeasure) ξ = f k * fourier k ξ := by
      rw [Filter.eventually_all_finset]
      intro k _
      filter_upwards [Lp.coeFn_smul (f k) (fourierLp (T := 1) 2 k),
        coeFn_fourierLp (T := 1) 2 k] with ξ h1 h2
      rw [h1, Pi.smul_apply, h2, smul_eq_mul]
    filter_upwards [Lp.coeFn_fun_finsetSum (hf.toFinset)
      (fun k => f k • fourierLp (T := 1) 2 k), hterm] with ξ h1 h2
    rw [h1]
    exact Finset.sum_congr rfl (fun k hk => h2 k hk)
  -- hence `m · 𝓕_ℤ F` is a.e. the product of `m` with that polynomial.
  have hcoe : ⇑(hm.toLp m • fourierZ F) =ᵐ[circleMeasure]
      fun ξ : Circle => m ξ * ∑ k ∈ hf.toFinset, f k * fourier (T := 1) k ξ := by
    filter_upwards [Lp.coeFn_lpSMul (p := ⊤) (q := 2) (r := 2) (hm.toLp m) (fourierZ F),
      MemLp.coeFn_toLp hm, hGcoe] with ξ h1 h2 h3
    rw [h1, Pi.smul_apply', h2, h3, smul_eq_mul]
  rw [fourierCoeff_congr_ae hcoe]
  -- move the finite sum out of the integral
  have hsummand_int : ∀ k ∈ hf.toFinset,
      Integrable (fun ξ : Circle => f k * (fourier (T := 1) k ξ * m ξ)) circleMeasure := by
    intro k _
    have hm_int : Integrable m circleMeasure := hm.integrable le_top
    have hfour : MemLp (fun ξ : Circle => fourier (T := 1) k ξ) ⊤ circleMeasure := by
      refine MemLp.of_bound (by fun_prop) 1 (Filter.Eventually.of_forall fun ξ => ?_)
      rw [fourier_apply, Circle.norm_coe]
    exact (hm_int.mul_of_top_right hfour).const_mul (f k)
  have hpt : (fun ξ : Circle => m ξ * ∑ k ∈ hf.toFinset, f k * fourier (T := 1) k ξ)
      = ∑ k ∈ hf.toFinset, (fun ξ : Circle => f k * (fourier (T := 1) k ξ * m ξ)) := by
    funext ξ
    rw [Finset.sum_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  rw [hpt, fourierCoeff.sum (hf.toFinset)
    (fun k => fun ξ : Circle => f k * (fourier (T := 1) k ξ * m ξ)) hsummand_int,
    Finset.sum_apply]
  -- identify each term with the Fourier coefficient of `m` at `n - k`
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [fourierCoeff.const_mul]
  congr 1
  rw [fourierCoeff, fourierCoeff]
  apply integral_congr_ae
  filter_upwards with ξ
  rw [smul_eq_mul, smul_eq_mul]
  have h1 : fourier (T := 1) (-(n - k)) ξ
      = fourier (T := 1) (-n) ξ * fourier (T := 1) k ξ := by
    have := fourier_add (T := 1) (m := -n) (n := k) (x := ξ)
    rwa [show -n + k = -(n - k) by ring] at this
  rw [h1]; ring

/-- **The Ionescu–Wainger multiplier on finitely supported sequences is the convolution with the
kernel of its symbol.**  For a finite set `A` of frequencies on the circle, a symbol `Φ` whose IW
symbol `iwSymbolSet A Φ` is bounded, and a finitely supported sequence `f : ℤ → ℂ` realised as
`F ∈ ℓ²(ℤ)`, the IW multiplier `iwOpSet A Φ h` acts on `F` by convolution with the Fourier
coefficients of `iwSymbolSet A Φ`, i.e. `n ↦ iwConv A Φ f n`. -/
theorem iwConv_eq_iwOpSet (A : Finset IonescuWainger.Circle) (Φ : IonescuWainger.Circle → ℂ)
    (h : MeasureTheory.MemLp (IonescuWainger.iwSymbolSet A Φ) ⊤ IonescuWainger.circleMeasure)
    (f : ℤ → ℂ) (hf : (Function.support f).Finite)
    (F : IonescuWainger.L2Z) (hF : ⇑F = f) :
    ⇑(IonescuWainger.iwOpSet A Φ h F) = fun n => iwConv A Φ f n := by
  funext n
  have h1 : ⇑(iwOpSet A Φ h F) n
      = fourierCoeff (⇑(h.toLp (iwSymbolSet A Φ) • fourierZ F)) n := by
    rw [show iwOpSet A Φ h F
        = fourierZ.symm (h.toLp (iwSymbolSet A Φ) • fourierZ F) from rfl]
    exact fourierZ_symm_apply _ n
  rw [h1, fourierCoeff_lpSMul_fourierZ (iwSymbolSet A Φ) h f hf F hF n]
  rw [iwConv_apply]
  simp only [iwKernel]
  exact (iwConv_tsum_eq_sum (iwSymbolSet A Φ) f hf n).symm

end Work.Analysis.IWMultiplier
