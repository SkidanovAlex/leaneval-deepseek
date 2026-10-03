import Mathlib
import Submission.Work.KMTAreas.iw_family
import Submission.Work.BourgainPlan.IonescuWainger.opArc_eq_tsum_kernel

/-!
# The arc multiplier `opArc` is the Ionescu–Wainger convolution `iwConv`

This file identifies the two implementations of the Ionescu–Wainger multiplier that occur in the
workspace:

* `Work.BourgainPlan.IonescuWainger.opArc ψ hψ E f hf` — Tao's multiplier with symbol
  `Σ_{β ∈ E} ψ(· - β)`, defined through the `ℓ²(ℤ) ≅ L²(𝕋)` dictionary (`opMul` /
  `fourierBasis.repr`);
* `Work.Analysis.IWMultiplier.iwConv E ψ f` — the same multiplier, realised as the convolution
  with the Fourier coefficients of `iwSymbolSet E ψ` (the definition used throughout the
  `IWMultiplier` chapter).

The two symbols are the same function (`iwSymbolSet` and `arcSymbol` are both
`ξ ↦ ∑_{β ∈ E} ψ (ξ - β)`), and `iwKernel` is by definition `fourierCoeff`, so the identity is the
convolution identity for the arc multiplier together with a reindexing of the sum.

## Contents

* `iwKernel_iwSymbolSet_eq` — the Fourier coefficients of `iwSymbolSet E ψ` are the coefficients of
  `ψ` modulated by `∑_{β ∈ E} star (fourier j β)` (from `integral_arcSymbol_mul_fourier`);
* `tsum_comp_sub_left` — reindexing `∑'_j g j = ∑'_k g (n - k)`;
* `opArc_eq_iwConv` — the identification.
-/

open MeasureTheory
open scoped BigOperators ENNReal

set_option autoImplicit false

namespace Work.KMTAreas

/-- The Fourier coefficients of the Ionescu–Wainger symbol `iwSymbolSet E ψ = Σ_{β ∈ E} ψ(· - β)`:
they factor as the coefficients of `ψ` modulated by the characters of the arc points,
`iwKernel (iwSymbolSet E ψ) j = (∑_{β ∈ E} star (fourier j β)) · iwKernel ψ j`.

This is `integral_arcSymbol_mul_fourier` (`arcSymbol` and `iwSymbolSet` are the same function, and
`iwKernel` is `fourierCoeff`). -/
theorem iwKernel_iwSymbolSet_eq (ψ : Work.BourgainPlan.IonescuWainger.Circle → ℂ)
    (hψ : MemLp ψ ⊤ (AddCircle.haarAddCircle (T := 1))) {K : ℤ → ℂ}
    (hK : ∀ m : ℤ, ∫ ξ : Work.BourgainPlan.IonescuWainger.Circle,
        ψ ξ * star (fourier m ξ) ∂(AddCircle.haarAddCircle (T := 1)) = K m)
    (E : Finset Work.BourgainPlan.IonescuWainger.Circle) (m : ℤ) :
    Work.Analysis.IWMultiplier.iwKernel (Work.Analysis.IonescuWainger.iwSymbolSet E ψ) m
      = (∑ β ∈ E, star (fourier m β)) * K m := by
  rw [Work.Analysis.IWMultiplier.iwKernel, fourierCoeff]
  have h : (∫ t : Work.BourgainPlan.IonescuWainger.Circle,
        fourier (-m) t • Work.Analysis.IonescuWainger.iwSymbolSet E ψ t
          ∂(AddCircle.haarAddCircle (T := 1)))
      = ∫ t : Work.BourgainPlan.IonescuWainger.Circle,
          Work.BourgainPlan.IonescuWainger.arcSymbol ψ E t * star (fourier m t)
            ∂(AddCircle.haarAddCircle (T := 1)) := by
    refine integral_congr_ae ?_
    filter_upwards with t
    simp only [Work.Analysis.IonescuWainger.iwSymbolSet,
      Work.BourgainPlan.IonescuWainger.arcSymbol,
      Work.BourgainPlan.IonescuWainger.arcTranslate]
    rw [fourier_neg, smul_eq_mul, mul_comm, Complex.star_def]
  rw [h]
  exact Work.BourgainPlan.IonescuWainger.integral_arcSymbol_mul_fourier ψ hψ hK E m

/-- Reindexing of an infinite sum over `ℤ` by the involution `k ↦ n - k`. -/
theorem tsum_comp_sub_left (g : ℤ → ℂ) (n : ℤ) : (∑' k : ℤ, g (n - k)) = ∑' j : ℤ, g j := by
  have h := Equiv.tsum_eq (Equiv.subLeft n) g
  simpa using h

/-- **The arc multiplier `opArc` is the Ionescu–Wainger convolution `iwConv`.**

Both are the Fourier multiplier with symbol `Σ_{β ∈ E} ψ(· - β)`: `opArc` is defined as such via
the `ℓ² ≅ L²` dictionary, while `iwConv` is the convolution with the Fourier coefficients of
`iwSymbolSet E ψ`, which the same symbol.  The proof combines the convolution identity
`opArc_eq_tsum_kernel` with the coefficient factorisation `iwKernel_iwSymbolSet_eq` and the
reindexing `tsum_comp_sub_left`. -/
theorem opArc_eq_iwConv (ψ : Work.BourgainPlan.IonescuWainger.Circle → ℂ)
    (hψ : MeasureTheory.MemLp ψ ⊤ (AddCircle.haarAddCircle (T := 1)))
    (E : Finset Work.BourgainPlan.IonescuWainger.Circle) (f : ℤ → ℂ) (hf : Memℓp f 2) (n : ℤ) :
    Work.BourgainPlan.IonescuWainger.opArc ψ hψ E f hf n
      = Work.Analysis.IWMultiplier.iwConv E ψ f n := by
  have hstep : (∑' j : ℤ, Work.Analysis.IWMultiplier.iwKernel
        (Work.Analysis.IonescuWainger.iwSymbolSet E ψ) j • f (n - j))
      = ∑' k : ℤ, f k * ((∑ β ∈ E, star (fourier (n - k) β))
          * (∫ ξ : Work.BourgainPlan.IonescuWainger.Circle,
              ψ ξ * star (fourier (n - k) ξ) ∂(AddCircle.haarAddCircle (T := 1)))) := by
    have h1 : (∑' j : ℤ, Work.Analysis.IWMultiplier.iwKernel
          (Work.Analysis.IonescuWainger.iwSymbolSet E ψ) j • f (n - j))
        = ∑' j : ℤ, ((∑ β ∈ E, star (fourier j β))
            * (∫ ξ : Work.BourgainPlan.IonescuWainger.Circle,
                ψ ξ * star (fourier j ξ) ∂(AddCircle.haarAddCircle (T := 1)))) * f (n - j) := by
      refine tsum_congr fun j => ?_
      rw [iwKernel_iwSymbolSet_eq ψ hψ (fun m => rfl) E j, smul_eq_mul]
    rw [h1, ← tsum_comp_sub_left (fun j => ((∑ β ∈ E, star (fourier j β))
            * (∫ ξ : Work.BourgainPlan.IonescuWainger.Circle,
                ψ ξ * star (fourier j ξ) ∂(AddCircle.haarAddCircle (T := 1)))) * f (n - j)) n]
    refine tsum_congr fun k => ?_
    simp only [sub_sub_cancel]
    ring
  rw [Work.BourgainPlan.IonescuWainger.opArc_eq_tsum_kernel ψ hψ (fun m => rfl) E f hf n,
      Work.Analysis.IWMultiplier.iwConv_apply, hstep]

end Work.KMTAreas
