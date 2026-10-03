/-
# Composition of Ionescu–Wainger multipliers at the level of the convolution kernels

The Ionescu–Wainger multiplier with symbol `iwSymbolSet A Φ` acts on sequences by convolution
with the kernel `j ↦ iwKernel (iwSymbolSet A Φ) j = fourierCoeff (iwSymbolSet A Φ) j`
(`Work.Analysis.IWMultiplier.iwConv`).

This file proves the *composition law* for these convolutions: if the symbols multiply,
`iwSymbolSet A Φ * iwSymbolSet D Ψ = iwSymbolSet D Φ`, then the corresponding convolutions
compose, `iwConv A Φ (iwConv D Ψ f) = iwConv D Φ f`, for **every bounded** sequence `f`
(no `ℓ²` hypothesis is needed — this is the `ℓ^∞` form of the functional calculus).

Two independent inputs are used.

* *Symbol-to-kernel*: since the Fourier series of `iwSymbolSet A Φ` converges pointwise to the
  symbol (`hserA`) with absolutely summable coefficients (`hkerA`), the Fourier coefficients of
  the product `iwSymbolSet A Φ · iwSymbolSet D Ψ` are the convolution of the coefficients
  (`Work.Analysis.Fourier.fourierCoeff_mul_summable_series`, applied to the `L²` symbol
  `iwSymbolSet D Ψ`, hypothesis `hmemD`).  Combined with `hsym` this gives the coefficient
  identity `iwKernel (iwSymbolSet D Φ) m = ∑'_j iwKernel (iwSymbolSet A Φ) j *
  iwKernel (iwSymbolSet D Ψ) (m - j)`.

* *Absolute convergence*: both kernels are in `ℓ¹` (`hkerA`, `hkerD`), so the double sum is
  absolutely convergent, and the two ways of summing it — `a ⋆ (b ⋆ f)` and `(a ⋆ b) ⋆ f` —
  agree (`Work.KMTPlan.A6.tsum_convAssoc`).
-/
import Mathlib
import Submission.Work.Analysis.IWMultiplier.Defs
import Submission.Work.Analysis.Fourier.fourierCoeff_mul_summable_series
import Submission.Work.KMTPlan.A6.tsum_convAssoc

namespace Work.KMTPlan.A6

open MeasureTheory in
theorem iwConv_comp_of_symbol {A D : Finset Work.Analysis.IonescuWainger.Circle}
    {Φ Ψ : Work.Analysis.IonescuWainger.Circle → ℂ}
    (hsym : Work.Analysis.IonescuWainger.iwSymbolSet A Φ
        * Work.Analysis.IonescuWainger.iwSymbolSet D Ψ
      = Work.Analysis.IonescuWainger.iwSymbolSet D Φ)
    (hkerA : Summable fun j : ℤ =>
      ‖Work.Analysis.IWMultiplier.iwKernel (Work.Analysis.IonescuWainger.iwSymbolSet A Φ) j‖)
    (hserA : ∀ ξ : Work.Analysis.IonescuWainger.Circle,
      HasSum (fun j : ℤ => Work.Analysis.IWMultiplier.iwKernel
          (Work.Analysis.IonescuWainger.iwSymbolSet A Φ) j * fourier (T := 1) j ξ)
        (Work.Analysis.IonescuWainger.iwSymbolSet A Φ ξ))
    (hmemD : MemLp (Work.Analysis.IonescuWainger.iwSymbolSet D Ψ) 2
      Work.Analysis.IonescuWainger.circleMeasure)
    (hkerD : Summable fun j : ℤ =>
      ‖Work.Analysis.IWMultiplier.iwKernel (Work.Analysis.IonescuWainger.iwSymbolSet D Ψ) j‖)
    {f : ℤ → ℂ} {B : ℝ} (hf : ∀ m : ℤ, ‖f m‖ ≤ B) :
    Work.Analysis.IWMultiplier.iwConv A Φ (Work.Analysis.IWMultiplier.iwConv D Ψ f)
      = Work.Analysis.IWMultiplier.iwConv D Φ f := by
  -- The Fourier coefficients of the product symbol: `c = a ⋆ b`.
  have hcoeff : ∀ m : ℤ,
      Work.Analysis.IWMultiplier.iwKernel (Work.Analysis.IonescuWainger.iwSymbolSet D Φ) m
        = ∑' j : ℤ, Work.Analysis.IWMultiplier.iwKernel
              (Work.Analysis.IonescuWainger.iwSymbolSet A Φ) j
            * Work.Analysis.IWMultiplier.iwKernel
              (Work.Analysis.IonescuWainger.iwSymbolSet D Ψ) (m - j) := by
    intro m
    have h := Work.Analysis.Fourier.fourierCoeff_mul_summable_series
      (a := fun j : ℤ => Work.Analysis.IWMultiplier.iwKernel
            (Work.Analysis.IonescuWainger.iwSymbolSet A Φ) j) hkerA hserA hmemD m
    rw [show (fun ξ => Work.Analysis.IonescuWainger.iwSymbolSet A Φ ξ
          * Work.Analysis.IonescuWainger.iwSymbolSet D Ψ ξ)
        = Work.Analysis.IonescuWainger.iwSymbolSet A Φ
          * Work.Analysis.IonescuWainger.iwSymbolSet D Ψ from rfl, hsym] at h
    simpa only [Work.Analysis.IWMultiplier.iwKernel] using h
  funext n
  -- The two convolutions, unfolded into iterated `tsum`s.
  have hinner : ∀ j : ℤ, Work.Analysis.IWMultiplier.iwConv D Ψ f (n - j)
      = ∑' i : ℤ, Work.Analysis.IWMultiplier.iwKernel
            (Work.Analysis.IonescuWainger.iwSymbolSet D Ψ) i * f (n - j - i) := by
    intro j
    rw [Work.Analysis.IWMultiplier.iwConv_apply]
    exact tsum_congr fun i => by rw [smul_eq_mul]
  have hL : Work.Analysis.IWMultiplier.iwConv A Φ
        (Work.Analysis.IWMultiplier.iwConv D Ψ f) n
      = ∑' j : ℤ, Work.Analysis.IWMultiplier.iwKernel
            (Work.Analysis.IonescuWainger.iwSymbolSet A Φ) j
          * (∑' i : ℤ, Work.Analysis.IWMultiplier.iwKernel
                (Work.Analysis.IonescuWainger.iwSymbolSet D Ψ) i * f (n - j - i)) := by
    rw [Work.Analysis.IWMultiplier.iwConv_apply]
    exact tsum_congr fun j => by rw [hinner j, smul_eq_mul]
  have hR : Work.Analysis.IWMultiplier.iwConv D Φ f n
      = ∑' m : ℤ, Work.Analysis.IWMultiplier.iwKernel
            (Work.Analysis.IonescuWainger.iwSymbolSet D Φ) m * f (n - m) := by
    rw [Work.Analysis.IWMultiplier.iwConv_apply]
    exact tsum_congr fun m => by rw [smul_eq_mul]
  rw [hL, hR]
  exact tsum_convAssoc hcoeff hkerA hkerD hf n

end Work.KMTPlan.A6
