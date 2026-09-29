/-
# Vanishing of a continuous `1`-periodic function with vanishing Fourier coefficients

If `f : ℝ → ℂ` is continuous and `1`-periodic and all of its Fourier coefficients
`cF f n` (integrals over one period against the characters `chr (-n)`) vanish, then `f = 0`.

The proof lifts `f` to a continuous function `g` on the circle `AddCircle 1`
(`AddCircle.liftIco 1 0 f`, continuous by `AddCircle.liftIco_zero_continuous`), whose
Fourier coefficients are exactly the `cF f n` (`cF_eq_fourierCoeff`).  They are all zero, so
the Fourier series of `g` is summable and converges pointwise to `g`
(`has_pointwise_sum_fourier_series_of_summable`); the series has all terms zero, hence `g = 0`.
Undoing the lift (`liftIco_coe_eq`) gives `f = 0`.
-/
import Mathlib
import Submission.Work.TMPuig.FourierAux

open MeasureTheory intervalIntegral
open scoped Real

noncomputable section

namespace Work.TMPuig

/-- A continuous `1`-periodic function all of whose Fourier coefficients vanish is identically
zero. -/
theorem dual_cF_vanishing {f : ℝ → ℂ} (hf : Continuous f) (hfp : ∀ x, f (x + 1) = f x)
    (h : ∀ n : ℤ, cF f n = 0) : ∀ x, f x = 0 := by
  -- `f 0 = f 1`, so `f` lifts to the circle.
  have hf0 : f 0 = f 1 := by simpa using (hfp 0).symm
  have hcont : Continuous (AddCircle.liftIco (1 : ℝ) 0 f) :=
    AddCircle.liftIco_zero_continuous (p := (1 : ℝ)) hf0 hf.continuousOn
  let g : C(AddCircle (1 : ℝ), ℂ) := ⟨AddCircle.liftIco (1 : ℝ) 0 f, hcont⟩
  -- The Fourier coefficients of the lift `g` are the `cF f n`, hence all vanish.
  have hcoeff : ∀ n : ℤ, fourierCoeff (⇑g) n = 0 := by
    intro n
    have h1 : fourierCoeff (AddCircle.liftIco (1 : ℝ) 0 f) n = cF f n :=
      (cF_eq_fourierCoeff f n).symm
    simp only [g, ContinuousMap.coe_mk]
    rw [h1, h n]
  -- So the Fourier series of `g` is summable (all coefficients vanish).
  have hsum : Summable (fourierCoeff (⇑g)) := by
    rw [show fourierCoeff (⇑g) = fun _ => 0 from funext hcoeff]
    exact summable_zero
  intro x
  -- Pointwise convergence of the (zero) Fourier series gives `g = 0`.
  have hpt := has_pointwise_sum_fourier_series_of_summable (f := g) hsum
    (x : AddCircle (1 : ℝ))
  have hzero : (fun i => fourierCoeff (⇑g) i • (fourier i) (x : AddCircle (1 : ℝ)))
      = fun _ => 0 := by
    funext i
    rw [hcoeff i, zero_smul]
  rw [hzero] at hpt
  have hgx : g (x : AddCircle (1 : ℝ)) = 0 := hpt.unique hasSum_zero
  -- Undo the lift.
  rw [← liftIco_coe_eq hfp x]
  exact hgx

end Work.TMPuig
