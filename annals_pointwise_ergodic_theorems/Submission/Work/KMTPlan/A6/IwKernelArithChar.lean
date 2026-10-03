/-
# The arithmetic-character identity for the Ionescu–Wainger kernel

This file proves the identity requested by area A6: for a finite set `A ⊆ ℝ/ℤ` of arithmetic
frequencies, an integrable symbol `φ : ℝ → ℂ` and an integer frequency `j`, the `j`-th Fourier
coefficient of the Ionescu–Wainger symbol `∑_{α ∈ A} (periodize φ)(· − α)` factors as the
arithmetic character sum `∑_{α ∈ A} e(−jα)` times the *continuous* Fourier transform
`cw φ j = ∫ φ θ e(−jθ) dθ` of `φ`:

`iwKernel (iwSymbolSet A (periodize φ)) j = (∑ α ∈ A, fourier (-j) α) * cw φ j`.

The mathematical content is the usual "unfolding"/de Leeuw transfer: the Fourier coefficients on
`ℝ/ℤ` of the periodisation of `φ` are the Fourier transform of `φ` on `ℝ`, and a shift
`ξ ↦ Φ(ξ − α)` of the symbol multiplies the coefficients by the character `fourier (-j) α`.

The proof is assembled here from two measure-theoretic facts about the periodisation, stated as
hypotheses `hInt`/`hFold` of the auxiliary lemma `iwKernelArithChar_aux`:

* `Integrable (periodize φ)` (`Work.KMTPlan.A6.IntegrablePeriodize`), needed to pull the finite
  sum `∑_{α ∈ A}` out of the defining integral of `fourierCoeff`;
* `∫ t, periodize φ t * X t = ∫ x, φ x * X (x : ℝ/ℤ)` for continuous `X`
  (`Work.KMTPlan.A6.PeriodizeFold`), needed to identify `fourierCoeff (periodize φ) j` with
  `cw φ j`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.Large.Defs
import Submission.Work.KMTPlan.A6.IntegrablePeriodize
import Submission.Work.KMTPlan.A6.PeriodizeFold

set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6

open MeasureTheory
open scoped BigOperators
open Work.Analysis.IonescuWainger

local notation "Circ" => Work.Analysis.IonescuWainger.Circle

/-- **The arithmetic-character identity, with the two periodisation facts as hypotheses.**

`hInt` is the `L¹`-integrability of the periodisation of `φ`, `hFold` is the identity
`∫ t, periodize φ t * X t = ∫ x, φ x * X (x : ℝ/ℤ)` for continuous `X`. -/
private theorem iwKernelArithChar_aux (A : Finset Circ) {φ : ℝ → ℂ} (j : ℤ)
    (hInt : Integrable (periodize φ) circleMeasure)
    (hFold : ∀ (X : Circ → ℂ), Continuous X →
      ∫ t : Circ, periodize φ t * X t ∂circleMeasure
        = ∫ x : ℝ, φ x * X ((x : ℝ) : Circ)) :
    Work.Analysis.IWMultiplier.iwKernel (iwSymbolSet A (periodize φ)) j
      = (∑ α ∈ A, fourier (T := 1) (-j) α) * Work.KMTAreas.A7.cw φ j := by
  -- Each summand of the symbol is integrable against the character `fourier (-j)`.
  have hterm : ∀ α ∈ A, Integrable
      (fun t : Circ => fourier (T := 1) (-j) t * periodize φ (t - α)) circleMeasure := by
    intro α _
    refine (hInt.comp_sub_right α).bdd_mul (c := 1)
      (fourier (T := 1) (-j)).continuous.aestronglyMeasurable ?_
    filter_upwards with t
    rw [fourier_apply]
    exact le_of_eq (Circle.norm_coe _)
  -- Additivity of the character in its argument.
  have hfourier_add : ∀ (s α : Circ), fourier (T := 1) (-j) (s + α)
      = fourier (T := 1) (-j) s * fourier (T := 1) (-j) α := by
    intro s α
    simp [fourier_apply, add_zsmul, AddCircle.toCircle_add, Circle.coe_mul]
  -- The Fourier coefficient of the periodisation is the continuous Fourier transform of `φ`.
  have hcw : fourierCoeff (periodize φ) j = Work.KMTAreas.A7.cw φ j := by
    have h1 : fourierCoeff (periodize φ) j
        = ∫ t : Circ, periodize φ t * fourier (T := 1) (-j) t ∂circleMeasure := by
      rw [fourierCoeff]
      refine integral_congr_ae ?_
      filter_upwards with t
      simp only [smul_eq_mul, mul_comm]
    rw [h1, hFold (fourier (T := 1) (-j)) (fourier (T := 1) (-j)).continuous]
    simp only [Work.KMTAreas.A7.cw]
    refine integral_congr_ae ?_
    filter_upwards with x
    -- `fourier (-j) (x : ℝ/ℤ) = e(-jx)`
    congr 1
    rw [fourier_coe_apply]
    norm_num [Work.KMTAreas.A7.ee]
    ring_nf
  -- Translating the symbol by `α` multiplies the coefficient by `fourier (-j) α`.
  have hshift : ∀ α : Circ,
      ∫ t : Circ, fourier (T := 1) (-j) t * periodize φ (t - α) ∂circleMeasure
        = fourier (T := 1) (-j) α * fourierCoeff (periodize φ) j := by
    intro α
    have hEq : (∫ t : Circ, fourier (T := 1) (-j) t * periodize φ (t - α) ∂circleMeasure)
        = ∫ s : Circ, fourier (T := 1) (-j) (s + α) * periodize φ s ∂circleMeasure := by
      rw [← integral_add_right_eq_self
        (fun t : Circ => fourier (T := 1) (-j) t * periodize φ (t - α)) α]
      refine integral_congr_ae ?_
      filter_upwards with s
      simp only [add_sub_cancel_right]
    rw [hEq]
    have hstep : (∫ s : Circ, fourier (T := 1) (-j) (s + α) * periodize φ s ∂circleMeasure)
        = ∫ s : Circ, fourier (T := 1) (-j) α
            * (fourier (T := 1) (-j) s * periodize φ s) ∂circleMeasure := by
      refine integral_congr_ae ?_
      filter_upwards with s
      rw [hfourier_add s α]
      ring
    rw [hstep, integral_const_mul]
    congr 1
  calc Work.Analysis.IWMultiplier.iwKernel (iwSymbolSet A (periodize φ)) j
      = fourierCoeff (fun ξ : Circ => ∑ α ∈ A, periodize φ (ξ - α)) j := by
        rw [Work.Analysis.IWMultiplier.iwKernel]; rfl
    _ = ∫ t : Circ,
          fourier (T := 1) (-j) t • (∑ α ∈ A, periodize φ (t - α)) ∂circleMeasure := rfl
    _ = ∫ t : Circ,
          ∑ α ∈ A, fourier (T := 1) (-j) t * periodize φ (t - α) ∂circleMeasure := by
        refine integral_congr_ae ?_
        filter_upwards with t
        rw [smul_eq_mul, Finset.mul_sum]
    _ = ∑ α ∈ A,
          ∫ t : Circ, fourier (T := 1) (-j) t * periodize φ (t - α) ∂circleMeasure :=
        integral_finsetSum _ hterm
    _ = ∑ α ∈ A, fourier (T := 1) (-j) α * fourierCoeff (periodize φ) j :=
        Finset.sum_congr rfl fun α _ => hshift α
    _ = (∑ α ∈ A, fourier (T := 1) (-j) α) * Work.KMTAreas.A7.cw φ j := by
        rw [Finset.sum_mul, hcw]

theorem IwKernelArithChar (A : Finset Work.Analysis.IonescuWainger.Circle)
    {φ : ℝ → ℂ} (hφ : MeasureTheory.Integrable φ) (j : ℤ) :
    Work.Analysis.IWMultiplier.iwKernel
        (Work.Analysis.IonescuWainger.iwSymbolSet A (Work.Analysis.IonescuWainger.periodize φ)) j
      = (∑ α ∈ A, fourier (T := 1) (-j) α) * Work.KMTAreas.A7.cw φ j := by
  exact iwKernelArithChar_aux A j (IntegrablePeriodize hφ) (fun X hX => PeriodizeFold hφ hX)

end Work.KMTPlan.A6
