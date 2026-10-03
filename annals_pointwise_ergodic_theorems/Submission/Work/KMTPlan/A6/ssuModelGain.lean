import Mathlib
import Submission.Work.KMTPlan.A6.ArithSymbolHeightSmall
import Submission.Work.KMTPlan.A6.ssuNonAliasing
import Submission.Work.KMTPlan.A6.ssuAverageModel
import Submission.Work.KMTPlan.A6.SsuAux
import Submission.Work.KMTAreas.A7.coeff_arithSymb_mul_iwSymbol
import Submission.Work.KMTPlan.A6.eLpNorm_iwConv_two_le_of_symbol_bound
import Submission.Work.KMTPlan.A6.ssuArithFinal
import Submission.Work.KMTPlan.A6.ssuBookkeeping
import Submission.Work.KMTPlan.A6.ssuNbBound
import Submission.Work.KMTPlan.A6.ssuProjZero
import Submission.Work.KMTPlan.A6.ssuQbBound
import Submission.Work.KMTPlan.A6.ssuSep
import Submission.Work.KMTPlan.A6.ssuTmMemLp

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6

open MeasureTheory
open scoped BigOperators

/-! ## An `L¹` product rule for Fourier coefficients (the enabling identity of the band collapse)

The landed `Work.Analysis.Fourier.fourierCoeff_mul_summable_series` gives the product rule
`fourierCoeff (σ₂ * σ₁) m = ∑'_j a j * fourierCoeff σ₁ (m - j)` when `σ₂` has an *absolutely
convergent* Fourier series `∑_j a_j e_j` and `σ₁ ∈ L²(𝕋)`.  In every application to the
frequency-band collapse of the Ionescu--Wainger multipliers `Tm ρ l φ` the symbol
`σ₁ = periodize φ` is in general only in `L¹(𝕋)`: the target's hypothesis on the bump `φ` is
merely `∀ξ, φ ξ ≠ 0 → |ξ| ≤ 2^{-3u}`, i.e. `φ` is *supported*, not bounded.  The proof of the
landed lemma uses `σ₁ ∈ L²` only to obtain `Integrable σ₁`, so the same argument yields:

  `fourierCoeff (σ₂ * σ₁) m = ∑'_j a j * fourierCoeff σ₁ (m - j)`   for `σ₁ ∈ L¹(𝕋)`.

This is the enabling identity for every band computation on `Tm ρ l φ` for a merely integrable
`φ`; see `NOTES_KMTPlan_A6_ssuModelGain_SESSION.md` §3. -/
theorem fourierCoeff_mul_hasSum_memLp_one {a : ℤ → ℂ} (ha : Summable fun j : ℤ => ‖a j‖)
    {σ₂ : Work.Analysis.IonescuWainger.Circle → ℂ}
    (hσ₂ : ∀ ξ, HasSum (fun j : ℤ => a j * fourier (T := 1) j ξ) (σ₂ ξ))
    {σ₁ : Work.Analysis.IonescuWainger.Circle → ℂ}
    (hσ₁ : MeasureTheory.MemLp σ₁ 1 Work.Analysis.IonescuWainger.circleMeasure) (m : ℤ) :
    fourierCoeff (fun ξ => σ₂ ξ * σ₁ ξ) m
      = ∑' j : ℤ, a j * fourierCoeff σ₁ (m - j) := by
  have hσ₁int : Integrable σ₁ (AddCircle.haarAddCircle (T := 1)) := hσ₁.integrable (by norm_num)
  set F : ℤ → Work.Analysis.IonescuWainger.Circle → ℂ :=
    fun j ξ => fourier (T := 1) (-m) ξ • (a j * fourier (T := 1) j ξ * σ₁ ξ) with hF
  have hFpt : ∀ j ξ, F j ξ = a j * (fourier (T := 1) (j - m) ξ * σ₁ ξ) := by
    intro j ξ
    have hfa : fourier (T := 1) (-m) ξ * fourier (T := 1) j ξ = fourier (T := 1) (j - m) ξ := by
      rw [sub_eq_add_neg, fourier_add]; ring
    simp only [hF, smul_eq_mul]
    rw [← hfa]; ring
  have hfournorm : ∀ (k : ℤ) (ξ : Work.Analysis.IonescuWainger.Circle),
      ‖fourier (T := 1) k ξ‖ = 1 := by
    intro k ξ
    rw [fourier_apply, Circle.norm_coe]
  have hFint : ∀ j, Integrable (F j) (AddCircle.haarAddCircle (T := 1)) := by
    intro j
    rw [show F j = fun ξ : Work.Analysis.IonescuWainger.Circle =>
      a j * (fourier (T := 1) (j - m) ξ * σ₁ ξ) from funext (hFpt j)]
    refine Integrable.const_mul ?_ (a j)
    refine hσ₁int.bdd_mul (c := 1) (f := fun ξ => fourier (T := 1) (j - m) ξ) ?_ ?_
    · exact (fourier (T := 1) (j - m)).continuous.aestronglyMeasurable
    · filter_upwards with ξ
      rw [hfournorm (j - m) ξ]
  have hnormpt : ∀ j ξ, ‖F j ξ‖ = ‖a j‖ * ‖σ₁ ξ‖ := by
    intro j ξ
    rw [hFpt j ξ]
    simp only [norm_mul, hfournorm, one_mul]
  have hFsum : Summable (fun j => ∫ ξ, ‖F j ξ‖ ∂AddCircle.haarAddCircle (T := 1)) := by
    rw [show (fun j => ∫ ξ, ‖F j ξ‖ ∂AddCircle.haarAddCircle (T := 1))
        = fun j => ‖a j‖ * (∫ ξ, ‖σ₁ ξ‖ ∂AddCircle.haarAddCircle (T := 1)) from
      funext (fun j => by
        rw [show (fun ξ => ‖F j ξ‖) = fun ξ => ‖a j‖ * ‖σ₁ ξ‖ from funext (hnormpt j)]
        rw [integral_const_mul])]
    exact ha.mul_right _
  have hmain := hasSum_integral_of_summable_integral_norm hFint hFsum
  have hkey : fourierCoeff (fun ξ => σ₂ ξ * σ₁ ξ) m
      = ∫ ξ, ∑' j : ℤ, F j ξ ∂AddCircle.haarAddCircle (T := 1) := by
    rw [fourierCoeff]
    apply integral_congr_ae
    filter_upwards with ξ
    exact (((hσ₂ ξ).mul_right (σ₁ ξ)).const_smul (fourier (T := 1) (-m) ξ)).tsum_eq.symm
  rw [hkey, ← hmain.tsum_eq]
  refine tsum_congr (fun j => ?_)
  have hcoeff : fourierCoeff σ₁ (m - j)
      = ∫ ξ, fourier (T := 1) (j - m) ξ * σ₁ ξ ∂AddCircle.haarAddCircle (T := 1) := by
    rw [fourierCoeff]
    apply integral_congr_ae
    filter_upwards with ξ
    rw [show -(m - j) = j - m from by ring, smul_eq_mul]
  rw [show (fun ξ : Work.Analysis.IonescuWainger.Circle => F j ξ)
      = fun ξ => a j * (fourier (T := 1) (j - m) ξ * σ₁ ξ) from funext (hFpt j),
    integral_const_mul, ← hcoeff]

/-! ## The band pieces are the `iwConv` pieces

`bandPiece m α h` is the convolution with the coefficients `j ↦ cw m j · e(-jα)`, which are
exactly the Fourier coefficients of `iwSymbolSet {α} (periodize m)` by
`Work.KMTPlan.A6.IwKernelArithChar`; hence `bandPiece m α = iwConv {α} (periodize m)`.  This
identifies the band pieces of `BtwistEx_eq_sum_bandPiece` with the one-frequency Ionescu--Wainger
multipliers `iwConv {α} (periodize φ)`, i.e. with the bands of `Tm ρ l φ`. -/
theorem bandPiece_eq_iwConv (m : ℝ → ℂ) (hm : MeasureTheory.Integrable m)
    (α : Work.Analysis.IonescuWainger.Circle) (h : ℤ → ℂ) :
    Work.KMTPlan.A6.bandPiece m α h
      = Work.Analysis.IWMultiplier.iwConv {α}
          (Work.Analysis.IonescuWainger.periodize m) h := by
  funext n
  rw [Work.Analysis.IWMultiplier.iwConv_apply, Work.KMTPlan.A6.bandPiece_apply]
  refine tsum_congr (fun j => ?_)
  rw [Work.KMTPlan.A6.IwKernelArithChar ({α} : Finset Work.Analysis.IonescuWainger.Circle) hm j]
  simp only [Finset.sum_singleton, smul_eq_mul]
  ring



open MeasureTheory Polynomial Finset
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier Work.KMTAreas.A7
open Submission.PointwiseErgodicTheorems

/-! ## The window-as-bump reduction

The chain `ssuMainBoundK` gives the estimate for the *model sum*
`∑_{αβ} mZ(α,β)·iwConv {α} (periodize φ) f · iwConv {β} (periodize ψ) g` of an arbitrary pair
`(f,g) ∈ ℓ²` and an arbitrary bounded bump `φ`.  Taking the bump to be the *window itself*,
`φ := mStarF u`, gives exactly the bands of the target's `BtwistEx` (by the unconditional
`bandPiece_eq_iwConv` and `BtwistEx_eq_sum_bandPiece`), and the two `ℓ²`-contractions of the
window multipliers (`eLpNorm_Tm_mStarF_le`, `eLpNorm_Tm_mStargF_le`, which cost a factor `1`) turn
the chain's right-hand side into `‖f‖₂‖g‖₂`.  This yields the estimate for *arbitrary* `ℓ²`
inputs, which the target instantiates at `f := Tm ρ l₁ φ f`, `g := Tm ρ l₂ ψ g`. -/
/-! ## The target -/

end Work.KMTPlan.A6
