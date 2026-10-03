import Mathlib
import Submission.Work.KMTAreas.A7Hi.FiberVarSampling

namespace Work.KMTAreas.A7Hi

open MeasureTheory
open scoped ENNReal NNReal BigOperators

/-!
# The gate identity for the fibre of the twisted projection (KMT §8, `form-1`)

The main theorem `fiberOp_Tex_eq_twisted` rewrites the fibre `fiberOp ρ l m n₀`, applied to the
exact-height projection `Tex ρ l φ f`, as a translate by `n₀` of the Ionescu--Wainger multiplier
with the *twisted* profile `χ · periodize φ` (where `χ = fourier (-n₀)` is the character of the
residue).

The proof is the multiplier calculus, in the `ℓ¹`-kernel form:

* `fiberOp ρ l m n₀ u = τ_{n₀} (iwConv A (m̃ · χ) u)` where `m̃ = periodize m`
  (`fiberOp_eq_translate_iwConv` below: the kernel of the fibre is
  `j ↦ (∑_{α∈A} χ (n₀-j) α) · cw m j`, which is the coefficient sequence of the twisted symbol
  `∑_{α∈A} (m̃ · χ)(· - α)` at `j - n₀`);
* `Tex ρ l φ f = iwConv A φ̃ f` by definition;
* the composition `iwConv A Φ₁ ∘ iwConv A Φ₂ = iwConv A Φ₃` follows from the *pointwise* symbol
  identity `gateSymbolProduct` (the aliasing/plateau collapse) together with the convolution
  theorem for Fourier coefficients in the `L¹` summability regime (`fourierCoeff_mul_l1`) and the
  `ℓ¹`-convolution associativity `tsum_conv_conv`.
-/

/-- The frequency circle `ℝ/ℤ`. -/
local notation "Circ" => Work.Analysis.IonescuWainger.Circle

/-! ## Elementary integrability of Ionescu--Wainger symbols -/

/-- The Ionescu--Wainger symbol of an integrable profile is integrable: it is a finite sum of
translates. -/
theorem integrable_iwSymbolSet (A : Finset Circ) {Ψ : Circ → ℂ}
    (hΨ : MeasureTheory.Integrable Ψ Work.Analysis.IonescuWainger.circleMeasure) :
    MeasureTheory.Integrable (Work.Analysis.IonescuWainger.iwSymbolSet A Ψ)
      Work.Analysis.IonescuWainger.circleMeasure := by
  have hterm : ∀ α ∈ A, MeasureTheory.Integrable (fun ξ : Circ => Ψ (ξ - α))
      Work.Analysis.IonescuWainger.circleMeasure := fun α _ => hΨ.comp_sub_right α
  have hsum : (∑ α ∈ A, fun ξ : Circ => Ψ (ξ - α))
      = Work.Analysis.IonescuWainger.iwSymbolSet A Ψ := by
    funext ξ
    simp [Work.Analysis.IonescuWainger.iwSymbolSet]
  rw [← hsum]
  exact integrable_finsetSum' A hterm

/-! ## The fibre as a translate of an Ionescu--Wainger convolution -/

/-! ## Composition of Ionescu--Wainger convolutions -/

/-- **Composition of two Ionescu--Wainger convolutions.**  If the pointwise product of the two
symbols is the third symbol (`gateSymbolProduct`), then the corresponding convolutions compose, for
every bounded input.  In kernel form this is the identity `K₁ ⋆ K₂ = K₃` for the coefficient
sequences, which is the convolution theorem `fourierCoeff_mul_l1`, followed by the reassociation
`tsum_conv_conv` of the double `tsum`. -/
theorem iwConv_comp (A : Finset Circ) (Ψ₁ Ψ₂ Ψ₃ : Circ → ℂ)
    (h1 : MeasureTheory.Integrable (Work.Analysis.IonescuWainger.iwSymbolSet A Ψ₁)
      Work.Analysis.IonescuWainger.circleMeasure)
    (h2 : MeasureTheory.Integrable (Work.Analysis.IonescuWainger.iwSymbolSet A Ψ₂)
      Work.Analysis.IonescuWainger.circleMeasure)
    (h3 : MeasureTheory.Integrable (Work.Analysis.IonescuWainger.iwSymbolSet A Ψ₃)
      Work.Analysis.IonescuWainger.circleMeasure)
    (hs1 : Summable (fun j : ℤ =>
      fourierCoeff (Work.Analysis.IonescuWainger.iwSymbolSet A Ψ₁) j))
    (hs2 : Summable (fun j : ℤ =>
      fourierCoeff (Work.Analysis.IonescuWainger.iwSymbolSet A Ψ₂) j))
    (hgate : ∀ ζ : Circ, Work.Analysis.IonescuWainger.iwSymbolSet A Ψ₁ ζ
        * Work.Analysis.IonescuWainger.iwSymbolSet A Ψ₂ ζ
      = Work.Analysis.IonescuWainger.iwSymbolSet A Ψ₃ ζ)
    (f : ℤ → ℂ) {B : ℝ} (hf : ∀ y : ℤ, ‖f y‖ ≤ B) :
    Work.Analysis.IWMultiplier.iwConv A Ψ₁ (Work.Analysis.IWMultiplier.iwConv A Ψ₂ f)
      = Work.Analysis.IWMultiplier.iwConv A Ψ₃ f := by
  have hFG : MeasureTheory.Integrable (fun ξ : Circ =>
      Work.Analysis.IonescuWainger.iwSymbolSet A Ψ₁ ξ
        * Work.Analysis.IonescuWainger.iwSymbolSet A Ψ₂ ξ)
      Work.Analysis.IonescuWainger.circleMeasure :=
    h3.congr (Filter.Eventually.of_forall (fun ξ => (hgate ξ).symm))
  have hK : ∀ m : ℤ, (∑' j : ℤ,
        fourierCoeff (Work.Analysis.IonescuWainger.iwSymbolSet A Ψ₁) j
          * fourierCoeff (Work.Analysis.IonescuWainger.iwSymbolSet A Ψ₂) (m - j))
      = fourierCoeff (Work.Analysis.IonescuWainger.iwSymbolSet A Ψ₃) m := by
    intro m
    rw [← fourierCoeff_mul_l1 h1 h2 hFG hs1 hs2 m]
    exact congrFun (fourierCoeff_congr_ae (Filter.Eventually.of_forall hgate)) m
  funext n
  simp only [Work.Analysis.IWMultiplier.iwConv_apply, smul_eq_mul]
  change (∑' j : ℤ, fourierCoeff (Work.Analysis.IonescuWainger.iwSymbolSet A Ψ₁) j
        * (∑' i : ℤ, fourierCoeff (Work.Analysis.IonescuWainger.iwSymbolSet A Ψ₂) i
          * f (n - j - i)))
      = ∑' m : ℤ, fourierCoeff (Work.Analysis.IonescuWainger.iwSymbolSet A Ψ₃) m * f (n - m)
  rw [tsum_conv_conv
    (a := fun j : ℤ => fourierCoeff (Work.Analysis.IonescuWainger.iwSymbolSet A Ψ₁) j)
    (b := fun i : ℤ => fourierCoeff (Work.Analysis.IonescuWainger.iwSymbolSet A Ψ₂) i)
    (u := f) (C := B) hs1.norm hs2.norm hf n]
  exact tsum_congr (fun m => by rw [hK m])

/-! ## The gate identity -/

end Work.KMTAreas.A7Hi
