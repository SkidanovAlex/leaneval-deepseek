/-
# The kernel of `T^{≤l}_φ` and the pointwise expansion of the twisted bilinear multiplier

This module fixes the elementary vocabulary used to *lift* the frequency-level integration-by-parts
identity `MdlBumpIntegIdent` (`A6/MdlBumpIntegIdent.lean`) to the *operator* level, i.e. to the
statement `Work.KMTPlan.A6.MdlDecayLowHigh`.

* `TleKer ρ l φ` — the convolution kernel of the Ionescu--Wainger multiplier `Tle ρ l φ = T^{≤l}_φ`,
  i.e. the Fourier coefficients of the symbol `∑_{α ∈ (ℚ/ℤ)_{≤l}} (periodize φ)(· - α)`.  Since
  `Tle` is *defined* as `iwConv (iwArithFreqs ρ l) (periodize φ)`, the identity
  `Tle ρ l φ f = convOp (TleKer ρ l φ) f` is definitional (`Tle_eq_convOp`).
* `TleArChar ρ l i = ∑_{α ∈ (ℚ/ℤ)_{≤l}} e(-iα)` — the arithmetic character sum, so that
  `TleKer ρ l φ i = TleArChar ρ l i * cw φ i` (`TleKer_eq_arChar_cw`, from `IwKernelArithChar`).
  This is what makes the *integration by parts in `t`* applicable: the `t`-dependence of
  `TleKer ρ l (φ_t) i` sits entirely in the continuous Fourier coefficient `cw φ_t i`, and the
  arithmetic character sum is a `t`-independent scalar.
* `twKer ρ P l₁ l₂ m₁ m₂` — the kernel of the twisted bilinear multiplier `Btwist`, so that
  `Btwist … h k = bilinOp (twKer …) h k` is definitional.
* `bilinOp_convOp_expansion` — the *pointwise* expansion of `Btwist` applied to two
  convolution operators, in the coefficients of the two kernels.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.MdlDefs
import Submission.Work.KMTPlan.A6.IwKernelArithChar
import Submission.Work.KMTAreas.A7.ModelOps

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators Interval
open Work.KMTAreas.A7

/-- **The convolution kernel of `T^{≤l}_φ`**: the Fourier coefficients of the Ionescu--Wainger
symbol `∑_{α ∈ (ℚ/ℤ)_{≤l}} (periodize φ)(· - α)`. -/
noncomputable def TleKer (ρ : ℝ) (l : ℕ) (φ : ℝ → ℂ) : ℤ → ℂ :=
  fun i => Work.Analysis.IWMultiplier.iwKernel
    (Work.Analysis.IonescuWainger.iwSymbolSet (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
      (Work.Analysis.IonescuWainger.periodize φ)) i

/-- `Tle` is the convolution with `TleKer` (definitional). -/
theorem Tle_eq_convOp_TleKer (ρ : ℝ) (l : ℕ) (φ : ℝ → ℂ) (f : ℤ → ℂ) :
    Tle ρ l φ f = convOp (TleKer ρ l φ) f := rfl

/-- **The arithmetic character sum of height `≤ l`**: `∑_{α ∈ (ℚ/ℤ)_{≤l}} e(-iα)`. -/
noncomputable def TleArChar (ρ : ℝ) (l : ℕ) (i : ℤ) : ℂ :=
  ∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l, fourier (T := 1) (-i) α

/-- **The kernel of `T^{≤l}_φ` factors as the arithmetic character sum times the continuous
Fourier transform `cw φ i = ∫ φ θ e(-iθ) dθ`.**  This is `IwKernelArithChar`. -/
theorem TleKer_eq_arChar_cw (ρ : ℝ) (l : ℕ) {φ : ℝ → ℂ} (hφ : Integrable φ) (i : ℤ) :
    TleKer ρ l φ i = TleArChar ρ l i * cw φ i :=
  IwKernelArithChar (Work.Analysis.IonescuWainger.iwArithFreqs ρ l) hφ i

/-- **The kernel of the twisted bilinear multiplier** `B^{l₁,l₂,m_Ẑ}_{m₁⊗m₂}`. -/
noncomputable def twKer (ρ : ℝ) (P : ℤ[X]) (l₁ l₂ : ℕ) (m₁ m₂ : ℝ → ℂ) : ℤ → ℤ → ℂ :=
  fun j₁ j₂ => arithKernel ρ P (arithQ ρ (max l₁ l₂)) l₁ l₂ j₁ j₂ * cw m₁ j₁ * cw m₂ j₂

/-- `Btwist` is the bilinear convolution with `twKer` (definitional). -/
theorem Btwist_eq_bilinOp_twKer (ρ : ℝ) (P : ℤ[X]) (l₁ l₂ : ℕ) (m₁ m₂ : ℝ → ℂ)
    (h k : ℤ → ℂ) :
    Btwist ρ P l₁ l₂ m₁ m₂ h k = bilinOp (twKer ρ P l₁ l₂ m₁ m₂) h k := rfl

/-! ## Summability helpers -/

/-- A kernel times a bounded sequence is summable, for an `ℓ¹` kernel. -/
theorem summable_ker_mul_bounded {κ : ℤ → ℂ} {F : ℤ → ℂ} {C : ℝ}
    (hκ : Summable fun i : ℤ => ‖κ i‖) (hF : ∀ y : ℤ, ‖F y‖ ≤ C) (y : ℤ) :
    Summable fun i : ℤ => κ i * F (y - i) := by
  refine Summable.of_norm ?_
  have h1 : Summable (fun i : ℤ => ‖κ i‖ * ‖F (y - i)‖) := by
    refine Summable.of_nonneg_of_le (fun i => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (fun i => ?_) (hκ.mul_right (max C 0))
    exact mul_le_mul_of_nonneg_left ((hF _).trans (le_max_left _ _)) (norm_nonneg _)
  exact h1.congr (fun i => (norm_mul _ _).symm)

/-- `convOp` of an `ℓ¹` kernel applied to a bounded function is bounded. -/
theorem norm_convOp_le {κ : ℤ → ℂ} {F : ℤ → ℂ} {C : ℝ}
    (hκ : Summable fun i : ℤ => ‖κ i‖) (hF : ∀ y : ℤ, ‖F y‖ ≤ C) (y : ℤ) :
    ‖convOp κ F y‖ ≤ (∑' i : ℤ, ‖κ i‖) * max C 0 := by
  have hsum : Summable fun i : ℤ => κ i * F (y - i) := summable_ker_mul_bounded hκ hF y
  have hmaj : Summable fun i : ℤ => max C 0 * ‖κ i‖ := hκ.mul_left (max C 0)
  calc ‖convOp κ F y‖ = ‖∑' i : ℤ, κ i * F (y - i)‖ := rfl
    _ ≤ ∑' i : ℤ, ‖κ i * F (y - i)‖ :=
        norm_tsum_le_tsum_norm (f := fun i : ℤ => κ i * F (y - i)) hsum.norm
    _ ≤ ∑' i : ℤ, max C 0 * ‖κ i‖ := by
        refine Summable.tsum_le_tsum (fun i => ?_) hsum.norm hmaj
        rw [norm_mul]
        calc ‖κ i‖ * ‖F (y - i)‖ ≤ ‖κ i‖ * max C 0 :=
              mul_le_mul_of_nonneg_left ((hF _).trans (le_max_left C 0)) (norm_nonneg (κ i))
          _ = max C 0 * ‖κ i‖ := by ring
    _ = (∑' i : ℤ, ‖κ i‖) * max C 0 := by rw [tsum_mul_left, mul_comm]

end

end Work.KMTPlan.A6
