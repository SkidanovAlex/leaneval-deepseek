/-
# The vocabulary of the operator-level integration-by-parts identities of §6 (area A6)

This module collects the definitions and the elementary identities that the *operator-level*
integration-by-parts identities `Work.KMTPlan.A6.MdlDecayHighLow` (identity (i), the case
`k₂ = 0`), `Work.KMTPlan.A6.MdlDecayLowHigh` (identity (ii), the case `k₁ = 0`) and their
auxiliary lemmas are stated in terms of.  It is kept free of the targets themselves so that the
targets may import (and be proved from) the auxiliary modules that use these definitions.

* `mdlBtwK ρ P l₁ l₂ m₁ m₂` is the kernel of the twisted bilinear multiplier `Btwist`
  (the named version of `twKer`, `MdlTleKer`), so that `Btwist = bilinOp mdlBtwK` holds
  definitionally;
* `mdlIWKer ρ l ψ` is the convolution kernel of the Ionescu--Wainger multiplier `Tle ρ l ψ`
  (the named version of `TleKer`), so that `Tle = convOp mdlIWKer` holds definitionally and
  `mdlIWKer ρ l ψ i = arithChar ρ l (-i) cw ψ i` for integrable `ψ`;
* `mdlNF K κ κ' F G x = ∑'_p ∑'_z (κ z₁ κ' z₂) K (p₁-z₁) (p₂-z₂) F (x-p₁) G (x-p₂)` is the
  normal form in which the composition `bilinOp (kernComp K κ κ') F G` of a bilinear convolution
  operator with the two convolutions `κ`, `κ'` is written
  (`bilinOp_kernComp_eq_mdlNF`).
-/
import Mathlib
import Submission.Work.KMTPlan.A6.MdlTleKer
import Submission.Work.KMTAreas.A7.measurable_iwKernel_varphiNt
import Submission.Work.KMTAreas.A7.measurable_iwKernel_varphitildeNt
import Submission.Work.A7.ModelApproxCore_aux.bilinOp_eq_tsum
import Submission.Work.A7.ModelApproxCore_aux.kernComp_eq_tsum
import Submission.Work.A7.ModelApproxCore_aux.summable_kernComp

set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators Interval
open Work.KMTAreas.A7

/-! ## The kernel of `Btwist` -/

/-- The kernel of the twisted bilinear multiplier `Btwist`: the product of the arithmetic kernel
with the two Fourier coefficients of the product symbol (the named version of `twKer`). -/
noncomputable def mdlBtwK (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ : ℕ) (m₁ m₂ : ℝ → ℂ) : ℤ → ℤ → ℂ :=
  twKer ρ P l₁ l₂ m₁ m₂

/-- `Btwist` is the bilinear convolution operator with kernel `mdlBtwK`. -/
theorem Btwist_eq_bilinOp (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ : ℕ) (m₁ m₂ : ℝ → ℂ)
    (h k : ℤ → ℂ) :
    Btwist ρ P l₁ l₂ m₁ m₂ h k = bilinOp (mdlBtwK ρ P l₁ l₂ m₁ m₂) h k :=
  Btwist_eq_bilinOp_twKer ρ P l₁ l₂ m₁ m₂ h k

/-! ## The convolution kernel of `Tle` -/

/-- The convolution kernel of the Ionescu--Wainger multiplier `Tle ρ l ψ`: the Fourier
coefficients of the symbol `∑_{α ∈ (ℚ/ℤ)_{≤l}} periodize ψ (· - α)` (the named version of
`TleKer`). -/
noncomputable def mdlIWKer (ρ : ℝ) (l : ℕ) (ψ : ℝ → ℂ) : ℤ → ℂ :=
  iwKer ρ l (Work.Analysis.IonescuWainger.periodize ψ)

/-- `Tle` is the convolution operator with kernel `mdlIWKer`. -/
theorem Tle_eq_convOp (ρ : ℝ) (l : ℕ) (ψ : ℝ → ℂ) (F : ℤ → ℂ) :
    Tle ρ l ψ F = convOp (mdlIWKer ρ l ψ) F := by
  funext n
  rw [Tle_apply]
  rfl

/-- **The arithmetic-character form of the convolution kernel of `Tle`**: for an integrable symbol
`ψ` the kernel is the arithmetic character times the continuous Fourier coefficient,
`mdlIWKer ρ l ψ i = arithChar ρ l (-i) · cw ψ i` (`Work.KMTKernelArithChar`). -/
theorem mdlIWKer_eq_cw (ρ : ℝ) (l : ℕ) {ψ : ℝ → ℂ} (hψ : MeasureTheory.Integrable ψ) (i : ℤ) :
    mdlIWKer ρ l ψ i = arithChar ρ l (-i) * cw ψ i := by
  have h := TleKer_eq_arChar_cw ρ l hψ i
  simpa only [mdlIWKer, TleKer, iwKer, TleArChar, arithChar] using h

/-- `mdlIWKer` is the kernel `TleKer` of `MdlTleKer` (definitionally). -/
@[simp] theorem mdlIWKer_eq_TleKer (ρ : ℝ) (l : ℕ) (ψ : ℝ → ℂ) :
    mdlIWKer ρ l ψ = TleKer ρ l ψ := rfl

/-- `mdlBtwK` is the kernel `twKer` of `MdlTleKer` (definitionally). -/
@[simp] theorem mdlBtwK_eq_twKer (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ : ℕ) (m₁ m₂ : ℝ → ℂ) :
    mdlBtwK ρ P l₁ l₂ m₁ m₂ = twKer ρ P l₁ l₂ m₁ m₂ := rfl

/-! ## The normal form -/

/-- **The normal form of the expansion of the model tuple.**  For a bilinear kernel `K`, two
convolution kernels `κ`, `κ'` and two functions `F`, `G`,

  `mdlNF K κ κ' F G x = ∑'_p ∑'_z (κ z₁ κ' z₂) · K (p₁-z₁) (p₂-z₂) · F (x-p₁) · G (x-p₂)`.

It is the common form in which both sides of the operator-level integration-by-parts identities
are written. -/
noncomputable def mdlNF (K : ℤ → ℤ → ℂ) (κ κ' : ℤ → ℂ) (F G : ℤ → ℂ) (x : ℤ) : ℂ :=
  ∑' p : ℤ × ℤ, ∑' z : ℤ × ℤ,
    (κ z.1 * κ' z.2) * (K (p.1 - z.1) (p.2 - z.2) * F (x - p.1) * G (x - p.2))

/-- The composition of a bilinear convolution operator (kernel `K`) with the two convolutions
`κ`, `κ'`, summed against `F`, `G`, in the normal form `mdlNF`.  This is
`Work.A7.ModelApproxCore_kernelComp` (`bilinOp (kernComp K κ κ') = bilinOp K (convOp κ ·) (convOp κ' ·)`)
followed by `kernComp_eq_tsum` and the flattening of the two sums. -/
theorem bilinOp_kernComp_eq_mdlNF {K : ℤ → ℤ → ℂ} {κ κ' F G : ℤ → ℂ} {CF CG : ℝ}
    (hK : Summable fun p : ℤ × ℤ => ‖K p.1 p.2‖) (hκ : Summable fun j : ℤ => ‖κ j‖)
    (hκ' : Summable fun j : ℤ => ‖κ' j‖) (hF : ∀ y : ℤ, ‖F y‖ ≤ CF)
    (hG : ∀ y : ℤ, ‖G y‖ ≤ CG) (x : ℤ) :
    bilinOp (kernComp K κ κ') F G x = mdlNF K κ κ' F G x := by
  rw [Work.A7.ModelApproxCore_aux.bilinOp_eq_tsum
        (Work.A7.ModelApproxCore_aux.summable_kernComp hK hκ hκ') hF hG, mdlNF]
  refine tsum_congr (fun p => ?_)
  rw [Work.A7.ModelApproxCore_aux.kernComp_eq_tsum hK hκ hκ' p.1 p.2]
  rw [← tsum_mul_right, ← tsum_mul_right]
  refine tsum_congr (fun z => ?_)
  ring

end

end Work.KMTPlan.A6
