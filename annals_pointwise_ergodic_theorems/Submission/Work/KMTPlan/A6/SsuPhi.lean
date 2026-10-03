/-
# The geometric scale `Φ(l)` of the `ssu` assembly

`ssuPhi ρ l = 1 + l · 2^{ρ l / 2} + l` is the ubiquitous scale of the Ionescu--Wainger height
bounds used in the proof of the paper's Lemma `ssu` (`Work.KMTPlan.A6.ssuBtwistExBdd`):

* `iwP_element_le_sharp`: `q ≤ 2^{C·Φ(l)}` for `q ∈ iwP ρ l`;
* `ssuNonAliasing`, `ssuSep`, `ssuBookkeeping`: all their thresholds are `C·Φ(l) + const`.

It is collected here so that the arithmetic lemmas of the assembly can refer to it without
importing the assembly itself.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.SsuDefs

set_option autoImplicit false

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial Finset
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger Work.KMTAreas.A7

/-- The geometric scale `Φ(l) = 1 + l · 2^{ρ l / 2} + l` of the Ionescu--Wainger height bounds. -/
noncomputable def ssuPhi (ρ : ℝ) (l : ℕ) : ℝ :=
  1 + (l : ℝ) * (2 : ℝ) ^ (ρ * (l : ℝ) / 2) + (l : ℝ)

theorem ssuPhi_nonneg (ρ : ℝ) (l : ℕ) : 0 ≤ ssuPhi ρ l := by
  have h : (0 : ℝ) ≤ (2 : ℝ) ^ (ρ * (l : ℝ) / 2) := Real.rpow_nonneg (by norm_num) _
  have hl : (0 : ℝ) ≤ (l : ℝ) := Nat.cast_nonneg l
  simp only [ssuPhi]
  linarith [mul_nonneg hl h]

theorem one_le_ssuPhi (ρ : ℝ) (l : ℕ) : 1 ≤ ssuPhi ρ l := by
  have h : (0 : ℝ) ≤ (2 : ℝ) ^ (ρ * (l : ℝ) / 2) := Real.rpow_nonneg (by norm_num) _
  have hl : (0 : ℝ) ≤ (l : ℝ) := Nat.cast_nonneg l
  simp only [ssuPhi]
  nlinarith [mul_nonneg hl h]

theorem cast_le_ssuPhi (ρ : ℝ) (l : ℕ) : (l : ℝ) ≤ ssuPhi ρ l := by
  have h : (0 : ℝ) ≤ (2 : ℝ) ^ (ρ * (l : ℝ) / 2) := Real.rpow_nonneg (by norm_num) _
  have hl : (0 : ℝ) ≤ (l : ℝ) := Nat.cast_nonneg l
  simp only [ssuPhi]
  linarith [mul_nonneg hl h]

/-- `Φ` is monotone in `l`. -/
theorem ssuPhi_mono {ρ : ℝ} (hρ : 0 ≤ ρ) {l l' : ℕ} (h : l ≤ l') :
    ssuPhi ρ l ≤ ssuPhi ρ l' := by
  have hl : (l : ℝ) ≤ (l' : ℝ) := by exact_mod_cast h
  have hexp : ρ * (l : ℝ) / 2 ≤ ρ * (l' : ℝ) / 2 := by
    have : ρ * (l : ℝ) ≤ ρ * (l' : ℝ) := mul_le_mul_of_nonneg_left hl hρ
    linarith
  have hrpow : (2 : ℝ) ^ (ρ * (l : ℝ) / 2) ≤ (2 : ℝ) ^ (ρ * (l' : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le (x := 2) (by norm_num) hexp
  have h0 : (0 : ℝ) ≤ (2 : ℝ) ^ (ρ * (l : ℝ) / 2) := Real.rpow_nonneg (by norm_num) _
  have hl0 : (0 : ℝ) ≤ (l : ℝ) := Nat.cast_nonneg l
  simp only [ssuPhi]
  have hl' : (0 : ℝ) ≤ (l' : ℝ) := Nat.cast_nonneg l'
  nlinarith [mul_le_mul hl hrpow h0 hl', hrpow, h0, hl0, hl]

end

end Work.KMTPlan.A6
