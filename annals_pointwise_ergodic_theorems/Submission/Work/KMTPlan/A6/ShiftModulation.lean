/-
# The right shift of `ℓ²(ℤ)` and the shift–modulation estimate for the IW bands

`shiftL2Z m F` is the shift `n ↦ F (n + m)` of an `ℓ²(ℤ)` sequence, defined on the Fourier side by
multiplication with the character `ξ ↦ e(-mξ)`:

`shiftL2Z m F := 𝓕⁻¹ (charLp (-m) · 𝓕 F)`.

The purpose of this file is the *shift–modulation* estimate used in the comparison of
`BtwistEx` with the halved average `Ã_N` (`NOTES_A6_ssuBtwistEx_SESSION2.md`, step 3): on the
disjoint frequency bands `α + realArc K`, `α ∈ S`, the shift by `m` acts like the modulation by
`e(-mα)`, with an error `O(|m| 2^K ‖·‖₂)`.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.multiplierOfPlancherel
import Submission.Work.KMTPlan.A6.iwConvEqIwOpSetMemlp

set_option autoImplicit false
set_option maxHeartbeats 1000000

open MeasureTheory
open scoped BigOperators ENNReal
open Work.Analysis.IonescuWainger

namespace Work.KMTPlan.A6

local notation "Circ" => Work.Analysis.IonescuWainger.Circle

/-- The character `ξ ↦ e(jξ)` of the circle is essentially bounded. -/
theorem memLp_fourier_char (j : ℤ) :
    MemLp (fun ξ : Circ => fourier (T := 1) j ξ) ⊤ circleMeasure :=
  MemLp.of_bound ((map_continuous (fourier (T := 1) j)).aestronglyMeasurable) 1
    (Filter.Eventually.of_forall (fun ξ => by
      have h1 : ‖fourier (T := 1) j ξ‖ = (1 : ℝ) := by rw [fourier_apply, Circle.norm_coe]
      exact h1.le))

/-- The character `ξ ↦ e(jξ)` of the circle, as an element of `L^∞(ℝ/ℤ)`. -/
noncomputable def charLp (j : ℤ) : Lp ℂ ⊤ circleMeasure :=
  (memLp_fourier_char j).toLp (fun ξ : Circ => fourier (T := 1) j ξ)

/-- **The right shift of an `ℓ²` sequence**, defined on the Fourier side: multiplication of the
Fourier transform by the character `ξ ↦ e(-mξ)`. -/
noncomputable def shiftL2Z (m : ℤ) (F : L2Z) : L2Z :=
  fourierZ.symm (charLp (-m) • fourierZ F)

theorem fourierZ_shiftL2Z (m : ℤ) (F : L2Z) :
    fourierZ (shiftL2Z m F) = charLp (-m) • fourierZ F :=
  fourierZ.apply_symm_apply _

/-- **The defining property of the shift**: `(shiftL2Z m F) n = F (n + m)`. -/
theorem shiftL2Z_apply (m : ℤ) (F : L2Z) (n : ℤ) : shiftL2Z m F n = F (n + m) := by
  have h1 : shiftL2Z m F n = fourierCoeff (⇑(charLp (-m) • fourierZ F)) n := by
    show (fourierZ.symm (charLp (-m) • fourierZ F)) n = _
    rw [show fourierZ.symm = (fourierBasis (T := 1)).repr from rfl]
    exact fourierBasis_repr _ n
  have hs1 : HasSum (fun k : ℤ => ⇑F k • (charLp (-m) • fourierLp (T := 1) 2 k))
      (charLp (-m) • fourierZ F) := by
    have h := ContinuousLinearMap.hasSum (circleMulOp (charLp (-m))) (fourierZ_hasSum F)
    simpa only [circleMulOp_apply, Lp.smul_comm] using h
  have hs2 := ContinuousLinearMap.hasSum (innerSL ℂ (fourierLp (T := 1) 2 n)) hs1
  have hterm : ∀ k : ℤ, (innerSL ℂ (fourierLp (T := 1) 2 n))
        (⇑F k • (charLp (-m) • fourierLp (T := 1) 2 k))
      = ⇑F k * fourierCoeff (⇑(charLp (-m))) (n - k) := by
    intro k
    rw [innerSL_apply_apply, inner_smul_right]
    congr 1
    rw [← innerSL_apply_apply,
      ← fourierCoeff_eq_innerSL (charLp (-m) • fourierLp (T := 1) 2 k) n,
      fourierCoeff_lpSMul_fourierLp (charLp (-m)) k n]
  have hs3 : HasSum (fun k : ℤ => ⇑F k * fourierCoeff (⇑(charLp (-m))) (n - k))
      ((innerSL ℂ (fourierLp (T := 1) 2 n)) (charLp (-m) • fourierZ F)) := by
    simpa only [hterm] using hs2
  have hcoeff : ∀ j : ℤ, fourierCoeff (⇑(charLp (-m))) j = if j = -m then 1 else 0 := by
    intro j
    rw [show charLp (-m)
        = (memLp_fourier_char (-m)).toLp (fun ξ : Circ => fourier (T := 1) (-m) ξ) from rfl]
    rw [congrFun (fourierCoeff_congr_ae (MemLp.coeFn_toLp (memLp_fourier_char (-m)))) j]
    have h := congrFun (fourierCoeff_fourier (T := 1) (-m)) j
    show fourierCoeff (⇑(fourier (T := 1) (-m))) j = (if j = -m then 1 else 0)
    rw [h]
    by_cases hj : j = -m <;> simp [hj]
  rw [h1, fourierCoeff_eq_innerSL, ← hs3.tsum_eq]
  rw [tsum_eq_single (n + m) (fun k hk => by
        rw [hcoeff]
        have hne : n - k ≠ -m := by omega
        simp [hne])]
  rw [hcoeff]
  simp

end Work.KMTPlan.A6
