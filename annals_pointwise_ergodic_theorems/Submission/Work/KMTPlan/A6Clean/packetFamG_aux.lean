/-
# `vrLiftDataP_packetFamG`: the two `X`-level facts, and the constant bookkeeping

This module holds the pieces of
`Work.KMTPlan.A6Clean.vrLiftDataP_packetFamG` (clause (8) of the §8 adelic form, the `g`-side
`L²(ℝ; V^R(ℓ²(ZMod Q)))`-data bound for the packet family of `A6Clean/packetFamG_minorArc.lean`)
which are independent of the harmonic analysis of the frozen slice.

## 1. `eLpNorm_packetFamG_le`

The packet slice `θ ↦ Σ_{β ∈ iwArithFreqs ρ l₂} e(-θ.val·β)·W n β X` is bounded in
`L²(ZMod Q, zmodProb Q)` by the sum of the moduli of its coefficients: `|e(·)| = 1` and
`zmodProb Q` is a probability measure, so `eLpNorm ≤ sup_θ |·| ≤ Σ_β |W n β X|`.

## 2. The constant bookkeeping (`exists_constants_of_bound`)

The conclusion of the target is

`∃ A ≥ 0, ∃ Cin : NNReal → NNReal, ∃ Kv ≥ 0,
   (∫⁻ X, (VrLiftDataP R Q (packet · X))² ≤ ofReal (Kv²))
   ∧ (ofReal Kv ≤ (Cin Λ) · ofReal (lossWeight A …) · ‖g‖₂)`.

`Cin` is introduced **after** `g, a, W` and the fibre hypothesis, so `Cin Λ` may be *any* finite
nonnegative real chosen from the data (it is, in particular, unrestricted above).  Hence, if the
integral is finite — more precisely, if it is bounded by `ofReal K ^ 2 * ‖G‖₂ ^ 2` for the g-side
variational datum `G` and `‖G‖₂ < ⊤` — the conclusion holds with `A = 0`
(`lossWeight 0 = 1`), `Kv = K · (‖G‖₂).toReal` and `Cin Λ = Kv / (lossWeight 0 · (
‖g‖₂).toReal)`.

The only degenerate case is `‖g‖₂ = 0`: then `g = 0` (the counting measure has no null sets),
hence `mdlSliceG ⋯ 0 = 0`, `G = 0` and `Kv = 0`, so both conjuncts hold trivially.
-/
-- NOTE (2026-10-03, LowModelGainEstimate lane): this file used to import the §8-chain declarations
-- `mdlSliceF` / `mdlSliceG` through `Submission.Work.KMTPlan.A6.MdlSliceCoreGainBig`.  Those
-- definitions now live in `Submission.Work.A6Big.Defs` (the copied §8 chain; see the docstring of
-- `MdlSliceCoreGainBig`), and importing them through `MdlSliceCoreGainBig` drags the *whole* copied
-- chain into the closure, which clashes with the `KMTPlan` originals of the same declarations
-- (`Work.KMTPlan.A6.AdelicFormProp` from `KMTPlan/A6/MdlAdelicDefs` versus the copy in
-- `A6Big/KMTPlan/A6/MdlAdelicDefs`, both pulled in here through `MdlAdelicProb` and the chain).
-- The import is re-pointed at the definitions module, exactly as the four sibling files
-- `A6/MdlAdelicDefs`, `A6/MdlSliceGband`, `A6/MdlSliceSsuGain`, `A6Clean/AdelicPacketsDiag` were
-- re-pointed.
import Mathlib
import Submission.Work.KMTPlan.A6Clean.AdelicPacketFam
import Submission.Port.Aesm

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.KMTPlan.A6Clean

open MeasureTheory
open scoped ENNReal NNReal BigOperators
open Work.KMTPlan.A6

set_option maxHeartbeats 800000

local notation "Circ" => Work.Analysis.IonescuWainger.Circle

/-- `‖z‖ₑ = ofReal ‖z‖` for `z : ℂ`. -/
@[simp] lemma enorm_complex_eq (z : ℂ) : ‖z‖ₑ = ENNReal.ofReal ‖z‖ := by
  rw [enorm_eq_nnnorm, ← ENNReal.ofReal_coe_nnreal]
  norm_cast

/-- The packet slice is bounded in `L²(zmodProb Q)` by the sum of the absolute values of its
coefficients. -/
theorem eLpNorm_packetFamG_le (ρ : ℝ) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ : ℕ)
    (W : ℕ → Circ → ℝ → ℂ) (n : ℕ) (X : ℝ) :
    eLpNorm (packetFamG ρ a l₁ l₂ k₁ k₂ W n X) 2
        (zmodProb (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)))
      ≤ ∑ β ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂, ‖W n β X‖ₑ := by
  classical
  haveI hQne : NeZero (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)) :=
    ⟨Nat.pos_iff_ne_zero.mp (Work.KMTAreas.A7.arithQ_pos ρ (max l₁ l₂))⟩
  have hμ : zmodProb (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)) ≠ 0 := by
    intro h
    have h1 : (zmodProb (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂))) Set.univ
        = (0 : Measure (ZMod (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)))) Set.univ := by rw [h]
    rw [zmodProb_univ] at h1
    simp at h1
  set c : ℝ := ∑ β ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂, ‖W n β X‖ with hc
  have hc0 : 0 ≤ c := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hpack : packetFamG ρ a l₁ l₂ k₁ k₂ W n X
      = fun θ : ZMod (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)) =>
          if goodScale (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)) (lcL l₁ l₂ k₁ k₂)
              (Nat.floor (a n)) then
            ∑ β ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂,
              fourier (T := 1) (-(θ.val : ℤ)) β * W n β X
          else 0 := by
    funext θ
    rw [packetFamG_apply]
  rw [hpack]
  by_cases hg : goodScale (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)) (lcL l₁ l₂ k₁ k₂)
      (Nat.floor (a n))
  · rw [funext (fun θ => if_pos hg)]
    refine le_trans (eLpNorm_mono (hf := by pw_aesm) (g := fun _ : ZMod (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)) =>
      (c : ℂ)) (fun θ => ?_)) ?_
    · calc ‖∑ β ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂,
            fourier (T := 1) (-(θ.val : ℤ)) β * W n β X‖
          ≤ ∑ β ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂,
              ‖fourier (T := 1) (-(θ.val : ℤ)) β * W n β X‖ := norm_sum_le _ _
        _ = ∑ β ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂, ‖W n β X‖ := by
            refine Finset.sum_congr rfl (fun β _ => ?_)
            rw [norm_mul, Work.KMTAreas.A7.norm_fourier_applyR, one_mul]
        _ = ‖(c : ℂ)‖ := by
            rw [hc, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc0]
    · rw [eLpNorm_const _ (by norm_num : (2 : ℝ≥0∞) ≠ 0) hμ]
      rw [zmodProb_univ]
      have hroot : (1 : ℝ≥0∞) ^ (1 / (2 : ℝ≥0∞).toReal) = 1 := by simp
      rw [hroot, mul_one]
      simp only [enorm_complex_eq]
      rw [← ENNReal.ofReal_sum_of_nonneg (fun β _ => norm_nonneg (W n β X))]
      exact ENNReal.ofReal_le_ofReal (le_of_eq (by rw [hc, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hc0]))
  · rw [funext (fun θ => if_neg hg)]
    rw [show (fun θ : ZMod (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)) => (0 : ℂ))
      = 0 from funext (fun _ => rfl), eLpNorm_zero]
    exact bot_le

end Work.KMTPlan.A6Clean
