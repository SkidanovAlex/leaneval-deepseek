import Mathlib
import Submission.Work.TMC7Core.Defs

/-!
# TMC7Core / Scale — shared definitions for the QSC (S4) development

The shift operator on `ℓ²(ℤ)` and its basic metric properties, used by
`Submission.Work.TMC7Core.Scale.qsc` (lemma `qsc`, S4 of the C7 design) and by the
delegated lemmas `amo_shift`, `perturb_win`, `tent_window`.
-/

open scoped ENNReal BigOperators
open LeanEval.Analysis.TenMartini

noncomputable section

namespace Work.TMC7Core.Scale

/-- Reindexing `n ↦ n + k` preserves `ℓ²(ℤ)`: the shift is a bijection of the index set,
hence square-summability of `‖·‖ ^ 2` is unchanged. -/
theorem memℓp_shift (f : EllTwo) (k : ℤ) : Memℓp (fun n : ℤ => f (n + k)) 2 := by
  have hf : Summable (fun n : ℤ => ‖f n‖ ^ ((2 : ℝ≥0∞).toReal)) :=
    (lp.memℓp f).summable (by norm_num)
  apply memℓp_gen
  have h := (Equiv.summable_iff (Equiv.addRight k)).2 hf
  simpa only [Function.comp_def, Equiv.coe_addRight] using h

/-- The shift `(shift k u) n = u (n + k)` of `ℓ²(ℤ)`. -/
def shift (k : ℤ) (u : EllTwo) : EllTwo := ⟨fun n => u (n + k), memℓp_shift u k⟩

@[simp] theorem shift_apply (k : ℤ) (u : EllTwo) (n : ℤ) : shift k u n = u (n + k) := rfl

theorem shift_zero (u : EllTwo) : shift 0 u = u := by
  apply lp.ext; funext n; simp

theorem shift_shift (k l : ℤ) (u : EllTwo) : shift k (shift l u) = shift (k + l) u := by
  apply lp.ext; funext n
  simp only [shift_apply, Int.add_assoc]

/-- The shift is an isometry of `ℓ²(ℤ)`. -/
theorem shift_norm (k : ℤ) (u : EllTwo) : ‖shift k u‖ = ‖u‖ := by
  have hs : ((2 : ℝ≥0∞).toReal) = 2 := by norm_num
  have h1 : ‖shift k u‖ ^ 2 = ∑' n : ℤ, ‖u (n + k)‖ ^ 2 := by
    have h := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (shift k u)
    simp only [hs] at h
    simp_rw [Real.rpow_two] at h
    simpa using h
  have h2 : ∑' n : ℤ, ‖u (n + k)‖ ^ 2 = ‖u‖ ^ 2 := by
    have h := (lp.norm_rpow_eq_tsum (p := 2) (by norm_num) u).symm
    simp only [hs] at h
    simp_rw [Real.rpow_two] at h
    rw [show (∑' n : ℤ, ‖u (n + k)‖ ^ 2) = ∑' n : ℤ, ‖u n‖ ^ 2 from
      Equiv.tsum_eq (Equiv.addRight k) (fun n : ℤ => ‖u n‖ ^ 2)]
    exact h
  have h3 : ‖shift k u‖ ^ 2 = ‖u‖ ^ 2 := by rw [h1, h2]
  nlinarith [norm_nonneg (shift k u), norm_nonneg u]

end Work.TMC7Core.Scale
