import Mathlib
import Submission.Work.BourgainPlan.Maximal.MtaDefs

/-!
# Integrability of the dilated bump family `ξ ↦ ψ̃(2^m ξ)`

`tildeFam m` is the complex lift of the smooth bump `dyadTilde` dilated by `2^m`.  Since `dyadTilde`
is continuous and compactly supported, so is `tildeFam m`, hence it is integrable against Lebesgue
measure on `ℝ`.
-/

open MeasureTheory
open Work.BourgainPlan.Maximal

namespace Work.BourgainPlan.MtaLin

/-- The complex lift of `dyadTilde` has compact support (`dyadTilde` vanishes for `|ξ| ≥ 4`). -/
lemma hasCompactSupport_dyadTilde_complex : HasCompactSupport (fun η : ℝ => (dyadTilde η : ℂ)) := by
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := (-4 : ℝ)) (b := 4)) ?_
  intro ξ hξ
  have hξ' : ¬ (4 ≤ |ξ|) := fun hh4 => hξ (by simp [dyadTilde_zero hh4])
  exact ⟨by linarith [neg_abs_le ξ], by linarith [le_abs_self ξ]⟩

/-- Compact support of the dilated family `ξ ↦ ψ̃(2^m ξ)`. -/
lemma hasCompactSupport_tildeFam (m : ℤ) : HasCompactSupport (tildeFam m) :=
  hasCompactSupport_comp_mul_left' hasCompactSupport_dyadTilde_complex
    (zpow_ne_zero m (by norm_num : (2 : ℝ) ≠ 0))

theorem integrable_tildeFam (m : ℤ) : MeasureTheory.Integrable (Work.BourgainPlan.Maximal.tildeFam m) MeasureTheory.volume :=
  (continuous_tildeFam m).integrable_of_hasCompactSupport (hasCompactSupport_tildeFam m)

end Work.BourgainPlan.MtaLin
