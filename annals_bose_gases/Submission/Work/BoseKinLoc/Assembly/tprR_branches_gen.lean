import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Submission.Work.BoseKinLoc.Assembly.assembly_two_regime
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.Assembly.tprR_branches_gen`

The two branches of the box-momentum two-regime kernel `tprR σ C q`
(`Assembly/TwoRegimeDefs.lean`) for **general** `C`.

`tprR σ C q = if (5/6)σ⁻¹ ≤ q then fsKinCoeff ((2σ)⁻¹) q else C σ³ q²`, so

* below the switch the kernel is the near-region Taylor branch `C σ³ q²`
  (`tprR_near`, already in `assembly_two_regime.lean`, general in `C`);
* above the switch the kernel is the squared cut-off `(q − (2σ)⁻¹)²`, **independent
  of `C`** — this file records that case for general `C` (`tprR_far` in
  `assembly_two_regime.lean` only states it at `C = 1`).

Together they let every regional case of the general-`(β,C)` budget be reduced to
elementary real arithmetic.
-/

noncomputable section

namespace Work.BoseKinLoc.Assembly

open Work.BoseKinLoc
open Submission.BoseGases

/-- **The far branch of `tprR` for general `C`.**  Above the switch
`(5/6)σ⁻¹ ≤ q` the kernel is the squared cut-off `(q − (2σ)⁻¹)²`, whatever `C` is. -/
lemma tprR_far_gen {σ C q : ℝ} (hσ : 0 < σ) (h : (5 / 6) * σ⁻¹ ≤ q) :
    tprR σ C q = (q - (2 * σ)⁻¹) ^ 2 := by
  have hσi : 0 ≤ σ⁻¹ := inv_nonneg.mpr hσ.le
  have h2 : (2 * σ)⁻¹ = (2 : ℝ)⁻¹ * σ⁻¹ := by rw [mul_inv_rev]; ring
  have hle : (2 * σ)⁻¹ ≤ (5 / 6) * σ⁻¹ := by
    rw [h2]; exact mul_le_mul_of_nonneg_right (by norm_num) hσi
  unfold tprR; rw [if_pos h]; unfold fsKinCoeff; rw [max_eq_left]; linarith

/-- The cut-offs `(2(2σ))⁻¹` and `(4σ)⁻¹` of the far branch coincide. -/
lemma two_two_inv (σ : ℝ) : (2 * (2 * σ))⁻¹ = (4 * σ)⁻¹ := by ring

end Work.BoseKinLoc.Assembly
