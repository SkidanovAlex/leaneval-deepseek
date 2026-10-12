import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.PCFU.coulombDual_W1_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.chiScale_mul_boxRestrictR_kcInsN`

The box window `chiScale ℓ` kills the difference between a state `Φ` and its box restriction
`boxRestrictR ℓ Φ = Φ · 1_{abox (m+1) ℓ}`, **at the one-slot insertion points** `kcInsN m i (u, r)`
with `r` already in the smaller box `abox m ℓ`.

Indeed, write `x := kcInsN m i (u, r)`.  Two cases:

* `x ∈ abox (m + 1) ℓ`: then the indicator is `1` and `boxRestrictR ℓ Φ x = Φ x`.
* `x ∉ abox (m + 1) ℓ`: the coordinates `x (i.succAbove j) = r j` all lie in `acube ℓ` (`hr`), so
  the offending coordinate must be `i`, where `x i = u`; hence `u ∉ acube ℓ`, and the support of
  `chiScale ℓ` (contained in `acube ℓ`) gives `chiScale ℓ u = 0`, so both sides vanish.

Everything below is `sorry`-free.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock.PCFU

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

set_option linter.unusedVariables false

open Submission.BoseGases

/-- `chiScale ℓ` vanishes off the centred cube `acube ℓ`. -/
lemma chiScale_eq_zero_of_not_mem_acube' {ℓ : ℝ} (hℓ : 0 < ℓ) {z : Ω}
    (hz : z ∉ Submission.BoseGases.acube ℓ) : Submission.BoseGases.chiScale ℓ z = 0 := by
  by_contra h
  exact hz (Submission.BoseGases.mem_acube_of_norm_le hℓ.le
    (Submission.BoseGases.chiScale_support_le hℓ h))

/-- **The `kcInsN`-bookkeeping of the box restriction.**  For `r ∈ abox m ℓ` and any one-particle
position `u`, the box window multiplies the difference of `boxRestrictR ℓ Φ` and `Φ` at the
insertion point `kcInsN m i (u, r)` to zero. -/
theorem chiScale_mul_boxRestrictR_kcInsN {m : ℕ} (i : Fin (m + 1)) {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Φ : Submission.BoseGases.X (m + 1) → ℝ} {r : Submission.BoseGases.X m}
    (hr : r ∈ Submission.BoseGases.abox m ℓ) (u : EuclideanSpace ℝ (Fin 3)) :
    Submission.BoseGases.chiScale ℓ u
        * Work.BoseBoxFock.boxRestrictR ℓ Φ (Submission.BoseGases.kcInsN m i (u, r))
      = Submission.BoseGases.chiScale ℓ u * Φ (Submission.BoseGases.kcInsN m i (u, r)) := by
  by_cases hx : Submission.BoseGases.kcInsN m i (u, r) ∈ Submission.BoseGases.abox (m + 1) ℓ
  · have h : Work.BoseBoxFock.boxRestrictR ℓ Φ (Submission.BoseGases.kcInsN m i (u, r))
        = Φ (Submission.BoseGases.kcInsN m i (u, r)) := by
      simp only [Work.BoseBoxFock.boxRestrictR]
      rw [Set.indicator_of_mem hx, mul_one]
    rw [h]
  · -- off the big box the offending coordinate is the inserted one, so `u` is off the cube
    have hu : u ∉ Submission.BoseGases.acube ℓ := by
      intro hu
      refine hx ?_
      intro j
      by_cases hj : j = i
      · subst hj
        rw [Submission.BoseGases.kc_insN_apply_same]
        exact hu
      · obtain ⟨j', rfl⟩ := Fin.exists_succAbove_eq hj
        rw [Submission.BoseGases.kc_insN_apply_succ]
        exact hr j'
    have hchi : Submission.BoseGases.chiScale ℓ u = 0 :=
      chiScale_eq_zero_of_not_mem_acube' hℓ hu
    have h0 : Work.BoseBoxFock.boxRestrictR ℓ Φ (Submission.BoseGases.kcInsN m i (u, r)) = 0 := by
      simp only [Work.BoseBoxFock.boxRestrictR]
      rw [Set.indicator_of_notMem hx, mul_zero]
    rw [h0, mul_zero, hchi, zero_mul]

end Work.BoseBoxFock.PCFU
