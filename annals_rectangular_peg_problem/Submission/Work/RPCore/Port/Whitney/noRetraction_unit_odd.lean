import Mathlib
import Submission.Work.RPCore.Port.PushDisc.degreeFunction

/-!
# No continuous retraction of the unit ball onto the unit sphere in odd dimensions

For odd `d` there is no continuous map `F : ℝ^d → ℝ^d` which maps the whole unit ball into the
unit sphere and fixes the unit sphere pointwise.

## Proof

Such an `F` would give a continuous sphere-valued homotopy from the identity to the antipodal map
of the unit sphere: the clamped straight-line family
`p ↦ -F (σ p.1 • p.2)`, `σ t = min 1 (max (-1) (2 * t - 1))`,
is sphere-valued (because `‖σ t‖ ≤ 1` on the unit sphere), equals the identity at `t = 0`
(because `σ 0 = -1` and `F (-x) = -x`) and the antipodal map at `t = 1` (because `σ 1 = 1` and
`F x = x`).  This contradicts `Work.RPCore.Port.PushDisc.no_continuous_homotopy_of_odd`: for odd `d` the
identity and the antipodal map of the unit sphere of `ℝ^d` are not homotopic.
-/

namespace Work.RPCore.Port.Whitney

open scoped Topology

theorem noRetraction_unit_odd {d : ℕ} (hodd : Odd d) :
    ¬ ∃ F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d),
        Continuous F ∧ (∀ x, ‖x‖ = 1 → F x = x) ∧ (∀ x, ‖x‖ ≤ 1 → ‖F x‖ = 1) := by
  rintro ⟨F, hFc, hFx, hFn⟩
  have hσc : Continuous fun t : ℝ => min 1 (max (-1) (2 * t - 1)) :=
    continuous_const.min
      (continuous_const.max ((continuous_const.mul continuous_id).sub continuous_const))
  have hσ : ∀ t : ℝ, |min 1 (max (-1) (2 * t - 1))| ≤ 1 := by
    intro t
    rw [abs_le]
    exact ⟨le_min (by norm_num) (le_max_left _ _), min_le_left _ _⟩
  refine Work.RPCore.Port.PushDisc.no_continuous_homotopy_of_odd hodd
    ⟨fun p => -F ((min 1 (max (-1) (2 * p.1 - 1))) • p.2), ?_, ?_, ?_, ?_⟩
  · exact (hFc.comp ((hσc.comp continuous_fst).smul continuous_snd)).neg
  · intro x hx
    show -F ((min 1 (max (-1) (2 * (0:ℝ) - 1))) • x) = x
    have h : (min 1 (max (-1) (2 * (0:ℝ) - 1))) = -1 := by norm_num
    rw [h, neg_one_smul, hFx (-x) (by rw [norm_neg]; exact hx), neg_neg]
  · intro x hx
    show -F ((min 1 (max (-1) (2 * (1:ℝ) - 1))) • x) = -x
    have h : (min 1 (max (-1) (2 * (1:ℝ) - 1))) = 1 := by norm_num
    rw [h, one_smul, hFx x hx]
  · intro t x hx
    show ‖-F ((min 1 (max (-1) (2 * t - 1))) • x)‖ = 1
    rw [norm_neg]
    refine hFn _ ?_
    rw [norm_smul, Real.norm_eq_abs, hx, mul_one]
    exact hσ t

end Work.RPCore.Port.Whitney
