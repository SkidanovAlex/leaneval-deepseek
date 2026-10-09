import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Ultra
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.Analysis.Normed

/-- In an ultrametric normed additive group, if `‖y‖ < ‖x‖` then `‖x + y‖ = ‖x‖`. -/
private lemma norm_add_eq_of_norm_lt {S : Type*} [SeminormedAddGroup S] [IsUltrametricDist S]
    {x y : S} (h : ‖y‖ < ‖x‖) : ‖x + y‖ = ‖x‖ := by
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (ne_of_gt h), max_eq_left h.le]

/-- In an ultrametric normed additive group, if `‖y‖ < ‖x‖` then `‖x - y‖ = ‖x‖`. -/
private lemma norm_sub_eq_of_norm_lt {S : Type*} [SeminormedAddGroup S] [IsUltrametricDist S]
    {x y : S} (h : ‖y‖ < ‖x‖) : ‖x - y‖ = ‖x‖ := by
  have h' : ‖-y‖ < ‖x‖ := by simpa using h
  simpa only [sub_eq_add_neg] using norm_add_eq_of_norm_lt (x := x) (y := -y) h'

lemma norm_sub_eq_of_close {L : Type*} [NormedField L] [IsUltrametricDist L]
    {α α' β β' : L} {δ : ℝ} (hδ : δ ≤ ‖α - α'‖)
    (h1 : ‖α - β‖ < δ) (h2 : ‖α' - β'‖ < δ) :
    ‖β - β'‖ = ‖α - α'‖ := by
  have key : β - β' = (α - α') - ((α - β) - (α' - β')) := by ring
  rw [key]
  refine norm_sub_eq_of_norm_lt ?_
  have hB : ‖(α - β) - (α' - β')‖ ≤ max ‖α - β‖ ‖α' - β'‖ := by
    simpa only [sub_eq_add_neg, norm_neg] using
      (IsUltrametricDist.norm_add_le_max (α - β) (-(α' - β')))
  exact hB.trans_lt ((max_lt h1 h2).trans_le hδ)

end Commons.Analysis.Normed