import Mathlib
import Submission.Work.TMComp.IDSDefs

/-!
# `IDSEqui`: the continuous minorant of the counting condition

`Work.TMComp.shiftCount α θ δ n` counts the `j < n` with `fracDist (θ + jα) < δ`, i.e. the
visits of the orbit `{θ + jα}` to the arc `{fracDist < δ}` of the circle (of measure `2δ`).
The counting lemma `Work.TMComp.IDSEqui.count` needs a *continuous* minorant `minor δ δ'` of
the indicator of that arc, so that Weyl equidistribution in its uniform form
(`Work.TMComp.prove_UniqErg`) can be applied to it.

`ramp δ δ'` is the trapezium profile in the distance variable: it is `1` for `t ≤ δ'`, `0`
for `t ≥ δ`, and linear in between; `minor δ δ' x = ramp δ δ' (fracDist x)`.

Main facts collected here (used by `IDSEqui/rampIntegral.lean` and by `count`):

* `continuous_fracDist` : `fracDist` is continuous (it is `min (fract x) (1 - fract x)`);
* `fracDist_eq_self`, `fracDist_eq_one_sub` : on `[0, 1/2]` and on `[1/2, 1]` it is the
  distance to the nearest *endpoint*;
* `minor_nonneg`, `minor_le_one`, `minor_eq_zero`, `minor_eq_one` : the pointwise bounds;
* `continuous_minor`, `minor_periodic` : what the equidistribution theorem consumes.
-/

noncomputable section

open Set

namespace Work.TMComp.IDSEqui

/-- Trapezium profile in the distance variable: `1` for `t ≤ δ'`, `0` for `t ≥ δ`, and
linear in between.  (For `δ' < δ`; the expression is also meaningful otherwise.) -/
def ramp (δ δ' t : ℝ) : ℝ := max 0 (min 1 ((δ - t) / (δ - δ')))

/-- The continuous `1`-periodic minorant of the indicator of `{fracDist < δ}`. -/
def minor (δ δ' : ℝ) (x : ℝ) : ℝ := ramp δ δ' (Work.TMContract.fracDist x)

/-- `fracDist` is `1`-periodic. -/
lemma fracDist_add_one (x : ℝ) : Work.TMContract.fracDist (x + 1) = Work.TMContract.fracDist x := by
  simp only [Work.TMContract.fracDist]
  rw [round_add_one]
  push_cast
  ring_nf

/-- `fracDist` is continuous. -/
lemma continuous_fracDist : Continuous (Work.TMContract.fracDist) := by
  have hfun : Work.TMContract.fracDist = fun x : ℝ => min (Int.fract x) (1 - Int.fract x) := by
    funext x
    show |x - (round x : ℝ)| = min (Int.fract x) (1 - Int.fract x)
    exact abs_sub_round_eq_min x
  rw [hfun]
  exact ContinuousOn.comp_fract'' (f := fun t : ℝ => min t (1 - t)) (by fun_prop) (by norm_num)

/-- On `[0, 1/2)` the distance to the nearest integer is the distance to `0`. -/
lemma fracDist_eq_self {x : ℝ} (h1 : 0 ≤ x) (h2 : x < 1 / 2) :
    Work.TMContract.fracDist x = x := by
  have hr : round x = 0 := by
    rw [round_eq_zero_iff]
    exact ⟨by linarith, h2⟩
  simp only [Work.TMContract.fracDist, hr, Int.cast_zero, sub_zero, abs_of_nonneg h1]

/-- On `[1/2, 1]` the distance to the nearest integer is the distance to `1`. -/
lemma fracDist_eq_one_sub {x : ℝ} (h1 : 1 / 2 ≤ x) (h2 : x ≤ 1) :
    Work.TMContract.fracDist x = 1 - x := by
  have hr : round x = 1 := by
    rw [round_eq_iff]
    exact ⟨by linarith, by linarith⟩
  simp only [Work.TMContract.fracDist, hr, Int.cast_one,
    abs_of_nonpos (show x - 1 ≤ 0 by linarith)]
  ring

lemma minor_nonneg (δ δ' : ℝ) (x : ℝ) : 0 ≤ minor δ δ' x := le_max_left _ _

lemma minor_le_one (δ δ' : ℝ) (x : ℝ) : minor δ δ' x ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

lemma minor_eq_zero {δ δ' : ℝ} (h : δ' < δ) {x : ℝ} (hx : δ ≤ Work.TMContract.fracDist x) :
    minor δ δ' x = 0 := by
  have hden : (0:ℝ) < δ - δ' := by linarith
  have hq : (δ - Work.TMContract.fracDist x) / (δ - δ') ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) hden.le
  simp only [minor, ramp]
  exact max_eq_left (le_trans (min_le_right _ _) hq)

lemma minor_eq_one {δ δ' : ℝ} (h : δ' < δ) {x : ℝ} (hx : Work.TMContract.fracDist x ≤ δ') :
    minor δ δ' x = 1 := by
  have hden : (0:ℝ) < δ - δ' := by linarith
  have hq : 1 ≤ (δ - Work.TMContract.fracDist x) / (δ - δ') := by
    rw [le_div_iff₀ hden]
    linarith
  simp only [minor, ramp, min_eq_left hq, max_eq_right zero_le_one]

lemma continuous_minor (δ δ' : ℝ) : Continuous (minor δ δ') := by
  have h1 : Continuous fun t : ℝ => ramp δ δ' t := by
    unfold ramp
    fun_prop
  exact h1.comp continuous_fracDist

lemma minor_periodic (δ δ' : ℝ) (x : ℝ) : minor δ δ' (x + 1) = minor δ δ' x := by
  simp only [minor, fracDist_add_one]

end Work.TMComp.IDSEqui
