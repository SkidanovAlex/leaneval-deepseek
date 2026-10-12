import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Submission.Work.SmallBoxA0.KinWitnessDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SmallBoxA0

open MeasureTheory Metric
open scoped ContDiff Topology Real BigOperators ENNReal
open Submission BoseGases
open Work.SmallBoxA0

/-- The derivative of the scaled bump vanishes outside the box `acube s`: for `0 < s`, `2/s < c`
and `z ∉ acube s`, `fderiv ℝ (kwBump c) z = 0`.

HINT.  As in the vanishing lemma `kwBump c z = 0` for `z ∉ acube s`, the hypothesis gives
`1 / (2 * c) < ‖z‖` (`z ∉ acube s` gives a coordinate with `|z m| > s/2` and `|z m| ≤ ‖z‖`, while
`1/(2c) < s/2` follows from `0 < s` and `2/s < c`).  The set
`U := {w : ℝ³ | 1 / (2 * c) < ‖w‖}` is *open* (`isOpen_lt continuous_const continuous_norm`) and
contains `z`, and `kwBump c` vanishes on `U` (`chiBase_eq_zero_of_norm_gt` since
`‖c • w‖ = c ‖w‖ > 1/2`).  Hence `kwBump c =ᶠ[𝓝 z] fun _ => (0 : ℝ)`
(`IsOpen.eventually_mem` + `Filter.EventuallyEq`), and `Filter.EventuallyEq.fderiv_eq` together
with `fderiv_const` yields
`fderiv ℝ (kwBump c) z = fderiv ℝ (Function.const _ (0 : ℝ)) z = 0`. -/
lemma kwFderivZero {s c : ℝ} (hs : 0 < s) (hcs : 2 / s < c) {z : EuclideanSpace ℝ (Fin 3)}
    (hz : z ∉ acube s) : fderiv ℝ (kwBump c) z = 0 := by
  -- `c` is positive because `2 / s > 0`.
  have hc : 0 < c := lt_trans (div_pos two_pos hs) hcs
  -- A coordinate of `z` has modulus `> s / 2`, hence `‖z‖ > s / 2`.
  have hcoord : s / 2 < ‖z‖ := by
    have hcoord' : ∃ m : Fin 3, s / 2 < |z m| := by
      rw [mem_acube_iff] at hz
      push Not at hz
      obtain ⟨m, hm⟩ := hz
      simp only [Set.mem_Icc, not_and_or, not_le] at hm
      refine ⟨m, ?_⟩
      rcases hm with h | h
      · rw [abs_of_neg (by linarith)]
        linarith
      · rw [abs_of_pos (by linarith)]
        exact h
    obtain ⟨m, hm⟩ := hcoord'
    exact lt_of_lt_of_le hm (abs_coord_le_norm z m)
  -- `2 / s < c` and `0 < s` give `1 / (2 * c) < s / 2`.
  have hgt : 1 / (2 * c) < s / 2 := by
    have h2 : (2 : ℝ) < c * s := by
      rw [div_lt_iff₀ hs] at hcs
      exact hcs
    rw [div_lt_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 2)]
    nlinarith
  have hzbig : 1 / (2 * c) < ‖z‖ := lt_trans hgt hcoord
  -- `kwBump c` agrees with the zero function in a neighbourhood of `z`.
  have heq : kwBump c =ᶠ[𝓝 z] Function.const (EuclideanSpace ℝ (Fin 3)) (0 : ℝ) := by
    filter_upwards
      [isOpen_lt continuous_const continuous_norm |>.eventually_mem hzbig] with w hw
    show chiBase (c • w) = 0
    apply chiBase_eq_zero_of_norm_gt
    rw [norm_smul, Real.norm_of_nonneg (le_of_lt hc)]
    have hwc : 1 / (2 * c) < ‖w‖ := hw
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * c)] at hwc
    nlinarith
  calc fderiv ℝ (kwBump c) z
      = fderiv ℝ (Function.const (EuclideanSpace ℝ (Fin 3)) (0 : ℝ)) z := heq.fderiv_eq
    _ = 0 := by simp

end Work.SmallBoxA0
