import Mathlib
import Submission.Work.PARIMPL2.Lavaurs.Defs
import Submission.Work.FlowerGlue2.Defs
import Submission.Work.FlowerGlue2.box_lands_step
import Submission.Work.FlowerGlue2.box_deep_of_transient_bound
import Submission.Work.FatouCoordFix.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `Work.PARIMPL2.Lavaurs.deep_tail_subset_pa` — the deep tail of the `c₀`-chart lies in the petal

In the `c₀`-chart `w₀ = −P.s c₀/(z − z₁)` (`Work.PARIMPL2.w0`) the attracting direction of the
parabolic point `z₁` is `Re (w₀ z) → +∞`.  This file proves that **the deep tail of that chart is
contained in the attracting petal `Pa`** of the flower of `Ft c₀`.

The two hypotheses are exactly the two halves of the delivered repelling-coordinate `Ψ`
(`Work.FatouCoord.ParabolicFlower.Ψ`), which is the inverse of the chart:

* `hRe` — the *far ends* of the repelling half-planes land in the petal
  (this is the delivered field `Ψ_ends`): if `|Im w|` is large (relative to `Re`) then `Ψ w ∈ Pa`;
* `hψ` — on the *remaining* part `|Im w| ≤ Re` of a deep half-plane `{Re w < −Re}`, the
  `w₀`-coordinate of the image `Ψ w` obeys
  `Re (w₀ (Ψ w)) ≤ Re w + C · (1 + log (2 + ‖w‖))`.

The two ingredients combine with the *cover* field
`ParabolicFlower.cover : ∀ R, ∃ r > 0, ∀ z, 0 < ‖z − z₁‖ < r → z ∈ Pa ∨ ∃ w, Re w < −R ∧ Ψ w = z`:

given `z` with `Re (w₀ z)` large, `z` is close to the parabolic point `z₁` (`‖z − z₁‖ = ‖s c₀‖ /
‖w₀ z‖`), hence by `cover` either `z ∈ Pa` already or `z = Ψ w` with `Re w < −Re`.  In the second
case `|Im w| > Re` forces `z ∈ Pa` by `hRe`, while `|Im w| ≤ Re` gives
`Re (w₀ z) = Re (w₀ (Ψ w)) ≤ Re w + C (1 + log (2 + ‖w‖))`, and the right-hand side is *bounded
above uniformly* on that region — `Re w < −Re` with `|Im w| ≤ Re` forces `Re w < 0`,
`|Re w| ≥ Re ≥ 0`, `‖w‖ ≤ √(Re w² + Re²) ≤ 2|Re w|`, and then `−t + C (1 + log (2 + 2t))` is
bounded on `t ≥ 0` by `1 + C + 2C²` (via `log x ≤ 2√x`).  Contradiction.

## Contents

* `Work.PARIMPL2.Lavaurs.neg_t_add_const_mul_log_two_le` — the elementary real bound
  `−t + C (1 + log (2 + 2t)) ≤ 1 + C + 2C²` for `t, C ≥ 0`;
* `Work.PARIMPL2.Lavaurs.exists_bound_log_of_im_le` — its consequence: the map
  `w ↦ Re w + C (1 + log (2 + ‖w‖))` is bounded above on `{Re w < −Re} ∩ {|Im w| ≤ Re}`;
* `Work.PARIMPL2.Lavaurs.deep_tail_subset_pa` — the target theorem.
-/

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

open Classical Filter Set Metric
open scoped Topology

noncomputable section

namespace Work.PARIMPL2.Lavaurs

/-- **Elementary real bound.**  For `C, t ≥ 0`,
`−t + C (1 + log (2 + 2t)) ≤ 1 + C + 2C²`.  With `s = √(2 + 2t)` (so `t = (s² − 2)/2`) and
`log (2 + 2t) ≤ 2s` (`Work.FlowerGlue2.bdtb_log_le_two_sqrt`), the left-hand side is at most
`1 − s²/2 + 2Cs + C ≤ 1 + 2C² + C` because `2C² + s²/2 − 2Cs = (s − 2C)²/2 ≥ 0`. -/
theorem neg_t_add_const_mul_log_two_le {C t : ℝ} (hC : 0 ≤ C) (ht : 0 ≤ t) :
    -t + C * (1 + Real.log (2 + 2 * t)) ≤ 1 + C + 2 * C ^ 2 := by
  have h1 : (1 : ℝ) ≤ 2 + 2 * t := by linarith
  have hlog : Real.log (2 + 2 * t) ≤ 2 * Real.sqrt (2 + 2 * t) :=
    Work.FlowerGlue2.bdtb_log_le_two_sqrt h1
  set s : ℝ := Real.sqrt (2 + 2 * t) with hs
  have hssq : s ^ 2 = 2 + 2 * t := Real.sq_sqrt (by linarith)
  have hmul : C * Real.log (2 + 2 * t) ≤ C * (2 * s) := mul_le_mul_of_nonneg_left hlog hC
  have hsq : 0 ≤ (s - 2 * C) ^ 2 := sq_nonneg _
  nlinarith [hmul, hsq, hssq]

/-- **Uniform boundedness of the shallow-`Im` part of the deep half-plane.**  For `C ≥ 0` the map
`w ↦ Re w + C (1 + log (2 + ‖w‖))` is bounded above on
`{w | Re w < −Re} ∩ {w | |Im w| ≤ Re}`; the region is empty when `Re < 0`.  The bound is
`1 + C + 2C²`, independent of `Re`. -/
theorem exists_bound_log_of_im_le {C : ℝ} (hC : 0 ≤ C) (Re : ℝ) :
    ∃ S : ℝ, ∀ w : ℂ, w.re < -Re → |w.im| ≤ Re →
      w.re + C * (1 + Real.log (2 + ‖w‖)) ≤ S := by
  refine ⟨1 + C + 2 * C ^ 2, ?_⟩
  intro w hwr hwim
  have hRe0 : 0 ≤ Re := le_trans (abs_nonneg w.im) hwim
  have ht : 0 ≤ -w.re := by linarith
  have him2 : w.im ^ 2 ≤ Re ^ 2 := by
    have h := abs_le.mp hwim
    nlinarith [h.1, h.2]
  have hnormle : ‖w‖ ≤ Real.sqrt (w.re ^ 2 + Re ^ 2) := by
    rw [Complex.norm_def, Complex.normSq_apply]
    apply Real.sqrt_le_sqrt
    nlinarith [him2]
  have hsqrtle : Real.sqrt (w.re ^ 2 + Re ^ 2) ≤ 2 * (-w.re) := by
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith [hRe0, hwr]
  have hlogle : Real.log (2 + ‖w‖) ≤ Real.log (2 + 2 * (-w.re)) := by
    apply Real.log_le_log (by positivity)
    linarith
  have hstep : w.re + C * (1 + Real.log (2 + ‖w‖)) ≤
      w.re + C * (1 + Real.log (2 + 2 * (-w.re))) := by
    have h : Real.log (2 + ‖w‖) ≤ Real.log (2 + 2 * (-w.re)) := hlogle
    have := mul_le_mul_of_nonneg_left h hC
    linarith
  have hfin := neg_t_add_const_mul_log_two_le hC ht
  linarith [hstep, hfin]

/-- **The deep tail of the `c₀`-chart is contained in the attracting petal `Pa`.**

Given the far-end membership `hRe` (`Ψ w ∈ Pa` when `|Im w| > Re` and `Re w < −Re`) and the
`w₀`-coordinate estimate `hψ` on the complementary strip `{Re w < −Re} ∩ {|Im w| ≤ Re}`, there is
`M₀` such that every `z` with `Re (w₀ z) > M₀` lies in `fl.Pa`. -/
theorem deep_tail_subset_pa {c₀ : ℂ} {d : Work.EL.RootParabolic c₀} (P : Work.PARIMPL.ParNormal d)
    (fl : Work.FatouCoordFix.ParabolicFlowerFix (Work.PARIMPL.Ft c₀) (Work.PARIMPL.gtc c₀) d.z₁)
    (Re : ℝ) (hRe : ∀ w : ℂ, w.re < -Re → Re < |w.im| → fl.Ψ w ∈ fl.Pa)
    (hψ : ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, w.re < -Re → |w.im| ≤ Re →
      (Work.PARIMPL2.w0 P (fl.Ψ w)).re ≤ w.re + C * (1 + Real.log (2 + ‖w‖))) :
    ∃ M₀ : ℝ, ∀ z : ℂ, M₀ < (Work.PARIMPL2.w0 P z).re → z ∈ fl.Pa := by
  obtain ⟨C, hC0, hψ'⟩ := hψ
  obtain ⟨S, hS⟩ := exists_bound_log_of_im_le hC0 Re
  obtain ⟨rc, hrcpos, hrc⟩ := fl.cover Re
  have hs_ne : P.s c₀ ≠ 0 := P.s_ne c₀ (Metric.mem_ball_self P.hρ₀)
  have hrcne : rc ≠ 0 := ne_of_gt hrcpos
  refine ⟨max (max S (‖P.s c₀‖ / rc + 1)) 1, ?_⟩
  intro z hz
  have hzS : S < (Work.PARIMPL2.w0 P z).re :=
    lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) hz
  have hzsp : ‖P.s c₀‖ / rc + 1 < (Work.PARIMPL2.w0 P z).re :=
    lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) hz
  have hz1 : 1 < (Work.PARIMPL2.w0 P z).re := lt_of_le_of_lt (le_max_right _ _) hz
  have hzpos : 0 < (Work.PARIMPL2.w0 P z).re := by linarith
  have hzne : z ≠ d.z₁ := by
    intro h
    rw [h] at hz1
    simp [Work.PARIMPL2.w0] at hz1
    exact absurd hz1 (by norm_num)
  have hw0norm : ‖Work.PARIMPL2.w0 P z‖ = ‖P.s c₀‖ / ‖z - d.z₁‖ := by
    simp only [Work.PARIMPL2.w0, norm_div, norm_neg]
  have hwnormpos : 0 < ‖Work.PARIMPL2.w0 P z‖ := lt_of_lt_of_le hzpos (Complex.re_le_norm _)
  have hprod : ‖z - d.z₁‖ * ‖Work.PARIMPL2.w0 P z‖ = ‖P.s c₀‖ := by
    rw [hw0norm, mul_comm]
    exact div_mul_cancel₀ _ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hzne))
  have hmul : ‖P.s c₀‖ < rc * ‖Work.PARIMPL2.w0 P z‖ := by
    have h1 : rc * (‖P.s c₀‖ / rc + 1) = ‖P.s c₀‖ + rc := by
      rw [mul_add, mul_one, mul_div_cancel₀ _ hrcne]
    have h2 : rc * (‖P.s c₀‖ / rc + 1) < rc * (Work.PARIMPL2.w0 P z).re :=
      mul_lt_mul_of_pos_left hzsp hrcpos
    have h3 : (Work.PARIMPL2.w0 P z).re ≤ ‖Work.PARIMPL2.w0 P z‖ := Complex.re_le_norm _
    nlinarith [h1, h2, h3]
  have hdist : ‖z - d.z₁‖ < rc := by
    have heq : ‖z - d.z₁‖ = ‖P.s c₀‖ / ‖Work.PARIMPL2.w0 P z‖ := by
      rw [eq_div_iff (ne_of_gt hwnormpos)]
      exact hprod
    rw [heq, div_lt_iff₀ hwnormpos]
    exact hmul
  have hdistpos : 0 < ‖z - d.z₁‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzne)
  rcases hrc z hdistpos hdist with hPa | ⟨w, hwr, hΨw⟩
  · exact hPa
  · by_cases him : Re < |w.im|
    · rw [← hΨw]; exact hRe w hwr him
    · exfalso
      push Not at him
      have hb := hψ' w hwr him
      have hSb := hS w hwr him
      have hzw : Work.PARIMPL2.w0 P (fl.Ψ w) = Work.PARIMPL2.w0 P z := by rw [hΨw]
      rw [hzw] at hb
      linarith [hzS, hb, hSb]

end Work.PARIMPL2.Lavaurs
