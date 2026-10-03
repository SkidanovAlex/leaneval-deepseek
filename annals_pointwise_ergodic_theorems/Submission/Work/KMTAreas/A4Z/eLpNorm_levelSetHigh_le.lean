import Mathlib
import Submission.Work.KMTAreas.A4.memLp_two_count_summable_norm_sq
import Submission.Work.KMTAreas.A4.structiiiAux

/-!
# The level-set (`high part`) `ℓᵖ` estimate, for `0 < p < 2`

For `f : ℤ → ℂ` in `ℓ²(ℤ, count)` and `0 < p < 2`, `lam > 0`,

`‖f · 1_{lam < ‖f‖}‖_{ℓ^p} ≤ lam^{1-2/p} ‖f‖_{ℓ²}^{2/p}`.

This is the standard interpolation/layer decomposition estimate: on the level set
`{lam < ‖f‖}` one has `‖f‖^p = ‖f‖^{p-2} ‖f‖^2 ≤ lam^{p-2} ‖f‖^2` (because `p - 2 < 0`),
so `∑ ‖f‖^p 1_{lam<‖f‖} ≤ lam^{p-2} ∑ ‖f‖^2 = lam^{p-2} ‖f‖_2^2`, and taking the `(1/p)`-th
power gives the claim.

The workspace already contains the same statement (`Work.KMTAreas.A4.eLpNorm_indicator_lp_le`,
in `Submission/Work/KMTAreas/A4/structiiiAux.lean`) under the *stronger* hypothesis `1 < p`; the
proof below repeats that argument, which nowhere uses `1 < p`, and therefore applies as soon as
`0 < p` (the hypothesis needed here).
-/

set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Work.KMTAreas.A4Z

/-- **The level-set (truncation) estimate, for `0 < p < 2`.**  If
`eLpNorm g 2 count = ofReal a` with `a ≥ 0`, then the part of `g` above the level `lam > 0`
satisfies the `ℓ^p` bound `‖g · 1_{lam < ‖g‖}‖_p ≤ lam^{1-2/p} a^{2/p}` for every `0 < p < 2`. -/
theorem eLpNorm_indicator_lp_le_of_pos {g : ℤ → ℂ} {p lam a : ℝ} (hp : 0 < p) (hp2 : p < 2)
    (hlam : 0 < lam) (ha : 0 ≤ a)
    (hg : MeasureTheory.eLpNorm g 2 Measure.count = ENNReal.ofReal a) :
    MeasureTheory.eLpNorm (fun x : ℤ => if lam < ‖g x‖ then g x else 0)
        (ENNReal.ofReal p) Measure.count
      ≤ ENNReal.ofReal (lam ^ (1 - 2 / p) * a ^ (2 / p)) := by
  obtain ⟨hsum2, htsum2⟩ := Work.KMTAreas.A4.summable_sq_tsum_eq_of_eLpNorm_two ha hg
  set G : ℤ → ℂ := fun x => if lam < ‖g x‖ then g x else 0 with hG
  have hpt : ∀ x : ℤ, ‖G x‖ ^ p ≤ lam ^ (p - 2) * ‖g x‖ ^ (2 : ℝ) := by
    intro x
    by_cases hx : lam < ‖g x‖
    · rw [hG]
      simp only [hx, if_true]
      have hgx : 0 < ‖g x‖ := lt_trans hlam hx
      have h1 : ‖g x‖ ^ (p - 2) ≤ lam ^ (p - 2) :=
        Real.rpow_le_rpow_of_nonpos hlam (le_of_lt hx) (by linarith)
      calc ‖g x‖ ^ p = ‖g x‖ ^ (p - 2) * ‖g x‖ ^ (2 : ℝ) := by
            rw [← Real.rpow_add hgx]
            norm_num
        _ ≤ lam ^ (p - 2) * ‖g x‖ ^ (2 : ℝ) :=
            mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg (norm_nonneg _) _)
    · rw [hG]
      simp only [hx, if_false, norm_zero, Real.zero_rpow (ne_of_gt hp)]
      exact mul_nonneg (Real.rpow_nonneg hlam.le _) (Real.rpow_nonneg (norm_nonneg _) _)
  have hsum1 : Summable (fun x : ℤ => ‖G x‖ ^ p) :=
    Summable.of_nonneg_of_le (fun x => Real.rpow_nonneg (norm_nonneg _) _) hpt
      (hsum2.mul_left (lam ^ (p - 2)))
  rw [Work.KMTAreas.A4.eLpNorm_count_eq_ofReal_tsum_rpow G hp hsum1]
  refine ENNReal.ofReal_le_ofReal ?_
  have hle : (∑' x : ℤ, ‖G x‖ ^ p) ≤ lam ^ (p - 2) * a ^ (2 : ℝ) := by
    have h1 : (∑' x : ℤ, ‖G x‖ ^ p) ≤ ∑' x : ℤ, lam ^ (p - 2) * ‖g x‖ ^ (2 : ℝ) :=
      Summable.tsum_le_tsum hpt hsum1 (hsum2.mul_left _)
    rw [tsum_mul_left, htsum2] at h1
    rwa [Work.KMTAreas.A4.pow_two_eq a] at h1
  have hnn : (0 : ℝ) ≤ ∑' x : ℤ, ‖G x‖ ^ p := tsum_nonneg fun x =>
    Real.rpow_nonneg (norm_nonneg _) _
  calc (∑' x : ℤ, ‖G x‖ ^ p) ^ (1 / p)
      ≤ (lam ^ (p - 2) * a ^ (2 : ℝ)) ^ (1 / p) :=
        Real.rpow_le_rpow hnn hle (by positivity)
    _ = lam ^ (1 - 2 / p) * a ^ (2 / p) := by
        have key1 : a ^ ((2 : ℝ) * (1 / p)) = (a ^ (2 : ℝ)) ^ (1 / p) :=
          Real.rpow_mul ha 2 (1 / p)
        have key2 : lam ^ ((p - 2) * (1 / p)) = (lam ^ (p - 2)) ^ (1 / p) :=
          Real.rpow_mul hlam.le (p - 2) (1 / p)
        have hp2' : (p - 2) * (1 / p) = 1 - 2 / p := by field_simp
        have hp3' : (2 : ℝ) * (1 / p) = 2 / p := by ring
        rw [Real.mul_rpow (Real.rpow_nonneg hlam.le _) (Real.rpow_nonneg ha _),
          ← key1, ← key2, hp2', hp3']

theorem eLpNorm_levelSetHigh_le {f : ℤ → ℂ} (hf : MeasureTheory.MemLp f 2 MeasureTheory.Measure.count) {p lam : ℝ} (hp : 0 < p) (hp2 : p < 2) (hlam : 0 < lam) : MeasureTheory.eLpNorm (fun x : ℤ => if lam < ‖f x‖ then f x else 0) (ENNReal.ofReal p) MeasureTheory.Measure.count ≤ ENNReal.ofReal (lam ^ (1 - 2 / p) * ((MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count).toReal) ^ (2 / p)) := by
  have ha : 0 ≤ (MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count).toReal :=
    ENNReal.toReal_nonneg
  have hg : MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
      = ENNReal.ofReal ((MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count).toReal) :=
    (ENNReal.ofReal_toReal hf.eLpNorm_ne_top).symm
  exact eLpNorm_indicator_lp_le_of_pos hp hp2 hlam ha hg

end Work.KMTAreas.A4Z
