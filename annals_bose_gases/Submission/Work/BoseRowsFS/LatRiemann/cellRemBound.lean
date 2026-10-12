import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseRowsFS.LatRiemann

/-- The purely algebraic core of `cellRemBound`: if `q ^ 2 = a ^ 2 + 2 * t + s ^ 2`,
`|t| ≤ a * s` and `s ≤ a / 4` (with `a > 0`), then the second-order remainder of the
expansion of `1/‖·‖²` around `P` is bounded by `(88/9) * s ^ 2 / a ^ 4`.

The proof is the natural two-step chain, with `q² = a² + 2t + s²`:

* `|4t² + 2ts² - a²s²| = |2t(q² - a²) - a²s²| ≤ 4t² + 2|t|s² + a²s² ≤ 5a²s² + 2as³`,
  and `2as³ ≤ (1/2)a²s²` because `s ≤ a/4`; so the numerator is `≤ (11/2)a²s²`;
* `q² ≥ (a - s)² ≥ (9/16)a²` because `t ≥ -as` and `s ≤ a/4`.

Combining, `(11/2)a²s² / ((9/16)a²) = (88/9)s²`, which is the stated bound.  The chain is
crude (the genuinely optimal constant is about `40/9`, approached at `s = a/4`,
`t = -a²/4`), which is why the requested constant `88/9` is available. -/
private lemma cellRemBound_arith {a s t q : ℝ} (ha : 0 < a) (_hs : 0 ≤ s) (hsl : s ≤ a / 4)
    (ht : |t| ≤ a * s) (hq : q ^ 2 = a ^ 2 + 2 * t + s ^ 2) :
    |(2 * t * (q ^ 2 - a ^ 2) - a ^ 2 * s ^ 2) / (a ^ 4 * q ^ 2)|
      ≤ (88 / 9) * s ^ 2 / a ^ 4 := by
  obtain ⟨ht_ge, ht_le⟩ := abs_le.mp ht
  have hsq : (0 : ℝ) ≤ s ^ 2 := sq_nonneg s
  have ht_sq : t ^ 2 ≤ a ^ 2 * s ^ 2 := by
    have h : t ^ 2 ≤ (a * s) ^ 2 := sq_le_sq' ht_ge ht_le
    nlinarith [h]
  have hts : t * s ^ 2 ≤ a * s ^ 3 := by
    have := mul_le_mul_of_nonneg_right ht_le hsq
    nlinarith [this]
  have hts_ge : -(a * s ^ 3) ≤ t * s ^ 2 := by
    have := mul_le_mul_of_nonneg_right ht_ge hsq
    nlinarith [this]
  have hs3 : a * s ^ 3 ≤ (a ^ 2 / 4) * s ^ 2 := by
    have has2 : (0 : ℝ) ≤ a * s ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_left hsl has2
    nlinarith [this]
  have hNle : 4 * t ^ 2 + 2 * t * s ^ 2 - a ^ 2 * s ^ 2 ≤ (11 / 2) * a ^ 2 * s ^ 2 := by
    nlinarith [ht_sq, hts, hs3]
  have hNge : -((11 / 2) * a ^ 2 * s ^ 2) ≤ 4 * t ^ 2 + 2 * t * s ^ 2 - a ^ 2 * s ^ 2 := by
    nlinarith [sq_nonneg t, hts_ge, hs3]
  have hq2 : (9 / 16) * a ^ 2 ≤ q ^ 2 := by nlinarith [hq, ht_ge, hsl, ha]
  have hq2pos : 0 < q ^ 2 := lt_of_lt_of_le (by positivity) hq2
  have hden : 0 < a ^ 4 * q ^ 2 := by positivity
  have ha4 : 0 < a ^ 4 := by positivity
  have hnum : |2 * t * (q ^ 2 - a ^ 2) - a ^ 2 * s ^ 2| ≤ (11 / 2) * a ^ 2 * s ^ 2 := by
    have hqq : 2 * t * (q ^ 2 - a ^ 2) - a ^ 2 * s ^ 2
        = 4 * t ^ 2 + 2 * t * s ^ 2 - a ^ 2 * s ^ 2 := by
      rw [hq]; ring
    rw [hqq]
    exact abs_le.mpr ⟨hNge, hNle⟩
  calc |(2 * t * (q ^ 2 - a ^ 2) - a ^ 2 * s ^ 2) / (a ^ 4 * q ^ 2)|
      = |2 * t * (q ^ 2 - a ^ 2) - a ^ 2 * s ^ 2| / (a ^ 4 * q ^ 2) := by
        rw [abs_div, abs_of_pos hden]
    _ ≤ ((11 / 2) * a ^ 2 * s ^ 2) / (a ^ 4 * q ^ 2) :=
        div_le_div_of_nonneg_right hnum hden.le
    _ ≤ (88 / 9) * s ^ 2 / a ^ 4 := by
        rw [div_le_div_iff₀ hden ha4]
        have hlin : 0 ≤ (88 / 9) * q ^ 2 - (11 / 2) * a ^ 2 := by linarith [hq2]
        have ha4s2 : 0 ≤ a ^ 4 * s ^ 2 := by positivity
        nlinarith [hlin, ha4s2]

theorem cellRemBound {P p : EuclideanSpace ℝ (Fin 3)} {a : ℝ} (ha : a = ‖P‖) (ha0 : 0 < a)
    (hd : ‖p - P‖ ≤ a / 4) :
    |(2 * inner ℝ P (p - P) * (‖p‖ ^ 2 - a ^ 2) - a ^ 2 * ‖p - P‖ ^ 2)
        / (a ^ 4 * ‖p‖ ^ 2)|
      ≤ (88 / 9) * ‖p - P‖ ^ 2 / a ^ 4 := by
  have hq : ‖p‖ ^ 2 = a ^ 2 + 2 * inner ℝ P (p - P) + ‖p - P‖ ^ 2 := by
    have h1 : P + (p - P) = p := by abel
    have h2 := norm_add_sq_real P (p - P)
    rw [h1, ← ha] at h2
    exact h2
  have hinner : |inner ℝ P (p - P)| ≤ a * ‖p - P‖ := by
    have h := abs_real_inner_le_norm P (p - P)
    rwa [← ha] at h
  exact cellRemBound_arith ha0 (norm_nonneg _) hd hinner hq

end Work.BoseRowsFS.LatRiemann
