import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace Commons.Probability.Levy

/-- Square the level condition `τ ≤ C·√(1−s)/√w` (all quantities nonnegative, `s ≤ 1`)
to get `s ≤ 1 − w·τ²/C²`. -/
private lemma sub_level_le {C w τ s : ℝ} (hC : 0 < C) (hw : 0 < w) (hτ : 0 ≤ τ)
    (hs1 : s ≤ 1) (h : τ ≤ C * Real.sqrt (1 - s) / Real.sqrt w) :
    s ≤ 1 - w * τ ^ 2 / C ^ 2 := by
  have hsqrtw : 0 < Real.sqrt w := Real.sqrt_pos.mpr hw
  have h1s : 0 ≤ 1 - s := by linarith
  have hnonneg : 0 ≤ C * Real.sqrt (1 - s) / Real.sqrt w := by
    exact div_nonneg (mul_nonneg (le_of_lt hC) (Real.sqrt_nonneg (1 - s))) (le_of_lt hsqrtw)
  have hsq : τ ^ 2 ≤ (C * Real.sqrt (1 - s) / Real.sqrt w) ^ 2 := by
    exact sq_le_sq.mpr (by
      rw [abs_of_nonneg hτ, abs_of_nonneg hnonneg]
      exact h)
  have hsq' : (C * Real.sqrt (1 - s) / Real.sqrt w) ^ 2 = C ^ 2 * (1 - s) / w := by
    calc
      (C * Real.sqrt (1 - s) / Real.sqrt w) ^ 2 = (C * Real.sqrt (1 - s)) ^ 2 / (Real.sqrt w) ^ 2 := by ring
      _ = (C ^ 2 * (Real.sqrt (1 - s)) ^ 2) / (Real.sqrt w) ^ 2 := by ring
      _ = C ^ 2 * (1 - s) / w := by rw [Real.sq_sqrt h1s, Real.sq_sqrt (le_of_lt hw)]
  have hmain : τ ^ 2 ≤ C ^ 2 * (1 - s) / w := by
    calc
      τ ^ 2 ≤ (C * Real.sqrt (1 - s) / Real.sqrt w) ^ 2 := hsq
      _ = C ^ 2 * (1 - s) / w := hsq'
  have hwτ : w * τ ^ 2 ≤ C ^ 2 * (1 - s) := by
    have htmp : τ ^ 2 * w ≤ C ^ 2 * (1 - s) := (le_div_iff₀ hw).mp hmain
    nlinarith
  have hC2 : 0 < C ^ 2 := pow_pos hC 2
  have hdiv : w * τ ^ 2 / C ^ 2 ≤ 1 - s := by
    rw [div_le_iff₀ hC2]
    nlinarith [hwτ]
  linarith

/-- `toReal` of the truncated interval length `1 − x` is at most `exp(−x)`
(the interval volume bound used below). -/
private lemma ofReal_sub_one_toReal_le_exp_neg (x : ℝ) :
    (ENNReal.ofReal (1 - x)).toReal ≤ Real.exp (-x) := by
  by_cases hx : 0 ≤ 1 - x
  · rw [ENNReal.toReal_ofReal hx]
    exact Real.one_sub_le_exp_neg x
  · have hxneg : 1 - x < 0 := lt_of_not_ge hx
    have hz : ENNReal.ofReal (1 - x) = 0 := ENNReal.ofReal_eq_zero.mpr (le_of_lt hxneg)
    rw [hz]
    simpa using Real.exp_nonneg (-x)

/-- Volume of the level set `{s ∈ [0,1] : τ ≤ levelB(s)}` (where `levelB` is either
`C·√(1−s)/√w` or the constant `2`) is bounded by `exp(−w·τ²/C²)`.

* For `0 < w` the level set is contained in `[0, 1 − w·τ²/C²]`, whose length is at most
  `exp(−w·τ²/C²)` (`1 − x ≤ exp(−x)`).
* For `w ≤ 0` the right-hand side is at least `exp(0) = 1`, while the level set lies in `[0,1]`.
-/
lemma levelB_vol_le {w C τ : ℝ} (hCpos : 0 < C) (hτ : 0 ≤ τ) :
    (volume ({s : ℝ | τ ≤ (fun s : ℝ => if s ∈ Set.Icc (0 : ℝ) 1 then (if 0 < w then C * Real.sqrt (1 - s) / Real.sqrt w else 2) else 0) s} ∩ Set.Icc (0 : ℝ) 1)).toReal ≤
      Real.exp (-(w * τ ^ 2 / C ^ 2)) := by
  by_cases hw : 0 < w
  · -- case 0 < w
    let x : ℝ := w * τ ^ 2 / C ^ 2
    let B : ℝ → ℝ := fun s : ℝ => if s ∈ Set.Icc (0 : ℝ) 1 then (if 0 < w then C * Real.sqrt (1 - s) / Real.sqrt w else 2) else 0
    let A : Set ℝ := {s : ℝ | τ ≤ B s} ∩ Set.Icc (0 : ℝ) 1
    change (volume A).toReal ≤ Real.exp (-x)
    have hA_sub : A ⊆ Set.Icc (0 : ℝ) (1 - x) := by
      intro s hs
      have hsτ : τ ≤ B s := by simpa using hs.1
      have hsI : s ∈ Set.Icc (0 : ℝ) 1 := hs.2
      have hs1 : s ≤ 1 := (Set.mem_Icc.mp hsI).2
      constructor
      · exact (Set.mem_Icc.mp hsI).1
      · have hBval : B s = C * Real.sqrt (1 - s) / Real.sqrt w := by
          dsimp [B]
          rw [if_pos hsI, if_pos hw]
        have hlevel : τ ≤ C * Real.sqrt (1 - s) / Real.sqrt w := by
          rw [hBval] at hsτ
          exact hsτ
        exact sub_level_le hCpos hw hτ hs1 hlevel
    have hA01 : A ⊆ Set.Icc (0 : ℝ) 1 := by
      intro s hs
      exact hs.2
    have hIccTop : volume (Set.Icc (0 : ℝ) 1) ≠ ∞ := by
      rw [Real.volume_Icc]
      exact ENNReal.ofReal_lt_top.ne
    have hBtop : volume (Set.Icc (0 : ℝ) (1 - x)) ≠ ∞ := by
      rw [Real.volume_Icc]
      exact ENNReal.ofReal_lt_top.ne
    have hAtop : volume A ≠ ∞ := by
      exact ne_of_lt (measure_lt_top_of_subset hA01 hIccTop)
    have hmono : (volume A).toReal ≤ (volume (Set.Icc (0 : ℝ) (1 - x))).toReal := by
      exact (ENNReal.toReal_le_toReal hAtop hBtop).mpr (measure_mono hA_sub)
    calc
      (volume A).toReal ≤ (volume (Set.Icc (0 : ℝ) (1 - x))).toReal := hmono
      _ = (ENNReal.ofReal (1 - x)).toReal := by
            rw [Real.volume_Icc]
            simp
      _ ≤ Real.exp (-x) := ofReal_sub_one_toReal_le_exp_neg x
  · -- case w ≤ 0
    let A : Set ℝ := {s : ℝ | τ ≤ (fun s : ℝ => if s ∈ Set.Icc (0 : ℝ) 1 then (if 0 < w then C * Real.sqrt (1 - s) / Real.sqrt w else 2) else 0) s} ∩ Set.Icc (0 : ℝ) 1
    change (volume A).toReal ≤ Real.exp (-(w * τ ^ 2 / C ^ 2))
    have hw0 : w ≤ 0 := le_of_not_gt hw
    have harg : 0 ≤ -(w * τ ^ 2 / C ^ 2) := by
      have hC2 : 0 < C ^ 2 := pow_pos hCpos 2
      have hτ2 : 0 ≤ τ ^ 2 := sq_nonneg τ
      have hprod : w * τ ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hw0 hτ2
      have hdiv : w * τ ^ 2 / C ^ 2 ≤ 0 := by
        rw [div_le_iff₀ hC2]
        simpa using hprod
      linarith
    have hA01 : A ⊆ Set.Icc (0 : ℝ) 1 := by
      intro s hs
      exact hs.2
    have hIccTop : volume (Set.Icc (0 : ℝ) 1) ≠ ∞ := by
      rw [Real.volume_Icc]
      exact ENNReal.ofReal_lt_top.ne
    have hAtop : volume A ≠ ∞ := by
      exact ne_of_lt (measure_lt_top_of_subset hA01 hIccTop)
    have hmono : (volume A).toReal ≤ (volume (Set.Icc (0 : ℝ) 1)).toReal := by
      exact (ENNReal.toReal_le_toReal hAtop hIccTop).mpr (measure_mono hA01)
    calc
      (volume A).toReal ≤ (volume (Set.Icc (0 : ℝ) 1)).toReal := hmono
      _ = 1 := by
            rw [Real.volume_Icc]
            norm_num
      _ ≤ Real.exp (-(w * τ ^ 2 / C ^ 2)) := by
            simpa [Real.exp_zero] using (Real.exp_le_exp).mpr harg

end Commons.Probability.Levy