import Mathlib
import Submission.Work.ZeroDensity.Jutila.LzDiffAux.CzRowAuxDefs

namespace Work.ZeroDensity.Jutila.LzDiffAux

open Finset
open Work.ZeroDensity.Jutila.BzCross

noncomputable section


/-- `|a - b| ≤ |a| + |b|`. -/
lemma abs_sub_le' (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  rw [sub_eq_add_neg]
  calc |a + -b| ≤ |a| + |-b| := abs_add_le a (-b)
    _ = |a| + |b| := by rw [abs_neg]

/-- Monotonicity of the de la Vallée Poussin envelope in the rate. -/
lemma czEps_le_of_le_rate {c₁ c₂ x : ℝ} (h : c₁ ≤ c₂) : czEps c₂ x ≤ czEps c₁ x := by
  unfold czEps
  rw [Real.exp_le_exp]
  have h3 : 0 ≤ Real.sqrt (Real.log x) := Real.sqrt_nonneg _
  nlinarith

/-- `|X_r| ≤ r`, where `X_r = y − r⌊y/r⌋`. -/
lemma rowRem_abs_le {y : ℝ} {r : ℕ} (hy : 0 < y) (hr : 1 ≤ r) (hry : (r : ℝ) ≤ y) :
    |rowRem y r| ≤ (r : ℝ) := by
  have h0 : 0 ≤ rowRem y r := czX_nonneg hy.le hry
  have h1 : rowRem y r < (r : ℝ) := czX_lt hy hr
  rw [abs_of_nonneg h0]
  exact le_of_lt h1

/-- `1 ≤ σ_{-1/2}(t)` for `t ≥ 1`. -/
lemma czSig_one_le {t : ℕ} (ht : 1 ≤ t) : 1 ≤ czSig t := by
  unfold czSig
  have hmem : 1 ∈ t.divisors := by
    rw [Nat.mem_divisors]
    exact ⟨one_dvd t, by omega⟩
  have h1 := Finset.single_le_sum (f := fun d : ℕ => 1 / Real.sqrt (d : ℝ))
    (fun d _ => by positivity) hmem
  simpa using h1

/-- The log-ratio of the row is bounded: `|log(Y/r₁)| ≤ 2` when `r₁ ∈ [Y-1, 2Y]` and `Y ≥ 1`. -/
lemma rowLog_abs_le_two {Y : ℝ} {r1 : ℕ} (hY1 : 1 ≤ Y) (hr1pos : 1 ≤ r1)
    (hr1ge : Y - 1 ≤ (r1 : ℝ)) (hr1le : (r1 : ℝ) ≤ 2 * Y) :
    |Real.log (Y / (r1 : ℝ))| ≤ 2 := by
  have hr1pos' : (0 : ℝ) < (r1 : ℝ) := by exact_mod_cast hr1pos
  have hYpos : 0 < Y := lt_of_lt_of_le one_pos hY1
  have h2 : Y / (r1 : ℝ) ≤ 2 := by
    rw [div_le_iff₀ hr1pos']
    by_cases h : 2 ≤ Y
    · linarith
    · push Not at h
      have : (1 : ℝ) ≤ (r1 : ℝ) := by exact_mod_cast hr1pos
      linarith
  have h1 : (1 : ℝ) / 2 ≤ Y / (r1 : ℝ) := by
    rw [le_div_iff₀ hr1pos']
    linarith
  have hpos : 0 < Y / (r1 : ℝ) := div_pos hYpos hr1pos'
  have hlog2 : Real.log (2 : ℝ) ≤ 2 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hloghalf : -(2 : ℝ) ≤ Real.log (1 / 2 : ℝ) := by
    rw [one_div, Real.log_inv]
    have h := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
    linarith
  rw [abs_le]
  constructor
  · have := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 2) h1
    linarith
  · have := Real.log_le_log hpos h2
    linarith

/-- `kap 1 = 1`. -/
lemma kap_one : kap 1 = 1 := by
  unfold kap
  simp only [Nat.primeFactors_one, Finset.prod_empty]

/-- `rowCoef t 1 = 1`. -/
lemma rowCoef_one (t : ℕ) : rowCoef t 1 = 1 := by
  unfold rowCoef
  rw [if_pos (Nat.coprime_one_left t), ArithmeticFunction.moebius_apply_one, kap_one]
  norm_num

/-- The `(q,t)`-row of `czRI` factors through `rowMain`. -/
lemma czRowSum_eq (w y : ℝ) (N q t : ℕ) :
    czRowSum w y N q t
      = ((t : ℝ) / kap t) * ((ArithmeticFunction.moebius t : ℤ) : ℝ)
          * rowMain w y t (min (czR w N q) (czD w y t)) := by
  rw [czRowSum, rowMain, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  unfold czMM rowCoef
  by_cases hc : Nat.Coprime r t
  · rw [if_pos hc, if_pos hc]
    ring
  · rw [if_neg hc, if_neg hc]
    ring


/-- `rowMain w y t 1 = ⌊y⌋·czFI w y 1 t`. -/
lemma rowMain_one (w y : ℝ) (t : ℕ) :
    rowMain w y t 1 = (⌊y⌋₊ : ℝ) * czFI w y 1 t := by
  rw [rowMain, Finset.Icc_self, Finset.sum_singleton, rowCoef_one]
  have hfl : ⌊y / ((1 : ℕ) : ℝ)⌋₊ = ⌊y⌋₊ := by
    rw [Nat.cast_one, div_one]
  rw [hfl]
  ring


/-- Triangle inequality for the five terms of the row decomposition. -/
lemma abs_row_tri {y e1 e2 e3 e4 e5 : ℝ} :
    |y * (-e1 + e2 + e3 + e4) - e5| ≤ |y * e1| + |y * e2| + |y * e3| + |y * e4| + |e5| := by
  have hshape : y * (-e1 + e2 + e3 + e4) - e5
      = -(y * e1) + (y * e2) + (y * e3) + (y * e4) - e5 := by ring
  rw [hshape]
  have h1 : |-(y * e1) + (y * e2) + (y * e3) + (y * e4) - e5|
      ≤ |-(y * e1) + (y * e2) + (y * e3) + (y * e4)| + |e5| := abs_sub_le' _ _
  have h2 : |-(y * e1) + (y * e2) + (y * e3) + (y * e4)|
      ≤ |-(y * e1) + (y * e2) + (y * e3)| + |y * e4| := abs_add_le _ _
  have h3 : |-(y * e1) + (y * e2) + (y * e3)| ≤ |-(y * e1) + (y * e2)| + |y * e3| := abs_add_le _ _
  have h4 : |-(y * e1) + (y * e2)| ≤ |-(y * e1)| + |y * e2| := abs_add_le _ _
  rw [abs_neg] at h4
  linarith [abs_nonneg (y * e1), abs_nonneg (y * e2), abs_nonneg (y * e3), abs_nonneg (y * e4),
    abs_nonneg e5]

end

end Work.ZeroDensity.Jutila.LzDiffAux
