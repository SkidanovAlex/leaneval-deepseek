/-
# `Work.FTS.PhiStar.FlatWAux.MomentChiaAux.CoefSummable`

Summability of the resummed angular coefficients `bco ψ j m = bmode m ψ · (lam m)^{-1}^j`
with the two polynomial weights needed by the eigenfunction-series calculus
(`MomentChiaAux/SeriesOde.lean`).

Given the mode decay `|bmode m ψ| ≤ C / (lam m · √(2m+1))` (`hdec`) one has, for `m ≥ 1`,

  `|bco ψ j m| ≤ C / (lam m^{j+1} · √(2m+1))`,

because `(lam m)^{-1}^j = (lam m^j)^{-1}`.  Since `(m+1)² ≤ lam m` for `m ≥ 1` and `j ≥ 1`,
`lam m^{j+1} ≥ (m+1)⁴`, so

  `|bco ψ j m| (m+1)² ≤ C (m+1)²/lam m^{j+1} ≤ C (m+1)²/(m+1)⁴ = C/(m+1)²`,

while

  `|bco ψ j m · lam m| (m+1) ≤ C (m+1)/lam m^j/√(2m+1) ≤ C (m+1)/(m+1)²√(m+1) = C/(m+1)^{3/2}`.

Both are summable.  Rather than compare with a shifted `p`-series directly, the comparison is
made against the (already proved) summable series `m ↦ (2m+1)/(lam m · √(2m+1))` of
`WtDerivAux/summable_lam_sqrt.lean`, which has exactly the decay `(m+1)^{-3/2}` and dominates
both bounds:

  `(m+1)²/(lam m^{j+1} √(2m+1)) ≤ (2m+1)/(lam m √(2m+1))`   was  `(m+1)² ≤ (2m+1) lam m^j`,

  `(m+1)/(lam m^j √(2m+1)) ≤ (2m+1)/(lam m √(2m+1))`       was  `(m+1) lam m ≤ (2m+1) lam m^j`,

both immediate from `(m+1)² ≤ lam m ≤ lam m^j` and `m+1 ≤ 2m+1`.  The `m = 0` term vanishes
because `bco ψ j 0 = 0` for `j ≥ 1`.
-/
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Tactic.NormNum.RealSqrt
import Submission.Work.FTS.PhiStar.FlatWAux.MomentChiaAux.Defs
import Submission.Work.FTS.PhiStar.FlatWAux.WtDerivAux.summable_lam_sqrt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.FlatWAux.MomentChiaAux

theorem CoefSummable (ψ : ℝ → ℝ)
    (hdec : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
      |Work.FTS.PhiStar.Series.bmode m ψ|
        ≤ C / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
    (j : ℕ) (hj : 1 ≤ j) :
    Summable (fun m : ℕ => |Work.FTS.PhiStar.FlatWAux.MomentChiaAux.bco ψ j m|
        * ((m : ℝ) + 1) ^ 2) ∧
      Summable (fun m : ℕ => |Work.FTS.PhiStar.FlatWAux.MomentChiaAux.bco ψ j m
          * Work.FTS.PhiStar.Gegenbauer.lam m| * ((m : ℝ) + 1)) := by
  obtain ⟨C, hCpos, hdec'⟩ := hdec
  -- the summable majorant `m ↦ (2m+1)/(λ_m √(2m+1))`, of decay `(m+1)^{-3/2}`
  have hG := Work.FTS.PhiStar.FlatWAux.WtDerivAux.summable_lam_sqrt
  -- per-term comparison for `m ≥ 1`
  have key : ∀ m : ℕ, 1 ≤ m →
      |bco ψ j m| * ((m : ℝ) + 1) ^ 2
          ≤ C * ((2 * (m : ℝ) + 1)
              / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))) ∧
      |bco ψ j m * Work.FTS.PhiStar.Gegenbauer.lam m| * ((m : ℝ) + 1)
          ≤ C * ((2 * (m : ℝ) + 1)
              / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))) := by
    intro m hm
    have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hLpos : 0 < Work.FTS.PhiStar.Gegenbauer.lam m := by
      rw [Work.FTS.PhiStar.Gegenbauer.lam]; nlinarith
    have hLge1 : 1 ≤ Work.FTS.PhiStar.Gegenbauer.lam m := by
      rw [Work.FTS.PhiStar.Gegenbauer.lam]; nlinarith
    have hLx2 : ((m : ℝ) + 1) ^ 2 ≤ Work.FTS.PhiStar.Gegenbauer.lam m := by
      rw [Work.FTS.PhiStar.Gegenbauer.lam]; nlinarith
    have hLle : Work.FTS.PhiStar.Gegenbauer.lam m
        ≤ (Work.FTS.PhiStar.Gegenbauer.lam m) ^ j := by
      simpa using pow_le_pow_right₀ hLge1 hj
    have hs_pos : 0 < Real.sqrt (2 * (m : ℝ) + 1) := Real.sqrt_pos.mpr (by linarith)
    have hden1 : 0 < Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1) :=
      mul_pos hLpos hs_pos
    have hden2 : 0 < Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)
        * (Work.FTS.PhiStar.Gegenbauer.lam m) ^ j :=
      mul_pos hden1 (pow_pos hLpos j)
    have hb := hdec' m hm
    -- `bco` as an explicit product, using `λ_m > 0`
    have hbco : |bco ψ j m| = |Work.FTS.PhiStar.Series.bmode m ψ|
        * ((Work.FTS.PhiStar.Gegenbauer.lam m) ^ j)⁻¹ := by
      rw [bco, abs_mul, abs_pow, abs_inv, abs_of_pos hLpos, inv_pow]
    have hbco_le : |bco ψ j m| ≤ C / (Work.FTS.PhiStar.Gegenbauer.lam m
        * Real.sqrt (2 * (m : ℝ) + 1) * (Work.FTS.PhiStar.Gegenbauer.lam m) ^ j) := by
      rw [hbco]
      calc |Work.FTS.PhiStar.Series.bmode m ψ| * ((Work.FTS.PhiStar.Gegenbauer.lam m) ^ j)⁻¹
          ≤ C / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))
              * ((Work.FTS.PhiStar.Gegenbauer.lam m) ^ j)⁻¹ :=
            mul_le_mul_of_nonneg_right hb (by positivity)
        _ = C / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)
              * (Work.FTS.PhiStar.Gegenbauer.lam m) ^ j) := by
            rw [inv_eq_one_div, div_mul_div_comm, mul_one]
    -- the two core inequalities `(m+1)² ≤ (2m+1)λ^j` and `(m+1)λ ≤ (2m+1)λ^j`
    have hcore : ((m : ℝ) + 1) ^ 2
        ≤ (2 * (m : ℝ) + 1) * (Work.FTS.PhiStar.Gegenbauer.lam m) ^ j := by
      have h3 : (1 : ℝ) ≤ 2 * (m : ℝ) + 1 := by linarith
      nlinarith [hLx2, hLle, h3, pow_pos hLpos j]
    have hcore2 : ((m : ℝ) + 1) * Work.FTS.PhiStar.Gegenbauer.lam m
        ≤ (2 * (m : ℝ) + 1) * (Work.FTS.PhiStar.Gegenbauer.lam m) ^ j := by
      have h3 : ((m : ℝ) + 1) ≤ 2 * (m : ℝ) + 1 := by linarith
      nlinarith [hLx2, hLle, h3, pow_pos hLpos j, hLpos]
    have hmul : (2 * (m : ℝ) + 1)
          / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))
        * (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)
            * (Work.FTS.PhiStar.Gegenbauer.lam m) ^ j)
        = (2 * (m : ℝ) + 1) * (Work.FTS.PhiStar.Gegenbauer.lam m) ^ j := by
      rw [div_mul_eq_mul_div, mul_div_assoc,
        mul_div_cancel_left₀ _ (ne_of_gt hden1)]
    have hfrac : ((m : ℝ) + 1) ^ 2 / (Work.FTS.PhiStar.Gegenbauer.lam m
          * Real.sqrt (2 * (m : ℝ) + 1) * (Work.FTS.PhiStar.Gegenbauer.lam m) ^ j)
        ≤ (2 * (m : ℝ) + 1)
          / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)) := by
      rw [div_le_iff₀ hden2, hmul]
      exact hcore
    have hfrac2 : ((m : ℝ) + 1) * Work.FTS.PhiStar.Gegenbauer.lam m
          / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)
              * (Work.FTS.PhiStar.Gegenbauer.lam m) ^ j)
        ≤ (2 * (m : ℝ) + 1)
          / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)) := by
      rw [div_le_iff₀ hden2, hmul]
      exact hcore2
    have hexpr : C / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)
          * (Work.FTS.PhiStar.Gegenbauer.lam m) ^ j) * ((m : ℝ) + 1) ^ 2
        = C * (((m : ℝ) + 1) ^ 2 / (Work.FTS.PhiStar.Gegenbauer.lam m
            * Real.sqrt (2 * (m : ℝ) + 1) * (Work.FTS.PhiStar.Gegenbauer.lam m) ^ j)) := by
      rw [div_eq_mul_inv, mul_assoc, inv_mul_eq_div]
    have hexpr2 : C / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)
          * (Work.FTS.PhiStar.Gegenbauer.lam m) ^ j)
          * Work.FTS.PhiStar.Gegenbauer.lam m * ((m : ℝ) + 1)
        = C * (((m : ℝ) + 1) * Work.FTS.PhiStar.Gegenbauer.lam m
            / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)
                * (Work.FTS.PhiStar.Gegenbauer.lam m) ^ j)) := by
      field_simp
    constructor
    · calc |bco ψ j m| * ((m : ℝ) + 1) ^ 2
          ≤ C / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)
              * (Work.FTS.PhiStar.Gegenbauer.lam m) ^ j) * ((m : ℝ) + 1) ^ 2 :=
            mul_le_mul_of_nonneg_right hbco_le (by positivity)
        _ = C * (((m : ℝ) + 1) ^ 2 / (Work.FTS.PhiStar.Gegenbauer.lam m
              * Real.sqrt (2 * (m : ℝ) + 1) * (Work.FTS.PhiStar.Gegenbauer.lam m) ^ j)) :=
            hexpr
        _ ≤ C * ((2 * (m : ℝ) + 1) / (Work.FTS.PhiStar.Gegenbauer.lam m
              * Real.sqrt (2 * (m : ℝ) + 1))) := mul_le_mul_of_nonneg_left hfrac hCpos.le
    · calc |bco ψ j m * Work.FTS.PhiStar.Gegenbauer.lam m| * ((m : ℝ) + 1)
          = |bco ψ j m| * Work.FTS.PhiStar.Gegenbauer.lam m * ((m : ℝ) + 1) := by
            rw [abs_mul, abs_of_pos hLpos]
        _ ≤ C / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)
              * (Work.FTS.PhiStar.Gegenbauer.lam m) ^ j)
              * Work.FTS.PhiStar.Gegenbauer.lam m * ((m : ℝ) + 1) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hbco_le hLpos.le)
              (by positivity)
        _ = C * (((m : ℝ) + 1) * Work.FTS.PhiStar.Gegenbauer.lam m
              / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)
                  * (Work.FTS.PhiStar.Gegenbauer.lam m) ^ j)) := hexpr2
        _ ≤ C * ((2 * (m : ℝ) + 1) / (Work.FTS.PhiStar.Gegenbauer.lam m
              * Real.sqrt (2 * (m : ℝ) + 1))) := mul_le_mul_of_nonneg_left hfrac2 hCpos.le
  -- the `m = 0` term of the majorant vanishes (`lam 0 = 0`)
  have hG0 : (2 * ((0 : ℕ) : ℝ) + 1)
      / (Work.FTS.PhiStar.Gegenbauer.lam 0 * Real.sqrt (2 * ((0 : ℕ) : ℝ) + 1)) = 0 := by
    rw [Work.FTS.PhiStar.Gegenbauer.lam]
    norm_num
  have bnd1 : ∀ m : ℕ, |bco ψ j m| * ((m : ℝ) + 1) ^ 2
      ≤ C * ((2 * (m : ℝ) + 1)
          / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))) := by
    intro m
    by_cases hm : m = 0
    · subst hm
      rw [bco_apply_zero ψ hj, abs_zero, zero_mul, hG0, mul_zero]
    · exact (key m (Nat.one_le_iff_ne_zero.mpr hm)).1
  have bnd2 : ∀ m : ℕ, |bco ψ j m * Work.FTS.PhiStar.Gegenbauer.lam m| * ((m : ℝ) + 1)
      ≤ C * ((2 * (m : ℝ) + 1)
          / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))) := by
    intro m
    by_cases hm : m = 0
    · subst hm
      rw [bco_apply_zero ψ hj, zero_mul, abs_zero, zero_mul, hG0, mul_zero]
    · exact (key m (Nat.one_le_iff_ne_zero.mpr hm)).2
  constructor
  · refine (hG.mul_left C).of_norm_bounded (fun m => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact bnd1 m
  · refine (hG.mul_left C).of_norm_bounded (fun m => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact bnd2 m

end Work.FTS.PhiStar.FlatWAux.MomentChiaAux
