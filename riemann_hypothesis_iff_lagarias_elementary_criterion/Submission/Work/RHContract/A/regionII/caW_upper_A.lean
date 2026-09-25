import Mathlib
import Submission.Work.RHContract.A.regionII.Defs
import Submission.Work.RHContract.A.regionII.theta_deficit_bound
import Submission.Work.RHContract.A.regionII.caW_core_bound
import Submission.Work.RHContract.A.regionII.psi_sub_theta_le_230
import Submission.Work.RHContract.A.ca_margin_lower
import Submission.Work.RHContract.Corpus

/-!
# `caW ε ≤ (3/100) · caU (ξ ε)` on the region `30000 ≤ ξ < 100000`

This is the `W`-bound of the "Region II" analytic chain (see
`Submission/Work/RHContract/A/regionII/Defs.lean`).  Writing `ξ = ξ(ε)`, `L = log ξ`,
`y = ψ ξ` and `δ = (y − ξ)/ξ`, one has the exact rewriting

`W = log log ξ + (y − ξ)/(ξ log ξ) − log log y = δ/L − log(1 + log(1+δ)/L)`,

so it suffices to control the two-variable function `f(δ) = δ/L − log(1 + log(1+δ)/L)`:

* `f(δ) ≤ (13/200) δ²` for `δ ≥ −1/50` and `L ≥ 10` (`caW_core_bound`);
* `|δ| ≤ 2.3/√ξ`, because `ψ ξ ≥ θ ξ ≥ ξ − 2.3 √ξ` (hypothesis `hθ`) and
  `ψ ξ ≤ ξ + 2.3 √ξ` (`theta_le_self_range` + `psi_sub_theta_le_230`).

Hence `W ≤ (13/200)·(2.3)²/ξ ≤ (3/100)/(√ξ log ξ)`, the last step being the numerical
comparison `(13/200)·(2.3)²·log ξ ≤ (3/100)·√ξ`, which follows from `log ξ ≤ 12 ≤ 173/14.4`
and `√ξ ≥ 173`.
-/

open scoped BigOperators

namespace Work.RHContract.A.regionII

/-- The exact rewriting of `caW` in terms of `δ = (ψ ξ − ξ)/ξ`: the two `log log` terms of
`caW` combine with the middle term into the single expression
`δ/L − log(1 + log(1+δ)/L)`, `L = log ξ`. -/
lemma log_algebra (ξ y : ℝ) (hξ : 1 < ξ) (hy : 1 < y) :
    Real.log (Real.log ξ) + (y - ξ)/(ξ * Real.log ξ) - Real.log (Real.log y)
      = (y - ξ)/ξ / Real.log ξ
        - Real.log (1 + Real.log (1 + (y-ξ)/ξ)/Real.log ξ) := by
  have hξpos : 0 < ξ := by linarith
  have hLpos : 0 < Real.log ξ := Real.log_pos hξ
  have hlogypos : 0 < Real.log y := Real.log_pos hy
  have hr : 0 < 1 + (y - ξ)/ξ := by
    have : 1 + (y-ξ)/ξ = y/ξ := by field_simp; ring
    rw [this]; positivity
  have hlogy : Real.log y = Real.log ξ + Real.log (1 + (y - ξ)/ξ) := by
    calc Real.log y = Real.log (ξ * (1 + (y - ξ)/ξ)) := by
          congr 1; field_simp; ring
      _ = Real.log ξ + Real.log (1 + (y - ξ)/ξ) := Real.log_mul hξpos.ne' hr.ne'
  have h1v : 1 + Real.log (1 + (y-ξ)/ξ) / Real.log ξ ≠ 0 := by
    have h2 : 1 + Real.log (1 + (y-ξ)/ξ) / Real.log ξ = Real.log y / Real.log ξ := by
      rw [hlogy]; field_simp
    rw [h2]; exact div_ne_zero hlogypos.ne' hLpos.ne'
  have hsplit : Real.log (Real.log ξ + Real.log (1 + (y-ξ)/ξ))
      = Real.log (Real.log ξ) + Real.log (1 + Real.log (1 + (y-ξ)/ξ)/Real.log ξ) := by
    have hfac : Real.log ξ + Real.log (1 + (y-ξ)/ξ)
        = Real.log ξ * (1 + Real.log (1 + (y-ξ)/ξ)/Real.log ξ) := by
      rw [mul_add, mul_one, mul_div_cancel₀ _ hLpos.ne']
    rw [hfac, Real.log_mul hLpos.ne' h1v]
  rw [hlogy, hsplit]
  ring

/-- `log 100000 ≤ 12`, from `2.7 ≤ exp 1`. -/
lemma log_1e5_le_twelve : Real.log 100000 ≤ 12 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h : (2.7:ℝ) ≤ Real.exp 1 := le_of_lt (lt_trans (by norm_num) Real.exp_one_gt_d9)
  have h12 : ((2.7:ℝ))^12 ≤ (Real.exp 1)^12 :=
    pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2.7) h 12
  have hexp : Real.exp 12 = (Real.exp 1)^12 := by
    rw [show (12:ℝ) = (12:ℕ) * 1 by norm_num, Real.exp_nat_mul 1 12]
  rw [hexp]
  have : (100000:ℝ) ≤ (2.7:ℝ)^12 := by norm_num
  linarith

/-- The two-variable core of the bound: if `ξ ∈ [30000,100000)` and
`|ψ ξ − ξ| ≤ 2.3 √ξ`, then the `W`-expression at `ξ` is at most `(3/100)·caU ξ`. -/
lemma caW_key (ξ y : ℝ) (hξlo : 30000 ≤ ξ) (hξhi : ξ < 100000)
    (hy1 : ξ - (23/10)*Real.sqrt ξ ≤ y) (hy2 : y ≤ ξ + (23/10)*Real.sqrt ξ) :
    Real.log (Real.log ξ) + (y - ξ)/(ξ * Real.log ξ) - Real.log (Real.log y)
      ≤ (3/100) * (1/(Real.sqrt ξ * Real.log ξ)) := by
  have hξpos : 0 < ξ := by linarith
  have hξ1 : 1 < ξ := by linarith
  have hLpos : 0 < Real.log ξ := Real.log_pos hξ1
  have hsqrtpos : 0 < Real.sqrt ξ := Real.sqrt_pos_of_pos hξpos
  have hsq : Real.sqrt ξ ^ 2 = ξ := Real.sq_sqrt hξpos.le
  have h115 : (115:ℝ) ≤ Real.sqrt ξ := Real.le_sqrt_of_sq_le (by norm_num; linarith)
  have hsqrtle : Real.sqrt ξ ≤ ξ/115 := by
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 115)]
    nlinarith [h115, hsq, Real.sqrt_nonneg ξ]
  have hy1' : 1 < y := by
    have h1 : Real.sqrt ξ < Real.sqrt 100000 := Real.sqrt_lt_sqrt hξpos.le hξhi
    have h2 : Real.sqrt 100000 < (317:ℝ) := by
      rw [Real.sqrt_lt' (by norm_num : (0:ℝ) < 317)]; norm_num
    nlinarith [hy1, h1, h2]
  have hL10 : 10 ≤ Real.log ξ := by
    have h1 : (10:ℝ) ≤ Real.log 30000 := by
      rw [Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 30000)]
      have h : Real.exp 1 ≤ 2.72 := le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))
      have h10 : (Real.exp 1)^10 ≤ (2.72:ℝ)^10 :=
        pow_le_pow_left₀ (Real.exp_pos 1).le h 10
      have hexp : Real.exp 10 = (Real.exp 1)^10 := by
        rw [show (10:ℝ) = (10:ℕ) * 1 by norm_num, Real.exp_nat_mul 1 10]
      rw [hexp]
      have : (2.72:ℝ)^10 ≤ 30000 := by norm_num
      linarith
    exact h1.trans (Real.log_le_log (by norm_num) hξlo)
  have hδlb : -((23/10)/Real.sqrt ξ) ≤ (y - ξ)/ξ := by
    rw [le_div_iff₀ hξpos]
    have h : -((23/10)/Real.sqrt ξ) * ξ = -(23/10)*Real.sqrt ξ := by
      calc -((23/10)/Real.sqrt ξ) * ξ = -((23/10) * (ξ/Real.sqrt ξ)) := by ring
        _ = -((23/10) * Real.sqrt ξ) := by rw [Real.div_sqrt]
        _ = -(23/10)*Real.sqrt ξ := by ring
    rw [h]; linarith
  have hδub : (y - ξ)/ξ ≤ (23/10)/Real.sqrt ξ := by
    rw [div_le_iff₀ hξpos]
    have h : ((23/10)/Real.sqrt ξ) * ξ = (23/10)*Real.sqrt ξ := by
      calc ((23/10)/Real.sqrt ξ) * ξ = (23/10) * (ξ/Real.sqrt ξ) := by ring
        _ = (23/10) * Real.sqrt ξ := by rw [Real.div_sqrt]
    rw [h]; linarith
  have hδlo : -(1/50:ℝ) ≤ (y - ξ)/ξ := by
    have h : (23/10)/Real.sqrt ξ ≤ 1/50 := by
      rw [div_le_iff₀ hsqrtpos]; nlinarith [h115]
    linarith
  have hδsq : ((y - ξ)/ξ)^2 ≤ (23/10)^2 / ξ := by
    have h1 : ((y - ξ)/ξ)^2 ≤ ((23/10)/Real.sqrt ξ)^2 := sq_le_sq' hδlb hδub
    have h2 : ((23/10)/Real.sqrt ξ)^2 = (23/10)^2 / ξ := by
      rw [div_pow, hsq]
    linarith [h1, h2.symm.le, h2.le]
  have hW := log_algebra ξ y hξ1 hy1'
  rw [hW]
  have hcore := caW_core_bound ((y - ξ)/ξ) (Real.log ξ) hδlo hL10
  refine le_trans hcore ?_
  have hL12 : Real.log ξ ≤ 12 := (Real.log_le_log hξpos (le_of_lt hξhi)).trans log_1e5_le_twelve
  have hsqrt173 : (173:ℝ) ≤ Real.sqrt ξ := Real.le_sqrt_of_sq_le (by norm_num; linarith)
  have h1 : (13/200) * ((y - ξ)/ξ)^2 ≤ (13/200) * ((23/10)^2 / ξ) :=
    mul_le_mul_of_nonneg_left hδsq (by norm_num)
  have h2 : (13/200) * ((23/10)^2 / ξ) ≤ (3/100) * (1/(Real.sqrt ξ * Real.log ξ)) := by
    have h3 : (13/200) * ((23/10)^2 / ξ) = ((13/200) * (23/10)^2) / ξ := by ring
    have h4 : (3/100) * (1/(Real.sqrt ξ * Real.log ξ))
        = (3/100) / (Real.sqrt ξ * Real.log ξ) := by ring
    rw [h3, h4, div_le_div_iff₀ hξpos (by positivity)]
    nlinarith [hL12, hsqrt173, hsq, Real.sqrt_nonneg ξ]
  linarith

/-- `θ t ≤ t` on the range `[59, 100000]`, from the certified bracket of
`Commons.NumberTheory.Chebyshev.theta_bracket_finite_range`. -/
lemma theta_le_self_range (t : ℝ) (h1 : 59 ≤ t) (h2 : t ≤ 100000) :
    Chebyshev.theta t ≤ t := by
  rw [Commons.NumberTheory.Chebyshev.theta_eq_theta_floor t]
  have ht0 : (0:ℝ) ≤ t := by linarith
  have hn1 : 59 ≤ ⌊t⌋₊ := Nat.le_floor (by exact_mod_cast h1)
  have hn2 : ⌊t⌋₊ ≤ 10 ^ 5 := by
    have hle : ((⌊t⌋₊ : ℕ) : ℝ) ≤ t := Nat.floor_le ht0
    have : ((⌊t⌋₊ : ℕ) : ℝ) ≤ ((10 ^ 5 : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  have hb := (Commons.NumberTheory.Chebyshev.theta_bracket_finite_range ⌊t⌋₊ hn1 hn2).2
  have hle : ((⌊t⌋₊ : ℕ) : ℝ) ≤ t := Nat.floor_le ht0
  linarith

theorem caW_upper_A (ε : ℝ) (hε : 0 < ε)
    (hlo : 30000 ≤ (Work.RHPlan.caXi ε : ℝ)) (hhi : (Work.RHPlan.caXi ε : ℝ) < 100000)
    (hθ : ∀ t : ℝ, 173 ≤ t → t ≤ 100000 → t - Chebyshev.theta t ≤ 2.3 * Real.sqrt t) :
    Work.RHContract.Margin.caW ε
      ≤ (3/100) * Work.RHContract.A.RegionII.caU (Work.RHPlan.caXi ε : ℝ) := by
  unfold Work.RHContract.Margin.caW Work.RHContract.A.RegionII.caU
  refine caW_key _ _ hlo hhi ?_ ?_
  · have h2 : (Work.RHPlan.caXi ε : ℝ) - (23/10) * Real.sqrt (Work.RHPlan.caXi ε : ℝ)
        ≤ Chebyshev.theta (Work.RHPlan.caXi ε : ℝ) := by
      have h := hθ (Work.RHPlan.caXi ε : ℝ) (by linarith) (by linarith)
      norm_num at h ⊢
      linarith
    have h3 := Chebyshev.theta_le_psi (Work.RHPlan.caXi ε : ℝ)
    linarith
  · have h1 := psi_sub_theta_le_230 (Work.RHPlan.caXi ε : ℝ) hlo
    have h2 : Chebyshev.theta (Work.RHPlan.caXi ε : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ) :=
      theta_le_self_range _ (by linarith) (by linarith)
    linarith

end Work.RHContract.A.regionII
