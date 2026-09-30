import Mathlib
import Submission.Work.BW.DefsAC
import Submission.Work.BW.pD0_succ_mul_log_le
import Submission.Work.BW.split_aux
import Submission.Work.BW.num_xi

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-!
# `Work.BW.yc_num` — the pure numeric core of the Y-free counting inequality

BW §20 (Baker–Wüstholz, *Logarithmic forms and group varieties*, Crelle 442 (1993))
compares a count of lattice points, `h·(D₀+1)`, against the size of the box cut out by
`ξ`, `T` and `S = 16 r d h`. In the degenerate (`Y`-free) level, whose level-index `Y`
vanishes, the comparison reduces to the single real inequality

`h·(D₀+1) < ξ·T·(4S − 1)`,   `D₀ = pD0 r d σ`, `T = pT r d σ`, `S = pS r d h`, `ξ = pxi r`,

under the standing normalisations `r ≥ 2`, `d ≥ 1`, `σ_j ≥ 1/d`.

The mathematics is entirely quantitative, with a very large margin (~1300·r·d·log(2rd)):
`D₀ ≤ r·pD/(2 log(2rd))`, `T > 11.75·r·pD − 1`, `4S − 1 ≥ 63 r d h`, `ξ ≥ 0.7`, and
`pD ≥ 1` (indeed `pD ≥ 2 r² d log(2rd)`). The only genuinely nonlinear step is isolated in
`yc_num_arith`.
-/

/-- Pure numeric core of `yc_num`: with `r ≥ 2`, `d ≥ 1`, `h ≥ 1`, `L ≥ 4/3` and `Y ≥ 0.18`,
`h·(Y/(2L) + 1) < 0.7·(11.75·Y − 1)·(63·r·d·h)`. The worst case is the corner
`r = 2, d = 1, Y = 0.18, L = 4/3`, where the two sides are `1.0675` and `98.343`. -/
lemma yc_num_arith {r d h : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) (hh : 1 ≤ h) {Y L : ℝ}
    (hL : (4 : ℝ) / 3 ≤ L) (hY : (0.18 : ℝ) ≤ Y) :
    (h : ℝ) * (Y / (2 * L) + 1) < 0.7 * (11.75 * Y - 1) * (63 * (r : ℝ) * (d : ℝ) * (h : ℝ)) := by
  have hr2 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hh1 : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
  have hhpos : (0 : ℝ) < (h : ℝ) := by linarith
  have hstep : Y / (2 * L) ≤ 3 * Y / 8 := by
    have h2L : (8 : ℝ) / 3 ≤ 2 * L := by linarith
    have h0 : (0 : ℝ) ≤ Y := by linarith
    calc Y / (2 * L) ≤ Y / ((8 : ℝ) / 3) := div_le_div_of_nonneg_left h0 (by norm_num) h2L
      _ = 3 * Y / 8 := by ring
  have hrd2 : (2 : ℝ) ≤ (r : ℝ) * (d : ℝ) := by nlinarith [hr2, hd1]
  have hcore : Y / (2 * L) + 1 < 44.1 * ((r : ℝ) * (d : ℝ)) * (11.75 * Y - 1) := by
    have hprod : (0 : ℝ) ≤ ((r : ℝ) * (d : ℝ) - 2) * (Y - 0.18) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith [hstep, hY, hrd2, hprod]
  calc (h : ℝ) * (Y / (2 * L) + 1)
      < (h : ℝ) * (44.1 * ((r : ℝ) * (d : ℝ)) * (11.75 * Y - 1)) :=
        mul_lt_mul_of_pos_left hcore hhpos
    _ = 0.7 * (11.75 * Y - 1) * (63 * (r : ℝ) * (d : ℝ) * (h : ℝ)) := by ring

/-- The pure numeric core of the Y-free counting inequality (BW §20, degenerate level): for `r ≥ 2`, `d ≥ 1`, `h ≥ 1` and `σ_j ≥ 1/d`, the reduced bound `h(D₀+1) < ξ·T·(4S−1)` holds, where `D₀ = pD0 r d σ`, `T = pT r d σ`, `S = pS r d h` and `ξ = pxi r`. -/
theorem yc_num {r d h : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) (hh : 1 ≤ h) (σ : Fin r → ℝ)
    (hσ : ∀ j, 1 / (d : ℝ) ≤ σ j) :
    (h : ℝ) * ((pD0 r d σ : ℝ) + 1) <
      pxi r * (pT r d σ : ℝ) * (4 * (pS r d h : ℝ) - 1) := by
  have hr2 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hh1 : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
  have hhpos : (0 : ℝ) < (h : ℝ) := by linarith
  -- positivity of `pD`
  have hPge : (1 : ℝ) ≤ pD r d σ := pD_ge_one hr hd σ hσ
  have hPpos : (0 : ℝ) < pD r d σ := by linarith
  -- the logarithm `L = log (2rd)`
  have hLge : (4 : ℝ) / 3 ≤ Real.log (2 * (r : ℝ) * (d : ℝ)) := log_2rd_ge hr hd
  have hLpos : (0 : ℝ) < Real.log (2 * (r : ℝ) * (d : ℝ)) := by linarith
  -- `D₀ = ⌊rD/(2L)⌋ ≤ rD/(2L)`
  have hD0le : (pD0 r d σ : ℝ) ≤ (r : ℝ) * pD r d σ / (2 * Real.log (2 * (r : ℝ) * (d : ℝ))) := by
    rw [pD0]
    apply Nat.floor_le
    exact div_nonneg (mul_nonneg (by linarith) (le_of_lt hPpos)) (by linarith)
  -- `T = ⌊11.75 rD⌋ > 11.75 rD − 1`
  have hTgt : (11.75 : ℝ) * ((r : ℝ) * pD r d σ) - 1 < (pT r d σ : ℝ) := by
    have h := Nat.lt_floor_add_one ((11.75 : ℝ) * (r : ℝ) * pD r d σ)
    rw [pT]
    linarith
  -- `4S − 1 = 64 r d h − 1 ≥ 63 r d h`
  have hone : (1 : ℝ) ≤ (r : ℝ) * (d : ℝ) * (h : ℝ) := by
    have hrd : (1 : ℝ) ≤ (r : ℝ) * (d : ℝ) :=
      one_le_mul_of_one_le_of_one_le (by linarith) (by linarith)
    exact one_le_mul_of_one_le_of_one_le hrd hh1
  have hS : 63 * (r : ℝ) * (d : ℝ) * (h : ℝ) ≤ 4 * (pS r d h : ℝ) - 1 := by
    have hcast : ((pS r d h : ℕ) : ℝ) = 16 * (r : ℝ) * (d : ℝ) * (h : ℝ) := by
      simp only [pS]; push_cast; ring
    rw [hcast]
    nlinarith [hone]
  have hSnn : (0 : ℝ) ≤ 4 * (pS r d h : ℝ) - 1 := by linarith [hS, hone]
  -- `ξ ≥ 0.7`, and the numeric core
  have hY : (0.18 : ℝ) ≤ (r : ℝ) * pD r d σ := by nlinarith [hr2, hPge]
  have harith := yc_num_arith (r := r) (d := d) (h := h) hr hd hh
    (Y := (r : ℝ) * pD r d σ) (L := Real.log (2 * (r : ℝ) * (d : ℝ))) hLge hY
  calc (h : ℝ) * ((pD0 r d σ : ℝ) + 1)
      ≤ (h : ℝ) * ((r : ℝ) * pD r d σ / (2 * Real.log (2 * (r : ℝ) * (d : ℝ))) + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hhpos)
    _ < 0.7 * (11.75 * ((r : ℝ) * pD r d σ) - 1) * (63 * (r : ℝ) * (d : ℝ) * (h : ℝ)) := harith
    _ ≤ 0.7 * (pT r d σ : ℝ) * (63 * (r : ℝ) * (d : ℝ) * (h : ℝ)) := by
        have h1 : (0.7 : ℝ) * (11.75 * ((r : ℝ) * pD r d σ) - 1) < 0.7 * (pT r d σ : ℝ) :=
          mul_lt_mul_of_pos_left hTgt (by norm_num)
        have hpos : (0 : ℝ) < 63 * (r : ℝ) * (d : ℝ) * (h : ℝ) := by linarith [hone]
        exact le_of_lt (mul_lt_mul_of_pos_right h1 hpos)
    _ ≤ 0.7 * (pT r d σ : ℝ) * (4 * (pS r d h : ℝ) - 1) := by
        exact mul_le_mul_of_nonneg_left hS (by positivity)
    _ ≤ pxi r * (pT r d σ : ℝ) * (4 * (pS r d h : ℝ) - 1) := by
        have hxi : (0.7 : ℝ) ≤ pxi r := pxi_ge hr
        have hTnn : (0 : ℝ) ≤ (pT r d σ : ℝ) := Nat.cast_nonneg _
        have h1 : (0.7 : ℝ) * (pT r d σ : ℝ) ≤ pxi r * (pT r d σ : ℝ) :=
          mul_le_mul_of_nonneg_right hxi hTnn
        exact mul_le_mul_of_nonneg_right h1 hSnn

end Work.BW
