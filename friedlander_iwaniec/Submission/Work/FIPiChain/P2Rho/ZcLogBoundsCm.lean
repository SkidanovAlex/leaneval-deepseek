/-
# `Submission.Work.FIPiChain.P2Rho.ZcLogBoundsCm`

The three logarithm bounds for the `B`-dependent `ρ`-window family of
`Submission/Work/FIChain/Defs.lean`:

  `sc x B = 2^{Jc x B}`,  `zc x B = ⌊Yc x B⌋₊`,  `Yc x B = √x/(sc x B·(log x)^{B+2})`,
  `DpiC x = ⌈exp(2^{40}(loglog x)³)⌉`,

namely, eventually in `x`,

* `log(e·(sc·zc)/(zc/Δπ)) ≤ 2 log x`,
* `log(⌊zc^{1-η_c}⌋) ≤ 2 log x` with `η_c = 1/32`,
* `log(e·(sc·zc)/zc) ≤ 2 log x`.

The mathematics is elementary and completely uniform in `B > 0`.  The single structural
input is the exact value `sc x B · Yc x B = √x/(log x)^{B+2}` (`Work.FIChain.Defs`), which
with `zc ≤ Yc` gives `sc·zc ≤ √x`; since `zc ≥ 1` this yields `sc ≤ √x`.  Together with
`zc ≤ x` (from `scale_factsC`) and `Δπ ≤ √x` (`eventually_Dpi_le_rpow`) all three bounds
follow: `e·sc·Δπ ≤ 2x`, `zc^{1-η} ≤ zc ≤ x`, and `sc ≤ √x`.

No `sorry`, no `axiom`.
-/
import Mathlib
import Submission.Work.FIChain.RhoWin2Defs
import Submission.Work.FIChain.scale_factsC
import Submission.Work.FIChain.BpWinAux

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIPiChain.P2Rho

open Filter

attribute [local instance] Classical.propDecidable

noncomputable section

/-- `0 < sc x B`: the dyadic scale is a positive power of two. -/
private lemma sc_pos' (x : ℕ) (B : ℝ) : 0 < Work.FIChain.sc x B := by
  rw [Work.FIChain.sc]; positivity

/-- The exact value of the window product: `sc x B · Yc x B = √x/(log x)^{B+2}`. -/
private lemma sc_mul_Yc' (x : ℕ) (B : ℝ) (hL : 0 < Real.log (x : ℝ)) :
    Work.FIChain.sc x B * Work.FIChain.Yc x B
      = Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ (B + 2) := by
  rw [Work.FIChain.Yc]
  have h1 : Work.FIChain.sc x B ≠ 0 := ne_of_gt (sc_pos' x B)
  have h2 : (Real.log (x : ℝ)) ^ (B + 2) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hL _)
  field_simp

theorem ZcLogBoundsCm (B : ℝ) (hB : 0 < B) :
    ∀ᶠ x : ℕ in Filter.atTop,
      Real.log ((Real.exp 1 * (Work.FIChain.sc x B * Work.FIChain.zc x B)) /
        (Work.FIChain.zc x B / (Work.FIChain.DpiC x : ℝ))) ≤ 2 * Real.log (x : ℝ) ∧
      Real.log (((⌊(Work.FIChain.zc x B) ^ (1 - Work.FIChain.etac)⌋₊ : ℕ) : ℝ))
        ≤ 2 * Real.log (x : ℝ) ∧
      Real.log ((Real.exp 1 * (Work.FIChain.sc x B * Work.FIChain.zc x B)) /
        Work.FIChain.zc x B) ≤ 2 * Real.log (x : ℝ) := by
  filter_upwards [Work.FIChain.scale_factsC B hB,
    Work.FIChain.eventually_Dpi_le_rpow ((2 : ℝ) ^ (40 : ℕ)) (1 / 2) (by positivity)
      (by norm_num),
    Work.FITop.FI_ev_log_ge_nat 1, eventually_ge_atTop 2] with x hsf hDpi hL1 hx2
  rcases hsf with ⟨-, -, -, -, -, -, -, -, hzc_le_x, hZc_ge, -, -, -, -, -, -⟩
  have hxpos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
  have hx1 : (1 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 1 < x)
  have hxhalf : (0 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hxpos.le _
  have hLpos : 0 < Real.log (x : ℝ) := lt_of_lt_of_le zero_lt_one hL1
  have hsc_pos : 0 < Work.FIChain.sc x B := sc_pos' x B
  have hsc_one : 1 ≤ Work.FIChain.sc x B := by
    rw [Work.FIChain.sc]; exact one_le_pow₀ (by norm_num)
  have hzc_ge1 : (1 : ℝ) ≤ Work.FIChain.zc x B := by
    rw [Work.FIChain.zc]; exact_mod_cast hZc_ge
  have hzc_pos : 0 < Work.FIChain.zc x B := lt_of_lt_of_le zero_lt_one hzc_ge1
  have hYc_pos : 0 < Work.FIChain.Yc x B := by
    rw [Work.FIChain.Yc]
    exact div_pos (Real.sqrt_pos.mpr hxpos)
      (mul_pos hsc_pos (Real.rpow_pos_of_pos hLpos _))
  have hzc_le_Yc : Work.FIChain.zc x B ≤ Work.FIChain.Yc x B := by
    rw [Work.FIChain.zc, Work.FIChain.Zc]
    exact Nat.floor_le hYc_pos.le
  have hscYc : Work.FIChain.sc x B * Work.FIChain.Yc x B
      = Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ (B + 2) := sc_mul_Yc' x B hLpos
  -- `sc·zc ≤ √x`, and hence (`zc ≥ 1`) `sc ≤ √x`
  have hprod_le_sqrt : Work.FIChain.sc x B * Work.FIChain.zc x B ≤ Real.sqrt (x : ℝ) := by
    calc Work.FIChain.sc x B * Work.FIChain.zc x B
        ≤ Work.FIChain.sc x B * Work.FIChain.Yc x B :=
          mul_le_mul_of_nonneg_left hzc_le_Yc hsc_pos.le
      _ = Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ (B + 2) := hscYc
      _ ≤ Real.sqrt (x : ℝ) := by
          rw [div_le_iff₀ (Real.rpow_pos_of_pos hLpos _)]
          have hge1 : 1 ≤ (Real.log (x : ℝ)) ^ (B + 2) :=
            Real.one_le_rpow hL1 (by linarith)
          nlinarith [Real.sqrt_nonneg (x : ℝ)]
  have hsc_le_sqrt : Work.FIChain.sc x B ≤ (x : ℝ) ^ ((1 : ℝ) / 2) := by
    have h1 : Work.FIChain.sc x B ≤ Work.FIChain.sc x B * Work.FIChain.zc x B := by
      simpa using mul_le_mul_of_nonneg_left hzc_ge1 hsc_pos.le
    rw [Real.sqrt_eq_rpow] at hprod_le_sqrt
    linarith
  have hDpi_le : (Work.FIChain.DpiC x : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2) := by
    simpa [Work.FIChain.DpiC] using hDpi
  have hDpi_pos : 0 < (Work.FIChain.DpiC x : ℝ) := by
    have : (0 : ℕ) < Work.FIChain.DpiC x := by
      rw [Work.FIChain.DpiC, Work.FIChain.Dpi]
      exact Nat.ceil_pos.mpr (Real.exp_pos _)
    exact_mod_cast this
  refine ⟨?_, ?_, ?_⟩
  · -- `log(e·(sc·zc)/(zc/Δπ)) = log(e·sc·Δπ) ≤ 2 log x`
    have hzc_ne : Work.FIChain.zc x B ≠ 0 := ne_of_gt hzc_pos
    have hratio : (Real.exp 1 * (Work.FIChain.sc x B * Work.FIChain.zc x B))
        / (Work.FIChain.zc x B / (Work.FIChain.DpiC x : ℝ))
        = Real.exp 1 * (Work.FIChain.sc x B * (Work.FIChain.DpiC x : ℝ)) := by
      field_simp
    rw [hratio]
    have hprod : Work.FIChain.sc x B * (Work.FIChain.DpiC x : ℝ) ≤ (x : ℝ) := by
      calc Work.FIChain.sc x B * (Work.FIChain.DpiC x : ℝ)
          ≤ (x : ℝ) ^ ((1 : ℝ) / 2) * (x : ℝ) ^ ((1 : ℝ) / 2) :=
            mul_le_mul hsc_le_sqrt hDpi_le hDpi_pos.le hxhalf
        _ = (x : ℝ) := by rw [← Real.rpow_add hxpos]; norm_num
    have hprod_pos : 0 < Work.FIChain.sc x B * (Work.FIChain.DpiC x : ℝ) :=
      mul_pos hsc_pos hDpi_pos
    rw [Real.log_mul (ne_of_gt (Real.exp_pos 1)) (ne_of_gt hprod_pos), Real.log_exp]
    have hlog : Real.log (Work.FIChain.sc x B * (Work.FIChain.DpiC x : ℝ))
        ≤ Real.log (x : ℝ) := Real.log_le_log hprod_pos hprod
    linarith
  · -- `log(⌊zc^{1-η}⌋) ≤ log zc ≤ log x`
    have hη : (0 : ℝ) ≤ 1 - Work.FIChain.etac := by norm_num [Work.FIChain.etac]
    have hA1 : (1 : ℝ) ≤ (Work.FIChain.zc x B) ^ (1 - Work.FIChain.etac) :=
      Real.one_le_rpow hzc_ge1 hη
    have hAle : (Work.FIChain.zc x B) ^ (1 - Work.FIChain.etac) ≤ Work.FIChain.zc x B := by
      simpa using Real.rpow_le_rpow_of_exponent_le hzc_ge1
        (show (1 - Work.FIChain.etac : ℝ) ≤ 1 by norm_num [Work.FIChain.etac])
    have hfl_le : ((⌊(Work.FIChain.zc x B) ^ (1 - Work.FIChain.etac)⌋₊ : ℕ) : ℝ)
        ≤ Work.FIChain.zc x B :=
      le_trans (Nat.floor_le (le_trans zero_le_one hA1)) hAle
    have hfl_pos : 0 < ((⌊(Work.FIChain.zc x B) ^ (1 - Work.FIChain.etac)⌋₊ : ℕ) : ℝ) := by
      have h1 : (1 : ℕ) ≤ ⌊(Work.FIChain.zc x B) ^ (1 - Work.FIChain.etac)⌋₊ :=
        Nat.le_floor (by simpa using hA1)
      exact_mod_cast (by omega : (0 : ℕ) < ⌊(Work.FIChain.zc x B) ^ (1 - Work.FIChain.etac)⌋₊)
    calc Real.log (((⌊(Work.FIChain.zc x B) ^ (1 - Work.FIChain.etac)⌋₊ : ℕ) : ℝ))
        ≤ Real.log (Work.FIChain.zc x B) := Real.log_le_log hfl_pos hfl_le
      _ ≤ Real.log (x : ℝ) := Real.log_le_log hzc_pos hzc_le_x
      _ ≤ 2 * Real.log (x : ℝ) := by linarith
  · -- `log(e·(sc·zc)/zc) = log(e·sc) = 1 + log sc ≤ 1 + log x/2`
    have hzc_ne : Work.FIChain.zc x B ≠ 0 := ne_of_gt hzc_pos
    have hratio : (Real.exp 1 * (Work.FIChain.sc x B * Work.FIChain.zc x B))
        / Work.FIChain.zc x B = Real.exp 1 * Work.FIChain.sc x B := by
      field_simp
    rw [hratio]
    rw [Real.log_mul (ne_of_gt (Real.exp_pos 1)) (ne_of_gt hsc_pos), Real.log_exp]
    have h2 : Real.log (Work.FIChain.sc x B) ≤ (1 / 2) * Real.log (x : ℝ) := by
      calc Real.log (Work.FIChain.sc x B) ≤ Real.log ((x : ℝ) ^ ((1 : ℝ) / 2)) :=
            Real.log_le_log hsc_pos hsc_le_sqrt
        _ = (1 / 2) * Real.log (x : ℝ) := Real.log_rpow hxpos _
    linarith

end

end Work.FIPiChain.P2Rho
