import Mathlib
import Submission.Work.CNum.Fx
import Submission.Work.CNum.LgInfra
import Submission.Work.CNum.LgNormSpec
import Submission.Work.CNum.artanh_tail_le
import Submission.Work.CNum.LgSerGe

/-!
# `Work.CNum.LgUpSpec` — soundness of the fixed-point logarithm `lgUp`

`Work.CNum.lgUp n` (scale `SC = 2^30`) is the integer mantissa of an upper bound for
`Real.log (n/SC)`, computed as `lgNorm n · LOG2UP + lgCore (halveU (lgNorm n) n) true + 2`:
the mantissa is first halved `lgNorm n` times (rounding *up*, `halveU`) until it lies in
`[SC, 2·SC]`, each halving being paid for by `LOG2UP ≥ log 2 · SC`, and on the reduced value the
artanh series `lgCore · true` is evaluated.

The proof has three layers:

* `Work.CNum.LgInfra` — the outward-rounded primitives (`mulU`, `divU`, `powM`, `lgvUp`, `halveU`,
  `halveD` and the numeric bound `log 2 ≤ m2r LOG2UP`);
* `Work.CNum.LgNormSpec` — the halving lands in `[SC, 2·SC]`;
* `Work.CNum.artanh_tail_le` together with `Work.CNum.LgSerGe` (partial artanh sum) and
  `LgUpSpec_lgRem_ge` (its tail) — the analytic core, giving `LgUpSpec_core`.

Everything is then assembled into `LgUpSpec`.
-/

namespace Work.CNum

open Work.ANum

/-! ## The artanh variable `lgvUp` -/

lemma LgUpSpec_m2r_lt_iff (a b : ℤ) : m2r a < m2r b ↔ a < b := by
  constructor
  · intro h
    by_contra hc
    rw [not_lt] at hc
    exact absurd (m2r_le hc) (not_le.mpr h)
  · exact m2r_lt

/-- For `SC ≤ n` the artanh variable `lgvUp n` is nonnegative. -/
lemma LgUpSpec_lgvUp_nonneg {n : ℤ} (h1 : SC ≤ n) : 0 ≤ lgvUp n := by
  have hSCpos : (0:ℤ) < SC := SC_pos
  have hD : (0:ℤ) < n + SC := by omega
  have hX : -((n - SC) * SC) ≤ 0 := by
    have : 0 ≤ (n - SC) * SC := mul_nonneg (by omega) hSCpos.le
    linarith
  have h : Int.ediv (-((n - SC) * SC)) (n + SC) ≤ 0 :=
    (Int.ediv_le_iff_le_mul hD (x := -((n - SC) * SC)) (y := 0)).mpr (by linarith)
  rw [lgvUp]
  linarith

/-- For `SC ≤ n ≤ 2·SC` the artanh variable `lgvUp n` is `< SC`. -/
lemma LgUpSpec_lgvUp_lt_SC {n : ℤ} (h1 : SC ≤ n) (h2 : n ≤ 2 * SC) : lgvUp n < SC := by
  have hSCpos : (0:ℤ) < SC := SC_pos
  have hD : (0:ℤ) < n + SC := by omega
  have hSC2 : (2:ℤ) ≤ SC := by norm_num [Work.ANum.SC]
  have hkey : (-SC + 1) * (n + SC) ≤ -((n - SC) * SC) := by nlinarith [h1, h2, hSC2]
  have h : -SC + 1 ≤ Int.ediv (-((n - SC) * SC)) (n + SC) :=
    (Int.le_ediv_iff_mul_le hD (a := -SC + 1) (b := -((n - SC) * SC))
      (c := n + SC)).mpr hkey
  rw [lgvUp]
  linarith

lemma LgUpSpec_lgvUp_m2r_lt_one {n : ℤ} (h1 : SC ≤ n) (h2 : n ≤ 2 * SC) :
    m2r (lgvUp n) < 1 := by
  rw [← m2r_SC]
  exact (LgUpSpec_m2r_lt_iff _ _).mpr (LgUpSpec_lgvUp_lt_SC h1 h2)

/-! ## The artanh tail `lgRem` -/

lemma LgUpSpec_lgRem_ge (v : ℤ) (hv : 0 ≤ v) (hv1 : m2r v < 1) :
    2 * (m2r v) ^ (2 * LOGP + 1) / ((2 * (LOGP : ℝ) + 1) * (1 - (m2r v) ^ 2))
      ≤ m2r (lgRem v true) := by
  have hSCpos : (0:ℝ) < (SC:ℝ) := SC_posR
  have hvSC : v < SC := (LgUpSpec_m2r_lt_iff v SC).mp (by rw [m2r_SC]; exact hv1)
  have hvv : v * v < SC * SC := by nlinarith
  have hDdef : (0:ℤ) < (2 * (LOGP:ℤ) + 1) * (SC * SC - v * v) := by
    have h1 : (0:ℤ) < SC * SC - v * v := by linarith
    have h2 : (0:ℤ) < (2 * (LOGP:ℤ) + 1) := by norm_num [LOGP]
    positivity
  have hx0 : 0 ≤ m2r v := (m2r_nonneg_iff v).mpr hv
  -- the ceiling bound for `lgRem`
  have hceil : m2r (2 * powM true v LOGP * (SC * SC)) /
        (((2 * (LOGP:ℤ) + 1) * (SC * SC - v * v) : ℤ) : ℝ) ≤ m2r (lgRem v true) := by
    have h0 := divUz_ge hDdef (2 * powM true v LOGP * (SC * SC))
    have he : divUz (2 * powM true v LOGP * (SC * SC))
        ((2 * (LOGP:ℤ) + 1) * (SC * SC - v * v)) = lgRem v true := by
      rw [lgRem, if_pos rfl]
      rfl
    rwa [he] at h0
  -- cleaned-up form of the ceiling bound
  have hceil' : 2 * m2r (powM true v LOGP) / ((2 * (LOGP : ℝ) + 1) * (1 - (m2r v) ^ 2))
      ≤ m2r (lgRem v true) := by
    have heq : m2r (2 * powM true v LOGP * (SC * SC)) /
          (((2 * (LOGP:ℤ) + 1) * (SC * SC - v * v) : ℤ) : ℝ)
        = 2 * m2r (powM true v LOGP) / ((2 * (LOGP : ℝ) + 1) * (1 - (m2r v) ^ 2)) := by
      rw [m2r, m2r]
      push_cast
      field_simp
    exact le_trans (le_of_eq heq.symm) hceil
  -- the series estimate `x ^ (2·LOGP+1) ≤ m2r (powM · v LOGP)`
  have hEpos : (0:ℝ) < (2 * (LOGP:ℝ) + 1) * (1 - (m2r v) ^ 2) := by
    have h1 : (0:ℝ) < 1 - (m2r v)^2 := by nlinarith
    have h2 : (0:ℝ) < 2 * (LOGP:ℝ) + 1 := by positivity
    positivity
  have hq : (m2r v) ^ (2 * LOGP + 1) ≤ m2r (powM true v LOGP) :=
    le_trans (pow_le_pow_of_le_one hx0 hv1.le (by omega))
      (powM_true_ge hx0 LOGP)
  have hstep : 2 * (m2r v) ^ (2 * LOGP + 1) / ((2 * (LOGP:ℝ) + 1) * (1 - (m2r v)^2))
      ≤ 2 * m2r (powM true v LOGP) / ((2 * (LOGP:ℝ) + 1) * (1 - (m2r v)^2)) := by
    gcongr
  exact le_trans hstep hceil'

/-! ## The analytic core: `lgCore · true` bounds `log` from above on `[SC, 2·SC]` -/

theorem LgUpSpec_core {n : ℤ} (h1 : SC ≤ n) (h2 : n ≤ 2 * SC) :
    Real.log (m2r n) ≤ m2r (lgCore n true) := by
  have hnpos : 0 < m2r n := (m2r_pos_iff n).mpr (lt_of_lt_of_le SC_pos h1)
  have hSCpos : (0:ℤ) < SC := SC_pos
  have hD : (0:ℤ) < n + SC := by omega
  have hnR : (0:ℝ) < (n:ℝ) + SC := by exact_mod_cast hD
  have hv0 : 0 ≤ lgvUp n := LgUpSpec_lgvUp_nonneg h1
  have hx0 : 0 ≤ m2r (lgvUp n) := (m2r_nonneg_iff _).mpr hv0
  have hx1 : m2r (lgvUp n) < 1 := LgUpSpec_lgvUp_m2r_lt_one h1 h2
  set t : ℝ := ((n:ℝ) - SC) / ((n:ℝ) + SC) with ht_def
  have ht : t ≤ m2r (lgvUp n) := lgvUp_ge hD
  have h1t : 0 < 1 - t := by
    rw [ht_def, sub_pos, div_lt_one hnR]
    have : (0:ℝ) < SC := SC_posR
    linarith
  have h1x : 0 < 1 - m2r (lgvUp n) := by linarith
  -- `m2r n = (1+t)/(1-t)`
  have hfrac : (1 + t) / (1 - t) = m2r n := by
    rw [m2r]
    rw [div_eq_div_iff (ne_of_gt h1t) (ne_of_gt SC_posR)]
    rw [ht_def]
    field_simp
    ring
  -- monotonicity in the artanh variable
  have hmono : (1 + t) / (1 - t) ≤ (1 + m2r (lgvUp n)) / (1 - m2r (lgvUp n)) := by
    rw [div_le_div_iff₀ h1t h1x]
    nlinarith [ht]
  have hmn : m2r n ≤ (1 + m2r (lgvUp n)) / (1 - m2r (lgvUp n)) := by
    rw [← hfrac]; exact hmono
  have hlog := Real.log_le_log hnpos hmn
  -- the artanh series and its tail
  have hS := LgSerGe (lgvUp n) hv0
  have hR := LgUpSpec_lgRem_ge (lgvUp n) hv0 hx1
  have hT := artanh_tail_le hx0 hx1 LOGP
  have hR2 : 2 * ((m2r (lgvUp n)) ^ (2 * LOGP + 1) /
        ((2 * (LOGP:ℝ) + 1) * (1 - (m2r (lgvUp n)) ^ 2))) ≤ m2r (lgRem (lgvUp n) true) := by
    rw [← mul_div_assoc]
    exact hR
  rw [lgCore, if_pos rfl, m2r_add]
  linarith

/-! ## Assembly -/

theorem LgUpSpec {n : ℤ} (h1 : Work.ANum.SC ≤ n) (h2 : n ≤ 2 ^ 60) :
    Real.log (Work.ANum.m2r n) ≤ Work.ANum.m2r (lgUp n) := by
  obtain ⟨hUlo, hUhi, -, -⟩ := LgNormSpec h1 h2
  have hn0 : 0 ≤ n := le_trans SC_pos.le h1
  have hnpos : 0 < m2r n := (m2r_pos_iff n).mpr (lt_of_lt_of_le SC_pos h1)
  have hlgUp : lgUp n = (lgNorm n : ℤ) * LOG2UP + lgCore (halveU (lgNorm n) n) true + 2 := by
    unfold lgUp
    rw [if_neg (not_lt.mpr h1)]
  rw [hlgUp]
  simp only [m2r_add]
  have hA : (lgNorm n : ℝ) * Real.log 2 ≤ m2r ((lgNorm n : ℤ) * LOG2UP) := by
    rw [m2r_mul_int']
    exact mul_le_mul_of_nonneg_left log_two_le_LOG2UP (by positivity)
  have hB : Real.log (m2r (halveU (lgNorm n) n)) ≤ m2r (lgCore (halveU (lgNorm n) n) true) :=
    LgUpSpec_core hUlo hUhi
  have hC : Real.log (m2r n) - (lgNorm n : ℝ) * Real.log 2
      ≤ Real.log (m2r (halveU (lgNorm n) n)) := by
    have hle := halveU_ge (lgNorm n) n hn0
    have hp2 : (0 : ℝ) < 2 ^ (lgNorm n) := by positivity
    have hp3 : 0 < m2r n / 2 ^ (lgNorm n) := div_pos hnpos hp2
    have hlog : Real.log (m2r n / 2 ^ (lgNorm n))
        = Real.log (m2r n) - (lgNorm n : ℝ) * Real.log 2 := by
      rw [Real.log_div (ne_of_gt hnpos) (ne_of_gt hp2), Real.log_pow]
    rw [← hlog]
    exact Real.log_le_log hp3 hle
  have h2pos : 0 ≤ m2r (2 : ℤ) := by rw [m2r_nonneg_iff]; norm_num
  linarith

end Work.CNum
