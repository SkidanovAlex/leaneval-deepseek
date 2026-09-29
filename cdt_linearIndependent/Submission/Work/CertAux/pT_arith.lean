import Mathlib
import Submission.Work.Cert.aLoop_aux

namespace Work.CertAux

/-- Pure arithmetic budget inequality for the `pT` recurrence.

With `S = 2^40·10^8 ≥ 43`, `n = k - 1 ≥ 0` and `0 ≤ μ ≤ 79/100`:

`3/S + (μ + 20 n/S)·(16/S) + μ²·(20 n/S) ≤ 20 k/S`.

Multiplying through by `S > 0` this is `3 + 16μ + 320 n/S + 20 μ² n ≤ 20 n + 20`, which splits
into `3 + 16μ ≤ 20` and `n·(320/S + 20μ² - 20) ≤ 0`; the bracket is `≤ 3759/500 + 20·(79/100)² - 20
= 0` because `S ≥ 43` gives `320/S ≤ 320/43 ≤ 3759/500`. -/
theorem pT_arith (k : ℕ) (hk : 1 ≤ k) (μ : ℝ) (hμ0 : 0 ≤ μ) (hμ : μ ≤ 79 / 100) :
    3 / (Work.Cert.S : ℝ)
      + (μ + 20 * ((k - 1 : ℕ) : ℝ) / (Work.Cert.S : ℝ)) * (16 / (Work.Cert.S : ℝ))
      + μ ^ 2 * (20 * ((k - 1 : ℕ) : ℝ) / (Work.Cert.S : ℝ))
    ≤ 20 * (k : ℝ) / (Work.Cert.S : ℝ) := by
  have hc : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub hk]; norm_num
  rw [hc]
  set s : ℝ := (Work.Cert.S : ℝ) with hs
  set n : ℝ := (k : ℝ) - 1 with hn
  have hSpos : (0:ℝ) < s := by rw [hs]; norm_num [Work.Cert.S]
  have hs43 : (43:ℝ) ≤ s := by rw [hs]; norm_num [Work.Cert.S]
  have hkn : (k:ℝ) = n + 1 := by linarith [hn]
  have hn0 : 0 ≤ n := by
    have : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
    linarith [hn]
  have hμ2 : μ ^ 2 ≤ (79/100)^2 := by
    have h1 : 0 ≤ 79/100 - μ := by linarith
    have h2 : 0 ≤ 79/100 + μ := by linarith
    nlinarith [mul_nonneg h1 h2]
  have h1 : 3 + 16 * μ ≤ 20 := by linarith
  have hdiv : 320 / s ≤ 3759/500 := by
    rw [div_le_iff₀ hSpos]; nlinarith [hs43]
  have hcoef : 320 / s + 20 * μ^2 - 20 ≤ 0 := by
    have hb : 20 * μ^2 ≤ 20 * (79/100)^2 := by linarith
    nlinarith [hdiv, hb]
  have h2 : 320 * n / s + μ^2 * (20 * n) ≤ 20 * n := by
    have hle : n * (320 / s + 20 * μ^2 - 20) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hn0 hcoef
    have hEq2 : n * (320 / s + 20 * μ^2 - 20) = 320 * n / s + μ^2 * (20 * n) - 20 * n := by
      field_simp
    linarith [hle, hEq2]
  have hkey : 3 + 16 * μ + 320 * n / s + μ^2 * (20 * n) ≤ 20 * (k:ℝ) := by
    linarith [h1, h2, hkn]
  have hEq : 3 / s + (μ + 20 * n / s) * (16 / s) + μ ^ 2 * (20 * n / s)
      = (3 + 16 * μ + 320 * n / s + μ ^ 2 * (20 * n)) / s := by
    field_simp
    ring
  rw [hEq]
  exact div_le_div_of_nonneg_right hkey hSpos.le

end Work.CertAux
