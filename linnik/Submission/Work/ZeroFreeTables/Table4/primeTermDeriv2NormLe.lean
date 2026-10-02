import Mathlib
import Submission.Work.ZeroFreeTables.Table4.eulerDerivs

/-!
# ZeroFreeTables/Table4/primeTermDeriv2NormLe

`‖d²/dz² (log p / (p^z - 1))‖ ≤ 16 (log p)^3 / p` for a prime `p` and `Re z ≥ 1` — the
pointwise bound on the second `z`-derivative of an Euler factor behind HB Table 4.
-/

open scoped Topology

namespace Work.ZeroFreeTables.Table4

theorem primeTermDeriv2NormLe (p : ℕ) (hp : p.Prime) (z : ℂ) (hz : 1 ≤ z.re) :
    ‖deriv (deriv (fun w : ℂ => (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ w - 1))) z‖
      ≤ 16 * (Real.log (p : ℝ)) ^ 3 / (p : ℝ) := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hppos : (0 : ℝ) < (p : ℝ) := by linarith only [hp2]
  have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by linarith only [hp2])
  have hpt : (p : ℝ) ≤ (p : ℝ) ^ z.re := by
    have h1 : (p : ℝ) ^ (1 : ℝ) ≤ (p : ℝ) ^ z.re :=
      Real.rpow_le_rpow_of_exponent_le (by linarith only [hp2]) hz
    rwa [Real.rpow_one] at h1
  have ht2 : (2 : ℝ) ≤ (p : ℝ) ^ z.re := le_trans hp2 hpt
  have htpos : (0 : ℝ) < (p : ℝ) ^ z.re := by linarith only [hp2, hpt]
  have hne : (p : ℂ) ^ z - 1 ≠ 0 := by
    intro h
    have h1 : ‖(p : ℂ) ^ z‖ = 1 := by rw [sub_eq_zero.mp h]; simp
    rw [cpow_norm_eq' p hp.pos z] at h1
    linarith only [hp2, hpt, h1]
  have hev : deriv (fun w : ℂ => (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ w - 1))
      =ᶠ[𝓝 z] eulerD1' p := by
    filter_upwards [eventually_half_le_re' z hz] with w hw
    exact (term_hasDerivAt' p hp w (cpow_sub_one_ne_zero_of_half' p hp w hw)).deriv
  have hnorm : ‖eulerD2' p z‖
      = (Real.log (p : ℝ)) ^ 3 * (p : ℝ) ^ z.re * ‖(p : ℂ) ^ z + 1‖
        / ‖(p : ℂ) ^ z - 1‖ ^ 3 := by
    simp only [eulerD2', norm_div, norm_mul, norm_pow]
    rw [cpow_norm_eq' p hp.pos z, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog]
    ring_nf
  rw [hev.deriv_eq, (derivTerm_hasDerivAt' p hp z hne).deriv, hnorm]
  have hplus : ‖(p : ℂ) ^ z + 1‖ ≤ (p : ℝ) ^ z.re + 1 := by
    calc ‖(p : ℂ) ^ z + 1‖ ≤ ‖(p : ℂ) ^ z‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ = (p : ℝ) ^ z.re + 1 := by rw [cpow_norm_eq' p hp.pos z]; simp
  have hden : (p : ℝ) ^ z.re - 1 ≤ ‖(p : ℂ) ^ z - 1‖ := by
    have h := norm_sub_norm_le ((p : ℂ) ^ z) 1
    rw [norm_one, cpow_norm_eq' p hp.pos z] at h
    linarith only [h]
  have hdenpos : 0 < (p : ℝ) ^ z.re - 1 := by linarith only [hp2, hpt]
  have hden3 : ((p : ℝ) ^ z.re - 1) ^ 3 ≤ ‖(p : ℂ) ^ z - 1‖ ^ 3 :=
    pow_le_pow_left₀ (le_of_lt hdenpos) hden 3
  have hkey : (p : ℝ) ^ z.re * ((p : ℝ) ^ z.re + 1) / ((p : ℝ) ^ z.re - 1) ^ 3
      ≤ 16 / (p : ℝ) := by
    have hcube : (0 : ℝ) < ((p : ℝ) ^ z.re - 1) ^ 3 := by positivity
    rw [le_div_iff₀ hppos, div_mul_eq_mul_div, div_le_iff₀ hcube]
    have hA : (p : ℝ) ^ z.re * (p : ℝ) ≤ 4 * ((p : ℝ) ^ z.re - 1) ^ 2 := by
      have h1 : (p : ℝ) ^ z.re * (p : ℝ) ≤ (p : ℝ) ^ z.re * (p : ℝ) ^ z.re :=
        mul_le_mul_of_nonneg_left hpt (by linarith only [hp2, hpt])
      have h2 : (p : ℝ) ^ z.re / 2 ≤ (p : ℝ) ^ z.re - 1 := by linarith only [hp2, hpt]
      have h3 : ((p : ℝ) ^ z.re / 2) ^ 2 ≤ ((p : ℝ) ^ z.re - 1) ^ 2 :=
        pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ (p : ℝ) ^ z.re / 2) h2 2
      linarith only [h1, h3]
    have hB : (p : ℝ) ^ z.re + 1 ≤ 3 * ((p : ℝ) ^ z.re - 1) := by linarith only [hp2, hpt]
    have hAB : (p : ℝ) ^ z.re * (p : ℝ) * ((p : ℝ) ^ z.re + 1)
        ≤ 4 * ((p : ℝ) ^ z.re - 1) ^ 2 * (3 * ((p : ℝ) ^ z.re - 1)) :=
      mul_le_mul hA hB (by linarith only [hp2, hpt]) (by positivity)
    linarith only [hAB, hcube, htpos, hdenpos]
  have hAlog : 0 ≤ (Real.log (p : ℝ)) ^ 3 * (p : ℝ) ^ z.re * ‖(p : ℂ) ^ z + 1‖ :=
    mul_nonneg (mul_nonneg (pow_nonneg hlog 3) (le_of_lt htpos)) (norm_nonneg _)
  calc (Real.log (p : ℝ)) ^ 3 * (p : ℝ) ^ z.re * ‖(p : ℂ) ^ z + 1‖ / ‖(p : ℂ) ^ z - 1‖ ^ 3
      ≤ (Real.log (p : ℝ)) ^ 3 * (p : ℝ) ^ z.re * ((p : ℝ) ^ z.re + 1)
          / ((p : ℝ) ^ z.re - 1) ^ 3 := by
        refine le_trans (div_le_div_of_nonneg_left hAlog (by positivity) hden3) ?_
        apply div_le_div_of_nonneg_right _ (pow_nonneg (le_of_lt hdenpos) 3)
        exact mul_le_mul_of_nonneg_left hplus
          (mul_nonneg (pow_nonneg hlog 3) (le_of_lt htpos))
    _ = (Real.log (p : ℝ)) ^ 3 *
          ((p : ℝ) ^ z.re * ((p : ℝ) ^ z.re + 1) / ((p : ℝ) ^ z.re - 1) ^ 3) := by ring
    _ ≤ (Real.log (p : ℝ)) ^ 3 * (16 / (p : ℝ)) :=
        mul_le_mul_of_nonneg_left hkey (pow_nonneg hlog 3)
    _ = 16 * (Real.log (p : ℝ)) ^ 3 / (p : ℝ) := by ring

end Work.ZeroFreeTables.Table4
