import Mathlib
import Submission.Work.LinnikAreas.Density4.selberg_U_aux

namespace Work.LinnikAreas.Density4.Udecay

open MeasureTheory
open scoped BigOperators

/-- On a unit interval `[k, k+1]` with `k ≥ 1`, `muRecip` equals the constant `muRecipSum k`
(up to the endpoints, which are null), so the integral of `muRecip t / t` against `dt` is
`muRecipSum k · (log(k+1) - log k)`. -/
theorem muRecip_unit_integral (k : ℕ) (hk : 1 ≤ k) :
    ∫ t in (k : ℝ)..((k : ℝ) + 1), Work.LinnikAreas.Density4.muRecip t / t
      = Commons.NumberTheory.Moebius.muRecipSum k * (Real.log ((k : ℝ) + 1) - Real.log (k : ℝ)) := by
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hkp1pos : (0 : ℝ) < (k : ℝ) + 1 := by linarith
  have hk_le : (k : ℝ) ≤ (k : ℝ) + 1 := by linarith
  -- `muRecip` is constant on the open interval `(k, k+1)`, hence a.e. on `[k, k+1]`.
  have hstep : ∫ t in (k : ℝ)..((k : ℝ) + 1), Work.LinnikAreas.Density4.muRecip t / t
      = ∫ t in (k : ℝ)..((k : ℝ) + 1), Commons.NumberTheory.Moebius.muRecipSum k / t := by
    apply intervalIntegral.integral_congr_Ioo_of_le hk_le
    intro t ht
    have htpos : (0 : ℝ) < t := lt_trans hkpos ht.1
    have hfloor : ⌊t⌋₊ = k :=
      (Nat.floor_eq_iff (le_of_lt htpos)).mpr ⟨le_of_lt ht.1, ht.2⟩
    simp only [Work.LinnikAreas.Density4.muRecip, hfloor]
  -- pull the constant factor out of the integral.
  have hconst : ∫ t in (k : ℝ)..((k : ℝ) + 1), Commons.NumberTheory.Moebius.muRecipSum k / t
      = Commons.NumberTheory.Moebius.muRecipSum k
          * ∫ t in (k : ℝ)..((k : ℝ) + 1), (1 : ℝ) / t := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    ring
  -- `∫ dt/t = log(k+1) - log k`.
  have hlog : ∫ t in (k : ℝ)..((k : ℝ) + 1), (1 : ℝ) / t
      = Real.log ((k : ℝ) + 1) - Real.log (k : ℝ) := by
    rw [integral_one_div_of_pos hkpos hkp1pos,
      Real.log_div (ne_of_gt hkp1pos) (ne_of_gt hkpos)]
  rw [hstep, hconst, hlog]

end Work.LinnikAreas.Density4.Udecay
