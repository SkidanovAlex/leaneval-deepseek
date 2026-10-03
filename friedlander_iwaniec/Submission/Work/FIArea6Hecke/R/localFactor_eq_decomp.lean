import Mathlib
import Submission.Work.FIArea6Hecke.R.PrincipalCharAux
import Submission.Work.FIArea6Hecke.R.AxisLogDefs

namespace Work.FIArea6Hecke.R

theorem localFactor_eq_decomp {d : ℕ} (hd : 1 ≤ d) {p : ℕ} (hp : p.Prime) {s : ℂ} (hs : 1 < s.re) :
    (if p ∣ 4 * d then (1 : ℂ) else
        ((1 - (p : ℂ) ^ (-s)) * (1 - Work.FIArea6Hecke.R.chi4fun p * (p : ℂ) ^ (-s)))⁻¹)
      = (1 - (p : ℂ) ^ (-s))⁻¹ * (1 - Work.FIArea6Hecke.R.chi4fun p * (p : ℂ) ^ (-s))⁻¹ *
        (if p ∈ (4 * d).primeFactors then
          (1 - (p : ℂ) ^ (-s)) * (1 - Work.FIArea6Hecke.R.chi4fun p * (p : ℂ) ^ (-s))
         else 1) := by
  have hp_pos : 0 < p := hp.pos
  have hnorm : ‖(p : ℂ) ^ (-s)‖ < 1 := by
    rw [Complex.norm_natCast_cpow_of_pos hp_pos, Complex.neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by linarith)
  have hA : (1 - (p : ℂ) ^ (-s)) ≠ 0 := by
    intro h
    have hx : (p : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp h).symm
    rw [hx, norm_one] at hnorm
    exact lt_irrefl 1 hnorm
  have hnorm2 : ‖chi4fun p * (p : ℂ) ^ (-s)‖ < 1 := by
    rw [norm_mul]
    calc ‖chi4fun p‖ * ‖(p : ℂ) ^ (-s)‖ ≤ 1 * ‖(p : ℂ) ^ (-s)‖ :=
          mul_le_mul_of_nonneg_right (chi4fun_norm_le_one p) (norm_nonneg _)
      _ = ‖(p : ℂ) ^ (-s)‖ := one_mul _
      _ < 1 := hnorm
  have hB : (1 - chi4fun p * (p : ℂ) ^ (-s)) ≠ 0 := by
    intro h
    have hx : chi4fun p * (p : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp h).symm
    rw [hx, norm_one] at hnorm2
    exact lt_irrefl 1 hnorm2
  have h4d : 4 * d ≠ 0 := by omega
  by_cases hpd : p ∣ 4 * d
  · have hmem : p ∈ (4 * d).primeFactors := hp.mem_primeFactors hpd h4d
    rw [if_pos hpd, if_pos hmem, ← mul_inv, inv_mul_cancel₀ (mul_ne_zero hA hB)]
  · have hnotmem : p ∉ (4 * d).primeFactors := by
      intro h; exact hpd ((Nat.mem_primeFactors.mp h).2.1)
    rw [if_neg hpd, if_neg hnotmem, mul_one, mul_inv]

end Work.FIArea6Hecke.R
