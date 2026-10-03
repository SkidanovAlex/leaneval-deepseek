import Mathlib
import Submission.Work.FIArea4.logSine_deriv2_base
import Submission.Work.FIArea4.logSine_psi_global_bound
import Submission.Work.FIArea4.one_sub_cos_ge_two_div_sq
import Submission.Work.FIArea4.logSine_psi_deriv
import Submission.Work.FIArea4.logSine_defs

namespace Work.FIArea4

/-- Pointwise bound for `u_N''` on the "middle" range `5/(2N) ≤ α ≤ π/2` (`N ≥ 3`), where both
`1 - cos α ≥ 2/N²` (`one_sub_cos_ge_two_div_sq`) and `1 + cos α ≥ 1 ≥ 2/N²`, so that
`Ψ_N'`, `Ψ_N''` are given by their exact off-window formulas `1/(2y)`, `-1/(2y²)`.  The result is
`≤ (144/43)(1/α² + 1) + 1`, which is integrable with `∫ dα/α² ≲ N`. -/
theorem logSine_deriv2_le_regionB (N : ℕ) (hN : 3 ≤ N) (K : ℝ) (hK : 1 ≤ K)
    (hK1 : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ K)
    (hK2 : ∀ x : ℝ, |deriv (deriv Real.smoothTransition) x| ≤ K) {α : ℝ}
    (hα1 : 5 / (2 * (N:ℝ)) ≤ α) (hαp : α ≤ Real.pi / 2) :
    |deriv (deriv (ufun N)) α| ≤ (144/43) * (1/α^2 + 1) + 1 := by
  have hN2 : 2 ≤ N := by omega
  have hN1 : 1 ≤ N := by omega
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hNsq : (0:ℝ) < (N:ℝ)^2 := by positivity
  have hαpos : 0 < α := lt_of_lt_of_le (by positivity) hα1
  have hαpi : α < Real.pi := by linarith [Real.pi_pos, hαp]
  -- `cos α ≥ 0`
  have hcosnn : 0 ≤ Real.cos α := by
    apply Real.cos_nonneg_of_mem_Icc
    rw [Set.mem_Icc]
    exact ⟨by linarith [Real.pi_pos, hαpos.le], hαp⟩
  -- `2/N² ≤ 1` and hence `2/N² ≤ 1 + cos α`
  have h2le1 : 2 / (N:ℝ)^2 ≤ 1 := by
    rw [div_le_one hNsq]
    have hN2r : (2:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN2
    nlinarith [sq_nonneg ((N:ℝ) - 2)]
  have hh2 : 2 / (N:ℝ)^2 ≤ 1 + Real.cos α := by linarith
  -- `2/N² ≤ 1 - cos α`
  have hg2 : 2 / (N:ℝ)^2 ≤ 1 - Real.cos α := one_sub_cos_ge_two_div_sq N hN hα1 hαp
  have h1cpos : 0 < 1 - Real.cos α :=
    lt_of_lt_of_le (by positivity : (0:ℝ) < 2/(N:ℝ)^2) hg2
  have h1cpos' : 0 < 1 + Real.cos α := by linarith
  -- exact off-window formulas for `Ψ_N` at `1 ± cos α`
  obtain ⟨hP1, hP2, _, _, _⟩ := logSine_psi_deriv N hN2 K hK hK1 hK2
  have hsinαpos : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hαpos hαpi
  -- rewrite `u_N''` with the exact expressions and evaluate it
  simp only [deriv_deriv_ufun_eq N hN1]
  rw [hP1 (1 + Real.cos α) hh2, hP1 (1 - Real.cos α) hg2,
      hP2 (1 - Real.cos α) hg2, hP2 (1 + Real.cos α) hh2]
  have hkey : Real.cos α * (1 / (2 * (1 + Real.cos α)) - 1 / (2 * (1 - Real.cos α)))
        - Real.sin α ^ 2 * (-(1 / (2 * (1 - Real.cos α) ^ 2)) + -(1 / (2 * (1 + Real.cos α) ^ 2)))
      = 1 / Real.sin α ^ 2 := by
    have hs2 : Real.sin α ^ 2 = (1 - Real.cos α) * (1 + Real.cos α) := by
      rw [Real.sin_sq]; ring
    rw [hs2]
    field_simp
    ring
  rw [hkey, abs_of_pos (one_div_pos.mpr (pow_pos hsinαpos 2))]
  -- now bound `1/sin²α ≤ π²/(4α²) ≤ (144/43)(1/α²+1)+1`
  have hsinlow : 2 / Real.pi * α ≤ Real.sin α := Real.mul_le_sin hαpos.le hαp
  have hlowpos : 0 < 2 / Real.pi * α := by positivity
  have hsq : (2 / Real.pi * α)^2 ≤ Real.sin α ^ 2 :=
    pow_le_pow_left₀ hlowpos.le hsinlow 2
  have hA : 1 / Real.sin α ^ 2 ≤ 1 / (2 / Real.pi * α)^2 :=
    one_div_le_one_div_of_le (pow_pos hlowpos 2) hsq
  have hB : 1 / (2 / Real.pi * α)^2 = (Real.pi^2 / 4) * (1/α^2) := by
    field_simp
    ring
  have hC : Real.pi^2 / 4 ≤ 144/43 := by
    nlinarith [Real.pi_lt_d4, Real.pi_pos]
  have hD : (Real.pi^2 / 4) * (1/α^2) ≤ (144/43) * (1/α^2 + 1) + 1 := by
    have hα2inv : 0 ≤ 1/α^2 := by positivity
    nlinarith [hC, hα2inv]
  rw [hB] at hA
  linarith [hA, hD]

end Work.FIArea4
