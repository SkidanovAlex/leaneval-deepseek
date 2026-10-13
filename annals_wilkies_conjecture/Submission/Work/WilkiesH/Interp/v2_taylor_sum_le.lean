import Mathlib
import Submission.Work.WilkiesH.Defs

namespace Work.WilkiesH.Interp

open Finset

/-- The term-wise form of `v2_taylor_sum_le`: the `j`-th summand of the left-hand side is
bounded by the `j`-th summand of the right-hand side, using `‖t - s₀‖ ≤ √μ * ρ` and
`μ^j * (√μ)^j = (√μ)^(3j)`. -/
private lemma taylor_term_le {μ b d j : ℕ} {ρ : ℝ} {t s₀ : Fin μ → ℝ} (hρ : 0 ≤ ρ)
    (hlt : ‖t - s₀‖ ≤ Real.sqrt (μ:ℝ) * ρ) (hjb : j ≤ b) :
    ((μ:ℝ)^j * ρ^(b-j) * Real.sqrt (Work.WilkiesH.monoCount (μ+1) d : ℝ) * (d:ℝ)^j)
        * ‖t - s₀‖^j / (((j.factorial : ℕ):ℝ))
      ≤ Real.sqrt (Work.WilkiesH.monoCount (μ+1) d : ℝ) * ρ^b
          * ((Real.sqrt (μ:ℝ))^(3*j) * (d:ℝ)^j / (((j.factorial:ℕ):ℝ))) := by
  set M := Real.sqrt (Work.WilkiesH.monoCount (μ+1) d : ℝ) with hMdef
  have hM : 0 ≤ M := Real.sqrt_nonneg _
  -- `μ^j * (√μ)^j = (√μ)^(3j)`, since `(√μ)^2 = μ`
  have hsq : (Real.sqrt (μ:ℝ))^2 = (μ:ℝ) := Real.sq_sqrt (Nat.cast_nonneg μ)
  have hkp : (μ:ℝ)^j * (Real.sqrt (μ:ℝ))^j = (Real.sqrt (μ:ℝ))^(3*j) := by
    calc (μ:ℝ)^j * (Real.sqrt (μ:ℝ))^j
        = ((Real.sqrt (μ:ℝ))^2)^j * (Real.sqrt (μ:ℝ))^j := by rw [hsq]
      _ = (Real.sqrt (μ:ℝ))^(2*j) * (Real.sqrt (μ:ℝ))^j := by rw [pow_mul]
      _ = (Real.sqrt (μ:ℝ))^(2*j + j) := by rw [← pow_add]
      _ = (Real.sqrt (μ:ℝ))^(3*j) := by ring_nf
  have h1 : ρ^(b-j) * ρ^j = ρ^b := by rw [← pow_add, Nat.sub_add_cancel hjb]
  have hnorm : ‖t - s₀‖^j ≤ (Real.sqrt (μ:ℝ) * ρ)^j :=
    pow_le_pow_left₀ (norm_nonneg _) hlt j
  have hC : 0 ≤ (μ:ℝ)^j * ρ^(b-j) * (d:ℝ)^j := by positivity
  -- the `M`-free term bound
  have hkey : ((μ:ℝ)^j * ρ^(b-j) * (d:ℝ)^j) * ‖t - s₀‖^j
      ≤ ρ^b * ((Real.sqrt (μ:ℝ))^(3*j) * (d:ℝ)^j) := by
    have heq : ((μ:ℝ)^j * ρ^(b-j) * (d:ℝ)^j) * ((Real.sqrt (μ:ℝ))*ρ)^j
        = ρ^b * ((Real.sqrt (μ:ℝ))^(3*j) * (d:ℝ)^j) := by
      rw [mul_pow]
      rw [show ((μ:ℝ)^j * ρ^(b-j) * (d:ℝ)^j) * (Real.sqrt (μ:ℝ)^j * ρ^j)
            = ((μ:ℝ)^j * (Real.sqrt (μ:ℝ))^j) * (ρ^(b-j) * ρ^j) * (d:ℝ)^j from by ring]
      rw [hkp, h1]; ring
    calc ((μ:ℝ)^j * ρ^(b-j) * (d:ℝ)^j) * ‖t - s₀‖^j
        ≤ ((μ:ℝ)^j * ρ^(b-j) * (d:ℝ)^j) * ((Real.sqrt (μ:ℝ))*ρ)^j :=
          mul_le_mul_of_nonneg_left hnorm hC
      _ = ρ^b * ((Real.sqrt (μ:ℝ))^(3*j) * (d:ℝ)^j) := heq
  have hf : (0:ℝ) < ((j.factorial : ℕ):ℝ) := by positivity
  have hkey2 : M * (((μ:ℝ)^j * ρ^(b-j) * (d:ℝ)^j) * ‖t - s₀‖^j)
      ≤ M * (ρ^b * ((Real.sqrt (μ:ℝ))^(3*j) * (d:ℝ)^j)) :=
    mul_le_mul_of_nonneg_left hkey hM
  have hdiv := div_le_div_of_nonneg_right hkey2 hf.le
  rw [hMdef] at hdiv
  have e1 : ((μ:ℝ)^j * ρ^(b-j) * Real.sqrt (↑(Work.WilkiesH.monoCount (μ+1) d))
        * (d:ℝ)^j) * ‖t - s₀‖^j / ((j.factorial : ℕ):ℝ)
      = (Real.sqrt (↑(Work.WilkiesH.monoCount (μ+1) d))
          * (((μ:ℝ)^j * ρ^(b-j) * (d:ℝ)^j) * ‖t - s₀‖^j)) / ((j.factorial : ℕ):ℝ) := by
    ring
  have e2 : Real.sqrt (↑(Work.WilkiesH.monoCount (μ+1) d)) * ρ^b
        * ((Real.sqrt (μ:ℝ))^(3*j) * (d:ℝ)^j / ((j.factorial : ℕ):ℝ))
      = Real.sqrt (↑(Work.WilkiesH.monoCount (μ+1) d))
          * (ρ^b * ((Real.sqrt (μ:ℝ))^(3*j) * (d:ℝ)^j)) / ((j.factorial : ℕ):ℝ) := by
    ring
  rw [e1, e2]
  exact hdiv

theorem v2_taylor_sum_le {μ b d : ℕ} {ρ : ℝ} {t s₀ : Fin μ → ℝ}
    (hρ : 0 ≤ ρ) (hlt : ‖t - s₀‖ ≤ Real.sqrt (μ : ℝ) * ρ) :
    (∑ j ∈ Finset.range (b + 1),
        ((μ : ℝ) ^ j * ρ ^ (b - j) * Real.sqrt (Work.WilkiesH.monoCount (μ + 1) d : ℝ)
            * (d : ℝ) ^ j) * ‖t - s₀‖ ^ j / (((j.factorial : ℕ) : ℝ)))
      ≤ Real.sqrt (Work.WilkiesH.monoCount (μ + 1) d : ℝ) * ρ ^ b
          * (∑ j ∈ Finset.range (b + 1),
              ((Real.sqrt (μ : ℝ)) ^ (3 * j) * (d : ℝ) ^ j) / ((((j.factorial : ℕ) : ℝ)))) := by
  have hterm : ∀ j ∈ Finset.range (b + 1),
      ((μ : ℝ) ^ j * ρ ^ (b - j) * Real.sqrt (Work.WilkiesH.monoCount (μ + 1) d : ℝ)
          * (d : ℝ) ^ j) * ‖t - s₀‖ ^ j / (((j.factorial : ℕ) : ℝ))
      ≤ Real.sqrt (Work.WilkiesH.monoCount (μ + 1) d : ℝ) * ρ ^ b
          * ((Real.sqrt (μ : ℝ)) ^ (3 * j) * (d : ℝ) ^ j / (((j.factorial : ℕ) : ℝ))) := by
    intro j hj
    exact taylor_term_le hρ hlt (by have := Finset.mem_range.mp hj; omega)
  have hsum := Finset.sum_le_sum hterm
  have hR : (∑ j ∈ Finset.range (b + 1),
        Real.sqrt (Work.WilkiesH.monoCount (μ + 1) d : ℝ) * ρ ^ b
          * ((Real.sqrt (μ : ℝ)) ^ (3 * j) * (d : ℝ) ^ j / (((j.factorial : ℕ) : ℝ))))
      = Real.sqrt (Work.WilkiesH.monoCount (μ + 1) d : ℝ) * ρ ^ b
          * (∑ j ∈ Finset.range (b + 1),
              ((Real.sqrt (μ : ℝ)) ^ (3 * j) * (d : ℝ) ^ j) / (((j.factorial : ℕ) : ℝ))) := by
    rw [Finset.mul_sum]
  exact hsum.trans_eq hR

end Work.WilkiesH.Interp
