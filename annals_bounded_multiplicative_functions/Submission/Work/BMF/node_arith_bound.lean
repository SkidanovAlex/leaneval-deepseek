import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

/-- Arithmetic bound used to control a single node in the local multilinear expansion.

For `n ≥ 1`,

`n · (n+1) · (n/2)^n ≤ (n+1)^(2n+4) / 2`.

The proof chains two elementary estimates: `n ≤ n+1` and `(n/2)^n ≤ (n+1)^n`
give `n(n+1)(n/2)^n ≤ (n+1)^(n+2)`, and since `n+1 ≥ 2` we have
`2 ≤ (n+1)^(n+2)`, whence `(n+1)^(n+2) ≤ (n+1)^(2n+4)/2`. -/
theorem node_arith_bound {n : ℕ} (hn : 1 ≤ n) :
    (n:ℝ) * ((n:ℝ) + 1) * ((n:ℝ)/2)^n ≤ ((n:ℝ) + 1)^(2*n+4) / 2 := by
  have hnp0 : (0:ℝ) ≤ (n:ℝ) + 1 := by
    have : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    linarith
  have hbase : (2:ℝ) ≤ (n:ℝ) + 1 := by
    have : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    linarith
  -- `(n/2)^n ≤ (n+1)^n`
  have hA : ((n:ℝ)/2)^n ≤ ((n:ℝ)+1)^n :=
    pow_le_pow_left₀ (by positivity) (by linarith) n
  -- `n(n+1)(n/2)^n ≤ (n+1)^2 (n+1)^n`
  have hB : (n:ℝ) * ((n:ℝ)+1) * ((n:ℝ)/2)^n
      ≤ ((n:ℝ)+1) * ((n:ℝ)+1) * ((n:ℝ)+1)^n := by
    apply mul_le_mul
    · apply mul_le_mul_of_nonneg_right _ hnp0
      linarith
    · exact hA
    · positivity
    · positivity
  -- `(n+1)^2 (n+1)^n = (n+1)^(n+2)`
  have hC : ((n:ℝ)+1) * ((n:ℝ)+1) * ((n:ℝ)+1)^n = ((n:ℝ)+1)^(n+2) := by
    rw [show n + 2 = 2 + n from by omega, pow_add, sq]
  -- `2 ≤ (n+1)^(n+2)` because `n+1 ≥ 2` and `n+2 ≥ 3`
  have h2 : (2:ℝ) ≤ ((n:ℝ)+1)^(n+2) := by
    have h3 : (2:ℝ)^(n+2) ≤ ((n:ℝ)+1)^(n+2) :=
      pow_le_pow_left₀ (by norm_num) hbase (n+2)
    have h4 : (2:ℝ)^3 ≤ (2:ℝ)^(n+2) :=
      pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (by omega)
    calc (2:ℝ) ≤ (2:ℝ)^3 := by norm_num
      _ ≤ (2:ℝ)^(n+2) := h4
      _ ≤ ((n:ℝ)+1)^(n+2) := h3
  have hP : (0:ℝ) < ((n:ℝ)+1)^(n+2) := by positivity
  -- `(n+1)^(n+2) ≤ (n+1)^(2n+4)/2`
  have hfinal : ((n:ℝ)+1)^(n+2) ≤ ((n:ℝ)+1)^(2*n+4) / 2 := by
    have hkey : (2:ℝ) * ((n:ℝ)+1)^(n+2)
        ≤ ((n:ℝ)+1)^(n+2) * ((n:ℝ)+1)^(n+2) := by
      nlinarith [hP, h2]
    have hpow : ((n:ℝ)+1)^(2*n+4) = ((n:ℝ)+1)^(n+2) * ((n:ℝ)+1)^(n+2) := by
      rw [show 2*n+4 = (n+2)+(n+2) from by omega, pow_add]
    rw [hpow]
    nlinarith [hkey]
  calc (n:ℝ) * ((n:ℝ)+1) * ((n:ℝ)/2)^n
      ≤ ((n:ℝ)+1) * ((n:ℝ)+1) * ((n:ℝ)+1)^n := hB
    _ = ((n:ℝ)+1)^(n+2) := hC
    _ ≤ ((n:ℝ)+1)^(2*n+4)/2 := hfinal

end Work.BMF
