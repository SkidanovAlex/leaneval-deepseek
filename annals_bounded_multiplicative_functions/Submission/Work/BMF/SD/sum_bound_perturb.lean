import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.SD

/-- A perturbative geometric-sum bound: for `L ≥ 1`, the sum
`∑_{j=2}^k (C₂/L^j) * (4^j * L^{j-1})` is at most `4^{k+1} * C₂ / L`.

Indeed each summand equals `C₂ * 4^j / L`, and `∑_{j=2}^k 4^j ≤ 4^{k+1}`. -/
theorem sum_bound_perturb (k L : ℕ) (C₂ : ℝ) (hL : 1 ≤ L) (hC₂ : 0 ≤ C₂) :
    (∑ j ∈ Finset.Icc 2 k, (C₂ / (L:ℝ)^j) * ((4:ℝ)^j * (L:ℝ)^(j-1)))
      ≤ (4:ℝ)^(k+1) * C₂ / (L:ℝ) := by
  have hLpos : (0:ℝ) < (L:ℝ) := by exact_mod_cast (by omega : 0 < L)
  have hLne : (L:ℝ) ≠ 0 := ne_of_gt hLpos
  -- Each summand simplifies: `L^{j-1}/L^j = 1/L`.
  have hterm : ∀ j ∈ Finset.Icc 2 k,
      (C₂ / (L:ℝ)^j) * ((4:ℝ)^j * (L:ℝ)^(j-1)) = C₂ * (4:ℝ)^j / (L:ℝ) := by
    intro j hj
    have hj1 : 1 ≤ j := by
      have := (Finset.mem_Icc.mp hj).1
      omega
    have hpow : (L:ℝ)^j = (L:ℝ)^(j-1) * (L:ℝ) := by
      conv_lhs => rw [← Nat.sub_add_cancel hj1]
      rw [pow_add, pow_one]
    rw [hpow]
    have hLp : (L:ℝ)^(j-1) ≠ 0 := pow_ne_zero _ hLne
    field_simp [hLne, hLp]
  rw [Finset.sum_congr rfl hterm]
  -- Factor out the common term `C₂ / L`.
  have hfactor : ∑ j ∈ Finset.Icc 2 k, C₂ * (4:ℝ)^j / (L:ℝ)
      = (C₂ / (L:ℝ)) * ∑ j ∈ Finset.Icc 2 k, (4:ℝ)^j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hfactor]
  -- Geometric bound `∑_{j=2}^k 4^j ≤ 4^{k+1}`.
  have hgeom : (∑ j ∈ Finset.Icc 2 k, (4:ℝ)^j) ≤ (4:ℝ)^(k+1) := by
    have hnat : ∑ j ∈ Finset.Icc 2 k, (4:ℕ)^j < (4:ℕ)^(k+1) := by
      apply Nat.geomSum_lt (n := k+1) (s := Finset.Icc 2 k) (by norm_num)
      intro j hj
      exact Nat.lt_succ_of_le (Finset.mem_Icc.mp hj).2
    have hcast : ((∑ j ∈ Finset.Icc 2 k, (4:ℕ)^j : ℕ) : ℝ) = ∑ j ∈ Finset.Icc 2 k, (4:ℝ)^j := by
      push_cast
      simp
    have hcast2 : ((4:ℕ)^(k+1) : ℝ) = (4:ℝ)^(k+1) := by push_cast; simp
    rw [← hcast, ← hcast2]
    exact_mod_cast hnat.le
  have hCL : (0:ℝ) ≤ C₂ / (L:ℝ) := div_nonneg hC₂ hLpos.le
  calc (C₂ / (L:ℝ)) * (∑ j ∈ Finset.Icc 2 k, (4:ℝ)^j)
      ≤ (C₂ / (L:ℝ)) * (4:ℝ)^(k+1) := mul_le_mul_of_nonneg_left hgeom hCL
    _ = (4:ℝ)^(k+1) * C₂ / (L:ℝ) := by ring

end Work.BMF.SD
