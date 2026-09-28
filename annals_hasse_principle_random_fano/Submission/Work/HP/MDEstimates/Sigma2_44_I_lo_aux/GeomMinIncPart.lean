import Mathlib

namespace Work.HP.MDEstimates.Sigma2_44_I_lo_aux

/-- For `a ≥ 0`, a natural power and a real power commute:
`(a ^ j) ^ s = (a ^ s) ^ j`. -/
lemma pow_rpow_eq_rpow_pow {a : ℝ} (ha : 0 ≤ a) (j : ℕ) (s : ℝ) :
    (a ^ j) ^ s = (a ^ s) ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, pow_succ]
    rw [Real.mul_rpow (pow_nonneg ha j) ha, ih]

/-- Geometric sum bound: for `ρ > 1`, `∑_{i<n} ρ^i ≤ ρ^n / (ρ - 1)`. -/
private lemma geom_range_le' {ρ : ℝ} (hρ : 1 < ρ) (n : ℕ) :
    (∑ i ∈ Finset.range n, ρ ^ i) ≤ ρ ^ n / (ρ - 1) := by
  have hne : ρ ≠ 1 := ne_of_gt hρ
  rw [geom_sum_eq hne n]
  have hpos : 0 < ρ - 1 := by linarith
  apply div_le_div_of_nonneg_right _ hpos.le
  have hp : (0:ℝ) < ρ ^ n := pow_pos (lt_trans zero_lt_one hρ) n
  linarith

theorem GeomMinIncPart {a θ : ℝ} (ha : 1 < a) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    {N C : ℝ} (hN : 0 < N) (hC : 0 < C) {k n : ℕ} (hk : 1 ≤ k)
    (hcross : a ^ (k-1) ≤ N / C) :
    (∑ j ∈ Finset.range (n+1), (if j < k then C * (a^j)^(1-θ) else 0))
      ≤ a^(1-θ) / (a^(1-θ) - 1) * C^θ * N^(1-θ) := by
  have ha0 : 0 ≤ a := le_of_lt (lt_trans zero_lt_one ha)
  have h1mθ : 0 < 1 - θ := by linarith
  -- write `R = a ^ (1-θ)`; note `1 < R` since `a > 1` and `1-θ > 0`.
  set R : ℝ := a ^ (1 - θ) with hRdef
  have hR1 : 1 < R := by rw [hRdef]; exact Real.one_lt_rpow ha h1mθ
  have hR0 : 0 < R := lt_trans zero_lt_one hR1
  -- replace each summand `(a^j)^(1-θ)` by `R^j`.
  have hsum_eq : (∑ j ∈ Finset.range (n+1), (if j < k then C * (a^j)^(1-θ) else 0))
      = ∑ j ∈ Finset.range (n+1), (if j < k then C * R^j else 0) := by
    apply Finset.sum_congr rfl
    intro j _
    by_cases hjk : j < k
    · rw [ite_eq_left hjk, ite_eq_left hjk, hRdef, pow_rpow_eq_rpow_pow ha0 j (1-θ)]
    · rw [ite_eq_right hjk, ite_eq_right hjk]
  rw [hsum_eq]
  -- the restricted sum is at most the full geometric sum over `range k`.
  have hle1 : (∑ j ∈ Finset.range (n+1), (if j < k then C * R^j else 0))
      ≤ ∑ j ∈ Finset.range k, C * R^j := by
    rw [← Finset.sum_filter]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
      exact hi.2
    · intro i _ _
      exact mul_nonneg hC.le (pow_nonneg hR0.le i)
  -- geometric series bound.
  have hle2 : (∑ j ∈ Finset.range k, C * R^j) ≤ C * (R ^ k / (R - 1)) := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (geom_range_le' hR1 k) hC.le
  -- the arithmetic core: `C * R^k ≤ R * C^θ * N^(1-θ)`.
  have harith : C * (R ^ k / (R - 1)) ≤ R / (R - 1) * C ^ θ * N ^ (1 - θ) := by
    have hR1' : 0 < R - 1 := by linarith
    have key : C * R ^ k ≤ R * C ^ θ * N ^ (1 - θ) := by
      have hk1 : k - 1 + 1 = k := Nat.sub_add_cancel hk
      have hRk : R ^ k = R ^ (k - 1) * R := by
        calc R ^ k = R ^ (k - 1 + 1) := by rw [hk1]
          _ = R ^ (k - 1) * R ^ 1 := by rw [pow_add]
          _ = R ^ (k - 1) * R := by rw [pow_one]
      have hRpow : R ^ (k - 1) = (a ^ (k - 1)) ^ (1 - θ) := by
        rw [hRdef]
        exact (pow_rpow_eq_rpow_pow ha0 (k-1) (1-θ)).symm
      -- `C * a^(k-1) ≤ N` from the cross condition.
      have hca : C * a ^ (k - 1) ≤ N := by
        have h := mul_le_mul_of_nonneg_left hcross hC.le
        rwa [mul_div_cancel₀ N (ne_of_gt hC)] at h
      have hmono : (C * a ^ (k - 1)) ^ (1 - θ) ≤ N ^ (1 - θ) :=
        Real.rpow_le_rpow (mul_nonneg hC.le (pow_nonneg ha0 (k-1))) hca (le_of_lt h1mθ)
      rw [Real.mul_rpow hC.le (pow_nonneg ha0 (k-1))] at hmono
      have hcomb : C ^ (1 - θ) * C ^ θ = C := by
        rw [← Real.rpow_add hC, show (1 - θ) + θ = 1 by ring, Real.rpow_one]
      have hstep : C * (a ^ (k - 1)) ^ (1 - θ) ≤ N ^ (1 - θ) * C ^ θ := by
        have hmul := mul_le_mul_of_nonneg_right hmono (Real.rpow_nonneg hC.le θ)
        calc C * (a ^ (k - 1)) ^ (1 - θ)
            = C ^ (1 - θ) * C ^ θ * (a ^ (k - 1)) ^ (1 - θ) := by rw [hcomb]
          _ = C ^ (1 - θ) * (a ^ (k - 1)) ^ (1 - θ) * C ^ θ := by ring
          _ ≤ N ^ (1 - θ) * C ^ θ := hmul
      have hmul2 := mul_le_mul_of_nonneg_right hstep hR0.le
      calc C * R ^ k = C * (R ^ (k - 1) * R) := by rw [hRk]
        _ = C * (a ^ (k - 1)) ^ (1 - θ) * R := by rw [hRpow]; ring
        _ ≤ N ^ (1 - θ) * C ^ θ * R := hmul2
        _ = R * C ^ θ * N ^ (1 - θ) := by ring
    calc C * (R ^ k / (R - 1)) = (C * R ^ k) / (R - 1) := by ring
      _ ≤ (R * C ^ θ * N ^ (1 - θ)) / (R - 1) := div_le_div_of_nonneg_right key hR1'.le
      _ = R / (R - 1) * C ^ θ * N ^ (1 - θ) := by ring
  linarith [hle1, hle2, harith]

end Work.HP.MDEstimates.Sigma2_44_I_lo_aux
