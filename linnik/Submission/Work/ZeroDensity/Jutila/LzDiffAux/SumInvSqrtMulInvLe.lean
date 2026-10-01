import Mathlib

namespace Work.ZeroDensity.Jutila.LzDiffAux

open Finset

/-- Auxiliary square-root inequality: for `x = y + 1` with `x, y > 0` one has
`(2x+1)√y ≤ 2x√x`. -/
private lemma sqrt_key {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hxy : x = y + 1) :
    (2 * x + 1) * Real.sqrt y ≤ 2 * x * Real.sqrt x := by
  have h1 : (2 * x + 1) * Real.sqrt y = Real.sqrt ((2 * x + 1) ^ 2 * y) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  have h2 : (2 * x) * Real.sqrt x = Real.sqrt ((2 * x) ^ 2 * x) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  rw [h1, h2, Real.sqrt_le_sqrt_iff (by positivity)]
  rw [hxy]
  nlinarith [hy.le]

/-- Termwise bound: for `d ≥ 2` one has `1/(√d · d) ≤ 2/√(d-1) - 2/√d`. -/
private lemma term_le (d : ℕ) (hd : 2 ≤ d) :
    (1 : ℝ) / Real.sqrt (d : ℝ) * (1 / (d : ℝ))
      ≤ 2 / Real.sqrt ((d - 1 : ℕ) : ℝ) - 2 / Real.sqrt (d : ℝ) := by
  have hd0 : 0 < d := by omega
  have hx0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
  have hy0 : (0 : ℝ) < ((d - 1 : ℕ) : ℝ) := by
    have h : 0 < d - 1 := by omega
    exact_mod_cast h
  have hxy : (d : ℝ) = ((d - 1 : ℕ) : ℝ) + 1 := by
    have hnat : d = (d - 1) + 1 := by omega
    exact_mod_cast hnat
  have hkey := sqrt_key hx0 hy0 hxy
  have hsne : Real.sqrt (d : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hx0)
  have hxne : (d : ℝ) ≠ 0 := ne_of_gt hx0
  have hpne : (d : ℝ) * Real.sqrt (d : ℝ) ≠ 0 := mul_ne_zero hxne hsne
  have hpne' : Real.sqrt (d : ℝ) * (d : ℝ) ≠ 0 := mul_ne_zero hsne hxne
  have hmain : (2 * (d : ℝ) + 1) / ((d : ℝ) * Real.sqrt (d : ℝ))
      ≤ 2 / Real.sqrt ((d - 1 : ℕ) : ℝ) := by
    rw [div_le_div_iff₀ (by positivity) (Real.sqrt_pos.mpr hy0)]
    linarith [hkey]
  rw [le_sub_iff_add_le]
  have hadd : (1 : ℝ) / Real.sqrt (d : ℝ) * (1 / (d : ℝ)) + 2 / Real.sqrt (d : ℝ)
      = (2 * (d : ℝ) + 1) / ((d : ℝ) * Real.sqrt (d : ℝ)) := by
    field_simp
    ring
  rw [hadd]
  exact hmain

/-- Telescoping bound: `∑_{d=2}^{T} (2/√(d-1) - 2/√d) ≤ 2`. -/
private lemma sum_Icc_two_le (T : ℕ) :
    (∑ d ∈ Finset.Icc 2 T,
        (2 / Real.sqrt ((d - 1 : ℕ) : ℝ) - 2 / Real.sqrt (d : ℝ))) ≤ 2 := by
  have hreindex : (∑ d ∈ Finset.Icc 2 T,
        (2 / Real.sqrt ((d - 1 : ℕ) : ℝ) - 2 / Real.sqrt (d : ℝ)))
      = ∑ k ∈ Finset.range (T - 1),
          (2 / Real.sqrt ((k + 1 : ℕ) : ℝ) - 2 / Real.sqrt ((k + 2 : ℕ) : ℝ)) := by
    rw [show Finset.Icc 2 T = Finset.Ico 2 (T + 1) from by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_Ico]
      omega]
    rw [Finset.sum_Ico_eq_sum_range]
    rw [show (T + 1) - 2 = T - 1 from by omega]
    apply Finset.sum_congr rfl
    intro k _
    rw [show ((2 + k) - 1 : ℕ) = k + 1 from by omega,
      show (2 + k : ℕ) = k + 2 from by omega]
  rw [hreindex]
  have hcongr : (∑ k ∈ Finset.range (T - 1),
        (2 / Real.sqrt ((k + 1 : ℕ) : ℝ) - 2 / Real.sqrt ((k + 2 : ℕ) : ℝ)))
      = ∑ k ∈ Finset.range (T - 1),
          ((fun n : ℕ => -(2 / Real.sqrt ((n : ℝ) + 1))) (k + 1)
            - (fun n : ℕ => -(2 / Real.sqrt ((n : ℝ) + 1))) k) := by
    apply Finset.sum_congr rfl
    intro k _
    change 2 / Real.sqrt ((k + 1 : ℕ) : ℝ) - 2 / Real.sqrt ((k + 2 : ℕ) : ℝ)
      = -(2 / Real.sqrt (((k + 1 : ℕ) : ℝ) + 1)) - -(2 / Real.sqrt (((k : ℕ) : ℝ) + 1))
    have h2 : ((k + 2 : ℕ) : ℝ) = ((k + 1 : ℕ) : ℝ) + 1 := by push_cast; ring
    rw [h2]
    push_cast
    ring
  rw [hcongr, Finset.sum_range_sub (fun n : ℕ => -(2 / Real.sqrt ((n : ℝ) + 1))) (T - 1)]
  change -(2 / Real.sqrt (((T - 1 : ℕ) : ℝ) + 1))
      - -(2 / Real.sqrt (((0 : ℕ) : ℝ) + 1)) ≤ 2
  have h1 : (0 : ℝ) ≤ 2 / Real.sqrt (((T - 1 : ℕ) : ℝ) + 1) := by positivity
  have h2 : 2 / Real.sqrt (((0 : ℕ) : ℝ) + 1) = 2 := by norm_num [Real.sqrt_one]
  linarith

theorem SumInvSqrtMulInvLe (T : ℕ) :
    (∑ d ∈ Finset.Icc 1 T, (1 : ℝ) / Real.sqrt (d : ℝ) * (1 / (d : ℝ))) ≤ 3 := by
  rcases Nat.eq_zero_or_pos T with hT | hT
  · subst hT
    rw [show Finset.Icc 1 0 = (∅ : Finset ℕ) from by
      rw [Finset.Icc_eq_empty_iff]; omega]
    simp only [Finset.sum_empty]
    norm_num
  · have hT1 : 1 ≤ T := by omega
    have hsplit : (∑ d ∈ Finset.Icc 1 T, (1 : ℝ) / Real.sqrt (d : ℝ) * (1 / (d : ℝ)))
        = (1 : ℝ) / Real.sqrt (1 : ℝ) * (1 / (1 : ℝ))
          + ∑ d ∈ Finset.Icc 2 T, (1 : ℝ) / Real.sqrt (d : ℝ) * (1 / (d : ℝ)) := by
      have hs : Finset.Icc 1 T = insert 1 (Finset.Icc 2 T) := by
        ext x
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      have hnot : (1 : ℕ) ∉ Finset.Icc 2 T := by
        intro h
        simp only [Finset.mem_Icc] at h
        omega
      rw [hs, Finset.sum_insert hnot]
      simp only [Nat.cast_one]
    have h1 : (1 : ℝ) / Real.sqrt (1 : ℝ) * (1 / (1 : ℝ)) = 1 := by
      norm_num [Real.sqrt_one]
    have h2 : (∑ d ∈ Finset.Icc 2 T, (1 : ℝ) / Real.sqrt (d : ℝ) * (1 / (d : ℝ))) ≤ 2 :=
      (Finset.sum_le_sum (fun d hd => term_le d (Finset.mem_Icc.mp hd).1)).trans
        (sum_Icc_two_le T)
    rw [hsplit, h1]
    linarith

end Work.ZeroDensity.Jutila.LzDiffAux
