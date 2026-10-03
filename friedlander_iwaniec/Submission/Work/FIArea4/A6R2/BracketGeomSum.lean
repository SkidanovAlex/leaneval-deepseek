import Mathlib

namespace Work.FIArea4.A6R2

open Finset
open scoped BigOperators

/-- Geometric bound for the base `2`: `∑_{k<n} 2^k ≤ 2^n`. -/
lemma geom_two_le (n : ℕ) : (∑ k ∈ Finset.range n, (2:ℝ)^k) ≤ (2:ℝ)^n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, pow_succ]
      have h : (0:ℝ) ≤ (2:ℝ)^n := by positivity
      linarith

/-- Geometric bound with ratio `c ≥ 5/4`: the partial sum of `m+1` terms is at most
`5 · c^m`. -/
lemma geom_c_le (c : ℝ) (hc : (5:ℝ)/4 ≤ c) (m : ℕ) :
    (∑ k ∈ Finset.range (m+1), c^k) ≤ 5 * c^m := by
  induction m with
  | zero => simp
  | succ n ih =>
      have hcn : (0:ℝ) ≤ c^n := by positivity
      have hstep : (5:ℝ) + c ≤ 5 * c := by linarith
      calc (∑ k ∈ Finset.range (n+1+1), c^k)
          = (∑ k ∈ Finset.range (n+1), c^k) + c^(n+1) := Finset.sum_range_succ _ _
        _ ≤ 5 * c^n + c^(n+1) := by linarith
        _ = c^n * (5 + c) := by rw [pow_succ]; ring
        _ ≤ c^n * (5 * c) := mul_le_mul_of_nonneg_left hstep hcn
        _ = 5 * c^(n+1) := by rw [pow_succ]; ring

/-- Rewriting lemma: the `(1/3)`-power of `2^k` is `(2^{1/3})^k`. -/
lemma rpow_two_third (k : ℕ) : ((2:ℝ)^k)^((1:ℝ)/3) = ((2:ℝ)^((1:ℝ)/3))^k := by
  have h2 : (0:ℝ) ≤ 2 := by norm_num
  rw [← Real.rpow_natCast_mul h2 k (1/3)]
  rw [show (k:ℝ) * ((1:ℝ)/3) = ((1:ℝ)/3) * (k:ℝ) by ring]
  exact Real.rpow_mul_natCast h2 ((1:ℝ)/3) k

/-- `2^{1/3} ≥ 5/4`. -/
lemma cbrt_two_ge : (5:ℝ)/4 ≤ (2:ℝ)^((1:ℝ)/3) := by
  have h43 : ((5:ℝ)/4)^3 ≤ 2 := by norm_num
  have hcast : ((5:ℝ)/4)^3 = ((5:ℝ)/4)^((3:ℕ):ℝ) := (Real.rpow_natCast _ 3).symm
  have hbase : (((5:ℝ)/4)^3)^((1:ℝ)/3) = (5:ℝ)/4 := by
    rw [hcast, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ (5:ℝ)/4)]
    rw [show ((3:ℕ):ℝ) * ((1:ℝ)/3) = 1 by norm_num, Real.rpow_one]
  have h := Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ ((5:ℝ)/4)^3) h43
    (by norm_num : (0:ℝ) ≤ (1:ℝ)/3)
  rwa [hbase] at h

/-- Numeric input: `5 · 4^{1/3} ≤ 16`. -/
lemma five_mul_cbrt_four_le : 5 * (4:ℝ)^((1:ℝ)/3) ≤ 16 := by
  have h : (4:ℝ)^((1:ℝ)/3) ≤ 16/5 := by
    have h43 : (4:ℝ) ≤ ((16:ℝ)/5)^3 := by norm_num
    have hcast : ((16:ℝ)/5)^3 = ((16:ℝ)/5)^((3:ℕ):ℝ) := (Real.rpow_natCast _ 3).symm
    have hbase : (((16:ℝ)/5)^3)^((1:ℝ)/3) = (16:ℝ)/5 := by
      rw [hcast, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ (16:ℝ)/5)]
      rw [show ((3:ℕ):ℝ) * ((1:ℝ)/3) = 1 by norm_num, Real.rpow_one]
    have h2 := Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ (4:ℝ)) h43
      (by norm_num : (0:ℝ) ≤ (1:ℝ)/3)
    rwa [hbase] at h2
  linarith

theorem BracketGeomSum (T : Finset ℕ) (kmax : ℕ) (hkmax : kmax ∈ T)
    (hle : ∀ k ∈ T, k ≤ kmax) {y : ℝ} (hy : 0 < y) (hbd : (2:ℝ)^kmax < 4*y) :
    (∑ k ∈ T, (2:ℝ)^k) ≤ 16 * y
      ∧ (∑ k ∈ T, ((2:ℝ)^k)^((1:ℝ)/3)) ≤ 16 * y^((1:ℝ)/3) := by
  have hsub : T ⊆ Finset.range (kmax+1) := by
    intro k hk
    simp only [Finset.mem_range]
    exact Nat.lt_succ_of_le (hle k hk)
  constructor
  · have h1 : (∑ k ∈ T, (2:ℝ)^k) ≤ ∑ k ∈ Finset.range (kmax+1), (2:ℝ)^k :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => by positivity)
    have h2 : (∑ k ∈ Finset.range (kmax+1), (2:ℝ)^k) ≤ (2:ℝ)^(kmax+1) := geom_two_le _
    have h3 : (2:ℝ)^(kmax+1) = (2:ℝ)^kmax * 2 := pow_succ _ _
    have h4 : (2:ℝ)^kmax * 2 < 8 * y := by linarith
    have h5 : (8:ℝ) * y ≤ 16 * y := by linarith
    linarith
  · have hsum : (∑ k ∈ T, ((2:ℝ)^k)^((1:ℝ)/3))
        = ∑ k ∈ T, ((2:ℝ)^((1:ℝ)/3))^k :=
      Finset.sum_congr rfl (fun k _ => rpow_two_third k)
    have h1 : (∑ k ∈ T, ((2:ℝ)^((1:ℝ)/3))^k)
        ≤ ∑ k ∈ Finset.range (kmax+1), ((2:ℝ)^((1:ℝ)/3))^k :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun i _ _ => pow_nonneg (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) _) i)
    have h2 : (∑ k ∈ Finset.range (kmax+1), ((2:ℝ)^((1:ℝ)/3))^k)
        ≤ 5 * ((2:ℝ)^((1:ℝ)/3))^kmax := geom_c_le _ cbrt_two_ge kmax
    have h3 : ((2:ℝ)^((1:ℝ)/3))^kmax = ((2:ℝ)^kmax)^((1:ℝ)/3) :=
      (rpow_two_third kmax).symm
    have h4 : ((2:ℝ)^kmax)^((1:ℝ)/3) < (4:ℝ)^((1:ℝ)/3) * y^((1:ℝ)/3) := by
      have h := Real.rpow_lt_rpow (by positivity : (0:ℝ) ≤ (2:ℝ)^kmax) hbd
        (by norm_num : (0:ℝ) < (1:ℝ)/3)
      rwa [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4) (le_of_lt hy)] at h
    have h5 : 5 * ((2:ℝ)^((1:ℝ)/3))^kmax < 16 * y^((1:ℝ)/3) := by
      rw [h3]
      have h6 : 5 * ((4:ℝ)^((1:ℝ)/3) * y^((1:ℝ)/3)) ≤ 16 * y^((1:ℝ)/3) := by
        rw [show (5:ℝ) * ((4:ℝ)^((1:ℝ)/3) * y^((1:ℝ)/3))
              = (5 * (4:ℝ)^((1:ℝ)/3)) * y^((1:ℝ)/3) by ring]
        exact mul_le_mul_of_nonneg_right five_mul_cbrt_four_le
          (Real.rpow_nonneg (le_of_lt hy) _)
      have h7 : 5 * ((2:ℝ)^kmax)^((1:ℝ)/3)
          < 5 * ((4:ℝ)^((1:ℝ)/3) * y^((1:ℝ)/3)) :=
        mul_lt_mul_of_pos_left h4 (by norm_num : (0:ℝ) < 5)
      linarith
    rw [hsum]
    exact le_of_lt (lt_of_le_of_lt (le_trans h1 h2) h5)

end Work.FIArea4.A6R2
