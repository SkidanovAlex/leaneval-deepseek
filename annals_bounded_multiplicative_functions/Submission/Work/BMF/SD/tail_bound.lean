import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Tail bound for the Taylor expansion of a multiplicative perturbation

This file proves `Work.BMF.SD.tail_bound`, the elementary estimate used to control the
tail of the binomial (Taylor) expansion in the "short interval on average" argument.

Writing `C_j = j.choose m` and `d^(j-m)` for the Taylor coefficients, the two sums
`∑ C_j x_j d^(j-m)` and `∑ C_j M_j d^(j-m)` are compared after dividing the second by
`H`.  The hypothesis `|H x_j - M_j| ≤ K / L^j` for `j ∈ [m+2, k+1]`, together with
`d ≤ L`, bounds every term by `C_j · K / L^m`, and the binomial coefficients are
estimated crudely by `2^(k+1)` each.

The two auxiliary inequalities are isolated below.
-/

namespace Work.BMF.SD

/-- Geometric comparison: for naturals `d ≤ L` and `m ≤ j`,
`d^(j-m) / L^j ≤ 1 / L^m`.  (Both sides are understood in Lean's division-by-zero
convention, and the statement remains true when `L = 0`.) -/
lemma tail_pow_div_pow_le (d L j m : ℕ) (hd : d ≤ L) (hm : m ≤ j) :
    (d:ℝ)^(j-m) / (L:ℝ)^j ≤ 1/(L:ℝ)^m := by
  rcases eq_or_lt_of_le (Nat.zero_le L) with hL | hL
  · subst hL
    have hd0 : d = 0 := by omega
    subst hd0
    rcases Nat.eq_zero_or_pos j with hj | hj
    · subst hj
      have hm0 : m = 0 := by omega
      subst hm0
      norm_num
    · simp only [Nat.cast_zero]
      rw [zero_pow (by omega : j ≠ 0), div_zero]
      positivity
  · have hLpos : (0:ℝ) < (L:ℝ) := by exact_mod_cast hL
    have hLsplit : (L:ℝ)^j = (L:ℝ)^(j-m) * (L:ℝ)^m := by
      rw [← pow_add]; congr 1; omega
    have hratio : (d:ℝ)/(L:ℝ) ≤ 1 := by
      rw [div_le_one hLpos]
      exact_mod_cast hd
    have hb : (d:ℝ)^(j-m)/(L:ℝ)^(j-m) ≤ 1 := by
      have h := pow_le_pow_left₀ (show (0:ℝ) ≤ (d:ℝ)/(L:ℝ) by positivity) hratio (j-m)
      rwa [one_pow, div_pow] at h
    rw [hLsplit, div_mul_eq_div_div]
    exact div_le_div_of_nonneg_right hb (by positivity)

/-- Crude bound for the sum of the truncated binomial coefficients:
`∑_{j=m+2}^{k+1} C(j,m) ≤ (k+2) · 2^(k+1)`.  Each term is `≤ 2^(k+1)` and there are at
most `k+2` terms. -/
lemma tail_sum_choose_le (k m : ℕ) :
    (∑ j ∈ Finset.Icc (m+2) (k+1), ((j.choose m : ℕ) : ℝ)) ≤ ((k:ℝ)+2) * 2^(k+1) := by
  calc (∑ j ∈ Finset.Icc (m+2) (k+1), ((j.choose m : ℕ) : ℝ))
      ≤ ∑ j ∈ Finset.Icc (m+2) (k+1), (2:ℝ)^(k+1) := by
        apply Finset.sum_le_sum
        intro j hj
        have hjle : j ≤ k+1 := (Finset.mem_Icc.mp hj).2
        have h1 : ((j.choose m : ℕ):ℝ) ≤ (2:ℝ)^j := by
          have h := Nat.choose_le_two_pow j m
          have h' : ((j.choose m : ℕ):ℝ) ≤ ((2^j : ℕ):ℝ) := by exact_mod_cast h
          simpa using h'
        have h2 : (2:ℝ)^j ≤ (2:ℝ)^(k+1) := pow_le_pow_right₀ (by norm_num) hjle
        exact le_trans h1 h2
    _ = ((Finset.Icc (m+2) (k+1)).card : ℝ) * (2:ℝ)^(k+1) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((k:ℝ)+2) * (2:ℝ)^(k+1) := by
        have hcard : (Finset.Icc (m+2) (k+1)).card ≤ k+2 := by
          rw [Nat.card_Icc]; omega
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)

/--
Tail bound: given `|H · x j - M j| ≤ K / L^j` for `j ∈ [m+2, k+1]` and `d ≤ L`,
the difference of the truncated binomial expansions is at most
`((k+2) 2^(k+1)) K / (H L^m)`.
-/
theorem tail_bound {k m L : ℕ} {x : ℕ → ℝ} {H : ℕ} (hH : 1 ≤ H) {K : ℝ} (hK : 0 ≤ K)
    {M : ℕ → ℤ} {d : ℕ} (hd : d ≤ L)
    (hinv : ∀ j ∈ Finset.Icc (m+2) (k+1), |(H:ℝ) * x j - (M j : ℝ)| ≤ K / (L:ℝ)^j) :
    |(∑ j ∈ Finset.Icc (m+2) (k+1), ((j.choose m : ℕ):ℝ) * x j * (d:ℝ)^(j-m))
      - (∑ j ∈ Finset.Icc (m+2) (k+1), ((j.choose m : ℕ):ℝ) * (M j : ℝ) * (d:ℝ)^(j-m)) / (H:ℝ)|
    ≤ (((k:ℝ)+2) * 2^(k+1)) * K / ((H:ℝ) * (L:ℝ)^m) := by
  have hHpos : (0:ℝ) < (H:ℝ) := by exact_mod_cast (by omega : 0 < H)
  have hHne : (H:ℝ) ≠ 0 := ne_of_gt hHpos
  have hkey :
      (∑ j ∈ Finset.Icc (m+2) (k+1), ((j.choose m : ℕ):ℝ) * x j * (d:ℝ)^(j-m))
        - (∑ j ∈ Finset.Icc (m+2) (k+1), ((j.choose m : ℕ):ℝ) * (M j : ℝ) * (d:ℝ)^(j-m)) / (H:ℝ)
      = (∑ j ∈ Finset.Icc (m+2) (k+1), ((j.choose m : ℕ):ℝ) * (d:ℝ)^(j-m) * ((H:ℝ) * x j - (M j : ℝ))) / (H:ℝ) := by
    simp only [Finset.sum_div]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    field_simp
  have hsum_abs :
      |∑ j ∈ Finset.Icc (m+2) (k+1), ((j.choose m : ℕ):ℝ) * (d:ℝ)^(j-m) * ((H:ℝ) * x j - (M j : ℝ))|
        ≤ ∑ j ∈ Finset.Icc (m+2) (k+1), ((j.choose m : ℕ):ℝ) * (d:ℝ)^(j-m) * |(H:ℝ) * x j - (M j : ℝ)| := by
    refine le_trans (Finset.abs_sum_le_sum_abs (fun j => ((j.choose m : ℕ):ℝ) * (d:ℝ)^(j-m) * ((H:ℝ) * x j - (M j : ℝ))) (Finset.Icc (m+2) (k+1))) ?_
    apply Finset.sum_le_sum
    intro j hj
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ ((j.choose m : ℕ):ℝ)),
        abs_of_nonneg (by positivity : (0:ℝ) ≤ (d:ℝ)^(j-m))]
  have hbound2 :
      (∑ j ∈ Finset.Icc (m+2) (k+1), ((j.choose m : ℕ):ℝ) * (d:ℝ)^(j-m) * |(H:ℝ) * x j - (M j : ℝ)|)
        ≤ ∑ j ∈ Finset.Icc (m+2) (k+1), ((j.choose m : ℕ):ℝ) * (d:ℝ)^(j-m) * (K / (L:ℝ)^j) := by
    apply Finset.sum_le_sum
    intro j hj
    exact mul_le_mul_of_nonneg_left (hinv j hj) (by positivity)
  have hbound3 :
      (∑ j ∈ Finset.Icc (m+2) (k+1), ((j.choose m : ℕ):ℝ) * (d:ℝ)^(j-m) * (K / (L:ℝ)^j))
        ≤ ∑ j ∈ Finset.Icc (m+2) (k+1), ((j.choose m : ℕ):ℝ) * (K / (L:ℝ)^m) := by
    apply Finset.sum_le_sum
    intro j hj
    have hmj : m ≤ j := by have := (Finset.mem_Icc.mp hj).1; omega
    have hgeo : (d:ℝ)^(j-m) * (K / (L:ℝ)^j) ≤ K / (L:ℝ)^m := by
      have h1 := tail_pow_div_pow_le d L j m hd hmj
      have h2 := mul_le_mul_of_nonneg_right h1 hK
      calc (d:ℝ)^(j-m) * (K / (L:ℝ)^j) = ((d:ℝ)^(j-m) / (L:ℝ)^j) * K := by ring
        _ ≤ (1 / (L:ℝ)^m) * K := h2
        _ = K / (L:ℝ)^m := by ring
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hgeo (by positivity)
  have hbound4 :
      (∑ j ∈ Finset.Icc (m+2) (k+1), ((j.choose m : ℕ):ℝ) * (K / (L:ℝ)^m))
        = (K / (L:ℝ)^m) * (∑ j ∈ Finset.Icc (m+2) (k+1), ((j.choose m : ℕ):ℝ)) := by
    rw [← Finset.sum_mul, mul_comm]
  have hbound5 :
      (K / (L:ℝ)^m) * (∑ j ∈ Finset.Icc (m+2) (k+1), ((j.choose m : ℕ):ℝ))
        ≤ (K / (L:ℝ)^m) * (((k:ℝ)+2) * 2^(k+1)) := by
    apply mul_le_mul_of_nonneg_left (tail_sum_choose_le k m)
    exact div_nonneg hK (by positivity)
  calc
    |(∑ j ∈ Finset.Icc (m+2) (k+1), ((j.choose m : ℕ):ℝ) * x j * (d:ℝ)^(j-m))
      - (∑ j ∈ Finset.Icc (m+2) (k+1), ((j.choose m : ℕ):ℝ) * (M j : ℝ) * (d:ℝ)^(j-m)) / (H:ℝ)|
      = |∑ j ∈ Finset.Icc (m+2) (k+1), ((j.choose m : ℕ):ℝ) * (d:ℝ)^(j-m) * ((H:ℝ) * x j - (M j : ℝ))| / (H:ℝ) := by
        rw [hkey, abs_div, abs_of_pos hHpos]
    _ ≤ (∑ j ∈ Finset.Icc (m+2) (k+1), ((j.choose m : ℕ):ℝ) * (d:ℝ)^(j-m) * |(H:ℝ) * x j - (M j : ℝ)|) / (H:ℝ) :=
        div_le_div_of_nonneg_right hsum_abs hHpos.le
    _ ≤ (∑ j ∈ Finset.Icc (m+2) (k+1), ((j.choose m : ℕ):ℝ) * (d:ℝ)^(j-m) * (K / (L:ℝ)^j)) / (H:ℝ) :=
        div_le_div_of_nonneg_right hbound2 hHpos.le
    _ ≤ (∑ j ∈ Finset.Icc (m+2) (k+1), ((j.choose m : ℕ):ℝ) * (K / (L:ℝ)^m)) / (H:ℝ) :=
        div_le_div_of_nonneg_right hbound3 hHpos.le
    _ = ((K / (L:ℝ)^m) * (∑ j ∈ Finset.Icc (m+2) (k+1), ((j.choose m : ℕ):ℝ))) / (H:ℝ) := by
        rw [hbound4]
    _ ≤ ((K / (L:ℝ)^m) * (((k:ℝ)+2) * 2^(k+1))) / (H:ℝ) :=
        div_le_div_of_nonneg_right hbound5 hHpos.le
    _ = (((k:ℝ)+2) * 2^(k+1)) * K / ((H:ℝ) * (L:ℝ)^m) := by ring

end Work.BMF.SD
