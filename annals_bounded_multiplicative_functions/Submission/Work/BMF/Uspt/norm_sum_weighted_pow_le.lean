import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.Uspt

/-- Weighted power-mean (Hölder) inequality with a natural exponent: for nonnegative weights `w`
and nonnegative values `r` on a finite set `t` and `1 ≤ m`,
`(∑ w r)^m ≤ (∑ w)^(m-1) * ∑ w r^m`. -/
lemma weighted_pow_mean {ι : Type*} (t : Finset ι) (m : ℕ) (hm : 1 ≤ m)
    (w r : ι → ℝ) (hw : ∀ c, 0 ≤ w c) (hr : ∀ c, 0 ≤ r c) :
    (∑ c ∈ t, w c * r c) ^ m
      ≤ (∑ c ∈ t, w c) ^ (m - 1) * (∑ c ∈ t, w c * r c ^ m) := by
  have hmR : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have hm0 : (m:ℝ) ≠ 0 := by
    have : (0:ℝ) < m := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
    exact ne_of_gt this
  set W := ∑ c ∈ t, w c with hWdef
  set N := ∑ c ∈ t, w c * r c ^ m with hNdef
  have hW0 : 0 ≤ W := by rw [hWdef]; exact Finset.sum_nonneg (fun c _ => hw c)
  have hN0 : 0 ≤ N := by
    rw [hNdef]; exact Finset.sum_nonneg (fun c _ => mul_nonneg (hw c) (pow_nonneg (hr c) m))
  have hF0 : 0 ≤ ∑ c ∈ t, w c * r c :=
    Finset.sum_nonneg (fun c _ => mul_nonneg (hw c) (hr c))
  have hrpow : (∑ c ∈ t, w c * r c ^ (m:ℝ)) = N := by
    rw [hNdef]; exact Finset.sum_congr rfl (fun c _ => by rw [Real.rpow_natCast])
  have h := Real.inner_le_weight_mul_Lp_of_nonneg t (p := (m:ℝ)) hmR w r hw hr
  rw [hrpow] at h
  have h2 := pow_le_pow_left₀ hF0 h m
  rw [mul_pow] at h2
  have hexp : (1 - (m:ℝ)⁻¹) * (m:ℝ) = ((m - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hm, Nat.cast_one, sub_mul, one_mul, inv_mul_cancel₀ hm0]
  have hW : (W ^ (1 - (m:ℝ)⁻¹)) ^ m = W ^ (m - 1) := by
    rw [← Real.rpow_natCast (W ^ (1 - (m:ℝ)⁻¹)) m, ← Real.rpow_mul hW0, hexp,
      Real.rpow_natCast]
  have hN : (N ^ ((m:ℝ)⁻¹)) ^ m = N := by
    rw [← Real.rpow_natCast (N ^ ((m:ℝ)⁻¹)) m, ← Real.rpow_mul hN0,
      inv_mul_cancel₀ hm0, Real.rpow_one]
  rw [hW, hN] at h2
  rw [hWdef, hNdef] at h2
  exact h2

/-- Auxiliary real-variable form of the estimate: for nonnegative weights `w`, nonnegative `r`
and `1 ≤ s`,
`(∑ w r)^(2s) ≤ (∑ w)^(2s-2) * (∑ w^2) * (∑ r^(2s))`. -/
lemma weighted_sum_pow_bound {ι : Type*} (s : ℕ) (hs : 1 ≤ s) (t : Finset ι)
    (w r : ι → ℝ) (hw : ∀ c, 0 ≤ w c) (hr : ∀ c, 0 ≤ r c) :
    (∑ c ∈ t, w c * r c) ^ (2 * s)
      ≤ (∑ c ∈ t, w c) ^ (2 * s - 2) * (∑ c ∈ t, w c ^ 2) * (∑ c ∈ t, r c ^ (2 * s)) := by
  have hF0 : 0 ≤ ∑ c ∈ t, w c * r c := Finset.sum_nonneg (fun c _ => mul_nonneg (hw c) (hr c))
  have hW0 : 0 ≤ ∑ c ∈ t, w c := Finset.sum_nonneg (fun c _ => hw c)
  have hpm := weighted_pow_mean t s hs w r hw hr
  have hsq : ((∑ c ∈ t, w c * r c) ^ s) ^ 2
      ≤ ((∑ c ∈ t, w c) ^ (s - 1) * (∑ c ∈ t, w c * r c ^ s)) ^ 2 :=
    pow_le_pow_left₀ (pow_nonneg hF0 s) hpm 2
  have hcs' : (∑ c ∈ t, (r c ^ s) ^ 2) = ∑ c ∈ t, r c ^ (2 * s) := by
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [← pow_mul, Nat.mul_comm]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq t w (fun c => r c ^ s)
  rw [hcs'] at hcs
  have hWsq : ((∑ c ∈ t, w c) ^ (s - 1)) ^ 2 = (∑ c ∈ t, w c) ^ (2 * s - 2) := by
    rw [← pow_mul, show (s - 1) * 2 = 2 * s - 2 by omega]
  calc (∑ c ∈ t, w c * r c) ^ (2 * s)
      = ((∑ c ∈ t, w c * r c) ^ s) ^ 2 := by rw [← pow_mul, show s * 2 = 2 * s by omega]
    _ ≤ ((∑ c ∈ t, w c) ^ (s - 1) * (∑ c ∈ t, w c * r c ^ s)) ^ 2 := hsq
    _ = ((∑ c ∈ t, w c) ^ (s - 1)) ^ 2 * (∑ c ∈ t, w c * r c ^ s) ^ 2 := by rw [mul_pow]
    _ = (∑ c ∈ t, w c) ^ (2 * s - 2) * (∑ c ∈ t, w c * r c ^ s) ^ 2 := by rw [hWsq]
    _ ≤ (∑ c ∈ t, w c) ^ (2 * s - 2) * ((∑ c ∈ t, w c ^ 2) * (∑ c ∈ t, r c ^ (2 * s))) :=
        mul_le_mul_of_nonneg_left hcs (pow_nonneg hW0 _)
    _ = (∑ c ∈ t, w c) ^ (2 * s - 2) * (∑ c ∈ t, w c ^ 2) * (∑ c ∈ t, r c ^ (2 * s)) := by ring

theorem norm_sum_weighted_pow_le {ι : Type*} (s : ℕ) (hs : 1 ≤ s) (t : Finset ι)
    (n : ι → ℕ) (y : ι → ℂ) :
    ‖∑ c ∈ t, (n c : ℂ) * y c‖ ^ (2 * s)
      ≤ (∑ c ∈ t, (n c : ℝ)) ^ (2 * s - 2) * (∑ c ∈ t, (n c : ℝ) ^ 2)
          * (∑ c ∈ t, ‖y c‖ ^ (2 * s)) := by
  have h1 : ‖∑ c ∈ t, (n c : ℂ) * y c‖ ≤ ∑ c ∈ t, (n c : ℝ) * ‖y c‖ := by
    calc ‖∑ c ∈ t, (n c : ℂ) * y c‖ ≤ ∑ c ∈ t, ‖(n c : ℂ) * y c‖ := norm_sum_le _ _
      _ = ∑ c ∈ t, (n c : ℝ) * ‖y c‖ := by
        refine Finset.sum_congr rfl (fun c _ => ?_)
        rw [norm_mul, Complex.norm_natCast]
  have h2 : ‖∑ c ∈ t, (n c : ℂ) * y c‖ ^ (2 * s) ≤ (∑ c ∈ t, (n c : ℝ) * ‖y c‖) ^ (2 * s) :=
    pow_le_pow_left₀ (norm_nonneg _) h1 (2 * s)
  have h3 := weighted_sum_pow_bound s hs t (fun c => (n c : ℝ)) (fun c => ‖y c‖)
    (fun c => Nat.cast_nonneg _) (fun c => norm_nonneg _)
  calc ‖∑ c ∈ t, (n c : ℂ) * y c‖ ^ (2 * s)
      ≤ (∑ c ∈ t, (n c : ℝ) * ‖y c‖) ^ (2 * s) := h2
    _ ≤ (∑ c ∈ t, (n c : ℝ)) ^ (2 * s - 2) * (∑ c ∈ t, (n c : ℝ) ^ 2)
          * (∑ c ∈ t, ‖y c‖ ^ (2 * s)) := h3

end Work.BMF.Uspt
