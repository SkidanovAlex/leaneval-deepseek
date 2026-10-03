/-
# Convolvability of the power-decay kernel on `ℤ`

For `M ≥ 2` the kernel `k(x) = (1 + |x|)^{-M}` is "convolvable": the sum over `m : ℤ` of
`k (m - i) * k (m - j)` is bounded by a constant times `k (i - j)`.

This is the elementary estimate behind the Schur test for the operators of Area A4Z: it says
that the matrix `(i, j) ↦ ∑_m k(i - m) k(m - j)` is dominated by the kernel `k (i - j)` itself.

## Proof

Write `K n = kern M (n : ℝ) = ((1 + |n|) ^ M)⁻¹`, so that `(1 + |x|) ^ (-(M : ℝ)) = K x`
(`kern_eq`). The argument has three parts.

* The triangle inequality in the form `|i - j| ≤ |m - i| + |m - j|` shows that for every `n`
  at least one of `|n - d|`, `|n|` is `≥ |d| / 2`.  Hence (`kern_le_two_pow_mul_kern`) at
  least one of `K (n - d)`, `K n` is at most `2^M * K d`; multiplying by the other (which is
  `≤ 1`) gives the pointwise bound

  `K (n - d) * K n ≤ 2^M * K d * (K (n - d) + K n)`.

* `∑_n K n` converges by comparison with the `p`-series `∑_n 1 / |n| ^ 2` (`kern_summable`),
  the single exceptional index `n = 0` being handled by the cofinite filter.

* Summing the pointwise bound and using translation invariance of the `ℤ`-series
  (`Equiv.tsum_eq` for `Equiv.addRight`) gives
  `∑_n K (n - d) K n ≤ 2^M K d (S + S) = 2^{M + 1} S K d` with `S = ∑_n K n`.
-/
import Mathlib

namespace Work.KMTAreas.A4Z

open scoped BigOperators

/-- The power-decay kernel in its natural-power form: `kern M x = ((1 + |x|) ^ M)⁻¹`. -/
private noncomputable def kern (M : ℕ) (x : ℝ) : ℝ := ((1 + |x|) ^ M)⁻¹

/-- The kernel agrees with the `rpow` expression occurring in the statement. -/
private lemma kern_eq (M : ℕ) (x : ℝ) : (1 + |x|) ^ (-(M : ℝ)) = kern M x := by
  rw [Real.rpow_neg (by positivity : (0:ℝ) ≤ 1 + |x|), Real.rpow_natCast]
  rfl

private lemma kern_nonneg (M : ℕ) (x : ℝ) : 0 ≤ kern M x := by
  rw [kern]
  exact inv_nonneg.mpr (pow_nonneg (add_nonneg zero_le_one (abs_nonneg x)) M)

private lemma kern_le_one (M : ℕ) (x : ℝ) : kern M x ≤ 1 := by
  rw [kern]
  exact inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith [abs_nonneg x] : (1:ℝ) ≤ 1 + |x|))

/-- If `D ≤ 2 * A` then `((1 + A) ^ M)⁻¹ ≤ 2 ^ M * ((1 + D) ^ M)⁻¹`. -/
private lemma kern_le_two_pow_mul_kern' {M : ℕ} {A D : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D)
    (h : D ≤ 2*A) : ((1+A)^M)⁻¹ ≤ (2:ℝ)^M * ((1+D)^M)⁻¹ := by
  have h1 : 1 + D ≤ 2 * (1 + A) := by linarith
  have h2 : (1 + D)^M ≤ (2 * (1 + A))^M := pow_le_pow_left₀ (by linarith) h1 M
  have h3 : (2 * (1 + A))^M = 2^M * (1 + A)^M := mul_pow 2 (1 + A) M
  have hD1 : (0:ℝ) < (1+D)^M := by positivity
  have h4 : (2^M * (1 + A)^M)⁻¹ ≤ ((1+D)^M)⁻¹ :=
    (inv_le_inv₀ (by positivity) hD1).mpr (h3 ▸ h2)
  have h5 : (2:ℝ)^M * (2^M * (1 + A)^M)⁻¹ ≤ (2:ℝ)^M * ((1+D)^M)⁻¹ :=
    mul_le_mul_of_nonneg_left h4 (by positivity)
  have heq : (2:ℝ)^M * (2^M * (1 + A)^M)⁻¹ = ((1+A)^M)⁻¹ := by
    rw [mul_inv]
    field_simp
  rw [heq] at h5
  exact h5

/-- Pointwise form: if `|d| ≤ 2 * |z|` then `kern M z ≤ 2 ^ M * kern M d`. -/
private lemma kern_le_two_pow_mul_kern {M : ℕ} {z d : ℝ} (h : |d| ≤ 2*|z|) :
    kern M z ≤ (2:ℝ)^M * kern M d := by
  simpa only [kern] using kern_le_two_pow_mul_kern' (abs_nonneg z) (abs_nonneg d) h

/-- The kernel is summable on `ℤ` as soon as `M ≥ 2`; the comparison series is the `p`-series
`∑_n 1 / |n| ^ 2`, whose only failing term (`n = 0`) is discarded by the cofinite filter. -/
private lemma kern_summable (M : ℕ) (hM : 2 ≤ M) :
    Summable (fun n : ℤ => kern M ((n:ℤ):ℝ)) := by
  have hg : Summable (fun n : ℤ => (1:ℝ) / |((n:ℤ):ℝ)| ^ (2:ℝ)) := by
    simpa using (Real.summable_one_div_int_add_rpow 0 2).mpr (by norm_num)
  refine Summable.of_norm_bounded_eventually hg ?_
  filter_upwards [Filter.eventually_cofinite_ne (0:ℤ)] with n hn
  have h1 : (1:ℝ) ≤ |((n:ℤ):ℝ)| := by
    have h := Int.one_le_abs hn
    have hcast : ((|n| : ℤ) : ℝ) = |((n:ℤ):ℝ)| := Int.cast_abs
    rw [← hcast]
    exact_mod_cast h
  rw [Real.norm_eq_abs, abs_of_nonneg (kern_nonneg M _)]
  have h2 : |((n:ℤ):ℝ)|^2 ≤ (1 + |((n:ℤ):ℝ)|)^M := by
    have hbase : (1:ℝ) ≤ 1 + |((n:ℤ):ℝ)| := by linarith [abs_nonneg ((n:ℤ):ℝ)]
    have hpow : (1 + |((n:ℤ):ℝ)|)^2 ≤ (1 + |((n:ℤ):ℝ)|)^M := pow_le_pow_right₀ hbase hM
    have hsq : |((n:ℤ):ℝ)|^2 ≤ (1 + |((n:ℤ):ℝ)|)^2 := by nlinarith [abs_nonneg ((n:ℤ):ℝ)]
    linarith
  have hpos : (0:ℝ) < |((n:ℤ):ℝ)|^2 := pow_pos (lt_of_lt_of_le zero_lt_one h1) 2
  calc kern M ((n:ℤ):ℝ) = ((1 + |((n:ℤ):ℝ)|)^M)⁻¹ := rfl
    _ ≤ (|((n:ℤ):ℝ)|^2)⁻¹ := (inv_le_inv₀ (by positivity) hpos).mpr h2
    _ = 1 / |((n:ℤ):ℝ)| ^ (2:ℝ) := by rw [one_div, Real.rpow_two]

/-- The translate-invariant form of the estimate: for `S = ∑_n kern M n`,

`∑_n kern M (n - d) * kern M n ≤ 2 ^ (M + 1) * S * kern M d`. -/
private theorem kernel_tsum_le (M : ℕ) (d : ℤ)
    (hS : Summable (fun n : ℤ => kern M ((n:ℤ):ℝ))) :
    (∑' n : ℤ, kern M (((n - d : ℤ) : ℝ)) * kern M ((n:ℤ):ℝ))
      ≤ (2:ℝ)^(M+1) * (∑' n : ℤ, kern M ((n:ℤ):ℝ)) * kern M ((d:ℤ):ℝ) := by
  have hS' : Summable (fun n : ℤ => kern M (((n - d : ℤ) : ℝ))) := by
    have hshift := (Equiv.summable_iff (f := fun n : ℤ => kern M ((n:ℤ):ℝ))
      (Equiv.addRight (-d))).mpr hS
    refine hshift.congr (fun n => ?_)
    simp only [Function.comp_apply, Equiv.coe_addRight]
    have hcast : (n + -d : ℤ) = (n - d : ℤ) := by ring
    rw [hcast]
  have hprodS : Summable (fun n : ℤ => kern M (((n-d:ℤ):ℝ)) * kern M ((n:ℤ):ℝ)) :=
    Summable.of_nonneg_of_le (fun n => mul_nonneg (kern_nonneg M _) (kern_nonneg M _))
      (fun n => mul_le_of_le_one_right (kern_nonneg M _) (kern_le_one M _)) hS'
  have hdomS : Summable (fun n : ℤ =>
      (2:ℝ)^M * kern M ((d:ℤ):ℝ) * (kern M (((n-d:ℤ):ℝ)) + kern M ((n:ℤ):ℝ))) :=
    ((hS'.add hS).mul_left ((2:ℝ)^M * kern M ((d:ℤ):ℝ)))
  have hpt : ∀ n : ℤ, kern M (((n-d:ℤ):ℝ)) * kern M ((n:ℤ):ℝ)
      ≤ (2:ℝ)^M * kern M ((d:ℤ):ℝ) * (kern M (((n-d:ℤ):ℝ)) + kern M ((n:ℤ):ℝ)) := by
    intro n
    have htri : |((d:ℤ):ℝ)| ≤ |(((n-d:ℤ):ℝ))| + |((n:ℤ):ℝ)| := by
      have h1 : ((d:ℤ):ℝ) = ((n:ℤ):ℝ) - (((n-d:ℤ):ℝ)) := by push_cast; ring
      have h2 := abs_sub_le ((n:ℤ):ℝ) (0:ℝ) (((n-d:ℤ):ℝ))
      have h3 : |((n:ℤ):ℝ) - (((n-d:ℤ):ℝ))| ≤ |((n:ℤ):ℝ)| + |(((n-d:ℤ):ℝ))| := by
        simpa only [sub_zero, zero_sub, abs_neg] using h2
      rw [h1]
      linarith
    have hc : 0 ≤ (2:ℝ)^M * kern M ((d:ℤ):ℝ) :=
      mul_nonneg (by positivity) (kern_nonneg M _)
    rcases le_total |(((n-d:ℤ):ℝ))| |((n:ℤ):ℝ)| with hle | hle
    · have hD : |((d:ℤ):ℝ)| ≤ 2 * |((n:ℤ):ℝ)| := by linarith
      have hv : kern M ((n:ℤ):ℝ) ≤ (2:ℝ)^M * kern M ((d:ℤ):ℝ) :=
        kern_le_two_pow_mul_kern (z := ((n:ℤ):ℝ)) (d := ((d:ℤ):ℝ)) hD
      calc kern M (((n-d:ℤ):ℝ)) * kern M ((n:ℤ):ℝ)
          ≤ kern M (((n-d:ℤ):ℝ)) * ((2:ℝ)^M * kern M ((d:ℤ):ℝ)) :=
            mul_le_mul_of_nonneg_left hv (kern_nonneg M _)
        _ ≤ (2:ℝ)^M * kern M ((d:ℤ):ℝ) * (kern M (((n-d:ℤ):ℝ)) + kern M ((n:ℤ):ℝ)) := by
            rw [mul_comm (kern M (((n-d:ℤ):ℝ))) ((2:ℝ)^M * kern M ((d:ℤ):ℝ))]
            exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (kern_nonneg M _)) hc
    · have hD : |((d:ℤ):ℝ)| ≤ 2 * |(((n-d:ℤ):ℝ))| := by linarith
      have hu : kern M (((n-d:ℤ):ℝ)) ≤ (2:ℝ)^M * kern M ((d:ℤ):ℝ) :=
        kern_le_two_pow_mul_kern (z := (((n-d:ℤ):ℝ))) (d := ((d:ℤ):ℝ)) hD
      calc kern M (((n-d:ℤ):ℝ)) * kern M ((n:ℤ):ℝ)
          ≤ ((2:ℝ)^M * kern M ((d:ℤ):ℝ)) * kern M ((n:ℤ):ℝ) :=
            mul_le_mul_of_nonneg_right hu (kern_nonneg M _)
        _ ≤ (2:ℝ)^M * kern M ((d:ℤ):ℝ) * (kern M (((n-d:ℤ):ℝ)) + kern M ((n:ℤ):ℝ)) :=
            mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (kern_nonneg M _)) hc
  have hstep := hprodS.tsum_le_tsum hpt hdomS
  have hTsum : (∑' n : ℤ, kern M (((n - d : ℤ) : ℝ))) = ∑' n : ℤ, kern M ((n:ℤ):ℝ) := by
    have h := Equiv.tsum_eq (Equiv.addRight (-d)) (fun n : ℤ => kern M ((n:ℤ):ℝ))
    simpa [Equiv.coe_addRight, sub_eq_add_neg] using h
  have hval : (∑' n : ℤ, (2:ℝ)^M * kern M ((d:ℤ):ℝ)
        * (kern M (((n-d:ℤ):ℝ)) + kern M ((n:ℤ):ℝ)))
      = (2:ℝ)^(M+1) * (∑' n : ℤ, kern M ((n:ℤ):ℝ)) * kern M ((d:ℤ):ℝ) := by
    rw [tsum_mul_left, Summable.tsum_add hS' hS, hTsum, pow_succ]
    ring
  rw [hval] at hstep
  exact hstep

theorem kernel_sum_le (M : ℕ) (hM : 2 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ (i j : ℤ),
      (∑' m : ℤ, (1 + |((m - i : ℤ) : ℝ)|) ^ (-(M : ℝ)) * (1 + |((m - j : ℤ) : ℝ)|) ^ (-(M : ℝ)))
        ≤ C * (1 + |((i - j : ℤ) : ℝ)|) ^ (-(M : ℝ)) := by
  have hS := kern_summable M hM
  have hSpos : 0 < ∑' n : ℤ, kern M ((n:ℤ):ℝ) := by
    have hz : kern M ((0:ℤ):ℝ) = 1 := by simp [kern]
    have h0 := hS.le_tsum 0 (fun j _ => kern_nonneg M (j:ℝ))
    rw [hz] at h0
    linarith
  refine ⟨(2:ℝ)^(M+1) * ∑' n : ℤ, kern M ((n:ℤ):ℝ), by positivity, ?_⟩
  intro i j
  have hmain := kernel_tsum_le M (i - j) hS
  have hstep1 : (∑' m : ℤ, (1 + |((m - i : ℤ) : ℝ)|) ^ (-(M : ℝ))
        * (1 + |((m - j : ℤ) : ℝ)|) ^ (-(M : ℝ)))
      = ∑' m : ℤ, kern M (((m - i : ℤ) : ℝ)) * kern M (((m - j : ℤ) : ℝ)) :=
    tsum_congr (fun m => by rw [kern_eq, kern_eq])
  have hstep2 : (∑' m : ℤ, kern M (((m - i : ℤ) : ℝ)) * kern M (((m - j : ℤ) : ℝ)))
      = ∑' n : ℤ, kern M (((n - (i-j) : ℤ) : ℝ)) * kern M ((n:ℤ):ℝ) := by
    have hpe : (fun m : ℤ => kern M (((m - i : ℤ) : ℝ)) * kern M (((m - j : ℤ) : ℝ)))
        = fun m : ℤ => kern M (((m + -j - (i - j) : ℤ) : ℝ)) * kern M (((m + -j : ℤ)) : ℝ) := by
      funext m
      have e1 : ((m - i : ℤ) : ℝ) = ((m + -j - (i - j) : ℤ) : ℝ) := by push_cast; ring
      have e2 : ((m - j : ℤ) : ℝ) = ((m + -j : ℤ) : ℝ) := by push_cast; ring
      rw [e1, e2]
    rw [hpe]
    exact Equiv.tsum_eq (Equiv.addRight (-j))
      (fun n : ℤ => kern M (((n - (i-j) : ℤ) : ℝ)) * kern M ((n:ℤ):ℝ))
  calc (∑' m : ℤ, (1 + |((m - i : ℤ) : ℝ)|) ^ (-(M : ℝ))
        * (1 + |((m - j : ℤ) : ℝ)|) ^ (-(M : ℝ)))
      = ∑' m : ℤ, kern M (((m - i : ℤ) : ℝ)) * kern M (((m - j : ℤ) : ℝ)) := hstep1
    _ = ∑' n : ℤ, kern M (((n - (i-j) : ℤ) : ℝ)) * kern M ((n:ℤ):ℝ) := hstep2
    _ ≤ (2:ℝ)^(M+1) * (∑' n : ℤ, kern M ((n:ℤ):ℝ)) * kern M (((i-j:ℤ):ℝ)) := hmain
    _ = (2:ℝ)^(M+1) * (∑' n : ℤ, kern M ((n:ℤ):ℝ))
          * (1 + |((i - j : ℤ) : ℝ)|) ^ (-(M : ℝ)) := by
        rw [kern_eq]

end Work.KMTAreas.A4Z
