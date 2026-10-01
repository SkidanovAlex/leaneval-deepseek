/-
# ZeroFreeTables/P9/prim/parityBound

Bound on the *real parts* of the two trivial (parity) series appearing in the explicit-formula
shape `SigmaP3L_eq_explicit_zeros`:

`|Re T₂| ≤ Ct`, `|Re T₃| ≤ Ct`  for `T_k = ∑_n (s + a + 2n)^{-k}`, `Re s ≥ 1/2`, `a ≤ 1`,

with the same uniform `Ct` as `trivSeriesBound`.  The proof is
`|Re T_k| ≤ ‖T_k‖ ≤ ∑_n ‖(s+a+2n)^{-k}‖ ≤ Ct`, the middle inequality being
`norm_tsum_le_tsum_norm`; summability of the norm series is the comparison test against
`2^k/(n+1)^k`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.P9.trivSeriesBound

namespace Work.ZeroFreeTables.P9

open scoped BigOperators

/-- Summability of `∑_n 1/(n+1)^k` for `k ≥ 2`. -/
private lemma summable_inv_succ_pow (k : ℕ) (hk : 2 ≤ k) :
    Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) ^ k) := by
  have h0 : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ k) :=
    (Real.summable_one_div_nat_pow (p := k)).mpr (by omega)
  have h1 : Summable (fun n : ℕ => (1 : ℝ) / (((n + 1 : ℕ) : ℝ)) ^ k) :=
    (summable_nat_add_iff 1).mpr h0
  exact h1.congr (fun n => by push_cast; ring)

/-- Pointwise norm bound: `‖(1/(s + a + 2n))^k‖ ≤ 2^k/(n+1)^k` when `Re s ≥ 1/2`. -/
private lemma norm_inv_pow_bound (s : ℂ) (hs : (1 : ℝ) / 2 ≤ s.re) (a n k : ℕ) :
    ‖(1 / (s + ((a + 2 * n : ℕ) : ℂ))) ^ k‖ ≤ (2 : ℝ) ^ k / ((n : ℝ) + 1) ^ k := by
  set z : ℂ := s + ((a + 2 * n : ℕ) : ℂ) with hzdef
  have h1 : ((n : ℝ) + 1) / 2 ≤ ‖z‖ := by
    have h1' : z.re = s.re + ((a + 2 * n : ℕ) : ℝ) := by
      rw [hzdef, Complex.add_re, Complex.natCast_re]
    have h2 : ((a + 2 * n : ℕ) : ℝ) = (a : ℝ) + 2 * (n : ℝ) := by push_cast; ring
    have h3re : ((n : ℝ) + 1) / 2 ≤ z.re := by
      rw [h1', h2]
      have : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
      nlinarith [hs]
    calc ((n : ℝ) + 1) / 2 ≤ z.re := h3re
      _ ≤ ‖z‖ := Complex.re_le_norm _
  have hpos : (0 : ℝ) < ((n : ℝ) + 1) / 2 := by positivity
  have hzpos : 0 < ‖z‖ := lt_of_lt_of_le hpos h1
  have hle : ‖z‖⁻¹ ≤ 2 / ((n : ℝ) + 1) := by
    rw [show (2 : ℝ) / ((n : ℝ) + 1) = (((n : ℝ) + 1) / 2)⁻¹ by field_simp]
    exact (inv_le_inv₀ hzpos hpos).mpr h1
  have hnorm : ‖(1 / z) ^ k‖ = (‖z‖⁻¹) ^ k := by
    rw [show (1 : ℂ) / z = z⁻¹ by simp, norm_pow, norm_inv]
  rw [hnorm, show (2 : ℝ) ^ k / ((n : ℝ) + 1) ^ k = (2 / ((n : ℝ) + 1)) ^ k by rw [div_pow]]
  exact pow_le_pow_left₀ (by positivity) hle k

/-- **Parity bound.**  There is a uniform constant `Ct > 0` with, for every `Re s ≥ 1/2` and
`a ≤ 1`, `|Re ∑_n (s + a + 2n)^{-2}| ≤ Ct` and `|Re ∑_n (s + a + 2n)^{-3}| ≤ Ct`. -/
theorem paritySum_re_bound :
    ∃ Ct : ℝ, 0 < Ct ∧ ∀ s : ℂ, (1 : ℝ) / 2 ≤ s.re → ∀ a : ℕ, a ≤ 1 →
      |(∑' n : ℕ, (1 / (s + ((a + 2 * n : ℕ) : ℂ))) ^ 2).re| ≤ Ct ∧
      |(∑' n : ℕ, (1 / (s + ((a + 2 * n : ℕ) : ℂ))) ^ 3).re| ≤ Ct := by
  obtain ⟨Ct, hpos, hCt⟩ := trivSeriesBound
  refine ⟨Ct, hpos, ?_⟩
  intro s hs a ha
  have hsumm : ∀ {k : ℕ}, 2 ≤ k →
      Summable (fun n : ℕ => ‖(1 / (s + ((a + 2 * n : ℕ) : ℂ))) ^ k‖) := by
    intro k hk
    have hbase := summable_inv_succ_pow k hk
    have hmaj : Summable (fun n : ℕ => (2 : ℝ) ^ k / ((n : ℝ) + 1) ^ k) :=
      (hbase.mul_left _).congr (fun n => by rw [mul_one_div])
    exact Summable.of_nonneg_of_le (fun n => norm_nonneg _)
      (fun n => norm_inv_pow_bound s hs a n k) hmaj
  constructor
  · calc |(∑' n : ℕ, (1 / (s + ((a + 2 * n : ℕ) : ℂ))) ^ 2).re|
        ≤ ‖∑' n : ℕ, (1 / (s + ((a + 2 * n : ℕ) : ℂ))) ^ 2‖ := Complex.abs_re_le_norm _
      _ ≤ ∑' n : ℕ, ‖(1 / (s + ((a + 2 * n : ℕ) : ℂ))) ^ 2‖ :=
          norm_tsum_le_tsum_norm (hsumm (by norm_num))
      _ ≤ Ct := (hCt s hs a ha).1
  · calc |(∑' n : ℕ, (1 / (s + ((a + 2 * n : ℕ) : ℂ))) ^ 3).re|
        ≤ ‖∑' n : ℕ, (1 / (s + ((a + 2 * n : ℕ) : ℂ))) ^ 3‖ := Complex.abs_re_le_norm _
      _ ≤ ∑' n : ℕ, ‖(1 / (s + ((a + 2 * n : ℕ) : ℂ))) ^ 3‖ :=
          norm_tsum_le_tsum_norm (hsumm (by norm_num))
      _ ≤ Ct := (hCt s hs a ha).2

end Work.ZeroFreeTables.P9
