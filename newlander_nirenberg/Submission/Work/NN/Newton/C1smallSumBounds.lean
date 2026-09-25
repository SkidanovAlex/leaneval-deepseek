import Mathlib
import Submission.Work.NN.Newton.C1smallSetup

/-!
# Sum bounds for the `C^{1,α}`-small Newton iteration

This module proves `Work.NN.Newton.C1smallSumBounds`: the elementary size
estimates for the perturbation sizes `asize ε N m = ε 2^{-2Nm}` and the
correction sizes `bsize C N ε m = (C/δ_m^N) a_m` used in
`Work.NN.Newton.exists_holFrame_of_C1small`.

Writing `A = C ε 2^{3N}` and `r = 2^{-N}`, the key identity (proved below as
`bsize_eq'`) is

  `bsize C N ε m = A · r^m`,

so the correction sizes form a geometric sequence with ratio `r ≤ 1/2`. Under
the smallness hypothesis `C ε 2^{5N} ≤ 1` one has `A ≤ 2^{-2N} ≤ 1/64`, which
yields the pointwise bound `β_m ≤ 1/32`, the uniform bound
`∑_{i<k} β_i ≤ 2A ≤ 1/32` on partial sums, and the tail bound
`∑_{k≤i<m} β_i ≤ 2A r^k`.

The two analytic inputs are `geom_sum_Ico_le_of_lt_one` (Mathlib) and the
elementary exponent identities `bsize_aux`, `key_shift`.
-/

namespace Work.NN.Newton

open Finset

/-! ## Rewriting the sizes -/

/-- `δ_m^N = 2^{-N(m+3)}`, written with base `1/2`. -/
lemma delta_pow (m N : ℕ) : delta m ^ N = (1/2:ℝ)^((m+3)*N) := by
  unfold delta
  rw [← pow_mul]

/-- The exponent identity underlying the closed form of `bsize`. -/
lemma bsize_aux (N m : ℕ) :
    ((1/2:ℝ)^((m+3)*N))⁻¹ * (1/2:ℝ)^(2*N*m)
      = (2:ℝ)^(3*N) * (1/2:ℝ)^(N*m) := by
  have hinv : ((1/2:ℝ)^((m+3)*N))⁻¹ = (2:ℝ)^((m+3)*N) := by
    rw [one_div, inv_pow, inv_inv]
  rw [hinv]
  have hr : (1/2:ℝ) = (2:ℝ)⁻¹ := by norm_num
  rw [hr, inv_pow, inv_pow, ← div_eq_mul_inv, ← div_eq_mul_inv]
  rw [div_eq_div_iff (by positivity) (by positivity)]
  rw [← pow_add, ← pow_add]
  congr 1
  ring

/-- Closed form of the correction size: `β_m = C ε 2^{3N} 2^{-Nm}`. -/
lemma bsize_eq (C : ℝ) (N : ℕ) (ε : ℝ) (m : ℕ) :
    bsize C N ε m = C * ε * (2:ℝ)^(3*N) * (1/2:ℝ)^(N*m) := by
  have h1 : bsize C N ε m
      = C * ε * (((1/2:ℝ)^((m+3)*N))⁻¹ * (1/2:ℝ)^(2*N*m)) := by
    unfold bsize asize
    rw [show C / delta m ^ N = C * (delta m ^ N)⁻¹ from div_eq_mul_inv C _,
        delta_pow]
    ring
  rw [h1, bsize_aux]
  ring

/-- `β_m` as a geometric sequence `A r^m` with `A = C ε 2^{3N}`, `r = 2^{-N}`. -/
lemma bsize_eq' (C : ℝ) (N : ℕ) (ε : ℝ) (m : ℕ) :
    bsize C N ε m = C * ε * (2:ℝ)^(3*N) * ((1/2:ℝ)^N)^m := by
  rw [bsize_eq, ← pow_mul]

/-! ## Monotonicity and positivity of the sizes -/

lemma asize_nonneg {ε : ℝ} (hε0 : 0 ≤ ε) (N m : ℕ) : 0 ≤ asize ε N m := by
  unfold asize
  exact mul_nonneg hε0 (pow_nonneg (by norm_num) _)

lemma asize_le {ε : ℝ} (hε0 : 0 ≤ ε) (N m : ℕ) : asize ε N m ≤ ε := by
  unfold asize
  calc ε * (1/2:ℝ)^(2*N*m) ≤ ε * 1 :=
        mul_le_mul_of_nonneg_left (pow_le_one₀ (by norm_num) (by norm_num)) hε0
    _ = ε := mul_one ε

lemma bsize_nonneg {C ε : ℝ} (hC : 0 < C) (hε0 : 0 ≤ ε) (N m : ℕ) :
    0 ≤ bsize C N ε m := by
  rw [bsize_eq]
  exact mul_nonneg (mul_nonneg (mul_nonneg hC.le hε0) (pow_nonneg (by norm_num) _))
    (pow_nonneg (by norm_num) _)

/-- `2^{5N} · 2^{-2N} = 2^{3N}`: the smallness hypothesis is exactly what makes
`C ε 2^{3N}` small. -/
lemma key_shift (N : ℕ) :
    (2:ℝ)^(5*N) * (1/2:ℝ)^(2*N) = (2:ℝ)^(3*N) := by
  rw [show (5:ℕ)*N = 3*N + 2*N from by ring, pow_add]
  rw [mul_assoc, ← mul_pow]
  norm_num

/-! ## The sum bounds -/

theorem C1smallSumBounds {C ε : ℝ} {N : ℕ} (hC : 0 < C) (hN : 3 ≤ N) (hε0 : 0 ≤ ε)
    (hε : C * ε * (2:ℝ)^(5*N) ≤ 1) :
    (∀ m : ℕ, 0 ≤ asize ε N m) ∧ (∀ m : ℕ, asize ε N m ≤ ε) ∧
    (∀ m : ℕ, 0 ≤ bsize C N ε m) ∧ (∀ m : ℕ, bsize C N ε m ≤ 1/32) ∧
    (∀ k : ℕ, ∑ i ∈ Finset.range k, bsize C N ε i ≤ 1/32) ∧
    (∀ k m : ℕ, ∑ i ∈ Finset.Ico k m, bsize C N ε i
      ≤ 2 * C * ε * (2:ℝ)^(3*N) * (1/2)^(N*k)) := by
  -- Basic facts about `r = 2^{-N}`.
  have hrle : (1/2:ℝ)^N ≤ 1/2 := by
    have h := pow_le_pow_of_le_one (a := (1/2:ℝ)) (by norm_num) (by norm_num)
      (by omega : 1 ≤ N)
    simpa using h
  have hrlt : (1/2:ℝ)^N < 1 := lt_of_le_of_lt hrle (by norm_num)
  have hr1 : (1/2:ℝ)^N ≤ 1 := le_trans hrle (by norm_num)
  have r0 : (0:ℝ) ≤ (1/2:ℝ)^N := by positivity
  have h2N : (1/2:ℝ)^(2*N) ≤ (1/2:ℝ)^6 := by
    have h := pow_le_pow_of_le_one (a := (1/2:ℝ)) (by norm_num) (by norm_num)
      (by omega : 6 ≤ 2*N)
    simpa using h
  -- `A = C ε 2^{3N}` is nonnegative and at most `2^{-2N}`.
  have hA0 : 0 ≤ C * ε * (2:ℝ)^(3*N) :=
    mul_nonneg (mul_nonneg hC.le hε0) (pow_nonneg (by norm_num) _)
  have hA : C * ε * (2:ℝ)^(3*N) ≤ (1/2:ℝ)^(2*N) := by
    calc C * ε * (2:ℝ)^(3*N)
        = C * ε * ((2:ℝ)^(5*N) * (1/2:ℝ)^(2*N)) := by rw [key_shift]
      _ = (C * ε * (2:ℝ)^(5*N)) * (1/2:ℝ)^(2*N) := by ring
      _ ≤ 1 * (1/2:ℝ)^(2*N) :=
          mul_le_mul_of_nonneg_right hε (pow_nonneg (by norm_num) _)
      _ = (1/2:ℝ)^(2*N) := one_mul _
  refine ⟨fun m => asize_nonneg hε0 N m, fun m => asize_le hε0 N m,
    fun m => bsize_nonneg hC hε0 N m, ?_, ?_, ?_⟩
  · -- Pointwise bound `β_m ≤ 1/32`.
    intro m
    rw [bsize_eq']
    calc C * ε * (2:ℝ)^(3*N) * ((1/2:ℝ)^N)^m
        ≤ C * ε * (2:ℝ)^(3*N) * 1 :=
          mul_le_mul_of_nonneg_left (pow_le_one₀ r0 hr1) hA0
      _ = C * ε * (2:ℝ)^(3*N) := mul_one _
      _ ≤ (1/2:ℝ)^(2*N) := hA
      _ ≤ (1/2:ℝ)^6 := h2N
      _ = 1/64 := by norm_num
      _ ≤ 1/32 := by norm_num
  · -- Uniform bound on the partial sums `∑_{i<k} β_i`.
    intro k
    have hsum : ∑ i ∈ Finset.range k, bsize C N ε i
        = C * ε * (2:ℝ)^(3*N) * ∑ i ∈ Finset.range k, ((1/2:ℝ)^N)^i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => bsize_eq' C N ε i)
    have hgeom : ∑ i ∈ Finset.range k, ((1/2:ℝ)^N)^i ≤ 1 / (1 - (1/2:ℝ)^N) := by
      have h := geom_sum_Ico_le_of_lt_one (m := 0) (n := k) r0 hrlt
      simpa using h
    have hInv : 1 / (1 - (1/2:ℝ)^N) ≤ 2 := by
      rw [div_le_iff₀ (by linarith : (0:ℝ) < 1 - (1/2:ℝ)^N)]
      linarith
    calc ∑ i ∈ Finset.range k, bsize C N ε i
        = C * ε * (2:ℝ)^(3*N) * ∑ i ∈ Finset.range k, ((1/2:ℝ)^N)^i := hsum
      _ ≤ C * ε * (2:ℝ)^(3*N) * (1 / (1 - (1/2:ℝ)^N)) :=
          mul_le_mul_of_nonneg_left hgeom hA0
      _ ≤ C * ε * (2:ℝ)^(3*N) * 2 := mul_le_mul_of_nonneg_left hInv hA0
      _ ≤ (1/2:ℝ)^(2*N) * 2 := mul_le_mul_of_nonneg_right hA (by norm_num)
      _ ≤ (1/2:ℝ)^6 * 2 := mul_le_mul_of_nonneg_right h2N (by norm_num)
      _ = 1/32 := by norm_num
  · -- Tail bound `∑_{k≤i<m} β_i ≤ 2 A r^k`.
    intro k m
    have hsum : ∑ i ∈ Finset.Ico k m, bsize C N ε i
        = C * ε * (2:ℝ)^(3*N) * ∑ i ∈ Finset.Ico k m, ((1/2:ℝ)^N)^i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => bsize_eq' C N ε i)
    have hgeom : ∑ i ∈ Finset.Ico k m, ((1/2:ℝ)^N)^i
        ≤ ((1/2:ℝ)^N)^k / (1 - (1/2:ℝ)^N) :=
      geom_sum_Ico_le_of_lt_one r0 hrlt
    have hInv : ((1/2:ℝ)^N)^k / (1 - (1/2:ℝ)^N) ≤ 2 * ((1/2:ℝ)^N)^k := by
      rw [div_le_iff₀ (by linarith : (0:ℝ) < 1 - (1/2:ℝ)^N)]
      nlinarith [pow_nonneg r0 k, hrle]
    calc ∑ i ∈ Finset.Ico k m, bsize C N ε i
        = C * ε * (2:ℝ)^(3*N) * ∑ i ∈ Finset.Ico k m, ((1/2:ℝ)^N)^i := hsum
      _ ≤ C * ε * (2:ℝ)^(3*N) * (((1/2:ℝ)^N)^k / (1 - (1/2:ℝ)^N)) :=
          mul_le_mul_of_nonneg_left hgeom hA0
      _ ≤ C * ε * (2:ℝ)^(3*N) * (2 * ((1/2:ℝ)^N)^k) :=
          mul_le_mul_of_nonneg_left hInv hA0
      _ = 2 * C * ε * (2:ℝ)^(3*N) * (1/2:ℝ)^(N*k) := by
          rw [← pow_mul]; ring

end Work.NN.Newton
