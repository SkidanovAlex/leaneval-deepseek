import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.bigW_le_pow
import Submission.Work.HP.Sig2.log_pow_le_rpow
import Submission.Work.HP.Sig2.caseF_arith
import Submission.Work.HP.Sig2.NN_ge_add_two

set_option maxHeartbeats 1200000

namespace Work.HP.MM2

open Work.HP

/-! ## Auxiliary arithmetic for `Sigma2mix_arith` -/

/-- Absorption of the polynomial loss.  If `a < 0` and `(5/6)a + b + δ < 0` then
`A^a B^b (log B + 1)^q ≤ K B^{-δ}` for all `B ≥ B₀` and `B^{5/6} ≤ A`:  `A ≥ B^{5/6}` with
`a < 0` gives `A^a ≤ (B^{5/6})^a = B^{(5/6)a}`, and the remaining power of `B` (negative
exponent) absorbs the power of `log B` by `Work.HP.Sig2.caseF_rpow_log_absorb`. -/
theorem Sig2arithMaster (a b δ q : ℝ) (ha : a < 0)
    (hc : (5 : ℝ) / 6 * a + b + δ < 0) :
    ∃ K B₀ : ℝ, 0 < K ∧ 1 ≤ B₀ ∧ ∀ A B : ℝ, B₀ ≤ B → B ^ ((5 : ℝ) / 6) ≤ A →
      A ^ a * B ^ b * (Real.log B + 1) ^ q ≤ K * B ^ (-δ) := by
  obtain ⟨K, B₀, hKpos, hB₀pos, hbound⟩ :=
    Work.HP.Sig2.caseF_rpow_log_absorb ((5 : ℝ) / 6 * a + b + δ) q hc
  refine ⟨K, max B₀ 2, hKpos,
    le_trans (by norm_num : (1 : ℝ) ≤ 2) (le_max_right _ _), ?_⟩
  intro A B hB hA
  have hB0 : B₀ ≤ B := le_trans (le_max_left _ _) hB
  have hB2 : (2 : ℝ) ≤ B := le_trans (le_max_right _ _) hB
  have hBpos : 0 < B := by linarith
  have hBnn : 0 ≤ B := le_of_lt hBpos
  have hB1 : (1 : ℝ) ≤ B := by linarith
  have hbase : 0 < B ^ ((5 : ℝ) / 6) := Real.rpow_pos_of_pos hBpos _
  have hlog1 : 0 ≤ Real.log B + 1 := by linarith [Real.log_nonneg hB1]
  have hAle : A ^ a ≤ B ^ ((5 : ℝ) / 6 * a) := by
    refine (Real.rpow_le_rpow_of_nonpos hbase hA (le_of_lt ha)).trans (le_of_eq ?_)
    exact (Real.rpow_mul hBnn ((5 : ℝ) / 6) a).symm
  have hstar : B ^ ((5 : ℝ) / 6 * a + b) = B ^ ((5 : ℝ) / 6 * a + b + δ) * B ^ (-δ) := by
    rw [← Real.rpow_add hBpos]
    congr 1
    ring
  calc A ^ a * B ^ b * (Real.log B + 1) ^ q
      ≤ B ^ ((5 : ℝ) / 6 * a) * B ^ b * (Real.log B + 1) ^ q := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hAle (Real.rpow_nonneg hBnn b))
          (Real.rpow_nonneg hlog1 q)
    _ = B ^ ((5 : ℝ) / 6 * a + b) * (Real.log B + 1) ^ q := by
        rw [← Real.rpow_add hBpos]
    _ = (B ^ ((5 : ℝ) / 6 * a + b + δ) * (Real.log B + 1) ^ q) * B ^ (-δ) := by
        rw [hstar]
        ring
    _ ≤ K * B ^ (-δ) := by
        exact mul_le_mul_of_nonneg_right (hbound B hB0) (Real.rpow_nonneg hBnn (-δ))

/-- Exponent bookkeeping, with `m = n + 1 - d` and `δ = 1/12`. -/
theorem Sig2arithExp (d n : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n) (h22 : (d, n) ≠ (2, 2)) :
    (3 : ℝ) ≤ (n : ℝ) ∧ (1 : ℝ) ≤ (((n + 1 - d : ℕ) : ℝ)) ∧
    ((1 : ℝ) / 20 - 3 * (n : ℝ) / 4 < 0) ∧
    ((5 : ℝ) / 6 * ((1 : ℝ) / 20 - 3 * (n : ℝ) / 4) + 1 / (((n + 1 - d : ℕ) : ℝ)) + 1 / 12 < 0) ∧
    (-7 * (n : ℝ) / 4 + 21 / 20 < 0) ∧
    ((5 : ℝ) / 6 * (-7 * (n : ℝ) / 4 + 21 / 20) + 1 / (((n + 1 - d : ℕ) : ℝ)) + 1 / 12 < 0) ∧
    ((5 : ℝ) / 6 * (-7 * (n : ℝ) / 4 + 21 / 20)
        + (n : ℝ) / (((n + 1 - d : ℕ) : ℝ)) + 1 / 12 < 0) ∧
    (-7 * (n : ℝ) / 4 + 1 / 20 < 0) ∧
    ((5 : ℝ) / 6 * (-7 * (n : ℝ) / 4 + 1 / 20)
        + (((n : ℝ) + 2) / (((n + 1 - d : ℕ) : ℝ)) - 1) + 1 / 12 < 0) := by
  have hn3 : 3 ≤ n := by
    by_contra h
    have hn2 : n = 2 := by omega
    have hd2 : d = 2 := by omega
    exact h22 (by simp [hd2, hn2])
  have hmcast : (((n + 1 - d : ℕ) : ℝ)) = (n : ℝ) + 1 - d := by
    rw [Nat.cast_sub (by omega : d ≤ n + 1), Nat.cast_add, Nat.cast_one]
  have hm1 : (1 : ℝ) ≤ (((n + 1 - d : ℕ) : ℝ)) := by
    rw [hmcast]
    have hdn' : (d : ℝ) ≤ (n : ℝ) := by exact_mod_cast hdn
    linarith
  have hmpos : (0 : ℝ) < (((n + 1 - d : ℕ) : ℝ)) := lt_of_lt_of_le zero_lt_one hm1
  have h3R : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn3
  have h1m : (1 : ℝ) / (((n + 1 - d : ℕ) : ℝ)) ≤ 1 := by
    rw [div_le_iff₀ hmpos]
    simpa using hm1
  have hnm : (n : ℝ) / (((n + 1 - d : ℕ) : ℝ)) ≤ (n : ℝ) := by
    rw [div_le_iff₀ hmpos]
    nlinarith [h3R, hm1]
  have hn2m : ((n : ℝ) + 2) / (((n + 1 - d : ℕ) : ℝ)) ≤ (n : ℝ) + 2 := by
    rw [div_le_iff₀ hmpos]
    nlinarith [h3R, hm1]
  exact ⟨h3R, hm1, by nlinarith, by nlinarith [h1m], by nlinarith,
    by nlinarith [h1m], by nlinarith [hnm], by nlinarith, by nlinarith [hn2m]⟩

/-- Substituting `X = B^{1/m}` (`m = n + 1 - d`) and `t = A^{3/4}/(C·W)` into the three shell
bounds: `X^{n+2-d} = B^{1+1/m}`, `X^{2n+1-d} = B^{1+n/m}`, `X^{n+2} = B^{(n+2)/m}` and
`1/t^n = (C·W)^n · A^{-3n/4}`. -/
theorem Sig2arithShells (d n : ℕ) (hdn : d ≤ n)
    (A B C Wr X t S₁ S₂ S₃ : ℝ) (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hW : 0 < Wr)
    (hX : X = B ^ (1 / ((n : ℝ) + 1 - d)))
    (ht : t = A ^ ((3 : ℝ) / 4) / (C * Wr))
    (hS₁ : S₁ ≤ X ^ ((n : ℝ) + 2 - d) * (1 + Real.log X) / t ^ n)
    (hS₂ : S₂ ≤ X ^ (2 * (n : ℝ) + 1 - d) * (1 + Real.log X) / t ^ n)
    (hS₃ : S₃ ≤ X ^ ((n : ℝ) + 2) * (1 + Real.log X) / t ^ n) :
    S₁ ≤ B ^ (1 + 1 / ((n : ℝ) + 1 - d)) * (1 + Real.log X) * (C * Wr) ^ n * A ^ (-(3 * (n : ℝ) / 4)) ∧
    S₂ ≤ B ^ (1 + (n : ℝ) / ((n : ℝ) + 1 - d)) * (1 + Real.log X) * (C * Wr) ^ n * A ^ (-(3 * (n : ℝ) / 4)) ∧
    S₃ ≤ B ^ (((n : ℝ) + 2) / ((n : ℝ) + 1 - d)) * (1 + Real.log X) * (C * Wr) ^ n * A ^ (-(3 * (n : ℝ) / 4)) := by
  have hdnR : (d : ℝ) ≤ (n : ℝ) := by exact_mod_cast hdn
  have hmpos : (0 : ℝ) < (n : ℝ) + 1 - d := by linarith
  have hm0 : (n : ℝ) + 1 - d ≠ 0 := ne_of_gt hmpos
  have hBnn : 0 ≤ B := le_of_lt hB
  have hAnn : 0 ≤ A := le_of_lt hA
  have hApow : (A ^ ((3 : ℝ) / 4)) ^ n = A ^ (3 * (n : ℝ) / 4) := by
    rw [← Real.rpow_natCast (A ^ ((3 : ℝ) / 4)) n, ← Real.rpow_mul hAnn]
    congr 1
    push_cast
    ring
  have htinv : (t ^ n)⁻¹ = (C * Wr) ^ n * A ^ (-(3 * (n : ℝ) / 4)) := by
    have ht1 : t = A ^ ((3 : ℝ) / 4) * (C * Wr)⁻¹ := by rw [ht, div_eq_mul_inv]
    have htt : t ^ n = A ^ (3 * (n : ℝ) / 4) * ((C * Wr) ^ n)⁻¹ := by
      rw [ht1, mul_pow, hApow, inv_pow]
    rw [htt, mul_inv_rev, inv_inv, ← Real.rpow_neg hAnn]
  have hX₁ : X ^ ((n : ℝ) + 2 - d) = B ^ (1 + 1 / ((n : ℝ) + 1 - d)) := by
    rw [hX, ← Real.rpow_mul hBnn,
      show (n : ℝ) + 2 - d = ((n : ℝ) + 1 - d) + 1 by ring]
    congr 1
    field_simp [hm0]
  have hX₂ : X ^ (2 * (n : ℝ) + 1 - d) = B ^ (1 + (n : ℝ) / ((n : ℝ) + 1 - d)) := by
    rw [hX, ← Real.rpow_mul hBnn,
      show 2 * (n : ℝ) + 1 - d = ((n : ℝ) + 1 - d) + (n : ℝ) by ring]
    congr 1
    field_simp [hm0]
  have hX₃ : X ^ ((n : ℝ) + 2) = B ^ (((n : ℝ) + 2) / ((n : ℝ) + 1 - d)) := by
    rw [hX, ← Real.rpow_mul hBnn]
    congr 1
    field_simp [hm0]
  refine ⟨?_, ?_, ?_⟩
  · calc S₁ ≤ X ^ ((n : ℝ) + 2 - d) * (1 + Real.log X) / t ^ n := hS₁
      _ = B ^ (1 + 1 / ((n : ℝ) + 1 - d)) * (1 + Real.log X)
            * ((C * Wr) ^ n * A ^ (-(3 * (n : ℝ) / 4))) := by
          rw [hX₁, div_eq_mul_inv, htinv]
      _ = B ^ (1 + 1 / ((n : ℝ) + 1 - d)) * (1 + Real.log X) * (C * Wr) ^ n
            * A ^ (-(3 * (n : ℝ) / 4)) := by ring
  · calc S₂ ≤ X ^ (2 * (n : ℝ) + 1 - d) * (1 + Real.log X) / t ^ n := hS₂
      _ = B ^ (1 + (n : ℝ) / ((n : ℝ) + 1 - d)) * (1 + Real.log X)
            * ((C * Wr) ^ n * A ^ (-(3 * (n : ℝ) / 4))) := by
          rw [hX₂, div_eq_mul_inv, htinv]
      _ = B ^ (1 + (n : ℝ) / ((n : ℝ) + 1 - d)) * (1 + Real.log X) * (C * Wr) ^ n
            * A ^ (-(3 * (n : ℝ) / 4)) := by ring
  · calc S₃ ≤ X ^ ((n : ℝ) + 2) * (1 + Real.log X) / t ^ n := hS₃
      _ = B ^ (((n : ℝ) + 2) / ((n : ℝ) + 1 - d)) * (1 + Real.log X)
            * ((C * Wr) ^ n * A ^ (-(3 * (n : ℝ) / 4))) := by
          rw [hX₃, div_eq_mul_inv, htinv]
      _ = B ^ (((n : ℝ) + 2) / ((n : ℝ) + 1 - d)) * (1 + Real.log X) * (C * Wr) ^ n
            * A ^ (-(3 * (n : ℝ) / 4)) := by ring

/-- The algebraic expansion of `Sigma2mix_arith`: each of the four contributions is written as
`Wr^{n+1} · A^{N-2-1/20} · B² · (log B·(1+log X)) · C^{...} · (a single A-power) · (a single
B-power)`, where `N = NN d n` and `m = n+1-d`. -/
theorem Sig2arithDecomp (d n : ℕ) (hN : n + 2 ≤ NN d n)
    (A B C Wr X Kc : ℝ) (hA : 0 < A) (hB : 0 < B) :
    (Kc * (Real.log B * Wr / 4) * B * (2 * A ^ (NN d n - 2) * (B ^ (1 + 1 / ((n : ℝ) + 1 - d)) * (1 + Real.log X) * (C * Wr) ^ n * A ^ (-(3 * (n : ℝ) / 4)))) = (Kc / 2) * Wr ^ (n + 1) * A ^ ((NN d n : ℝ) - 2 - 1 / 20) * B ^ 2 * (Real.log B * (1 + Real.log X)) * C ^ n * (A ^ ((1 : ℝ) / 20 - 3 * (n : ℝ) / 4) * B ^ (1 / ((n : ℝ) + 1 - d)))) ∧
    (Kc * (Real.log B * Wr / 4) * B * (A ^ (NN d n - n - 1) * C ^ (n - 1) * (B ^ (1 + 1 / ((n : ℝ) + 1 - d)) * (1 + Real.log X) * (C * Wr) ^ n * A ^ (-(3 * (n : ℝ) / 4)))) = (Kc / 4) * Wr ^ (n + 1) * A ^ ((NN d n : ℝ) - 2 - 1 / 20) * B ^ 2 * (Real.log B * (1 + Real.log X)) * C ^ (2 * n - 1) * (A ^ (-7 * (n : ℝ) / 4 + 21 / 20) * B ^ (1 / ((n : ℝ) + 1 - d)))) ∧
    (Kc * (Real.log B * Wr / 4) * B * (A ^ (NN d n - n - 1) * C ^ (n - 1) * (B ^ (1 + (n : ℝ) / ((n : ℝ) + 1 - d)) * (1 + Real.log X) * (C * Wr) ^ n * A ^ (-(3 * (n : ℝ) / 4)))) = (Kc / 4) * Wr ^ (n + 1) * A ^ ((NN d n : ℝ) - 2 - 1 / 20) * B ^ 2 * (Real.log B * (1 + Real.log X)) * C ^ (2 * n - 1) * (A ^ (-7 * (n : ℝ) / 4 + 21 / 20) * B ^ ((n : ℝ) / ((n : ℝ) + 1 - d)))) ∧
    (Kc * (Real.log B * Wr / 4) * B * (A ^ (NN d n - n - 2) * (1 + Real.log A) * (B ^ (((n : ℝ) + 2) / ((n : ℝ) + 1 - d)) * (1 + Real.log X) * (C * Wr) ^ n * A ^ (-(3 * (n : ℝ) / 4)))) = (Kc / 4) * Wr ^ (n + 1) * A ^ ((NN d n : ℝ) - 2 - 1 / 20) * B ^ 2 * (Real.log B * (1 + Real.log X)) * C ^ n * (1 + Real.log A) * (A ^ (-7 * (n : ℝ) / 4 + 1 / 20) * B ^ (((n : ℝ) + 2) / ((n : ℝ) + 1 - d) - 1))) := by
  have hN2 : 2 ≤ NN d n := by omega
  have hcast1 : (((NN d n - 2 : ℕ) : ℝ)) = (NN d n : ℝ) - 2 :=
    Nat.cast_sub hN2
  have hcast2 : (((NN d n - n - 1 : ℕ) : ℝ)) = (NN d n : ℝ) - (n : ℝ) - 1 := by
    rw [Nat.cast_sub (show 1 ≤ NN d n - n by omega),
      Nat.cast_sub (show n ≤ NN d n by omega), Nat.cast_one]
  have hcast4 : (((NN d n - n - 2 : ℕ) : ℝ)) = (NN d n : ℝ) - (n : ℝ) - 2 := by
    rw [Nat.cast_sub (show 2 ≤ NN d n - n by omega),
      Nat.cast_sub (show n ≤ NN d n by omega)]
    push_cast
    ring
  have hAid1 : A ^ ((NN d n : ℝ) - 2) * A ^ (-(3 * (n : ℝ) / 4))
      = A ^ ((NN d n : ℝ) - 2 - 1 / 20) * A ^ ((1 : ℝ) / 20 - 3 * (n : ℝ) / 4) := by
    rw [← Real.rpow_add hA, ← Real.rpow_add hA]
    congr 1
    ring
  have hAid2 : A ^ ((NN d n : ℝ) - (n : ℝ) - 1) * A ^ (-(3 * (n : ℝ) / 4))
      = A ^ ((NN d n : ℝ) - 2 - 1 / 20) * A ^ (-7 * (n : ℝ) / 4 + 21 / 20) := by
    rw [← Real.rpow_add hA, ← Real.rpow_add hA]
    congr 1
    ring
  have hAid4 : A ^ ((NN d n : ℝ) - (n : ℝ) - 2) * A ^ (-(3 * (n : ℝ) / 4))
      = A ^ ((NN d n : ℝ) - 2 - 1 / 20) * A ^ (-7 * (n : ℝ) / 4 + 1 / 20) := by
    rw [← Real.rpow_add hA, ← Real.rpow_add hA]
    congr 1
    ring
  have hWid1 : Wr * (C * Wr) ^ n = C ^ n * Wr ^ (n + 1) := by
    rw [mul_pow, pow_succ']
    ring
  have hWid2 : Wr * (C ^ (n - 1) * (C * Wr) ^ n) = C ^ (2 * n - 1) * Wr ^ (n + 1) := by
    rw [mul_pow]
    have hre : Wr * (C ^ (n - 1) * (C ^ n * Wr ^ n))
        = C ^ (n - 1) * C ^ n * (Wr * Wr ^ n) := by ring
    rw [hre, ← pow_add, show n - 1 + n = 2 * n - 1 by omega, ← pow_succ']
  have hB2r : B ^ (2 : ℝ) = B ^ 2 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hBid1 : B * B ^ (1 + 1 / ((n : ℝ) + 1 - d)) = B ^ 2 * B ^ (1 / ((n : ℝ) + 1 - d)) := by
    calc B * B ^ (1 + 1 / ((n : ℝ) + 1 - d)) = B ^ (1 : ℝ) * B ^ (1 + 1 / ((n : ℝ) + 1 - d)) := by
          rw [Real.rpow_one]
      _ = B ^ ((1 : ℝ) + (1 + 1 / ((n : ℝ) + 1 - d))) := by rw [← Real.rpow_add hB]
      _ = B ^ (2 + 1 / ((n : ℝ) + 1 - d)) := by congr 1; ring
      _ = B ^ 2 * B ^ (1 / ((n : ℝ) + 1 - d)) := by rw [Real.rpow_add hB, hB2r]
  have hBid3 : B * B ^ (1 + (n : ℝ) / ((n : ℝ) + 1 - d)) = B ^ 2 * B ^ ((n : ℝ) / ((n : ℝ) + 1 - d)) := by
    calc B * B ^ (1 + (n : ℝ) / ((n : ℝ) + 1 - d)) = B ^ (1 : ℝ) * B ^ (1 + (n : ℝ) / ((n : ℝ) + 1 - d)) := by
          rw [Real.rpow_one]
      _ = B ^ ((1 : ℝ) + (1 + (n : ℝ) / ((n : ℝ) + 1 - d))) := by rw [← Real.rpow_add hB]
      _ = B ^ (2 + (n : ℝ) / ((n : ℝ) + 1 - d)) := by congr 1; ring
      _ = B ^ 2 * B ^ ((n : ℝ) / ((n : ℝ) + 1 - d)) := by rw [Real.rpow_add hB, hB2r]
  have hBid4 : B * B ^ (((n : ℝ) + 2) / ((n : ℝ) + 1 - d))
      = B ^ 2 * B ^ (((n : ℝ) + 2) / ((n : ℝ) + 1 - d) - 1) := by
    calc B * B ^ (((n : ℝ) + 2) / ((n : ℝ) + 1 - d))
          = B ^ (1 : ℝ) * B ^ (((n : ℝ) + 2) / ((n : ℝ) + 1 - d)) := by rw [Real.rpow_one]
      _ = B ^ ((1 : ℝ) + ((n : ℝ) + 2) / ((n : ℝ) + 1 - d)) := by rw [← Real.rpow_add hB]
      _ = B ^ (2 + (((n : ℝ) + 2) / ((n : ℝ) + 1 - d) - 1)) := by congr 1; ring
      _ = B ^ 2 * B ^ (((n : ℝ) + 2) / ((n : ℝ) + 1 - d) - 1) := by rw [Real.rpow_add hB, hB2r]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hgroup : Kc * (Real.log B * Wr / 4) * B * (2 * A ^ (NN d n - 2) * (B ^ (1 + 1 / ((n : ℝ) + 1 - d)) * (1 + Real.log X) * (C * Wr) ^ n * A ^ (-(3 * (n : ℝ) / 4)))) = Kc * (Real.log B / 4) * 2 * (1 + Real.log X) * (Wr * (C * Wr) ^ n) * (B * B ^ (1 + 1 / ((n : ℝ) + 1 - d))) * (A ^ (NN d n - 2) * A ^ (-(3 * (n : ℝ) / 4))) := by ring
    rw [hgroup, ← Real.rpow_natCast A (NN d n - 2), hcast1, hAid1, hWid1, hBid1]
    ring_nf
  · have hgroup : Kc * (Real.log B * Wr / 4) * B * (A ^ (NN d n - n - 1) * C ^ (n - 1) * (B ^ (1 + 1 / ((n : ℝ) + 1 - d)) * (1 + Real.log X) * (C * Wr) ^ n * A ^ (-(3 * (n : ℝ) / 4)))) = Kc * (Real.log B / 4) * (1 + Real.log X) * (Wr * (C ^ (n - 1) * (C * Wr) ^ n)) * (B * B ^ (1 + 1 / ((n : ℝ) + 1 - d))) * (A ^ (NN d n - n - 1) * A ^ (-(3 * (n : ℝ) / 4))) := by ring
    rw [hgroup, ← Real.rpow_natCast A (NN d n - n - 1), hcast2, hAid2, hWid2, hBid1]
    ring_nf
  · have hgroup : Kc * (Real.log B * Wr / 4) * B * (A ^ (NN d n - n - 1) * C ^ (n - 1) * (B ^ (1 + (n : ℝ) / ((n : ℝ) + 1 - d)) * (1 + Real.log X) * (C * Wr) ^ n * A ^ (-(3 * (n : ℝ) / 4)))) = Kc * (Real.log B / 4) * (1 + Real.log X) * (Wr * (C ^ (n - 1) * (C * Wr) ^ n)) * (B * B ^ (1 + (n : ℝ) / ((n : ℝ) + 1 - d))) * (A ^ (NN d n - n - 1) * A ^ (-(3 * (n : ℝ) / 4))) := by ring
    rw [hgroup, ← Real.rpow_natCast A (NN d n - n - 1), hcast2, hAid2, hWid2, hBid3]
    ring_nf
  · have hgroup : Kc * (Real.log B * Wr / 4) * B * (A ^ (NN d n - n - 2) * (1 + Real.log A) * (B ^ (((n : ℝ) + 2) / ((n : ℝ) + 1 - d)) * (1 + Real.log X) * (C * Wr) ^ n * A ^ (-(3 * (n : ℝ) / 4)))) = Kc * (Real.log B / 4) * (1 + Real.log X) * (1 + Real.log A) * (Wr * (C * Wr) ^ n) * (B * B ^ (((n : ℝ) + 2) / ((n : ℝ) + 1 - d))) * (A ^ (NN d n - n - 2) * A ^ (-(3 * (n : ℝ) / 4))) := by ring
    rw [hgroup, ← Real.rpow_natCast A (NN d n - n - 2), hcast4, hAid4, hWid1, hBid4]
    ring_nf
/-- Pure arithmetic of `Sigma2mix_bound`.  With `N = NN d n`, `α = log B`, `W = bigW (wOf B)`, `X = B^{1/(n+1-d)}` and `t = A^{3/4}/(C·W)`, and with the three sums `S₁,S₂,S₃` bounded by the shells `s = -d, n-1-d, 0` (in the second the factor `1/‖ν(x)‖` has already been replaced by `≪ ‖x‖^{-d}`), one has `Kc(αW/4)B·((2A^{N-2}+A^{N-n-1}C^{n-1})S₁ + A^{N-n-1}C^{n-1}S₂ + A^{N-n-2}(1+log A)S₃) ≤ K A^{N-2-1/20}B²`.  Since every `A`-exponent is negative the worst case is `A = B^{5/6}`, where the three `B`-exponents are `1/(n+1-d) + 1/24 - 5n/8`, `n/(n+1-d) + 7/8 - 35n/24`, `(d+1)/(n+1-d) - 23/24 - 35n/24`; all are `≤ -1/3` on `2 ≤ d ≤ n`, `(d,n) ≠ (2,2)` (worst case `(d,n) = (3,3)`), which absorbs the polylog and `αW^{n+1}` losses via `bigW_le_pow` and `Sig2.log_pow_le_rpow`. -/
theorem Sigma2mix_arith (d n : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n) (h22 : (d, n) ≠ (2, 2)) :
    ∀ C : ℝ, 1 ≤ C → ∀ Kc : ℝ, 1 ≤ Kc → ∃ K B₀ : ℝ, 0 < K ∧
      ∀ A B X t S₁ S₂ S₃ : ℝ, B₀ ≤ B → B ^ ((5 : ℝ) / 6) ≤ A → A ≤ B ^ 2 →
        1 ≤ X → 1 ≤ t → X = B ^ (1 / ((n : ℝ) + 1 - d)) →
        t = A ^ ((3 : ℝ) / 4) / (C * (bigW (wOf B) : ℝ)) →
        S₁ ≤ X ^ ((n : ℝ) + 2 - d) * (1 + Real.log X) / t ^ n →
        S₂ ≤ X ^ (2 * (n : ℝ) + 1 - d) * (1 + Real.log X) / t ^ n →
        S₃ ≤ X ^ ((n : ℝ) + 2) * (1 + Real.log X) / t ^ n →
        Kc * (Real.log B * (bigW (wOf B) : ℝ) / 4) * B *
          ((2 * A ^ (NN d n - 2) + A ^ (NN d n - n - 1) * C ^ (n - 1)) * S₁
            + A ^ (NN d n - n - 1) * C ^ (n - 1) * S₂
            + A ^ (NN d n - n - 2) * (1 + Real.log A) * S₃)
          ≤ K * A ^ ((NN d n : ℝ) - 2 - (1 : ℝ) / 20) * B ^ 2 := by
  have hN : n + 2 ≤ NN d n := Sig2.NN_ge_add_two d n hd hdn
  obtain ⟨hn3R, hm1_cast, ha1neg, hc1_cast, ha2neg, hc2_cast, hc3_cast, ha4neg, hc4_cast⟩ :=
    Sig2arithExp d n hd hdn h22
  have hmcast : (((n + 1 - d : ℕ) : ℝ)) = (n : ℝ) + 1 - d := by
    rw [Nat.cast_sub (by omega : d ≤ n + 1), Nat.cast_add, Nat.cast_one]
  have hm1 : (1 : ℝ) ≤ (n : ℝ) + 1 - d := by
    rw [← hmcast]; exact hm1_cast
  have hmpos : (0 : ℝ) < (n : ℝ) + 1 - d := lt_of_lt_of_le zero_lt_one hm1
  have hc1 : (5 : ℝ) / 6 * ((1 : ℝ) / 20 - 3 * (n : ℝ) / 4) + 1 / ((n : ℝ) + 1 - d) + 1 / 12 < 0 := by
    have h := hc1_cast; rw [hmcast] at h; exact h
  have hc2 : (5 : ℝ) / 6 * (-7 * (n : ℝ) / 4 + 21 / 20) + 1 / ((n : ℝ) + 1 - d) + 1 / 12 < 0 := by
    have h := hc2_cast; rw [hmcast] at h; exact h
  have hc3 : (5 : ℝ) / 6 * (-7 * (n : ℝ) / 4 + 21 / 20) + (n : ℝ) / ((n : ℝ) + 1 - d) + 1 / 12 < 0 := by
    have h := hc3_cast; rw [hmcast] at h; exact h
  have hc4 : (5 : ℝ) / 6 * (-7 * (n : ℝ) / 4 + 1 / 20)
      + (((n : ℝ) + 2) / ((n : ℝ) + 1 - d) - 1) + 1 / 12 < 0 := by
    have h := hc4_cast; rw [hmcast] at h; exact h
  intro C hC1 Kc hKc1
  obtain ⟨K₁, B₁, hK₁, hB₁, hb₁⟩ :=
    Sig2arithMaster ((1 : ℝ) / 20 - 3 * (n : ℝ) / 4) (1 / ((n : ℝ) + 1 - d)) (1 / 12) 2 ha1neg hc1
  obtain ⟨K₂, B₂, hK₂, hB₂, hb₂⟩ :=
    Sig2arithMaster (-7 * (n : ℝ) / 4 + 21 / 20) (1 / ((n : ℝ) + 1 - d)) (1 / 12) 2 ha2neg hc2
  obtain ⟨K₃, B₃, hK₃, hB₃, hb₃⟩ :=
    Sig2arithMaster (-7 * (n : ℝ) / 4 + 21 / 20) ((n : ℝ) / ((n : ℝ) + 1 - d)) (1 / 12) 2 ha2neg hc3
  obtain ⟨K₄, B₄, hK₄, hB₄, hb₄⟩ :=
    Sig2arithMaster (-7 * (n : ℝ) / 4 + 1 / 20) (((n : ℝ) + 2) / ((n : ℝ) + 1 - d) - 1) (1 / 12) 3
      ha4neg hc4
  obtain ⟨BW, hBWe⟩ := bigW_le_pow (1 / (12 * ((n : ℝ) + 1))) (by positivity)
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC1
  have hKc : 0 < Kc := lt_of_lt_of_le zero_lt_one hKc1
  have hKpos : 0 < (Kc / 4) * (2 * C ^ n * K₁ + C ^ (2 * n - 1) * (K₂ + K₃) + 3 * C ^ n * K₄) := by positivity
  refine ⟨(Kc / 4) * (2 * C ^ n * K₁ + C ^ (2 * n - 1) * (K₂ + K₃) + 3 * C ^ n * K₄), max BW (max B₁ (max B₂ (max B₃ (max B₄ 2)))), hKpos, ?_⟩
  intro A B X t S₁ S₂ S₃ hB0 hAlow hAhigh hXge htge hXeq hteq hS₁ hS₂ hS₃
  have hBW : BW ≤ B := le_trans (le_max_left _ _) hB0
  have hBb₁ : B₁ ≤ B := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hB0
  have hBb₂ : B₂ ≤ B :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hB0
  have hBb₃ : B₃ ≤ B :=
    le_trans (le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
      (le_max_right _ _)) (le_max_right _ _)) hB0
  have hBb₄ : B₄ ≤ B :=
    le_trans (le_trans (le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
      (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)) hB0
  have hB2le : (2 : ℝ) ≤ B :=
    le_trans (le_trans (le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
      (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)) hB0
  have hBpos : 0 < B := by linarith
  have hBnn : 0 ≤ B := le_of_lt hBpos
  have hB1 : (1 : ℝ) ≤ B := by linarith
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg hB1
  have hbase : 0 < B ^ ((5 : ℝ) / 6) := Real.rpow_pos_of_pos hBpos _
  have hApos : 0 < A := lt_of_lt_of_le hbase hAlow
  have hAnn : 0 ≤ A := le_of_lt hApos
  have hA1 : (1 : ℝ) ≤ A := le_trans (Real.one_le_rpow hB1 (by norm_num)) hAlow
  have hlogA0 : 0 ≤ Real.log A := Real.log_nonneg hA1
  have hWr1 : (1 : ℝ) ≤ ((bigW (wOf B) : ℕ) : ℝ) := by
    exact_mod_cast one_le_bigW (wOf B)
  have hWrpos : 0 < ((bigW (wOf B) : ℕ) : ℝ) := lt_of_lt_of_le zero_lt_one hWr1
  have hWrnn : 0 ≤ ((bigW (wOf B) : ℕ) : ℝ) := le_of_lt hWrpos
  have hlogX : Real.log X ≤ Real.log B := by
    have hXle : X ≤ B := by
      have h1 : 1 / ((n : ℝ) + 1 - d) ≤ 1 := by
        rw [div_le_iff₀ hmpos]; simpa using hm1
      calc X = B ^ (1 / ((n : ℝ) + 1 - d)) := hXeq
        _ ≤ B ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hB1 h1
        _ = B := Real.rpow_one B
    exact Real.log_le_log (lt_of_lt_of_le zero_lt_one hXge) hXle
  have hlogBX : Real.log B * (1 + Real.log X) ≤ (Real.log B + 1) ^ 2 := by
    have h1 : Real.log B * (1 + Real.log X) ≤ Real.log B * (1 + Real.log B) :=
      mul_le_mul_of_nonneg_left (by linarith) hlogB
    have h2 : Real.log B * (1 + Real.log B) ≤ (Real.log B + 1) ^ 2 := by nlinarith
    linarith
  have hlogA : 1 + Real.log A ≤ 3 * (Real.log B + 1) := by
    have h1 : Real.log A ≤ Real.log (B ^ 2) := Real.log_le_log hApos hAhigh
    have h2 : Real.log (B ^ 2) = 2 * Real.log B := by
      rw [Real.log_pow]; norm_num
    nlinarith [h1, h2, hlogB]
  have hlogBXA : Real.log B * (1 + Real.log X) * (1 + Real.log A)
      ≤ 3 * (Real.log B + 1) ^ 3 := by
    have h1 := mul_le_mul hlogBX hlogA (by linarith : (0 : ℝ) ≤ 1 + Real.log A)
      (by positivity : (0 : ℝ) ≤ (Real.log B + 1) ^ 2)
    have h2 : (Real.log B + 1) ^ 2 * (3 * (Real.log B + 1)) = 3 * (Real.log B + 1) ^ 3 := by
      ring
    exact h1.trans (le_of_eq h2)
  obtain ⟨hSh1, hSh2, hSh3⟩ :=
    Sig2arithShells d n hdn A B C (((bigW (wOf B) : ℕ) : ℝ)) X t S₁ S₂ S₃ hApos hBpos hCpos hWrpos hXeq hteq
      hS₁ hS₂ hS₃
  have hc1nn : 0 ≤ 2 * A ^ (NN d n - 2) + A ^ (NN d n - n - 1) * C ^ (n - 1) := by positivity
  have hc2nn : 0 ≤ A ^ (NN d n - n - 1) * C ^ (n - 1) := by positivity
  have hc3nn : 0 ≤ A ^ (NN d n - n - 2) * (1 + Real.log A) := by positivity
  have hT1 : (2 * A ^ (NN d n - 2) + A ^ (NN d n - n - 1) * C ^ (n - 1)) * S₁
      ≤ (2 * A ^ (NN d n - 2) + A ^ (NN d n - n - 1) * C ^ (n - 1)) * (B ^ (1 + 1 / ((n : ℝ) + 1 - d)) * (1 + Real.log X) * (C * ((bigW (wOf B) : ℕ) : ℝ)) ^ n * A ^ (-(3 * (n : ℝ) / 4))) :=
    mul_le_mul_of_nonneg_left hSh1 hc1nn
  have hT2 : A ^ (NN d n - n - 1) * C ^ (n - 1) * S₂
      ≤ A ^ (NN d n - n - 1) * C ^ (n - 1) * (B ^ (1 + (n : ℝ) / ((n : ℝ) + 1 - d)) * (1 + Real.log X) * (C * ((bigW (wOf B) : ℕ) : ℝ)) ^ n * A ^ (-(3 * (n : ℝ) / 4))) :=
    mul_le_mul_of_nonneg_left hSh2 hc2nn
  have hT3 : A ^ (NN d n - n - 2) * (1 + Real.log A) * S₃
      ≤ A ^ (NN d n - n - 2) * (1 + Real.log A) * (B ^ (((n : ℝ) + 2) / ((n : ℝ) + 1 - d)) * (1 + Real.log X) * (C * ((bigW (wOf B) : ℕ) : ℝ)) ^ n * A ^ (-(3 * (n : ℝ) / 4))) :=
    mul_le_mul_of_nonneg_left hSh3 hc3nn
  have hU : (2 * A ^ (NN d n - 2) + A ^ (NN d n - n - 1) * C ^ (n - 1)) * S₁
            + A ^ (NN d n - n - 1) * C ^ (n - 1) * S₂
            + A ^ (NN d n - n - 2) * (1 + Real.log A) * S₃
      ≤ (2 * A ^ (NN d n - 2) + A ^ (NN d n - n - 1) * C ^ (n - 1)) * (B ^ (1 + 1 / ((n : ℝ) + 1 - d)) * (1 + Real.log X) * (C * ((bigW (wOf B) : ℕ) : ℝ)) ^ n * A ^ (-(3 * (n : ℝ) / 4)))
            + A ^ (NN d n - n - 1) * C ^ (n - 1) * (B ^ (1 + (n : ℝ) / ((n : ℝ) + 1 - d)) * (1 + Real.log X) * (C * ((bigW (wOf B) : ℕ) : ℝ)) ^ n * A ^ (-(3 * (n : ℝ) / 4)))
            + A ^ (NN d n - n - 2) * (1 + Real.log A) * (B ^ (((n : ℝ) + 2) / ((n : ℝ) + 1 - d)) * (1 + Real.log X) * (C * ((bigW (wOf B) : ℕ) : ℝ)) ^ n * A ^ (-(3 * (n : ℝ) / 4))) := add_le_add (add_le_add hT1 hT2) hT3
  have hE : 0 ≤ Kc * (Real.log B * ((bigW (wOf B) : ℕ) : ℝ) / 4) * B := by
    have h1 : 0 ≤ Real.log B * ((bigW (wOf B) : ℕ) : ℝ) / 4 := div_nonneg (mul_nonneg hlogB hWrnn) (by norm_num)
    exact mul_nonneg (mul_nonneg (le_of_lt hKc) h1) hBnn
  have hp1 : (A ^ ((1 : ℝ) / 20 - 3 * (n : ℝ) / 4) * B ^ (1 / ((n : ℝ) + 1 - d))) * (Real.log B + 1) ^ 2 ≤ K₁ * B ^ (-(1 / 12 : ℝ)) := by
    have hq : (A ^ ((1 : ℝ) / 20 - 3 * (n : ℝ) / 4) * B ^ (1 / ((n : ℝ) + 1 - d))) * (Real.log B + 1) ^ (2 : ℝ) ≤ K₁ * B ^ (-(1 / 12 : ℝ)) :=
      hb₁ A B hBb₁ hAlow
    rwa [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at hq
  have hp2 : (A ^ (-7 * (n : ℝ) / 4 + 21 / 20) * B ^ (1 / ((n : ℝ) + 1 - d))) * (Real.log B + 1) ^ 2 ≤ K₂ * B ^ (-(1 / 12 : ℝ)) := by
    have hq : (A ^ (-7 * (n : ℝ) / 4 + 21 / 20) * B ^ (1 / ((n : ℝ) + 1 - d))) * (Real.log B + 1) ^ (2 : ℝ) ≤ K₂ * B ^ (-(1 / 12 : ℝ)) :=
      hb₂ A B hBb₂ hAlow
    rwa [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at hq
  have hp3 : (A ^ (-7 * (n : ℝ) / 4 + 21 / 20) * B ^ ((n : ℝ) / ((n : ℝ) + 1 - d))) * (Real.log B + 1) ^ 2 ≤ K₃ * B ^ (-(1 / 12 : ℝ)) := by
    have hq : (A ^ (-7 * (n : ℝ) / 4 + 21 / 20) * B ^ ((n : ℝ) / ((n : ℝ) + 1 - d))) * (Real.log B + 1) ^ (2 : ℝ) ≤ K₃ * B ^ (-(1 / 12 : ℝ)) :=
      hb₃ A B hBb₃ hAlow
    rwa [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at hq
  have hp4 : (A ^ (-7 * (n : ℝ) / 4 + 1 / 20) * B ^ (((n : ℝ) + 2) / ((n : ℝ) + 1 - d) - 1)) * (Real.log B + 1) ^ 3 ≤ K₄ * B ^ (-(1 / 12 : ℝ)) := by
    have hq : (A ^ (-7 * (n : ℝ) / 4 + 1 / 20) * B ^ (((n : ℝ) + 2) / ((n : ℝ) + 1 - d) - 1)) * (Real.log B + 1) ^ (3 : ℝ) ≤ K₄ * B ^ (-(1 / 12 : ℝ)) :=
      hb₄ A B hBb₄ hAlow
    rwa [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at hq
  have hpiece1 : 2 * C ^ n * (A ^ ((1 : ℝ) / 20 - 3 * (n : ℝ) / 4) * B ^ (1 / ((n : ℝ) + 1 - d))) * (Real.log B * (1 + Real.log X))
      ≤ 2 * C ^ n * K₁ * B ^ (-(1 / 12 : ℝ)) := by
    have hP1nn : 0 ≤ (A ^ ((1 : ℝ) / 20 - 3 * (n : ℝ) / 4) * B ^ (1 / ((n : ℝ) + 1 - d))) := by positivity
    have hstep : (A ^ ((1 : ℝ) / 20 - 3 * (n : ℝ) / 4) * B ^ (1 / ((n : ℝ) + 1 - d))) * (Real.log B * (1 + Real.log X)) ≤ (A ^ ((1 : ℝ) / 20 - 3 * (n : ℝ) / 4) * B ^ (1 / ((n : ℝ) + 1 - d))) * (Real.log B + 1) ^ 2 :=
      mul_le_mul_of_nonneg_left hlogBX hP1nn
    have hstep2 : (A ^ ((1 : ℝ) / 20 - 3 * (n : ℝ) / 4) * B ^ (1 / ((n : ℝ) + 1 - d))) * (Real.log B * (1 + Real.log X)) ≤ K₁ * B ^ (-(1 / 12 : ℝ)) :=
      hstep.trans hp1
    have hCnn : 0 ≤ 2 * C ^ n := by positivity
    calc 2 * C ^ n * (A ^ ((1 : ℝ) / 20 - 3 * (n : ℝ) / 4) * B ^ (1 / ((n : ℝ) + 1 - d))) * (Real.log B * (1 + Real.log X))
        = (2 * C ^ n) * ((A ^ ((1 : ℝ) / 20 - 3 * (n : ℝ) / 4) * B ^ (1 / ((n : ℝ) + 1 - d))) * (Real.log B * (1 + Real.log X))) := by ring
      _ ≤ (2 * C ^ n) * (K₁ * B ^ (-(1 / 12 : ℝ))) := mul_le_mul_of_nonneg_left hstep2 hCnn
      _ = 2 * C ^ n * K₁ * B ^ (-(1 / 12 : ℝ)) := by ring
  have hpiece2 : C ^ (2 * n - 1) * (A ^ (-7 * (n : ℝ) / 4 + 21 / 20) * B ^ (1 / ((n : ℝ) + 1 - d))) * (Real.log B * (1 + Real.log X))
      ≤ C ^ (2 * n - 1) * K₂ * B ^ (-(1 / 12 : ℝ)) := by
    have hP2nn : 0 ≤ (A ^ (-7 * (n : ℝ) / 4 + 21 / 20) * B ^ (1 / ((n : ℝ) + 1 - d))) := by positivity
    have hstep : (A ^ (-7 * (n : ℝ) / 4 + 21 / 20) * B ^ (1 / ((n : ℝ) + 1 - d))) * (Real.log B * (1 + Real.log X)) ≤ (A ^ (-7 * (n : ℝ) / 4 + 21 / 20) * B ^ (1 / ((n : ℝ) + 1 - d))) * (Real.log B + 1) ^ 2 :=
      mul_le_mul_of_nonneg_left hlogBX hP2nn
    have hstep2 : (A ^ (-7 * (n : ℝ) / 4 + 21 / 20) * B ^ (1 / ((n : ℝ) + 1 - d))) * (Real.log B * (1 + Real.log X)) ≤ K₂ * B ^ (-(1 / 12 : ℝ)) :=
      hstep.trans hp2
    have hCnn : 0 ≤ C ^ (2 * n - 1) := by positivity
    calc C ^ (2 * n - 1) * (A ^ (-7 * (n : ℝ) / 4 + 21 / 20) * B ^ (1 / ((n : ℝ) + 1 - d))) * (Real.log B * (1 + Real.log X))
        = (C ^ (2 * n - 1)) * ((A ^ (-7 * (n : ℝ) / 4 + 21 / 20) * B ^ (1 / ((n : ℝ) + 1 - d))) * (Real.log B * (1 + Real.log X))) := by ring
      _ ≤ (C ^ (2 * n - 1)) * (K₂ * B ^ (-(1 / 12 : ℝ))) := mul_le_mul_of_nonneg_left hstep2 hCnn
      _ = C ^ (2 * n - 1) * K₂ * B ^ (-(1 / 12 : ℝ)) := by ring
  have hpiece3 : C ^ (2 * n - 1) * (A ^ (-7 * (n : ℝ) / 4 + 21 / 20) * B ^ ((n : ℝ) / ((n : ℝ) + 1 - d))) * (Real.log B * (1 + Real.log X))
      ≤ C ^ (2 * n - 1) * K₃ * B ^ (-(1 / 12 : ℝ)) := by
    have hP3nn : 0 ≤ (A ^ (-7 * (n : ℝ) / 4 + 21 / 20) * B ^ ((n : ℝ) / ((n : ℝ) + 1 - d))) := by positivity
    have hstep : (A ^ (-7 * (n : ℝ) / 4 + 21 / 20) * B ^ ((n : ℝ) / ((n : ℝ) + 1 - d))) * (Real.log B * (1 + Real.log X)) ≤ (A ^ (-7 * (n : ℝ) / 4 + 21 / 20) * B ^ ((n : ℝ) / ((n : ℝ) + 1 - d))) * (Real.log B + 1) ^ 2 :=
      mul_le_mul_of_nonneg_left hlogBX hP3nn
    have hstep2 : (A ^ (-7 * (n : ℝ) / 4 + 21 / 20) * B ^ ((n : ℝ) / ((n : ℝ) + 1 - d))) * (Real.log B * (1 + Real.log X)) ≤ K₃ * B ^ (-(1 / 12 : ℝ)) :=
      hstep.trans hp3
    have hCnn : 0 ≤ C ^ (2 * n - 1) := by positivity
    calc C ^ (2 * n - 1) * (A ^ (-7 * (n : ℝ) / 4 + 21 / 20) * B ^ ((n : ℝ) / ((n : ℝ) + 1 - d))) * (Real.log B * (1 + Real.log X))
        = (C ^ (2 * n - 1)) * ((A ^ (-7 * (n : ℝ) / 4 + 21 / 20) * B ^ ((n : ℝ) / ((n : ℝ) + 1 - d))) * (Real.log B * (1 + Real.log X))) := by ring
      _ ≤ (C ^ (2 * n - 1)) * (K₃ * B ^ (-(1 / 12 : ℝ))) := mul_le_mul_of_nonneg_left hstep2 hCnn
      _ = C ^ (2 * n - 1) * K₃ * B ^ (-(1 / 12 : ℝ)) := by ring
  have hpiece4 : C ^ n * (1 + Real.log A) * (A ^ (-7 * (n : ℝ) / 4 + 1 / 20) * B ^ (((n : ℝ) + 2) / ((n : ℝ) + 1 - d) - 1)) * (Real.log B * (1 + Real.log X))
      ≤ 3 * C ^ n * K₄ * B ^ (-(1 / 12 : ℝ)) := by
    have hP4nn : 0 ≤ (A ^ (-7 * (n : ℝ) / 4 + 1 / 20) * B ^ (((n : ℝ) + 2) / ((n : ℝ) + 1 - d) - 1)) := by positivity
    have hstep : (A ^ (-7 * (n : ℝ) / 4 + 1 / 20) * B ^ (((n : ℝ) + 2) / ((n : ℝ) + 1 - d) - 1)) * ((Real.log B * (1 + Real.log X)) * (1 + Real.log A))
        ≤ (A ^ (-7 * (n : ℝ) / 4 + 1 / 20) * B ^ (((n : ℝ) + 2) / ((n : ℝ) + 1 - d) - 1)) * (3 * (Real.log B + 1) ^ 3) := mul_le_mul_of_nonneg_left hlogBXA hP4nn
    have hstep2 : (A ^ (-7 * (n : ℝ) / 4 + 1 / 20) * B ^ (((n : ℝ) + 2) / ((n : ℝ) + 1 - d) - 1)) * (3 * (Real.log B + 1) ^ 3) ≤ 3 * (K₄ * B ^ (-(1 / 12 : ℝ))) := by
      have h3 : 3 * ((A ^ (-7 * (n : ℝ) / 4 + 1 / 20) * B ^ (((n : ℝ) + 2) / ((n : ℝ) + 1 - d) - 1)) * (Real.log B + 1) ^ 3) ≤ 3 * (K₄ * B ^ (-(1 / 12 : ℝ))) :=
        mul_le_mul_of_nonneg_left hp4 (by norm_num : (0 : ℝ) ≤ 3)
      calc (A ^ (-7 * (n : ℝ) / 4 + 1 / 20) * B ^ (((n : ℝ) + 2) / ((n : ℝ) + 1 - d) - 1)) * (3 * (Real.log B + 1) ^ 3) = 3 * ((A ^ (-7 * (n : ℝ) / 4 + 1 / 20) * B ^ (((n : ℝ) + 2) / ((n : ℝ) + 1 - d) - 1)) * (Real.log B + 1) ^ 3) := by ring
        _ ≤ 3 * (K₄ * B ^ (-(1 / 12 : ℝ))) := h3
    have hstep3 : 3 * (K₄ * B ^ (-(1 / 12 : ℝ))) = 3 * K₄ * B ^ (-(1 / 12 : ℝ)) := by ring
    have hCnn : 0 ≤ C ^ n := by positivity
    calc C ^ n * (1 + Real.log A) * (A ^ (-7 * (n : ℝ) / 4 + 1 / 20) * B ^ (((n : ℝ) + 2) / ((n : ℝ) + 1 - d) - 1)) * (Real.log B * (1 + Real.log X))
        = (C ^ n) * ((A ^ (-7 * (n : ℝ) / 4 + 1 / 20) * B ^ (((n : ℝ) + 2) / ((n : ℝ) + 1 - d) - 1)) * ((Real.log B * (1 + Real.log X)) * (1 + Real.log A))) := by
          ring
      _ ≤ (C ^ n) * (3 * (K₄ * B ^ (-(1 / 12 : ℝ)))) :=
          mul_le_mul_of_nonneg_left (hstep.trans hstep2) hCnn
      _ = 3 * C ^ n * K₄ * B ^ (-(1 / 12 : ℝ)) := by rw [hstep3]; ring
  have hbr : Real.log B * (1 + Real.log X) * (2 * C ^ n * (A ^ ((1 : ℝ) / 20 - 3 * (n : ℝ) / 4) * B ^ (1 / ((n : ℝ) + 1 - d))) + C ^ (2 * n - 1) * (A ^ (-7 * (n : ℝ) / 4 + 21 / 20) * B ^ (1 / ((n : ℝ) + 1 - d))) + C ^ (2 * n - 1) * (A ^ (-7 * (n : ℝ) / 4 + 21 / 20) * B ^ ((n : ℝ) / ((n : ℝ) + 1 - d))) + C ^ n * (1 + Real.log A) * (A ^ (-7 * (n : ℝ) / 4 + 1 / 20) * B ^ (((n : ℝ) + 2) / ((n : ℝ) + 1 - d) - 1)))
      ≤ (2 * C ^ n * K₁ + C ^ (2 * n - 1) * (K₂ + K₃) + 3 * C ^ n * K₄) * B ^ (-(1 / 12 : ℝ)) := by
    have hexp : Real.log B * (1 + Real.log X) * (2 * C ^ n * (A ^ ((1 : ℝ) / 20 - 3 * (n : ℝ) / 4) * B ^ (1 / ((n : ℝ) + 1 - d))) + C ^ (2 * n - 1) * (A ^ (-7 * (n : ℝ) / 4 + 21 / 20) * B ^ (1 / ((n : ℝ) + 1 - d))) + C ^ (2 * n - 1) * (A ^ (-7 * (n : ℝ) / 4 + 21 / 20) * B ^ ((n : ℝ) / ((n : ℝ) + 1 - d))) + C ^ n * (1 + Real.log A) * (A ^ (-7 * (n : ℝ) / 4 + 1 / 20) * B ^ (((n : ℝ) + 2) / ((n : ℝ) + 1 - d) - 1)))
        = 2 * C ^ n * (A ^ ((1 : ℝ) / 20 - 3 * (n : ℝ) / 4) * B ^ (1 / ((n : ℝ) + 1 - d))) * (Real.log B * (1 + Real.log X))
          + C ^ (2 * n - 1) * (A ^ (-7 * (n : ℝ) / 4 + 21 / 20) * B ^ (1 / ((n : ℝ) + 1 - d))) * (Real.log B * (1 + Real.log X))
          + C ^ (2 * n - 1) * (A ^ (-7 * (n : ℝ) / 4 + 21 / 20) * B ^ ((n : ℝ) / ((n : ℝ) + 1 - d))) * (Real.log B * (1 + Real.log X))
          + C ^ n * (1 + Real.log A) * (A ^ (-7 * (n : ℝ) / 4 + 1 / 20) * B ^ (((n : ℝ) + 2) / ((n : ℝ) + 1 - d) - 1)) * (Real.log B * (1 + Real.log X)) := by
      ring
    rw [hexp]
    have hsum := add_le_add (add_le_add (add_le_add hpiece1 hpiece2) hpiece3) hpiece4
    exact hsum.trans (le_of_eq (by ring))
  have hcomb : Kc * (Real.log B * ((bigW (wOf B) : ℕ) : ℝ) / 4) * B * ((2 * A ^ (NN d n - 2) + A ^ (NN d n - n - 1) * C ^ (n - 1)) * (B ^ (1 + 1 / ((n : ℝ) + 1 - d)) * (1 + Real.log X) * (C * ((bigW (wOf B) : ℕ) : ℝ)) ^ n * A ^ (-(3 * (n : ℝ) / 4)))
            + A ^ (NN d n - n - 1) * C ^ (n - 1) * (B ^ (1 + (n : ℝ) / ((n : ℝ) + 1 - d)) * (1 + Real.log X) * (C * ((bigW (wOf B) : ℕ) : ℝ)) ^ n * A ^ (-(3 * (n : ℝ) / 4)))
            + A ^ (NN d n - n - 2) * (1 + Real.log A) * (B ^ (((n : ℝ) + 2) / ((n : ℝ) + 1 - d)) * (1 + Real.log X) * (C * ((bigW (wOf B) : ℕ) : ℝ)) ^ n * A ^ (-(3 * (n : ℝ) / 4))))
      = Kc * (Real.log B * ((bigW (wOf B) : ℕ) : ℝ) / 4) * B * (2 * A ^ (NN d n - 2) * (B ^ (1 + 1 / ((n : ℝ) + 1 - d)) * (1 + Real.log X) * (C * ((bigW (wOf B) : ℕ) : ℝ)) ^ n * A ^ (-(3 * (n : ℝ) / 4)))) + Kc * (Real.log B * ((bigW (wOf B) : ℕ) : ℝ) / 4) * B * (A ^ (NN d n - n - 1) * C ^ (n - 1) * (B ^ (1 + 1 / ((n : ℝ) + 1 - d)) * (1 + Real.log X) * (C * ((bigW (wOf B) : ℕ) : ℝ)) ^ n * A ^ (-(3 * (n : ℝ) / 4)))) + Kc * (Real.log B * ((bigW (wOf B) : ℕ) : ℝ) / 4) * B * (A ^ (NN d n - n - 1) * C ^ (n - 1) * (B ^ (1 + (n : ℝ) / ((n : ℝ) + 1 - d)) * (1 + Real.log X) * (C * ((bigW (wOf B) : ℕ) : ℝ)) ^ n * A ^ (-(3 * (n : ℝ) / 4)))) + Kc * (Real.log B * ((bigW (wOf B) : ℕ) : ℝ) / 4) * B * (A ^ (NN d n - n - 2) * (1 + Real.log A) * (B ^ (((n : ℝ) + 2) / ((n : ℝ) + 1 - d)) * (1 + Real.log X) * (C * ((bigW (wOf B) : ℕ) : ℝ)) ^ n * A ^ (-(3 * (n : ℝ) / 4)))) := by ring
  obtain ⟨hc1', hc2', hc3', hc4'⟩ := Sig2arithDecomp d n hN A B C (((bigW (wOf B) : ℕ) : ℝ)) X Kc hApos hBpos
  have hmain : Kc * (Real.log B * ((bigW (wOf B) : ℕ) : ℝ) / 4) * B * ((2 * A ^ (NN d n - 2) + A ^ (NN d n - n - 1) * C ^ (n - 1)) * (B ^ (1 + 1 / ((n : ℝ) + 1 - d)) * (1 + Real.log X) * (C * ((bigW (wOf B) : ℕ) : ℝ)) ^ n * A ^ (-(3 * (n : ℝ) / 4)))
            + A ^ (NN d n - n - 1) * C ^ (n - 1) * (B ^ (1 + (n : ℝ) / ((n : ℝ) + 1 - d)) * (1 + Real.log X) * (C * ((bigW (wOf B) : ℕ) : ℝ)) ^ n * A ^ (-(3 * (n : ℝ) / 4)))
            + A ^ (NN d n - n - 2) * (1 + Real.log A) * (B ^ (((n : ℝ) + 2) / ((n : ℝ) + 1 - d)) * (1 + Real.log X) * (C * ((bigW (wOf B) : ℕ) : ℝ)) ^ n * A ^ (-(3 * (n : ℝ) / 4)))) = (Kc / 4) * ((bigW (wOf B) : ℕ) : ℝ) ^ (n + 1) * A ^ ((NN d n : ℝ) - 2 - 1 / 20) * B ^ 2 * (Real.log B * (1 + Real.log X)) * (2 * C ^ n * (A ^ ((1 : ℝ) / 20 - 3 * (n : ℝ) / 4) * B ^ (1 / ((n : ℝ) + 1 - d))) + C ^ (2 * n - 1) * (A ^ (-7 * (n : ℝ) / 4 + 21 / 20) * B ^ (1 / ((n : ℝ) + 1 - d))) + C ^ (2 * n - 1) * (A ^ (-7 * (n : ℝ) / 4 + 21 / 20) * B ^ ((n : ℝ) / ((n : ℝ) + 1 - d))) + C ^ n * (1 + Real.log A) * (A ^ (-7 * (n : ℝ) / 4 + 1 / 20) * B ^ (((n : ℝ) + 2) / ((n : ℝ) + 1 - d) - 1))) := by
    rw [hcomb, hc1', hc2', hc3', hc4']
    ring
  have hComnn : 0 ≤ (Kc / 4) * ((bigW (wOf B) : ℕ) : ℝ) ^ (n + 1) * A ^ ((NN d n : ℝ) - 2 - 1 / 20) * B ^ 2 := by
    have hA2 : 0 ≤ A ^ ((NN d n : ℝ) - 2 - 1 / 20) := Real.rpow_nonneg hAnn _
    have hW2 : 0 ≤ ((bigW (wOf B) : ℕ) : ℝ) ^ (n + 1) := by positivity
    have hB2 : 0 ≤ B ^ 2 := by positivity
    have hKc4 : 0 ≤ Kc / 4 := by linarith
    exact mul_nonneg (mul_nonneg (mul_nonneg hKc4 hW2) hA2) hB2
  have hWB : (((bigW (wOf B) : ℕ) : ℝ)) ^ (n + 1) * B ^ (-(1 / 12 : ℝ)) ≤ 1 := by
    have hWle : (((bigW (wOf B) : ℕ) : ℝ)) ≤ B ^ (1 / (12 * ((n : ℝ) + 1))) := hBWe B hBW
    have hpow : (((bigW (wOf B) : ℕ) : ℝ)) ^ (n + 1) ≤ B ^ (1 / 12 : ℝ) := by
      have h1 : (((bigW (wOf B) : ℕ) : ℝ)) ^ (n + 1) ≤ (B ^ (1 / (12 * ((n : ℝ) + 1)))) ^ (n + 1) :=
        pow_le_pow_left₀ hWrnn hWle (n + 1)
      have h2 : (B ^ (1 / (12 * ((n : ℝ) + 1)))) ^ (n + 1) = B ^ (1 / 12 : ℝ) := by
        rw [← Real.rpow_natCast (B ^ (1 / (12 * ((n : ℝ) + 1)))) (n + 1), ← Real.rpow_mul hBnn]
        congr 1
        rw [Nat.cast_add, Nat.cast_one]
        field_simp
      linarith
    calc (((bigW (wOf B) : ℕ) : ℝ)) ^ (n + 1) * B ^ (-(1 / 12 : ℝ)) ≤ B ^ (1 / 12 : ℝ) * B ^ (-(1 / 12 : ℝ)) :=
          mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hBnn _)
      _ = B ^ ((1 : ℝ) / 12 + -(1 / 12)) := by rw [← Real.rpow_add hBpos]
      _ = 1 := by rw [show (1 : ℝ) / 12 + -(1 / 12) = 0 by ring, Real.rpow_zero]
  have hAnn2 : 0 ≤ A ^ ((NN d n : ℝ) - 2 - 1 / 20) * B ^ 2 := by positivity
  have hlast : (Kc / 4) * (2 * C ^ n * K₁ + C ^ (2 * n - 1) * (K₂ + K₃) + 3 * C ^ n * K₄) * (((bigW (wOf B) : ℕ) : ℝ)) ^ (n + 1) * B ^ (-(1 / 12 : ℝ)) * A ^ ((NN d n : ℝ) - 2 - 1 / 20) * B ^ 2
      ≤ (Kc / 4) * (2 * C ^ n * K₁ + C ^ (2 * n - 1) * (K₂ + K₃) + 3 * C ^ n * K₄) * A ^ ((NN d n : ℝ) - 2 - 1 / 20) * B ^ 2 := by
    have hKnn : 0 ≤ (Kc / 4) * (2 * C ^ n * K₁ + C ^ (2 * n - 1) * (K₂ + K₃) + 3 * C ^ n * K₄) := le_of_lt hKpos
    calc (Kc / 4) * (2 * C ^ n * K₁ + C ^ (2 * n - 1) * (K₂ + K₃) + 3 * C ^ n * K₄) * (((bigW (wOf B) : ℕ) : ℝ)) ^ (n + 1) * B ^ (-(1 / 12 : ℝ)) * A ^ ((NN d n : ℝ) - 2 - 1 / 20) * B ^ 2
        = (Kc / 4) * (2 * C ^ n * K₁ + C ^ (2 * n - 1) * (K₂ + K₃) + 3 * C ^ n * K₄) * (((((bigW (wOf B) : ℕ) : ℝ)) ^ (n + 1) * B ^ (-(1 / 12 : ℝ))) * (A ^ ((NN d n : ℝ) - 2 - 1 / 20) * B ^ 2)) := by
          ring
      _ ≤ (Kc / 4) * (2 * C ^ n * K₁ + C ^ (2 * n - 1) * (K₂ + K₃) + 3 * C ^ n * K₄) * (1 * (A ^ ((NN d n : ℝ) - 2 - 1 / 20) * B ^ 2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hWB hAnn2) hKnn
      _ = (Kc / 4) * (2 * C ^ n * K₁ + C ^ (2 * n - 1) * (K₂ + K₃) + 3 * C ^ n * K₄) * A ^ ((NN d n : ℝ) - 2 - 1 / 20) * B ^ 2 := by ring
  calc Kc * (Real.log B * ((bigW (wOf B) : ℕ) : ℝ) / 4) * B * ((2 * A ^ (NN d n - 2) + A ^ (NN d n - n - 1) * C ^ (n - 1)) * S₁
            + A ^ (NN d n - n - 1) * C ^ (n - 1) * S₂
            + A ^ (NN d n - n - 2) * (1 + Real.log A) * S₃)
      ≤ Kc * (Real.log B * ((bigW (wOf B) : ℕ) : ℝ) / 4) * B * ((2 * A ^ (NN d n - 2) + A ^ (NN d n - n - 1) * C ^ (n - 1)) * (B ^ (1 + 1 / ((n : ℝ) + 1 - d)) * (1 + Real.log X) * (C * ((bigW (wOf B) : ℕ) : ℝ)) ^ n * A ^ (-(3 * (n : ℝ) / 4)))
            + A ^ (NN d n - n - 1) * C ^ (n - 1) * (B ^ (1 + (n : ℝ) / ((n : ℝ) + 1 - d)) * (1 + Real.log X) * (C * ((bigW (wOf B) : ℕ) : ℝ)) ^ n * A ^ (-(3 * (n : ℝ) / 4)))
            + A ^ (NN d n - n - 2) * (1 + Real.log A) * (B ^ (((n : ℝ) + 2) / ((n : ℝ) + 1 - d)) * (1 + Real.log X) * (C * ((bigW (wOf B) : ℕ) : ℝ)) ^ n * A ^ (-(3 * (n : ℝ) / 4)))) := mul_le_mul_of_nonneg_left hU hE
    _ = (Kc / 4) * ((bigW (wOf B) : ℕ) : ℝ) ^ (n + 1) * A ^ ((NN d n : ℝ) - 2 - 1 / 20) * B ^ 2 * (Real.log B * (1 + Real.log X)) * (2 * C ^ n * (A ^ ((1 : ℝ) / 20 - 3 * (n : ℝ) / 4) * B ^ (1 / ((n : ℝ) + 1 - d))) + C ^ (2 * n - 1) * (A ^ (-7 * (n : ℝ) / 4 + 21 / 20) * B ^ (1 / ((n : ℝ) + 1 - d))) + C ^ (2 * n - 1) * (A ^ (-7 * (n : ℝ) / 4 + 21 / 20) * B ^ ((n : ℝ) / ((n : ℝ) + 1 - d))) + C ^ n * (1 + Real.log A) * (A ^ (-7 * (n : ℝ) / 4 + 1 / 20) * B ^ (((n : ℝ) + 2) / ((n : ℝ) + 1 - d) - 1))) := hmain
    _ = (Kc / 4) * ((bigW (wOf B) : ℕ) : ℝ) ^ (n + 1) * A ^ ((NN d n : ℝ) - 2 - 1 / 20) * B ^ 2 * (Real.log B * (1 + Real.log X) * (2 * C ^ n * (A ^ ((1 : ℝ) / 20 - 3 * (n : ℝ) / 4) * B ^ (1 / ((n : ℝ) + 1 - d))) + C ^ (2 * n - 1) * (A ^ (-7 * (n : ℝ) / 4 + 21 / 20) * B ^ (1 / ((n : ℝ) + 1 - d))) + C ^ (2 * n - 1) * (A ^ (-7 * (n : ℝ) / 4 + 21 / 20) * B ^ ((n : ℝ) / ((n : ℝ) + 1 - d))) + C ^ n * (1 + Real.log A) * (A ^ (-7 * (n : ℝ) / 4 + 1 / 20) * B ^ (((n : ℝ) + 2) / ((n : ℝ) + 1 - d) - 1)))) := by ring
    _ ≤ (Kc / 4) * ((bigW (wOf B) : ℕ) : ℝ) ^ (n + 1) * A ^ ((NN d n : ℝ) - 2 - 1 / 20) * B ^ 2
          * ((2 * C ^ n * K₁ + C ^ (2 * n - 1) * (K₂ + K₃) + 3 * C ^ n * K₄) * B ^ (-(1 / 12 : ℝ))) :=
        mul_le_mul_of_nonneg_left hbr hComnn
    _ = (Kc / 4) * (2 * C ^ n * K₁ + C ^ (2 * n - 1) * (K₂ + K₃) + 3 * C ^ n * K₄) * (((bigW (wOf B) : ℕ) : ℝ)) ^ (n + 1) * B ^ (-(1 / 12 : ℝ)) * A ^ ((NN d n : ℝ) - 2 - 1 / 20) * B ^ 2 := by ring
    _ ≤ (Kc / 4) * (2 * C ^ n * K₁ + C ^ (2 * n - 1) * (K₂ + K₃) + 3 * C ^ n * K₄) * A ^ ((NN d n : ℝ) - 2 - 1 / 20) * B ^ 2 := hlast

end Work.HP.MM2
