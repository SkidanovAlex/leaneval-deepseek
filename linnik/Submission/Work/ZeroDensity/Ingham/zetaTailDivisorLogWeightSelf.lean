import Mathlib
import Submission.Work.ZeroDensity.Ingham.divisorSqSummatory
import Submission.Work.ZeroDensity.Ingham.tauSqLogWeightedSummatory
import Submission.Work.ZeroDensity.Ingham.zetaTailTermLogWeightSelf

namespace Work.ZeroDensity.Ingham

open scoped BigOperators

/-- For `x ≥ 2`, `1 ≤ log (2x)`.  (Small utility for absorbing logarithmic powers by raising the
power of `log (2·)`.) -/
private lemma one_le_log_two_mul {x : ℝ} (hx : 2 ≤ x) : 1 ≤ Real.log (2 * x) := by
  have h4 : Real.log 4 ≤ Real.log (2 * x) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    ring
  rw [hlog4] at h4
  have := Real.log_two_gt_d9
  linarith

/-- Absorption of logarithmic powers: for `a, b ≥ 1`, `X, W ≥ 0`, `C ≥ 0`,
`C a⁷ (X + W b⁸) ≤ C a¹² b¹² (X + W)`. -/
private lemma absorbLogPowers (a b X W C : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hX : 0 ≤ X) (hW : 0 ≤ W) (hC : 0 ≤ C) :
    C * a ^ 7 * (X + W * b ^ 8) ≤ C * a ^ 12 * b ^ 12 * (X + W) := by
  have hb1 : (1 : ℝ) ≤ b ^ 8 := one_le_pow₀ hb
  have ha7 : a ^ 7 ≤ a ^ 12 := pow_le_pow_right₀ ha (by norm_num)
  have hb8 : b ^ 8 ≤ b ^ 12 := pow_le_pow_right₀ hb (by norm_num)
  have ha7nn : 0 ≤ a ^ 7 := pow_nonneg (by linarith) 7
  have ha12nn : 0 ≤ a ^ 12 := pow_nonneg (by linarith) 12
  have hb8nn : 0 ≤ b ^ 8 := pow_nonneg (by linarith) 8
  have hXW : 0 ≤ X + W := by linarith
  have h3 : X + W * b ^ 8 ≤ b ^ 8 * (X + W) := by
    have h1 : 0 ≤ X * (b ^ 8 - 1) := mul_nonneg hX (by linarith)
    nlinarith [h1, hb8nn, hX, hW]
  have h2 : a ^ 7 * b ^ 8 ≤ a ^ 12 * b ^ 12 := mul_le_mul ha7 hb8 hb8nn ha12nn
  calc C * a ^ 7 * (X + W * b ^ 8)
      = C * (a ^ 7 * (X + W * b ^ 8)) := by ring
    _ ≤ C * (a ^ 7 * (b ^ 8 * (X + W))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 ha7nn) hC
    _ = C * ((a ^ 7 * b ^ 8) * (X + W)) := by ring
    _ ≤ C * ((a ^ 12 * b ^ 12) * (X + W)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 hXW) hC
    _ = C * a ^ 12 * b ^ 12 * (X + W) := by ring

/-- Weighted divisor-tail estimate for the zero-detector tail, with the log-cubed weight and cutoff `Y (log (B H))^4`: for all `1 ≤ K`, `1/2 ≤ σ ≤ 1`, `1 ≤ Y`, `2 ≤ H`, `1 ≤ B` and `L` with `L ≤ Y (log (B H))^4`, `Σ_{K < n ≤ L} τ(n)² e^{-2n/Y} n^{-2σ} (H + n) (1 + log n)^3 ≤ C (log 2L)^12 (log (2BH))^12 (H K^{1-2σ} + Y^{2-2σ})`, where `τ(n) = (Nat.divisors n).card` and `C` is absolute. It should be derived from the proved `Work.ZeroDensity.Ingham.divisorSqSummatory` (`Σ_{n≤N} τ(n)² ≤ C N (log 2N)^3`): for the `H`-part use `n^{-2σ} = n^{-1} n^{-(2σ-1)} ≤ n^{-1} K^{1-2σ}` and for the `n`-part `n^{1-2σ} = n^{-1} n^{2-2σ} ≤ n^{-1} L^{2-2σ} ≤ n^{-1} Y^{2-2σ} (log (BH))^8`, both reducing to `Σ_{n ≤ L} τ(n)² n^{-1} (1 + log n)^3 ≪ (log 2L)^A` (drop the damping, then dyadic splitting or Abel summation). This is the `(1+log n)^3`-weighted variant of the unproved node `Work.ZeroDensity.Ingham.divisorTailBound`, which must not be used. -/
theorem zetaTailDivisorLogWeightSelf : ∃ C : ℝ, 0 < C ∧ ∀ (K L : ℕ) (σ Y H B : ℝ),
    1 ≤ K → 1 / 2 ≤ σ → σ ≤ 1 → 1 ≤ Y → 2 ≤ H → 1 ≤ B → (L : ℝ) ≤ Y * (Real.log (B * H)) ^ 4 →
    (∑ n ∈ Finset.Ioc K L, ((Nat.divisors n).card : ℝ) ^ 2 * Real.exp (-(2 * (n : ℝ) / Y))
        * (n : ℝ) ^ (-(2 * σ)) * (H + (n : ℝ)) * (1 + Real.log (n : ℝ)) ^ 3)
      ≤ C * (Real.log (2 * (L : ℝ))) ^ 12 * (Real.log (2 * (B * H))) ^ 12
          * (H * (K : ℝ) ^ (1 - 2 * σ) + Y ^ (2 - 2 * σ)) := by
  rcases tauSqLogWeightedSummatory with ⟨C₁, hC₁pos, hC₁⟩
  refine ⟨C₁, hC₁pos, ?_⟩
  intro K L σ Y H B hK hσ1 hσ2 hY hH hB hL
  by_cases hLK : L ≤ K
  · -- the sum is empty
    have hempty : Finset.Ioc K L = ∅ := Finset.Ioc_eq_empty_iff.mpr (by omega)
    rw [hempty, Finset.sum_empty]
    have hlog1 : (0 : ℝ) ≤ (Real.log (2 * (L : ℝ))) ^ 12 := by positivity
    have hlog2 : (0 : ℝ) ≤ (Real.log (2 * (B * H))) ^ 12 := by positivity
    have hX : (0 : ℝ) ≤ H * (K : ℝ) ^ (1 - 2 * σ) :=
      mul_nonneg (by linarith) (Real.rpow_nonneg (Nat.cast_nonneg K) _)
    have hW : (0 : ℝ) ≤ Y ^ (2 - 2 * σ) := Real.rpow_nonneg (by linarith) _
    have hnn : (0 : ℝ) ≤ C₁ * (Real.log (2 * (L : ℝ))) ^ 12 * (Real.log (2 * (B * H))) ^ 12
        * (H * (K : ℝ) ^ (1 - 2 * σ) + Y ^ (2 - 2 * σ)) :=
      mul_nonneg (mul_nonneg (mul_nonneg (le_of_lt hC₁pos) hlog1) hlog2) (add_nonneg hX hW)
    linarith
  · have hKL : K < L := Nat.not_le.mp hLK
    -- `K < L`
    have hL1 : 1 ≤ L := by omega
    have hL2 : 2 ≤ L := by omega
    have hBH2 : (2 : ℝ) ≤ B * H := by nlinarith
    have ha : 1 ≤ Real.log (2 * (L : ℝ)) :=
      one_le_log_two_mul (by exact_mod_cast hL2)
    have hb : 1 ≤ Real.log (2 * (B * H)) := one_le_log_two_mul hBH2
    have hXnn : (0 : ℝ) ≤ H * (K : ℝ) ^ (1 - 2 * σ) :=
      mul_nonneg (by linarith) (Real.rpow_nonneg (Nat.cast_nonneg K) _)
    have hWnn : (0 : ℝ) ≤ Y ^ (2 - 2 * σ) := Real.rpow_nonneg (by linarith) _
    have hBnn : (0 : ℝ) ≤ H * (K : ℝ) ^ (1 - 2 * σ)
        + Y ^ (2 - 2 * σ) * (Real.log (2 * (B * H))) ^ 8 :=
      add_nonneg hXnn (mul_nonneg hWnn (pow_nonneg (by linarith) 8))
    -- termwise bound
    have hterm : ∀ n ∈ Finset.Ioc K L,
        ((Nat.divisors n).card : ℝ) ^ 2 * Real.exp (-(2 * (n : ℝ) / Y)) * (n : ℝ) ^ (-(2 * σ))
          * (H + (n : ℝ)) * (1 + Real.log (n : ℝ)) ^ 3
        ≤ ((Nat.divisors n).card : ℝ) ^ 2 * (1 + Real.log (n : ℝ)) ^ 3 * ((n : ℝ))⁻¹
          * (H * (K : ℝ) ^ (1 - 2 * σ)
            + Y ^ (2 - 2 * σ) * (Real.log (2 * (B * H))) ^ 8) :=
      fun n hn => zetaTailTermLogWeightSelf K L σ Y H B n hK hσ1 hσ2 hY hH hB hL hn
    -- the weighted summatory bound on the range `(K, L]`
    have hW'nn : ∀ n ∈ Finset.Icc 1 L,
        (0 : ℝ) ≤ ((Nat.divisors n).card : ℝ) ^ 2 * (1 + Real.log (n : ℝ)) ^ 3 * ((n : ℝ))⁻¹ := by
      intro n hn
      rw [Finset.mem_Icc] at hn
      have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
      have hlog : (0 : ℝ) ≤ 1 + Real.log (n : ℝ) := by
        have := Real.log_nonneg (by exact_mod_cast hn.1 : (1 : ℝ) ≤ (n : ℝ))
        linarith
      exact mul_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg hlog 3)) (inv_nonneg.mpr hnpos.le)
    have hsub : Finset.Ioc K L ⊆ Finset.Icc 1 L := by
      intro n hn
      rw [Finset.mem_Ioc] at hn
      rw [Finset.mem_Icc]
      omega
    have hsumW : ∑ n ∈ Finset.Ioc K L,
          ((Nat.divisors n).card : ℝ) ^ 2 * (1 + Real.log (n : ℝ)) ^ 3 * ((n : ℝ))⁻¹
        ≤ C₁ * (Real.log (2 * (L : ℝ))) ^ 7 :=
      (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i hi _ => hW'nn i hi)).trans (hC₁ L hL1)
    calc ∑ n ∈ Finset.Ioc K L, ((Nat.divisors n).card : ℝ) ^ 2 * Real.exp (-(2 * (n : ℝ) / Y))
            * (n : ℝ) ^ (-(2 * σ)) * (H + (n : ℝ)) * (1 + Real.log (n : ℝ)) ^ 3
        ≤ ∑ n ∈ Finset.Ioc K L,
            (((Nat.divisors n).card : ℝ) ^ 2 * (1 + Real.log (n : ℝ)) ^ 3 * ((n : ℝ))⁻¹)
              * (H * (K : ℝ) ^ (1 - 2 * σ)
                + Y ^ (2 - 2 * σ) * (Real.log (2 * (B * H))) ^ 8) :=
          Finset.sum_le_sum hterm
      _ = (∑ n ∈ Finset.Ioc K L,
            ((Nat.divisors n).card : ℝ) ^ 2 * (1 + Real.log (n : ℝ)) ^ 3 * ((n : ℝ))⁻¹)
              * (H * (K : ℝ) ^ (1 - 2 * σ)
                + Y ^ (2 - 2 * σ) * (Real.log (2 * (B * H))) ^ 8) := by
          rw [Finset.sum_mul]
      _ ≤ (C₁ * (Real.log (2 * (L : ℝ))) ^ 7)
              * (H * (K : ℝ) ^ (1 - 2 * σ)
                + Y ^ (2 - 2 * σ) * (Real.log (2 * (B * H))) ^ 8) :=
          mul_le_mul_of_nonneg_right hsumW hBnn
      _ ≤ C₁ * (Real.log (2 * (L : ℝ))) ^ 12 * (Real.log (2 * (B * H))) ^ 12
            * (H * (K : ℝ) ^ (1 - 2 * σ) + Y ^ (2 - 2 * σ)) :=
          absorbLogPowers _ _ _ _ C₁ ha hb hXnn hWnn (le_of_lt hC₁pos)

end Work.ZeroDensity.Ingham
