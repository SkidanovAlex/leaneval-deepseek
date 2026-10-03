import Mathlib
import Submission.Work.FIArea7.Classical172Defs
import Submission.Commons.NumberTheory.ArithmeticFunction.sum_tau_pow_div_le_logpow_explicit
import Submission.Commons.NumberTheory.DivisorBound.card_divisors_le_rpow
import Submission.Commons.NumberTheory.FriedlanderIwaniec.tau_le_nine_sum_divisors_cube

namespace Work.FIArea7

/-- Pointwise estimate for the inner `m`-sum of the second Vaughan term `S₂`, from
Proposition 23.2 (`Prop232`, the `L(N)` half) applied with `m := c·(a·b)` and `N := ⌊N/(ab)⌋`:
the sum `∑_{n ≤ ⌊N/(ab)⌋} λ(c·(ab)·n)` is at most
`C d (|k|+1) τ(c)^4 τ(a)^4 τ(b)^4 √c N^{3/4} a^{-1/4} b^{-1/4} log(cN+2)`, using
`τ(cab) ≤ τ(c)τ(a)τ(b)` (`Commons.NumberTheory.FriedlanderIwaniec.card_divisors_mul_le`, imported by
`Submission.Work.FIArea7.S2Imports`) and `√(ab)·(N/(ab))^{3/4} = N^{3/4} a^{-1/4} b^{-1/4}`. -/
theorem t2psi_S2_inner_le (h32 : Work.FIArea7.Prop232) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N cc d : ℕ) (k : ℤ) (chi : GaussianInt → ℂ) (a b : ℕ),
        1 ≤ N → 1 ≤ cc → 1 ≤ d → 1 ≤ a → 1 ≤ b → a * b ≤ N →
        (∀ z, ‖chi z‖ ≤ 1) →
        (∀ z1 z2 : GaussianInt, IsCoprime z1 z2 → chi (z1 * z2) = chi z1 * chi z2) →
        (∀ (x y : ℤ), chi (⟨x + 4 * (d : ℤ), y⟩ : GaussianInt) = chi ⟨x, y⟩) →
        (∀ (x y : ℤ), chi (⟨x, y + 4 * (d : ℤ)⟩ : GaussianInt) = chi ⟨x, y⟩) →
        ‖∑ m ∈ Finset.Icc 1 (N / (a * b)),
            Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) (cc * ((a * b) * m))‖
          ≤ C * (d : ℝ) * (|(k : ℝ)| + 1) * (((cc.divisors.card : ℕ) : ℝ)) ^ 4 * Real.sqrt cc
              * (N : ℝ) ^ ((3:ℝ)/4) * Real.log ((cc : ℝ) * (N : ℝ) + 2)
              * ((((a.divisors.card : ℕ) : ℝ)) ^ 4 * (a : ℝ) ^ (-(1:ℝ)/4))
              * ((((b.divisors.card : ℕ) : ℝ)) ^ 4 * (b : ℝ) ^ (-(1:ℝ)/4)) := by
  rcases h32 with ⟨C32, hC32, h32b⟩
  refine ⟨C32, hC32, ?_⟩
  intro N cc d k chi a b hN hcc hd ha hb hab hchi_bd hchi_mul hper1 hper2
  have hm1 : 1 ≤ cc * (a*b) := by
    have : 0 < cc * (a*b) := by positivity
    omega
  have hN1 : 1 ≤ N / (a*b) := Nat.div_pos hab (by positivity)
  -- the inner `m`-sum is `LLinear` at `m := cc*(a*b)`, `N := ⌊N/(ab)⌋`
  have hLHS : (∑ m ∈ Finset.Icc 1 (N / (a * b)),
        Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) (cc * ((a * b) * m)))
      = Work.FIArea7.LLinear (cc * (a*b)) (N / (a*b)) (Work.FIArea7.grossenChar chi k) := by
    rw [Work.FIArea7.LLinear]
    refine Finset.sum_congr rfl fun m hm => ?_
    congr 1
    ring
  rw [hLHS]
  -- Proposition 23.2, `L(N)` half
  have hle := (h32b (N/(a*b)) (cc*(a*b)) d k chi hm1 hd hN1 hchi_bd hchi_mul hper1 hper2).1
  refine le_trans hle ?_
  have habpos : (0:ℝ) < (((a*b : ℕ)) : ℝ) := by positivity
  have hNnn : (0:ℝ) ≤ (N:ℝ) := by positivity
  have hL1nn : (0:ℝ) ≤ Real.log ((((cc*(a*b) : ℕ)) : ℝ) * ((N/(a*b) : ℕ) : ℝ) + 2) :=
    Real.log_nonneg (by
      have : (0:ℝ) ≤ (((cc*(a*b) : ℕ)) : ℝ) * ((N/(a*b) : ℕ) : ℝ) := by positivity
      linarith)
  -- `τ(c·(ab))^4 ≤ τ(c)^4 τ(a)^4 τ(b)^4`
  have hτ : ((((cc*(a*b)).divisors.card : ℕ) : ℝ)) ^ 4
      ≤ (((cc.divisors.card : ℕ) : ℝ)) ^ 4 * (((a.divisors.card : ℕ) : ℝ)) ^ 4
        * (((b.divisors.card : ℕ) : ℝ)) ^ 4 := by
    have h1 := Commons.NumberTheory.FriedlanderIwaniec.card_divisors_mul_le cc (a*b)
    have h2 := Commons.NumberTheory.FriedlanderIwaniec.card_divisors_mul_le a b
    have h1r : ((((cc*(a*b)).divisors.card : ℕ) : ℝ))
        ≤ ((cc.divisors.card : ℕ) : ℝ) * (((a*b).divisors.card : ℕ) : ℝ) := by
      exact_mod_cast h1
    have h2r : ((((a*b).divisors.card : ℕ) : ℝ))
        ≤ ((a.divisors.card : ℕ) : ℝ) * ((b.divisors.card : ℕ) : ℝ) := by
      exact_mod_cast h2
    have hT : ((((cc*(a*b)).divisors.card : ℕ) : ℝ))
        ≤ ((cc.divisors.card : ℕ) : ℝ) * ((a.divisors.card : ℕ) : ℝ)
          * ((b.divisors.card : ℕ) : ℝ) := by
      calc ((((cc*(a*b)).divisors.card : ℕ) : ℝ))
          ≤ ((cc.divisors.card : ℕ) : ℝ) * (((a*b).divisors.card : ℕ) : ℝ) := h1r
        _ ≤ ((cc.divisors.card : ℕ) : ℝ)
              * (((a.divisors.card : ℕ) : ℝ) * ((b.divisors.card : ℕ) : ℝ)) := by
            exact mul_le_mul_of_nonneg_left h2r (by positivity)
        _ = _ := by ring
    calc ((((cc*(a*b)).divisors.card : ℕ) : ℝ)) ^ 4
        ≤ (((cc.divisors.card : ℕ) : ℝ) * ((a.divisors.card : ℕ) : ℝ)
            * ((b.divisors.card : ℕ) : ℝ)) ^ 4 :=
          pow_le_pow_left₀ (by positivity) hT 4
      _ = _ := by ring
  -- `√(c·(ab)) = √c·√(ab)`
  have hS : Real.sqrt (((cc*(a*b) : ℕ)) : ℝ)
      = Real.sqrt (cc:ℝ) * Real.sqrt (((a*b:ℕ)):ℝ) := by
    rw [Nat.cast_mul, Real.sqrt_mul (by positivity)]
  -- `√(ab)·⌊N/(ab)⌋^{3/4} ≤ N^{3/4} a^{-1/4} b^{-1/4}`
  have hkey : Real.sqrt (((a*b:ℕ)):ℝ) * ((N/(a*b) : ℕ) : ℝ) ^ ((3:ℝ)/4)
      ≤ (N:ℝ) ^ ((3:ℝ)/4) * (a:ℝ) ^ (-(1:ℝ)/4) * (b:ℝ) ^ (-(1:ℝ)/4) := by
    have hNr : ((N/(a*b) : ℕ) : ℝ) ≤ (N:ℝ)/(((a*b : ℕ)):ℝ) := Nat.cast_div_le
    have hrpow : ((N/(a*b) : ℕ) : ℝ) ^ ((3:ℝ)/4) ≤ ((N:ℝ)/(((a*b : ℕ)):ℝ)) ^ ((3:ℝ)/4) :=
      Real.rpow_le_rpow (by positivity) hNr (by norm_num)
    calc Real.sqrt (((a*b:ℕ)):ℝ) * ((N/(a*b) : ℕ) : ℝ) ^ ((3:ℝ)/4)
        ≤ Real.sqrt (((a*b:ℕ)):ℝ) * ((N:ℝ)/(((a*b : ℕ)):ℝ)) ^ ((3:ℝ)/4) :=
          mul_le_mul_of_nonneg_left hrpow (Real.sqrt_nonneg _)
      _ = (N:ℝ) ^ ((3:ℝ)/4) * (((a*b : ℕ)) : ℝ) ^ (-(1:ℝ)/4) := by
          rw [Real.sqrt_eq_rpow, Real.div_rpow hNnn (le_of_lt habpos)]
          rw [show (-(1:ℝ)/4 : ℝ) = (1:ℝ)/2 - (3:ℝ)/4 by norm_num, Real.rpow_sub habpos]
          ring
      _ = (N : ℝ) ^ ((3:ℝ)/4) * (a : ℝ) ^ (-(1:ℝ)/4) * (b : ℝ) ^ (-(1:ℝ)/4) := by
          rw [Nat.cast_mul, Real.mul_rpow (by positivity) (by positivity), mul_assoc]
  -- `log(c(ab)⌊N/(ab)⌋ + 2) ≤ log(cN + 2)`
  have hlog : Real.log ((((cc*(a*b) : ℕ)) : ℝ) * ((N/(a*b) : ℕ) : ℝ) + 2)
      ≤ Real.log ((cc : ℝ) * (N : ℝ) + 2) := by
    have hNr : ((N/(a*b) : ℕ) : ℝ) ≤ (N:ℝ)/(((a*b : ℕ)):ℝ) := Nat.cast_div_le
    have hmul : (((cc*(a*b) : ℕ)) : ℝ) * ((N/(a*b) : ℕ) : ℝ) ≤ (cc:ℝ)*(N:ℝ) := by
      rw [Nat.cast_mul]
      calc (cc:ℝ) * (((a*b:ℕ)):ℝ) * ((N/(a*b):ℕ):ℝ)
          ≤ (cc:ℝ) * (((a*b:ℕ)):ℝ) * ((N:ℝ)/(((a*b:ℕ)):ℝ)) := by
            apply mul_le_mul_of_nonneg_left hNr
            positivity
        _ = (cc:ℝ)*(N:ℝ) := by field_simp
    exact Real.log_le_log (by positivity) (by linarith)
  rw [hS]
  -- assemble
  calc C32 * (d : ℝ) * (|(k : ℝ)| + 1) * ((((cc*(a*b)).divisors.card : ℕ) : ℝ)) ^ 4
        * (Real.sqrt (cc:ℝ) * Real.sqrt (((a*b:ℕ)):ℝ))
        * ((N/(a*b) : ℕ) : ℝ) ^ ((3:ℝ)/4)
        * Real.log ((((cc*(a*b) : ℕ)) : ℝ) * ((N/(a*b) : ℕ) : ℝ) + 2)
      = (C32 * (d:ℝ) * (|(k:ℝ)|+1))
        * ((((((cc*(a*b)).divisors.card : ℕ) : ℝ)) ^ 4)
            * (Real.sqrt (cc:ℝ) * (Real.sqrt (((a*b:ℕ)):ℝ)
              * ((N/(a*b) : ℕ) : ℝ) ^ ((3:ℝ)/4))))
        * Real.log ((((cc*(a*b) : ℕ)) : ℝ) * ((N/(a*b) : ℕ) : ℝ) + 2) := by ring
    _ ≤ (C32 * (d:ℝ) * (|(k:ℝ)|+1))
        * (((((cc.divisors.card : ℕ) : ℝ)) ^ 4 * (((a.divisors.card : ℕ) : ℝ)) ^ 4
            * (((b.divisors.card : ℕ) : ℝ)) ^ 4)
          * (Real.sqrt (cc:ℝ) * (((N:ℝ) ^ ((3:ℝ)/4) * (a:ℝ) ^ (-(1:ℝ)/4)
              * (b:ℝ) ^ (-(1:ℝ)/4)))))
        * Real.log ((cc : ℝ) * (N : ℝ) + 2) := by
          gcongr
    _ = C32 * (d : ℝ) * (|(k : ℝ)| + 1) * (((cc.divisors.card : ℕ) : ℝ)) ^ 4 * Real.sqrt cc
          * (N : ℝ) ^ ((3:ℝ)/4) * Real.log ((cc : ℝ) * (N : ℝ) + 2)
          * ((((a.divisors.card : ℕ) : ℝ)) ^ 4 * (a : ℝ) ^ (-(1:ℝ)/4))
          * ((((b.divisors.card : ℕ) : ℝ)) ^ 4 * (b : ℝ) ^ (-(1:ℝ)/4)) := by ring

end Work.FIArea7
