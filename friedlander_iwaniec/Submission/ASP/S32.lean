/-
  Companion paper, §9: the **signed** assembly of (9.7).

  `S9c.Rtilde_sum_le` bounds `∑♭_{d ≤ D}|r̃_d(t)|` by the paper's `E = ∑_{ν ≤ t}∑♭_{d ≤ D}|r_{[ν²,d]}(t)|`
  *plus* the lossy term `(∑♭_{d ≤ D}|g̃(d)|)·(∑_{ν ≤ t}|r_{ν²}(t)|)`.  The second factor is NOT
  small (it is `≍ A(t)` for the Friedlander–Iwaniec sequence), so the resulting bound can never be
  `≤ Ã(x)(log x)^{−3}` as the companion's (R′) requires.

  The point is that the `g̃(d)·r_{ν²}(t)` part of `r̃_d` carries the SAME `μ(ν)` sign for every `d`,
  so the `ν`-sum can be taken *once*:
      `∑♭_d |r̃_d| ≤ ∑_{ν ≤ t, ♭}∑♭_d |r_{[ν²,d]}(t)| + (∑♭_d |g̃(d)|)·|∑_{ν ≤ t} μ(ν)·r_{ν²}(t)|`,
  and the last factor is `|FI_T|-like`, hence genuinely small (see `S30.FI_decomp`, `S29.FI_sq_*`).
-/
import Mathlib
import Submission.ASP.S31
import Submission.ASP.S9f
import Submission.ASP.S9b
import Submission.ASP.S24

set_option maxHeartbeats 3200000

namespace Submission.ASP

open Finset
open scoped ArithmeticFunction.Moebius

noncomputable section

/-- The signed assembly of `(9.7)`.  Only the last `ν`-sum is kept *inside* the absolute value. -/
theorem Rtilde_sum_le_signed (r : ℕ → ℕ → ℝ) (gtil : ℕ → ℝ) (t D : ℕ) {T : ℝ}
    (hT : |∑ ν ∈ Finset.Icc 1 t, (ArithmeticFunction.moebius ν : ℝ) * r (ν ^ 2) t| ≤ T) :
    (∑ d ∈ (Finset.Icc 1 D).filter Squarefree, |rtilde r gtil d t|)
      ≤ (∑ ν ∈ (Finset.Icc 1 t).filter Squarefree,
            ∑ d ∈ (Finset.Icc 1 D).filter Squarefree, |r (Nat.lcm (ν ^ 2) d) t|)
        + (∑ d ∈ (Finset.Icc 1 D).filter Squarefree, |gtil d|) * T := by
  classical
  have hS : (∑ ν ∈ Finset.Icc 1 t, (ArithmeticFunction.moebius ν : ℝ) * r (ν ^ 2) t)
      = ∑ ν ∈ (Finset.Icc 1 t).filter Squarefree,
          (ArithmeticFunction.moebius ν : ℝ) * r (ν ^ 2) t := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun ν _ => ?_)
    by_cases h : Squarefree ν
    · rw [if_pos h]
    · rw [if_neg h, ArithmeticFunction.moebius_eq_zero_of_not_squarefree h]
      simp
  have h4' : |∑ ν ∈ (Finset.Icc 1 t).filter Squarefree,
      (ArithmeticFunction.moebius ν : ℝ) * r (ν ^ 2) t| ≤ T := by
    rw [← hS]; exact hT
  -- pointwise: `|r̃_d| ≤ ∑_{ν,♭} |r_{[ν²,d]}| + |g̃ d|·|S|`
  have hpt : ∀ d : ℕ, |rtilde r gtil d t|
      ≤ (∑ ν ∈ (Finset.Icc 1 t).filter Squarefree, |r (Nat.lcm (ν ^ 2) d) t|)
        + |gtil d| * |∑ ν ∈ (Finset.Icc 1 t).filter Squarefree,
            (ArithmeticFunction.moebius ν : ℝ) * r (ν ^ 2) t| := by
    intro d
    have h1 : rtilde r gtil d t
        = (∑ ν ∈ (Finset.Icc 1 t).filter Squarefree,
            (ArithmeticFunction.moebius ν : ℝ) * r (Nat.lcm (ν ^ 2) d) t)
          - gtil d * (∑ ν ∈ (Finset.Icc 1 t).filter Squarefree,
              (ArithmeticFunction.moebius ν : ℝ) * r (ν ^ 2) t) := by
      rw [rtilde, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_filter]
      refine Finset.sum_congr rfl (fun ν _ => ?_)
      by_cases h : Squarefree ν
      · simp only [h, if_true]; ring
      · simp only [h, if_false]
        rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree h]
        simp
    rw [h1]
    refine le_trans (abs_sub _ _) ?_
    rw [abs_mul]
    refine add_le_add ?_ le_rfl
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum (fun ν hν => ?_)
    have hsf : Squarefree ν := (Finset.mem_filter.mp hν).2
    rw [abs_mul, ← Int.cast_abs]
    norm_num [ArithmeticFunction.abs_moebius_eq_one_of_squarefree hsf]
  -- sum over `d`
  refine le_trans (Finset.sum_le_sum (fun d _ => hpt d)) ?_
  rw [Finset.sum_add_distrib, Finset.sum_mul]
  refine add_le_add ?_ (Finset.sum_le_sum (fun d _ =>
    mul_le_mul_of_nonneg_left h4' (abs_nonneg _)))
  -- swap the `(d,ν)` sums
  rw [Finset.sum_comm]

/-- The signed assembly of `(9.7)`, with the paper's `E` split at `ν = L` into `E₁` and `E₂`. -/
theorem Rtilde_sum_le_signed_of_inputs (a g : ℕ → ℝ) (r : ℕ → ℕ → ℝ) (gtil : ℕ → ℝ)
    (t D L : ℕ) (hLt : L ≤ t) {T X1 E2 : ℝ}
    (ha : ∀ n, 0 ≤ a n) (hg : ∀ n, 0 ≤ g n) (happ : Approx a g r (t : ℝ))
    (hT : |∑ ν ∈ Finset.Icc 1 t, (ArithmeticFunction.moebius ν : ℝ) * r (ν ^ 2) t| ≤ T)
    (hE1 : Eone r t D L ≤ X1) (hE2 : Etwo a g t D L ≤ E2) :
    (∑ d ∈ (Finset.Icc 1 D).filter Squarefree, |rtilde r gtil d t|)
      ≤ X1 + E2 + (∑ d ∈ (Finset.Icc 1 D).filter Squarefree, |gtil d|) * T := by
  classical
  refine le_trans (Rtilde_sum_le_signed r gtil t D hT) ?_
  -- split the paper's `E` at `ν = L`
  have hsplit : (∑ ν ∈ (Finset.Icc 1 t).filter Squarefree,
        ∑ d ∈ (Finset.Icc 1 D).filter Squarefree, |r (Nat.lcm (ν ^ 2) d) t|)
      = Eone r t D L
        + ∑ ν ∈ (Finset.Icc (L + 1) t).filter Squarefree,
            ∑ d ∈ (Finset.Icc 1 D).filter Squarefree, |r (Nat.lcm (ν ^ 2) d) t| := by
    rw [Eone, ← Finset.sum_filter_add_sum_filter_not ((Finset.Icc 1 t).filter Squarefree)
      (fun ν => ν ≤ L)]
    congr 1
    · congr 1
      ext ν
      simp only [Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨⟨h1, -⟩, hsf⟩, h3⟩; exact ⟨⟨h1, h3⟩, hsf⟩
      · rintro ⟨⟨h1, h3⟩, hsf⟩; exact ⟨⟨⟨h1, le_trans h3 hLt⟩, hsf⟩, h3⟩
    · congr 1
      ext ν
      simp only [Finset.mem_filter, Finset.mem_Icc, not_le]
      constructor
      · rintro ⟨⟨⟨-, h2⟩, hsf⟩, h3⟩; exact ⟨⟨by omega, h2⟩, hsf⟩
      · rintro ⟨⟨h3, h2⟩, hsf⟩; exact ⟨⟨⟨by omega, h2⟩, hsf⟩, h3⟩
  rw [hsplit]
  have hE2' : (∑ ν ∈ (Finset.Icc (L + 1) t).filter Squarefree,
        ∑ d ∈ (Finset.Icc 1 D).filter Squarefree, |r (Nat.lcm (ν ^ 2) d) t|) ≤ E2 := by
    refine le_trans ?_ hE2
    rw [Etwo]
    refine Finset.sum_le_sum (fun ν _ => Finset.sum_le_sum (fun d _ => ?_))
    exact abs_r_le a g r t ha hg happ (Nat.lcm (ν ^ 2) d)
  linarith [hE1, hE2']


/-! ### A small utility: `∑_{d | n} τ(d)^K ≤ τ(n)^{K+1}` -/

/-- `∑_{d | n} τ(d)^K ≤ τ(n)^{K+1}`: `τ(d) ≤ τ(n)` for `d ∣ n`, and there are `τ(n)` divisors. -/
theorem sum_divisors_card_pow_le (K : ℕ) (n : ℕ) :
    (∑ d ∈ n.divisors, (d.divisors.card : ℕ) ^ K) ≤ (n.divisors.card) ^ (K + 1) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  calc (∑ d ∈ n.divisors, (d.divisors.card : ℕ) ^ K)
      ≤ ∑ d ∈ n.divisors, (n.divisors.card) ^ K := by
        refine Finset.sum_le_sum (fun d hd => ?_)
        exact Nat.pow_le_pow_left (card_divisors_le_of_dvd (Nat.mem_divisors.mp hd).1 hn) K
    _ = (n.divisors.card) ^ K * (n.divisors.card) := by
        rw [Finset.sum_const, nsmul_eq_mul]; push_cast; ring
    _ = (n.divisors.card) ^ (K + 1) := by rw [pow_succ]

end

end Submission.ASP
