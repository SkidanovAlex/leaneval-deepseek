import Mathlib
import Submission.Work.BMF.zeta_tsum_rpow_le
import Submission.Work.BMF.nat_mul_rpow_sub_le
import Submission.Work.BMF.sum_Icc_diff_mul_eq

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Total mass bound: `∑_p (log p) / p^{1+β} ≤ C / β`

We prove the elementary bound
`∑' p, (if p.Prime then log p / p ^ (1 + β) else 0) ≤ C / β` uniformly for `0 < β ≤ 2`.

The proof combines Chebyshev's bound `θ(x) ≤ (log 4) · x` for `θ(x) = ∑_{p ≤ x} log p`
with discrete summation by parts against the decreasing weight `n ↦ n^{-(1+β)}`:
for `M ≥ 1`,
`∑_{n=1}^{M} c n · n^{-(1+β)} = θ(M) M^{-(1+β)} - ∑_{n=1}^{M-1} θ(n) (n^{-(1+β)} - (n+1)^{-(1+β)})`,
where `c n = log n` for prime `n` and `0` otherwise. Bounding `θ(n) ≤ log 4 · n` and using
`n (n^{-s} - (n+1)^{-s}) ≤ s n^{-s}` together with the elementary bound
`∑_n n^{-s} ≤ 1 + 1/(s-1)` yields the claim.
-/

namespace Work.BMF

open Finset Real

/-- Chebyshev's `θ` at a natural number, written as a partial sum over `Finset.range`. -/
private lemma theta_eq_sum_range_aux (n : ℕ) :
    Chebyshev.theta (n : ℝ) =
      ∑ k ∈ Finset.range (n + 1), (if k.Prime then Real.log (k : ℝ) else 0) := by
  have hset : (Finset.Icc 1 n).filter Nat.Prime = (Finset.range (n + 1)).filter Nat.Prime := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
    constructor
    · rintro ⟨⟨h1, h2⟩, hp⟩; exact ⟨by omega, hp⟩
    · rintro ⟨h1, hp⟩; exact ⟨⟨hp.one_le, by omega⟩, hp⟩
  rw [Chebyshev.theta_eq_sum_primesLE_log, Nat.primesLE_eq_filter_Icc_one, hset,
    Finset.sum_filter]

/-- The backward difference of `θ` at integers is the prime indicator. -/
private lemma theta_sub_self_aux (n : ℕ) (hn : 1 ≤ n) :
    Chebyshev.theta (n : ℝ) - Chebyshev.theta ((n - 1 : ℕ) : ℝ) =
      (if n.Prime then Real.log (n : ℝ) else 0) := by
  have hn' : n - 1 + 1 = n := Nat.sub_add_cancel hn
  have h1 : Chebyshev.theta (n : ℝ) =
      ∑ k ∈ Finset.range (n + 1), (if k.Prime then Real.log (k : ℝ) else 0) :=
    theta_eq_sum_range_aux n
  have h2 : Chebyshev.theta ((n - 1 : ℕ) : ℝ) =
      ∑ k ∈ Finset.range n, (if k.Prime then Real.log (k : ℝ) else 0) := by
    rw [theta_eq_sum_range_aux (n - 1), hn']
  rw [h1, h2, Finset.sum_range_succ]
  ring

/-- For `0 < β ≤ 2` and every `M`, `∑_{p ≤ M} log p / p^{1+β} ≤ 24 / β`. -/
private lemma primeSum_log_div_rpow_le (β : ℝ) (hβ0 : 0 < β) (hβ2 : β ≤ 2) (M : ℕ) :
    (∑ p ∈ M.primesLE, Real.log (p : ℝ) / (p : ℝ) ^ (1 + β)) ≤ 24 / β := by
  rcases Nat.eq_zero_or_pos M with hM0 | hM
  · subst hM0
    have hempty : Nat.primesLE 0 = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      rw [Nat.mem_primesLE] at hp
      exact hp.2.ne_zero (Nat.eq_zero_of_le_zero hp.1)
    rw [hempty, Finset.sum_empty]
    positivity
  · set c : ℕ → ℝ := fun n => if n.Prime then Real.log (n : ℝ) else 0 with hc
    set f : ℕ → ℝ := fun n => (n : ℝ) ^ (-(1 + β)) with hf
    set a : ℕ → ℝ := fun k => Chebyshev.theta (k : ℝ) with ha
    have hlog4nn : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
    -- Step 1: the prime sum is a sum over `Icc 1 M` of `c n * f n`.
    have hstep1 : (∑ p ∈ M.primesLE, Real.log (p : ℝ) / (p : ℝ) ^ (1 + β))
        = ∑ n ∈ Finset.Icc 1 M, c n * f n := by
      rw [Nat.primesLE_eq_filter_Icc_one, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro n _
      simp only [hc, hf]
      by_cases hp : n.Prime
      · rw [if_pos hp, if_pos hp]
        rw [Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]
      · rw [if_neg hp, if_neg hp]; ring
    -- Step 2: the backward difference of `a` at `n ≥ 1` is `c n`.
    have hdiff : ∀ n, 1 ≤ n → a n - a (n - 1) = c n := by
      intro n hn
      simp only [ha, hc]
      exact theta_sub_self_aux n hn
    have hstep2 : (∑ n ∈ Finset.Icc 1 M, c n * f n)
        = ∑ n ∈ Finset.Icc 1 M, (a n - a (n - 1)) * f n := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [hdiff n (Finset.mem_Icc.mp hn).1]
    have hpb := sum_Icc_diff_mul_eq a f hM
    rw [hstep1, hstep2, hpb]
    -- Step 3: bounds on the individual pieces.
    have ha0 : a 0 = 0 := by
      simp only [ha]
      rw [theta_eq_sum_range_aux 0]
      simp
    have hAM : a M * f M ≤ Real.log 4 := by
      have hfM0 : 0 ≤ f M := by
        simp only [hf]; exact Real.rpow_nonneg (Nat.cast_nonneg M) _
      have haM : a M ≤ Real.log 4 * (M : ℝ) := by
        simp only [ha]; exact Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg M)
      have hMfm : (M : ℝ) * f M ≤ 1 := by
        have hpow : (M : ℝ) * f M = (M : ℝ) ^ (-β) := by
          simp only [hf]
          calc (M : ℝ) * (M : ℝ) ^ (-(1 + β))
              = (M : ℝ) ^ (1 : ℝ) * (M : ℝ) ^ (-(1 + β)) := by rw [Real.rpow_one]
            _ = (M : ℝ) ^ ((1 : ℝ) + -(1 + β)) := by rw [Real.rpow_add hMpos]
            _ = (M : ℝ) ^ (-β) := by congr 1; ring
        rw [hpow]
        have h := Real.rpow_le_rpow_of_exponent_le
          (show (1 : ℝ) ≤ (M : ℝ) by exact_mod_cast hM) (show -β ≤ (0 : ℝ) by linarith)
        simpa using h
      calc a M * f M ≤ (Real.log 4 * (M : ℝ)) * f M := mul_le_mul_of_nonneg_right haM hfM0
        _ = Real.log 4 * ((M : ℝ) * f M) := by ring
        _ ≤ Real.log 4 * 1 := mul_le_mul_of_nonneg_left hMfm hlog4nn
        _ = Real.log 4 := by ring
    have hneg : - (∑ n ∈ Finset.Icc 1 (M - 1), a n * (f (n + 1) - f n))
        = ∑ n ∈ Finset.Icc 1 (M - 1), a n * (f n - f (n + 1)) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro n _; ring
    have hU : (∑ n ∈ Finset.Icc 1 (M - 1), a n * (f n - f (n + 1)))
        ≤ Real.log 4 * (1 + β) * (1 + 1 / β) := by
      have hterm : ∀ n ∈ Finset.Icc 1 (M - 1),
          a n * (f n - f (n + 1)) ≤ Real.log 4 * (1 + β) * (n : ℝ) ^ (-(1 + β)) := by
        intro n hn
        have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
        have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
        have hfdec : f (n + 1) ≤ f n := by
          simp only [hf]
          push_cast
          exact Real.rpow_le_rpow_of_nonpos hnpos (by linarith) (by linarith)
        have hdnn : 0 ≤ f n - f (n + 1) := by linarith
        have han : a n ≤ Real.log 4 * (n : ℝ) := by
          simp only [ha]; exact Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg n)
        have hkey : (n : ℝ) * (f n - f (n + 1)) ≤ (1 + β) * (n : ℝ) ^ (-(1 + β)) := by
          have h := nat_mul_rpow_sub_le (1 + β) (by linarith) n
          simpa only [hf, Nat.cast_add, Nat.cast_one] using h
        calc a n * (f n - f (n + 1)) ≤ (Real.log 4 * (n : ℝ)) * (f n - f (n + 1)) :=
              mul_le_mul_of_nonneg_right han hdnn
          _ = Real.log 4 * ((n : ℝ) * (f n - f (n + 1))) := by ring
          _ ≤ Real.log 4 * ((1 + β) * (n : ℝ) ^ (-(1 + β))) :=
              mul_le_mul_of_nonneg_left hkey hlog4nn
          _ = Real.log 4 * (1 + β) * (n : ℝ) ^ (-(1 + β)) := by ring
      have hcoef : 0 ≤ Real.log 4 * (1 + β) := mul_nonneg hlog4nn (by linarith)
      calc (∑ n ∈ Finset.Icc 1 (M - 1), a n * (f n - f (n + 1)))
          ≤ ∑ n ∈ Finset.Icc 1 (M - 1), Real.log 4 * (1 + β) * (n : ℝ) ^ (-(1 + β)) :=
              Finset.sum_le_sum hterm
        _ = Real.log 4 * (1 + β) * ∑ n ∈ Finset.Icc 1 (M - 1), (n : ℝ) ^ (-(1 + β)) := by
              rw [Finset.mul_sum]
        _ ≤ Real.log 4 * (1 + β) * (1 + 1 / β) := by
              apply mul_le_mul_of_nonneg_left _ hcoef
              have hsumm : Summable (fun n : ℕ => (n : ℝ) ^ (-(1 + β))) := by
                have h2 : Summable (fun n : ℕ => ((n : ℝ) ^ (1 + β))⁻¹) :=
                  (Real.summable_nat_rpow_inv (p := 1 + β)).mpr (by linarith)
                exact h2.congr (fun n => (Real.rpow_neg (Nat.cast_nonneg n) (1 + β)).symm)
              have hle := Summable.sum_le_tsum (s := Finset.Icc 1 (M - 1))
                (fun i _ => Real.rpow_nonneg (Nat.cast_nonneg i) _) hsumm
              have hz := zeta_tsum_rpow_le (σ := 1 + β) (by linarith)
              rw [show 1 + β - 1 = β by ring] at hz
              linarith
    have hEq : a M * f M - a 0 * f 1
          - (∑ n ∈ Finset.Icc 1 (M - 1), a n * (f (n + 1) - f n))
        = a M * f M + (∑ n ∈ Finset.Icc 1 (M - 1), a n * (f n - f (n + 1))) := by
      have h1 : a 0 * f 1 = 0 := by rw [ha0]; ring
      have h2 : a M * f M - a 0 * f 1
            - (∑ n ∈ Finset.Icc 1 (M - 1), a n * (f (n + 1) - f n))
          = a M * f M + - (∑ n ∈ Finset.Icc 1 (M - 1), a n * (f (n + 1) - f n)) := by
        rw [h1]; ring
      rw [h2, hneg]
    rw [hEq]
    have hlog4lt : Real.log 4 < 2 := by
      have h4 : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
      rw [h4]
      have h2 : Real.log 2 < 1 := by
        have := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num)
        linarith
      linarith
    have hβbracket : 3 + β + 1 / β ≤ 11 / β := by
      have h1 : (3 : ℝ) + β + 1 / β ≤ 5 + 1 / β := by linarith
      have h2 : (5 : ℝ) ≤ 10 / β := by
        rw [le_div_iff₀ hβ0]; nlinarith [hβ2]
      have h3 : (5 : ℝ) + 1 / β ≤ 11 / β := by
        rw [show (11 : ℝ) / β = 10 / β + 1 / β by ring]; linarith
      linarith
    have hconst : Real.log 4 + Real.log 4 * (1 + β) * (1 + 1 / β) ≤ 24 / β := by
      have heq : Real.log 4 + Real.log 4 * (1 + β) * (1 + 1 / β)
          = Real.log 4 * (3 + β + 1 / β) := by
        field_simp; ring
      rw [heq]
      have h1 : Real.log 4 * (3 + β + 1 / β) ≤ Real.log 4 * (11 / β) :=
        mul_le_mul_of_nonneg_left hβbracket hlog4nn
      have h2 : Real.log 4 * (11 / β) ≤ 2 * (11 / β) :=
        mul_le_mul_of_nonneg_right hlog4lt.le (by positivity)
      have h3 : 2 * (11 / β) ≤ 24 / β := by
        rw [show 2 * (11 / β) = 22 / β by ring]
        rw [div_le_div_iff_of_pos_right hβ0]; norm_num
      linarith
    linarith [hAM, hU, hconst]

theorem Psi1_L2_total_mass :
    ∃ C : ℝ, 0 < C ∧ ∀ (β : ℝ), 0 < β → β ≤ 2 →
      (∑' p : ℕ, (if p.Prime then Real.log p / (p : ℝ) ^ (1 + β) else 0)) ≤ C / β := by
  refine ⟨24, by norm_num, ?_⟩
  intro β hβ0 hβ2
  refine Real.tsum_le_of_sum_range_le (fun n => ?_) (fun N => ?_)
  · by_cases h : n.Prime
    · rw [if_pos h]
      exact div_nonneg (Real.log_nonneg (by exact_mod_cast h.one_le))
        (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    · rw [if_neg h]
  · have h1 : (∑ i ∈ Finset.range N,
          (if i.Prime then Real.log i / (i : ℝ) ^ (1 + β) else 0))
        = ∑ i ∈ (Finset.range N).filter Nat.Prime, Real.log i / (i : ℝ) ^ (1 + β) := by
      rw [Finset.sum_filter]
    rw [h1]
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_)
      (primeSum_log_div_rpow_le β hβ0 hβ2 N)
    · intro p hp
      rw [Finset.mem_filter, Finset.mem_range] at hp
      rw [Nat.mem_primesLE]
      exact ⟨le_of_lt hp.1, hp.2⟩
    · intro p hp _
      exact div_nonneg
        (Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_le))
        (Real.rpow_nonneg (Nat.cast_nonneg p) _)

end Work.BMF
