import Mathlib
import Submission.Commons.NumberTheory.Chebyshev.theta_le_log3_mul
import Submission.Commons.NumberTheory.Chebyshev.psi_sub_theta_le_three_sqrt

namespace Work.FIArea4

open Finset

/-- The sum of `log p` over the primes in the dyadic window `(P, 2P]` is the difference
`θ(2P) - θ(P)` of Chebyshev's `θ`-function. -/
lemma sum_window_log_eq_theta_sub (P : ℕ) :
    ∑ p ∈ (Finset.Ioc P (2 * P)).filter Nat.Prime, Real.log (p : ℝ)
      = Chebyshev.theta (2 * P : ℝ) - Chebyshev.theta (P : ℝ) := by
  have hsplit : (Finset.Icc 0 (2 * P)).filter Nat.Prime
      = (Finset.Icc 0 P).filter Nat.Prime ∪ (Finset.Ioc P (2 * P)).filter Nat.Prime := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨h0, h2P⟩, hp⟩
      by_cases h : p ≤ P
      · exact Or.inl ⟨⟨h0, h⟩, hp⟩
      · exact Or.inr ⟨⟨by omega, h2P⟩, hp⟩
    · rintro (⟨⟨h0, hP'⟩, hp⟩ | ⟨⟨hP', h2P⟩, hp⟩)
      · exact ⟨⟨h0, by omega⟩, hp⟩
      · exact ⟨⟨by omega, h2P⟩, hp⟩
  have hdisj : Disjoint ((Finset.Icc 0 P).filter Nat.Prime)
      ((Finset.Ioc P (2 * P)).filter Nat.Prime) := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc] at hp1 hp2
    omega
  have hsd := Finset.sum_union hdisj (f := fun p : ℕ => Real.log (p : ℝ))
  rw [← hsplit] at hsd
  have hcast : ((2 * P : ℕ) : ℝ) = 2 * (P : ℝ) := by push_cast; ring
  have hθ2 : Chebyshev.theta (2 * (P : ℝ))
      = ∑ p ∈ (Finset.Icc 0 (2 * P)).filter Nat.Prime, Real.log (p : ℝ) := by
    have h := Chebyshev.theta_eq_sum_primesLE_log (2 * P)
    rw [Nat.primesLE_eq_filter_Icc_zero, hcast] at h
    exact h
  have hθP : Chebyshev.theta ((P : ℕ) : ℝ)
      = ∑ p ∈ (Finset.Icc 0 P).filter Nat.Prime, Real.log (p : ℝ) := by
    have h := Chebyshev.theta_eq_sum_primesLE_log P
    rw [Nat.primesLE_eq_filter_Icc_zero] at h
    exact h
  rw [hθ2, hθP]
  linarith

/-- Each summand `log p / p` over the window `(P, 2P]` dominates `log p / (2P)`, so the
weighted sum dominates `(θ(2P) - θ(P)) / (2P)`. -/
lemma window_sum_div_ge (P : ℕ) :
    (∑ p ∈ (Finset.Ioc P (2 * P)).filter Nat.Prime, Real.log (p : ℝ)) / (2 * (P : ℝ))
      ≤ ∑ p ∈ (Finset.Ioc P (2 * P)).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ) := by
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_Ioc] at hp
  obtain ⟨⟨hPp, hp2P⟩, hprime⟩ := hp
  have hp_pos : (0 : ℝ) < (p : ℝ) := by
    have : 0 < p := hprime.pos
    exact_mod_cast this
  have hPpR : (P : ℝ) < (p : ℝ) := by exact_mod_cast hPp
  have hp2PR : (p : ℝ) ≤ 2 * (P : ℝ) := by exact_mod_cast hp2P
  have hPpos : (0 : ℝ) < (P : ℝ) := by linarith
  have h2P_pos : (0 : ℝ) < 2 * (P : ℝ) := by linarith
  have hp1R : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hprime.one_lt.le
  have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg hp1R
  rw [div_le_div_iff₀ h2P_pos hp_pos]
  exact mul_le_mul_of_nonneg_left hp2PR hlog

/-- Numerical bound: for `P ≥ 10^6` the lower-order terms in the Chebyshev estimate are
dominated by `P·(7/4 log 2 - log 3)`, which is `P·(2 log 2 - log 3 - log 2 / 4)`. -/
private lemma large_P_bound (P : ℕ) (hP : 1000000 ≤ P) :
    (2 : ℝ) * (P : ℝ) * Real.log 2 - Real.log (2 * (P : ℝ) + 1)
        - 3 * Real.sqrt (2 * (P : ℝ)) - (P : ℝ) * Real.log 3
      ≥ (2 : ℝ) * (P : ℝ) * (Real.log 2 / 8) := by
  have ha : (1 / 10 : ℝ) ≤ 7 / 4 * Real.log 2 - Real.log 3 := by
    linarith [Real.log_two_gt_d9, Real.log_three_lt_d9]
  have hx : (1000000 : ℝ) ≤ (P : ℝ) := by exact_mod_cast hP
  have hx0 : (0 : ℝ) < (P : ℝ) := by linarith
  have hsqrtx : (1000 : ℝ) ≤ Real.sqrt (P : ℝ) := by
    apply Real.le_sqrt_of_sq_le
    have : ((1000 : ℝ)) ^ 2 = 1000000 := by norm_num
    rw [this]; exact hx
  -- bound the logarithmic term by a square root
  have hlog_le : Real.log (2 * (P : ℝ) + 1) ≤ 2 * Real.sqrt (2 * (P : ℝ) + 1) := by
    have h := Real.log_le_rpow_div (show (0 : ℝ) ≤ 2 * (P : ℝ) + 1 by positivity)
      (show (0 : ℝ) < (1 / 2 : ℝ) by norm_num)
    have hrw : ((2 * (P : ℝ) + 1) ^ (1 / 2 : ℝ)) / (1 / 2)
        = 2 * Real.sqrt (2 * (P : ℝ) + 1) := by
      rw [Real.sqrt_eq_rpow]; ring
    rwa [hrw] at h
  have h1 : Real.sqrt (2 * (P : ℝ) + 1) ≤ Real.sqrt (3 * (P : ℝ)) := by
    apply Real.sqrt_le_sqrt; linarith
  have h2 : Real.sqrt (3 * (P : ℝ)) = Real.sqrt 3 * Real.sqrt (P : ℝ) := by
    rw [Real.sqrt_mul (show (0 : ℝ) ≤ 3 by norm_num)]
  have h3 : Real.sqrt (2 * (P : ℝ)) ≤ Real.sqrt (3 * (P : ℝ)) := by
    apply Real.sqrt_le_sqrt; linarith
  have hbound : Real.log (2 * (P : ℝ) + 1) + 3 * Real.sqrt (2 * (P : ℝ))
      ≤ 5 * Real.sqrt 3 * Real.sqrt (P : ℝ) := by
    calc Real.log (2 * (P : ℝ) + 1) + 3 * Real.sqrt (2 * (P : ℝ))
        ≤ 2 * Real.sqrt (3 * (P : ℝ)) + 3 * Real.sqrt (3 * (P : ℝ)) := by
          linarith [hlog_le, h1, h3]
      _ = 5 * Real.sqrt (3 * (P : ℝ)) := by ring
      _ = 5 * (Real.sqrt 3 * Real.sqrt (P : ℝ)) := by rw [h2]
      _ = 5 * Real.sqrt 3 * Real.sqrt (P : ℝ) := by ring
  have hs3 : 5 * Real.sqrt 3 ≤ 100 := by
    have : Real.sqrt 3 ≤ 20 := by rw [Real.sqrt_le_iff]; norm_num
    linarith
  have hsqrt_sq : Real.sqrt (P : ℝ) * Real.sqrt (P : ℝ) = (P : ℝ) := by
    rw [← sq]; exact Real.sq_sqrt hx0.le
  have hfinal : 5 * Real.sqrt 3 * Real.sqrt (P : ℝ) ≤ (1 / 10) * (P : ℝ) := by
    have hstep : 5 * Real.sqrt 3 ≤ (1 / 10) * Real.sqrt (P : ℝ) := by
      linarith [hs3, hsqrtx]
    have hxnn : 0 ≤ Real.sqrt (P : ℝ) := Real.sqrt_nonneg _
    calc 5 * Real.sqrt 3 * Real.sqrt (P : ℝ)
        ≤ ((1 / 10) * Real.sqrt (P : ℝ)) * Real.sqrt (P : ℝ) :=
          mul_le_mul_of_nonneg_right hstep hxnn
      _ = (1 / 10) * (Real.sqrt (P : ℝ) * Real.sqrt (P : ℝ)) := by ring
      _ = (1 / 10) * (P : ℝ) := by rw [hsqrt_sq]
  have hmain : Real.log (2 * (P : ℝ) + 1) + 3 * Real.sqrt (2 * (P : ℝ))
      ≤ (7 / 4 * Real.log 2 - Real.log 3) * (P : ℝ) :=
    le_trans hbound (le_trans hfinal (mul_le_mul_of_nonneg_right ha hx0.le))
  linarith [hmain]

/-- The weighted prime sum over a dyadic window, uniform in `P ≥ 1`.

This is the lower half of the first Mertens theorem.  For small `P` a Bertrand prime in
`(P, 2P]` already contributes `≥ log 2/(2·10^6)`; for large `P` the Chebyshev bounds on `ψ`,
on `θ` and on `ψ - θ` give a positive linear main term. -/
theorem P13_prime_window_sum :
    ∃ c : ℝ, 0 < c ∧ ∀ P : ℕ, 1 ≤ P →
      c ≤ ∑ p ∈ (Finset.Ioc P (2 * P)).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ) := by
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨min (Real.log 2 / 8) (Real.log 2 / (2 * 1000000)), ?_, ?_⟩
  · exact lt_min (by linarith) (by linarith)
  · intro P hP
    by_cases hbig : 1000000 ≤ P
    · have hstep := window_sum_div_ge P
      rw [sum_window_log_eq_theta_sub P] at hstep
      have hpsi : 2 * (P : ℝ) * Real.log 2 - Real.log (2 * (P : ℝ) + 1)
          ≤ Chebyshev.psi (2 * (P : ℝ)) := by
        have h := Chebyshev.psi_ge (2 * P)
        simpa using h
      have hdiff : Chebyshev.psi (2 * (P : ℝ)) - Chebyshev.theta (2 * (P : ℝ))
          ≤ 3 * Real.sqrt (2 * (P : ℝ)) := by
        have h2P : (1 : ℝ) ≤ 2 * (P : ℝ) := by
          have : (1 : ℝ) ≤ (P : ℝ) := by exact_mod_cast hP
          linarith
        exact Commons.NumberTheory.Chebyshev.psi_sub_theta_le_three_sqrt (2 * (P : ℝ)) h2P
      have hthetaP : Chebyshev.theta (P : ℝ) ≤ Real.log 3 * (P : ℝ) := by
        have h := Commons.NumberTheory.Chebyshev.theta_le_log3_mul P
        simpa using h
      have hnum := large_P_bound P hbig
      have hgt : (Real.log 2 / 8)
          ≤ ∑ p ∈ (Finset.Ioc P (2 * P)).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ) := by
        refine le_trans ?_ hstep
        have h2Ppos : (0 : ℝ) < 2 * (P : ℝ) := by
          have : (0 : ℝ) < (P : ℝ) := by exact_mod_cast (by omega : 0 < P)
          linarith
        rw [le_div_iff₀ h2Ppos]
        linarith [hpsi, hdiff, hthetaP, hnum]
      exact le_trans (min_le_left _ _) hgt
    · have hPle : P ≤ 1000000 := le_of_lt (Nat.lt_of_not_le hbig)
      obtain ⟨q, hqprime, hPq, hq2P⟩ :=
        Nat.exists_prime_lt_and_le_two_mul P (Nat.one_le_iff_ne_zero.mp hP)
      have hmem : q ∈ (Finset.Ioc P (2 * P)).filter Nat.Prime := by
        simp only [Finset.mem_filter, Finset.mem_Ioc]
        exact ⟨⟨hPq, hq2P⟩, hqprime⟩
      have hnonneg : ∀ p ∈ (Finset.Ioc P (2 * P)).filter Nat.Prime,
          (0 : ℝ) ≤ Real.log (p : ℝ) / (p : ℝ) := by
        intro p hp
        simp only [Finset.mem_filter, Finset.mem_Ioc] at hp
        have hp2R : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.2.two_le
        have hp1R : (1 : ℝ) ≤ (p : ℝ) := by linarith
        have hppos : (0 : ℝ) < (p : ℝ) := by linarith
        exact div_nonneg (Real.log_nonneg hp1R) hppos.le
      have hsingle : Real.log (q : ℝ) / (q : ℝ)
          ≤ ∑ p ∈ (Finset.Ioc P (2 * P)).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ) :=
        Finset.single_le_sum hnonneg hmem
      have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hqprime.two_le
      have hqle : (q : ℝ) ≤ 2 * 1000000 := by
        have h1 : (q : ℝ) ≤ 2 * (P : ℝ) := by exact_mod_cast hq2P
        have h2 : (2 : ℝ) * (P : ℝ) ≤ 2 * 1000000 := by
          have : (P : ℝ) ≤ 1000000 := by exact_mod_cast hPle
          linarith
        linarith
      have hqpos : (0 : ℝ) < (q : ℝ) := by linarith
      have hlogq : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by linarith)
      have hterm : Real.log 2 / (2 * 1000000) ≤ Real.log (q : ℝ) / (q : ℝ) := by
        have hlog2le : Real.log 2 ≤ Real.log (q : ℝ) := Real.log_le_log (by norm_num) hq2
        have h1 : Real.log 2 / (2 * 1000000) ≤ Real.log (q : ℝ) / (2 * 1000000) :=
          div_le_div_of_nonneg_right hlog2le (by norm_num)
        have h2 : Real.log (q : ℝ) / (2 * 1000000) ≤ Real.log (q : ℝ) / (q : ℝ) := by
          rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2 * 1000000) hqpos]
          exact mul_le_mul_of_nonneg_left hqle hlogq
        linarith
      exact le_trans (min_le_right _ _) (le_trans hterm hsingle)

end Work.FIArea4
