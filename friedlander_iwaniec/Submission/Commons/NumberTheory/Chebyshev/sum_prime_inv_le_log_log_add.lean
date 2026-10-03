import Mathlib
import Submission.Commons.NumberTheory.Mertens.primeRecips_sub_loglog_bound_ge_three

namespace Commons.NumberTheory.Chebyshev

open Finset

/-- The set of primes in `Icc 1 N` is exactly `Nat.primesLE N` (primes `≤ N`). -/
lemma filter_Icc_one_prime_eq_primesLE (N : ℕ) :
    (Finset.Icc 1 N).filter Nat.Prime = Nat.primesLE N := by
  rw [Nat.primesLE_eq_filter_Icc_zero]
  ext p
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨h1, h2⟩, hp⟩
    exact ⟨⟨by omega, h2⟩, hp⟩
  · rintro ⟨⟨h0, h2⟩, hp⟩
    have h2le : 2 ≤ p := hp.two_le
    exact ⟨⟨by omega, h2⟩, hp⟩

/-- A crude negative lower bound for `log log 2`, used only for `N = 2`. -/
lemma log_log_two_ge_neg_two : (-2 : ℝ) ≤ Real.log (Real.log (2 : ℝ)) := by
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hhalf_le : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.log_two_gt_d9
    linarith
  have hlogle1 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)
    linarith
  have h1 : Real.log (1 / 2) ≤ Real.log (Real.log 2) :=
    Real.log_le_log (by norm_num) hhalf_le
  have h2 : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [one_div, Real.log_inv]
  rw [h2] at h1
  linarith

theorem sum_prime_inv_le_log_log_add :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N →
      (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, 1 / (p : ℝ))
        ≤ Real.log (Real.log (N : ℝ)) + C := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ :=
    Commons.NumberTheory.Mertens.primeRecips_sub_loglog_bound_ge_three
  refine ⟨C₀ + 3, by linarith, ?_⟩
  intro N hN
  rw [filter_Icc_one_prime_eq_primesLE]
  by_cases hN3 : 3 ≤ N
  · have h := hC₀ N hN3
    have hle : (∑ p ∈ Nat.primesLE N, (1 : ℝ) / (p : ℝ))
        - Real.log (Real.log (N : ℝ)) ≤ C₀ := (abs_le.mp h).2
    linarith
  · have hN2 : N = 2 := by omega
    subst hN2
    have hprimes : Nat.primesLE 2 = ({2} : Finset ℕ) := by
      ext p
      rw [Nat.mem_primesLE, Finset.mem_singleton]
      constructor
      · rintro ⟨hle, hp⟩
        have h2 := hp.two_le
        omega
      · rintro rfl
        exact ⟨le_refl 2, Nat.prime_two⟩
    have hsum : (∑ p ∈ Nat.primesLE 2, (1 : ℝ) / (p : ℝ)) = 1 / 2 := by
      rw [hprimes]
      simp
    rw [hsum]
    have := log_log_two_ge_neg_two
    linarith

end Commons.NumberTheory.Chebyshev
