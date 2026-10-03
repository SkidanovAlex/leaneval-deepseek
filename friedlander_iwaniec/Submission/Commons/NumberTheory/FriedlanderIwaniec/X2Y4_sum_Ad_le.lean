import Mathlib
import Submission.Commons.NumberTheory.FriedlanderIwaniec.X2Y4_sieve_remainder_le
import Submission.Commons.NumberTheory.DivisorBound.card_divisors_le_rpow

/-!
# `∑_{d ≤ D} A_d(t) ≤ D + C t^{1/100} A(t)`

For the Friedlander–Iwaniec sequence `a_n = #{(a, c) ∈ ℤ² : a² + c⁴ = n}` with
`A_d(t) = ∑_{n ≤ t, d ∣ n} a_n` (paper (2.3)) and `A(t) = ∑_{n ≤ t} a_n`, we have

  `∑_{d ≤ D} A_d(t) ≤ D + C t^{1/100} A(t)`  for all `D, t`,

because interchanging the two summations counts each lattice point `n = a² + c⁴ ≤ t`
with multiplicity `#{d ≤ D : d ∣ n} ≤ τ(n)`, and `τ(n) ≪ n^{1/100} ≤ t^{1/100}` for
`n ≥ 1`; the single exceptional index `n = 0` (i.e. `a = c = 0`, whose congruence sum
`A_d(0)` equals `1` for every `d ≥ 1`) contributes exactly `D`.  This is the "trivial"
weight bound used in the companion paper's reduction to the sieve hypotheses.

The divisor bound is `Commons.NumberTheory.DivisorBound.card_divisors_le_rpow`.
-/

namespace Commons.NumberTheory.FriedlanderIwaniec

open Finset

/-- `a_0 = 1`: the only lattice point with `a² + c⁴ = 0` is the origin. -/
lemma X2Y4_an_zero : Submission.an 0 = 1 := by
  unfold Submission.an
  rw [Set.ncard_eq_one]
  refine ⟨(0, 0), ?_⟩
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · intro hx
    rw [Nat.cast_zero] at hx
    have h1 : (0 : ℤ) ≤ x.1 ^ 2 := sq_nonneg x.1
    have h2 : (0 : ℤ) ≤ x.2 ^ 4 := by positivity
    have hx1 : x.1 ^ 2 = 0 := by linarith
    have hx2 : x.2 ^ 4 = 0 := by linarith
    exact Prod.ext (sq_eq_zero_iff.mp hx1)
      ((pow_eq_zero_iff (by norm_num : (4 : ℕ) ≠ 0)).mp hx2)
  · rintro rfl
    norm_num

/-- `∑_{d ≤ D} A_d(t) ≤ D + C t^{1/100} A(t)`: the lattice points `a₁² + a₂⁴ ≤ t`,
weighted by the number of their divisors `d ≤ D` (using `τ(n) ≪ n^{1/100}`). -/
theorem X2Y4_sum_Ad_le :
    ∃ C : ℝ, 0 < C ∧ ∀ D t : ℕ,
      (∑ d ∈ Finset.Icc 1 D, (Submission.Ad d t : ℝ))
        ≤ (D : ℝ) + C * (t : ℝ) ^ ((1 : ℝ) / 100) * (Submission.Aseq t : ℝ) := by
  obtain ⟨C, hC, hb⟩ :=
    Commons.NumberTheory.DivisorBound.card_divisors_le_rpow (1 / 100 : ℝ) (by norm_num)
  refine ⟨C, hC, fun D t => ?_⟩
  -- Interchange the two summations: rewrite `A_d(t)` as a sum over `n ≤ t` of the
  -- indicator of `d ∣ n`, then swap the order of summation.
  have hswap : (∑ d ∈ Finset.Icc 1 D, (Submission.Ad d t : ℝ))
      = ∑ n ∈ Finset.range (t + 1),
          (Submission.an n : ℝ) * (((Finset.Icc 1 D).filter (fun d => d ∣ n)).card : ℝ) := by
    have h1 : (∑ d ∈ Finset.Icc 1 D, (Submission.Ad d t : ℝ))
        = ∑ d ∈ Finset.Icc 1 D, ∑ n ∈ Finset.range (t + 1),
            (if d ∣ n then (Submission.an n : ℝ) else 0) := by
      refine Finset.sum_congr rfl fun d _ => ?_
      unfold Submission.Ad
      rw [Finset.sum_filter]
      simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_zero]
    rw [h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    ring
  rw [hswap]
  -- Pointwise bound: the number of divisors `d ≤ D` of `n` is at most `D` for `n = 0`
  -- and at most `τ(n) ≪ n^{1/100} ≤ t^{1/100}` for `n ≥ 1`.
  have hsplit : ∀ n ∈ Finset.range (t + 1),
      (Submission.an n : ℝ) * (((Finset.Icc 1 D).filter (fun d => d ∣ n)).card : ℝ)
        ≤ (Submission.an n : ℝ) *
            (if n = 0 then (D : ℝ) else C * (t : ℝ) ^ ((1 : ℝ) / 100)) := by
    intro n hn
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      have hcard : ((Finset.Icc 1 D).filter (fun d => d ∣ 0)).card = D := by
        rw [Finset.filter_true_of_mem (fun d _ => dvd_zero d), Nat.card_Icc]
        simp
      rw [if_pos rfl, hcard]
    · have hsub : (Finset.Icc 1 D).filter (fun d => d ∣ n) ⊆ Nat.divisors n := by
        intro d hd
        rw [Finset.mem_filter] at hd
        exact Nat.mem_divisors.mpr ⟨hd.2, by omega⟩
      have hcard : (((Finset.Icc 1 D).filter (fun d => d ∣ n)).card : ℝ)
          ≤ ((Nat.divisors n).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
      have htau : ((Nat.divisors n).card : ℝ) ≤ C * (n : ℝ) ^ ((1 : ℝ) / 100) := hb n
      have hnt : (n : ℝ) ≤ (t : ℝ) := by
        have := Finset.mem_range.mp hn
        exact_mod_cast (by omega : n ≤ t)
      have hlt : (n : ℝ) ^ ((1 : ℝ) / 100) ≤ (t : ℝ) ^ ((1 : ℝ) / 100) :=
        Real.rpow_le_rpow (Nat.cast_nonneg n) hnt (by norm_num)
      have hfin : (((Finset.Icc 1 D).filter (fun d => d ∣ n)).card : ℝ)
          ≤ C * (t : ℝ) ^ ((1 : ℝ) / 100) :=
        le_trans hcard (le_trans htau (mul_le_mul_of_nonneg_left hlt hC.le))
      rw [if_neg (by omega : n ≠ 0)]
      exact mul_le_mul_of_nonneg_left hfin (by positivity)
  -- The tail `∑_{0 < n ≤ t} a_n` is at most `A(t)`.
  have hshift : (∑ n ∈ Finset.range t, (Submission.an (n + 1) : ℝ))
      ≤ (Submission.Aseq t : ℝ) := by
    rw [Submission.Aseq, Nat.cast_sum]
    conv_rhs => rw [Finset.sum_range_succ']
    have hnn : (0 : ℝ) ≤ (Submission.an 0 : ℝ) := by positivity
    linarith
  calc ∑ n ∈ Finset.range (t + 1),
        (Submission.an n : ℝ) * (((Finset.Icc 1 D).filter (fun d => d ∣ n)).card : ℝ)
      ≤ ∑ n ∈ Finset.range (t + 1),
          (Submission.an n : ℝ) *
            (if n = 0 then (D : ℝ) else C * (t : ℝ) ^ ((1 : ℝ) / 100)) :=
        Finset.sum_le_sum hsplit
    _ = (Submission.an 0 : ℝ) * (D : ℝ) + ∑ n ∈ Finset.range t,
          (Submission.an (n + 1) : ℝ) * (C * (t : ℝ) ^ ((1 : ℝ) / 100)) := by
        rw [Finset.sum_range_succ']
        have h0 : (Submission.an 0 : ℝ) *
              (if 0 = 0 then (D : ℝ) else C * (t : ℝ) ^ ((1 : ℝ) / 100))
            = (Submission.an 0 : ℝ) * (D : ℝ) := by rw [if_pos rfl]
        rw [h0, add_comm]
        refine congrArg (fun z => (Submission.an 0 : ℝ) * (D : ℝ) + z) ?_
        exact Finset.sum_congr rfl fun n _ => by rw [if_neg (by omega : ¬ n + 1 = 0)]
    _ = (Submission.an 0 : ℝ) * (D : ℝ) + C * (t : ℝ) ^ ((1 : ℝ) / 100) *
          (∑ n ∈ Finset.range t, (Submission.an (n + 1) : ℝ)) := by
        rw [Finset.mul_sum]
        exact congrArg₂ (· + ·) rfl (Finset.sum_congr rfl fun n _ => by ring)
    _ ≤ (D : ℝ) + C * (t : ℝ) ^ ((1 : ℝ) / 100) * (Submission.Aseq t : ℝ) := by
        rw [X2Y4_an_zero]
        push_cast
        have h1 : (0 : ℝ) ≤ C * (t : ℝ) ^ ((1 : ℝ) / 100) := by positivity
        nlinarith [hshift, h1]

end Commons.NumberTheory.FriedlanderIwaniec
