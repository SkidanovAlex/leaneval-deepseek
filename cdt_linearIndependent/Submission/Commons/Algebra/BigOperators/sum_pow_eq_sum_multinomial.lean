import Mathlib.Data.Nat.Choose.Multinomial

namespace Commons.Algebra.BigOperators

open Finset

/-- The multinomial theorem, in the form summing over the box `∏_i {0, …, m}` and
killing the terms whose exponent-sum is not `m` with an indicator function. -/
theorem sum_pow_eq_sum_multinomial {k : ℕ} {A : Type*} [CommRing A] (f : Fin k → A) (m : ℕ) :
    (∑ i, f i) ^ m =
      ∑ p ∈ Fintype.piFinset (fun _ : Fin k => Finset.range (m + 1)),
        (if ∑ i, p i = m then ((Nat.multinomial Finset.univ p : ℕ) : A) else 0) *
          ∏ i, f i ^ (p i) := by
  classical
  rw [Finset.sum_pow_eq_sum_piAntidiag Finset.univ f m]
  have hfilter :
      ∑ p ∈ Fintype.piFinset (fun _ : Fin k => Finset.range (m + 1)),
          (if ∑ i, p i = m then ((Nat.multinomial Finset.univ p : ℕ) : A) else 0) *
            ∏ i, f i ^ (p i)
        = ∑ p ∈ (Fintype.piFinset (fun _ : Fin k => Finset.range (m + 1))).filter
              (fun p => ∑ i, p i = m),
            ((Nat.multinomial Finset.univ p : ℕ) : A) * ∏ i, f i ^ (p i) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases h : ∑ i, p i = m <;> simp [h]
  have hbox :
      (Fintype.piFinset (fun _ : Fin k => Finset.range (m + 1))).filter
          (fun p => ∑ i, p i = m)
        = Finset.piAntidiag Finset.univ m := by
    ext p
    rw [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_piAntidiag]
    constructor
    · rintro ⟨hbox, hsum⟩
      exact ⟨by simpa using hsum, fun i _ => Finset.mem_univ i⟩
    · rintro ⟨hsum, -⟩
      refine ⟨fun i => ?_, hsum⟩
      rw [Finset.mem_range]
      have hle : p i ≤ Finset.univ.sum p := by
        simpa using Finset.single_le_sum (f := p) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
      exact Nat.lt_succ_of_le (hle.trans (le_of_eq hsum))
  rw [hfilter, hbox]

end Commons.Algebra.BigOperators