import Mathlib
import Submission.Work.FIPlan.Interface
import Submission.Work.FIArea4.SqfreeKernel
import Submission.Work.FIArea4.sqfree_kernel
import Submission.Work.FIArea4.card_sqfreeKernel_eq_le_sqrt
import Submission.Work.FIArea7.sqfreeKernel_dvd_iff_odd
import Submission.Work.FIArea7.card_Icc_neg_filter_le_two_mul
import Submission.Work.FIArea7.card_filter_sqfreeKernel_subset_le
import Submission.Work.FIArea7.prod_one_add_inv_sqrt_primeFactors_le_four

namespace Work.FIArea7

/-- The `(4dq)`-coprime part of `n` has no prime of `4dq` to an odd power. -/
def badN (d q : ℕ) (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → ¬ (p : ℤ) ∣ (4 * (d : ℤ) * (q : ℤ)) → ¬ Odd (n.factorization p)

open Classical in
/-- **Sparsity of the `r` whose `(4dq)`-coprime part is a square** (the *FI* §22 remark (ii)):
those `r` are exactly the numbers `r = ±a·s²` with every prime of `a` dividing `4·d·q`, so their
number up to `Rz` is `≪ ∏_{p ∣ 4dq}(1-p^{-1/2})^{-1}·√Rz ≤ 24·d·√q·√Rz` (for `0 < d`, `0 < q`).
Here `Odd (r.natAbs.factorization p)` means `p` divides `r` to an odd power, and
`¬ (p : ℤ) ∣ (4*d*q : ℤ)` excludes the primes of `4dq`, so the predicate `¬ ∃ p, ...` says that the
`(4dq)`-coprime part of `r` has all exponents even (i.e. is a square).
Intended use: for those `r` the inner `s`-sum of the `K`-sum is estimated trivially. -/
theorem card_bad_r_le (d q : ℕ) (hd : 1 ≤ d) (hq : 1 ≤ q) (Rz : ℤ) :
    (((Finset.Icc (-Rz) Rz).filter (fun r : ℤ => Odd r ∧
        ¬ ∃ p : ℕ, p.Prime ∧ ¬ (p : ℤ) ∣ (4 * (d : ℤ) * (q : ℤ)) ∧
          Odd (r.natAbs.factorization p))).card : ℝ)
      ≤ 24 * (d : ℝ) * Real.sqrt (q : ℝ)
          * (Real.sqrt (((max Rz 0).toNat : ℝ)) + 1) := by
  classical
  -- ## 0.  Put the counted predicate into `badN` form.
  have hfilter : (Finset.Icc (-Rz) Rz).filter (fun r : ℤ => Odd r ∧
        ¬ ∃ p : ℕ, p.Prime ∧ ¬ (p : ℤ) ∣ (4 * (d : ℤ) * (q : ℤ)) ∧
          Odd (r.natAbs.factorization p))
      = (Finset.Icc (-Rz) Rz).filter (fun r : ℤ => Odd r ∧ badN d q r.natAbs) := by
    apply Finset.filter_congr
    intro r _
    simp only [badN]
    constructor
    · rintro ⟨ho, hne⟩
      exact ⟨ho, fun p hp hp2 ho2 => hne ⟨p, hp, hp2, ho2⟩⟩
    · rintro ⟨ho, hF⟩
      exact ⟨ho, fun ⟨p, hp, hp2, ho2⟩ => hF p hp hp2 ho2⟩
  rw [hfilter]
  -- ## 1.  `|S| ≤ 2 |T|`  (the two-to-one map `r ↦ |r|`)
  have hstep1 : (((Finset.Icc (-Rz) Rz).filter (fun r : ℤ => Odd r ∧ badN d q r.natAbs)).card : ℝ)
      ≤ 2 * (((Finset.Icc 1 (max Rz 0).toNat).filter
          (fun n : ℕ => Odd n ∧ badN d q n)).card : ℝ) := by
    exact_mod_cast card_Icc_neg_filter_le_two_mul Rz (badN d q)
  -- ## 2.  `|T| ≤ √M · ∏_{p | 4dq} (1 + 1/√p)`
  -- (`T` consists of the `n ∈ [1,M]` whose squarefree kernel has all prime factors dividing `4dq`)
  have hstep2 : (((Finset.Icc 1 (max Rz 0).toNat).filter (fun n : ℕ => Odd n ∧ badN d q n)).card : ℝ)
      ≤ Real.sqrt (((max Rz 0).toNat : ℝ))
          * ∏ p ∈ (4 * d * q).primeFactors, (1 + 1 / Real.sqrt (p : ℝ)) := by
    have hsub : (Finset.Icc 1 (max Rz 0).toNat).filter (fun n : ℕ => Odd n ∧ badN d q n) ⊆
        (Finset.Icc 1 (max Rz 0).toNat).filter
          (fun n : ℕ => (Work.FIArea4.sqfreeKernel n).primeFactors ⊆ (4 * d * q).primeFactors) := by
      intro n hn
      simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
      obtain ⟨⟨hn1, hn2⟩, -, hF⟩ := hn
      refine ⟨⟨hn1, hn2⟩, ?_⟩
      intro p hp
      obtain ⟨hpp, hpdvd, -⟩ := Nat.mem_primeFactors.mp hp
      have hn0 : n ≠ 0 := by omega
      have hodd : Odd (n.factorization p) := (sqfreeKernel_dvd_iff_odd n p hn0 hpp).mp hpdvd
      have hint : (p : ℤ) ∣ (4 * (d : ℤ) * (q : ℤ)) := by
        by_contra hcon
        exact hF p hpp hcon hodd
      have hcast : (4 * (d : ℤ) * (q : ℤ)) = ((4 * d * q : ℕ) : ℤ) := by push_cast; ring
      rw [hcast] at hint
      exact Nat.mem_primeFactors.mpr ⟨hpp, Int.natCast_dvd_natCast.mp hint, by positivity⟩
    have h1 : (((Finset.Icc 1 (max Rz 0).toNat).filter
          (fun n : ℕ => Odd n ∧ badN d q n)).card : ℝ)
        ≤ (((Finset.Icc 1 (max Rz 0).toNat).filter (fun n : ℕ =>
            (Work.FIArea4.sqfreeKernel n).primeFactors ⊆ (4 * d * q).primeFactors)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    have h2 := card_filter_sqfreeKernel_subset_le (max Rz 0).toNat (4 * d * q).primeFactors
      (fun p hp => Nat.prime_of_mem_primeFactors hp)
    exact le_trans h1 h2
  -- ## 3.  the product bound `∏_{p | 4dq} (1 + 1/√p) ≤ 4·d·√q`
  have hstep3 : ∏ p ∈ (4 * d * q).primeFactors, (1 + 1 / Real.sqrt (p : ℝ))
      ≤ 4 * (d : ℝ) * Real.sqrt (q : ℝ) :=
    prod_one_add_inv_sqrt_primeFactors_le_four d q hd hq
  -- ## 4.  arithmetic
  have hdn : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hqn : (0 : ℝ) ≤ Real.sqrt (q : ℝ) := Real.sqrt_nonneg _
  have hMn : (0 : ℝ) ≤ Real.sqrt (((max Rz 0).toNat : ℝ)) := Real.sqrt_nonneg _
  calc (((Finset.Icc (-Rz) Rz).filter (fun r : ℤ => Odd r ∧ badN d q r.natAbs)).card : ℝ)
      ≤ 2 * (((Finset.Icc 1 (max Rz 0).toNat).filter (fun n : ℕ => Odd n ∧ badN d q n)).card : ℝ) :=
        hstep1
    _ ≤ 2 * (Real.sqrt (((max Rz 0).toNat : ℝ))
          * ∏ p ∈ (4 * d * q).primeFactors, (1 + 1 / Real.sqrt (p : ℝ))) := by linarith
    _ ≤ 2 * (Real.sqrt (((max Rz 0).toNat : ℝ))
          * (4 * (d : ℝ) * Real.sqrt (q : ℝ))) := by
        have hmul := mul_le_mul_of_nonneg_left hstep3 hMn
        linarith
    _ = 8 * (d : ℝ) * Real.sqrt (q : ℝ) * Real.sqrt (((max Rz 0).toNat : ℝ)) := by ring
    _ ≤ 24 * (d : ℝ) * Real.sqrt (q : ℝ)
          * (Real.sqrt (((max Rz 0).toNat : ℝ)) + 1) := by
        have h1 : (0 : ℝ) ≤ (d : ℝ) * Real.sqrt (q : ℝ) := mul_nonneg hdn hqn
        nlinarith [h1, hMn, mul_nonneg h1 hMn]

end Work.FIArea7
