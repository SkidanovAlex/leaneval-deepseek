import Mathlib
import Submission.Work.BW.HilbSerreDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `kFun` with all multiplicities zero

When every multiplicity `β i` is `0`, the binomial kernel `cbeta 0 ·` is the indicator of `0`, so
`kFun N (fun _ => 0) P u` is the single coefficient `P.coeff (toNatF u)` when `u` is
non-negative (i.e. `u = castF (toNatF u)`), and vanishes as soon as some coordinate of `u` is
negative.
-/

namespace Work.BW

open MvPolynomial

theorem kFun_zero_eq {N : ℕ} (P : MvPolynomial (Fin (N + 1)) ℚ) (u : Fin (N + 1) →₀ ℤ) :
    kFun N (fun _ => 0) P u =
      if ∀ i, 0 ≤ u i then P.coeff (HilbSerre.toNatF u) else 0 := by
  classical
  by_cases h : ∀ i, 0 ≤ u i
  · rw [ite_eq_left h, kFun]
    -- the product for `v = toNatF u` is `1`
    have hprod : (∏ i, cbeta ((fun _ => 0 : Fin (N + 1) → ℕ) i)
        (u i - ((HilbSerre.toNatF u) i : ℤ))) = 1 := by
      refine Finset.prod_eq_one (fun i _ => ?_)
      have hi : u i - ((HilbSerre.toNatF u) i : ℤ) = 0 := by
        rw [HilbSerre.toNatF_apply, Int.toNat_of_nonneg (h i), sub_self]
      simp only [hi, cbeta_zero_zero]
    rw [Finset.sum_eq_single (HilbSerre.toNatF u) ?_ ?_, hprod, mul_one]
    · -- every other term vanishes: some kernel factor is `0`
      intro b _ hb
      obtain ⟨i, hi⟩ : ∃ i, b i ≠ HilbSerre.toNatF u i := by
        by_contra hc
        simp only [not_exists, not_not] at hc
        exact hb (Finsupp.ext hc)
      have hz : cbeta ((fun _ => 0 : Fin (N + 1) → ℕ) i) (u i - (b i : ℤ)) = 0 := by
        apply cbeta_zero_of_ne_zero
        intro hc
        apply hi
        have h1 : (u i).toNat = b i := by
          have h2 : ((u i).toNat : ℤ) = u i := Int.toNat_of_nonneg (h i)
          omega
        rw [HilbSerre.toNatF_apply]
        exact h1.symm
      rw [Finset.prod_eq_zero (Finset.mem_univ i) hz, mul_zero]
    · -- and if `toNatF u` is outside the support, the whole sum is `0`
      intro hnot
      rw [MvPolynomial.notMem_support_iff.mp hnot, zero_mul]
  · -- a negative coordinate kills `kFun` by the binomial kernel in that coordinate
    rw [ite_eq_right h]
    obtain ⟨i, hi⟩ := not_forall.mp h
    exact kFun_eq_zero_of_neg N (fun _ => 0) P u i (not_le.mp hi)

end Work.BW
