import Mathlib
import Submission.Work.Peluse.Basic

namespace Work.Peluse.PET

/-- Shifting the argument of a series over `ℤ` does not change its sum: for every `a : ℤ`, the
series `x ↦ F (x + a)` has the same sum as `F`.  This is the `ℤ`-translation invariance of
`tsum`, transported along the bijection `Equiv.addRight a : ℤ ≃ ℤ`, `x ↦ x + a`. -/
private lemma hasSum_comp_addRight {F : ℤ → ℂ} (hF : Summable F) (a : ℤ) :
    HasSum (fun x : ℤ => F (x + a)) (∑' y : ℤ, F y) :=
  (Equiv.hasSum_iff (Equiv.addRight a)).2 hF.hasSum

/-- Summing a shifted function over `x : ℤ` and then over a finite set `Q` of shifts gives
`Q.card` copies of the total sum. -/
theorem tsum_sum_shift {F : ℤ → ℂ} (Q : Finset ℤ) (hF : Summable F) :
    ∑' x : ℤ, ∑ a ∈ Q, F (x + a) = (Q.card : ℂ) * ∑' y : ℤ, F y := by
  have hsum : HasSum (fun x : ℤ => ∑ a ∈ Q, F (x + a)) (∑ a ∈ Q, ∑' y : ℤ, F y) :=
    hasSum_sum (fun a _ => hasSum_comp_addRight hF a)
  rw [hsum.tsum_eq, Finset.sum_const, nsmul_eq_mul]

end Work.Peluse.PET
