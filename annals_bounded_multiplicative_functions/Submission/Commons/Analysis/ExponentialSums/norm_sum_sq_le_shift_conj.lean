import Mathlib.Analysis.CStarAlgebra.Classes

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.Analysis.ExponentialSums

open scoped ComplexConjugate

/-- A function `f : ℤ → ℂ` which is periodic of period `n` has the same sum over any `n`
consecutive integers.  In particular, summing `f` over `x, x + 1, …, x + n - 1` gives the same
value as the complete sum of `f` over the `n` residues `0, 1, …, n - 1`. -/
lemma sum_range_add_eq_sum_range_of_periodic (n : ℕ) (f : ℤ → ℂ)
    (hf : ∀ x : ℤ, f (x + n) = f x) (x : ℤ) :
    ∑ h ∈ Finset.range n, f (x + (h : ℤ)) = ∑ h ∈ Finset.range n, f (h : ℤ) := by
  -- Sliding the summation window by one does not change the sum.
  have step : ∀ y : ℤ, (∑ h ∈ Finset.range n, f (y + (h : ℤ) + 1))
      = ∑ h ∈ Finset.range n, f (y + (h : ℤ)) := by
    intro y
    -- Both sides, completed by the terms `f y` and `f (y + n)`, agree.
    have e1 : (∑ h ∈ Finset.range n, f (y + (h : ℤ) + 1)) + f y
        = ∑ k ∈ Finset.range (n + 1), f (y + (k : ℤ)) := by
      rw [Finset.sum_range_succ']
      congr 1
      · apply Finset.sum_congr rfl
        intro k _
        congr 1
        push_cast
        ring
      · simp
    have e2 : ∑ k ∈ Finset.range (n + 1), f (y + (k : ℤ))
        = (∑ k ∈ Finset.range n, f (y + (k : ℤ))) + f (y + ↑n) := by
      rw [Finset.sum_range_succ]
    have key : (∑ h ∈ Finset.range n, f (y + (h : ℤ) + 1)) + f y
        = (∑ h ∈ Finset.range n, f (y + (h : ℤ))) + f y := by
      rw [e1, e2, hf y]
    exact add_right_cancel key
  -- The sum is therefore constant along the integers.
  refine Int.induction_on x ?_ ?_ ?_
  · simp
  · intro i hi
    have hs := step (i : ℤ)
    rw [show (∑ h ∈ Finset.range n, f (((i : ℤ) + 1) + (h : ℤ)))
        = ∑ h ∈ Finset.range n, f ((i : ℤ) + (h : ℤ) + 1) from
      Finset.sum_congr rfl (fun h _ => by congr 1; ring)]
    rw [hs]
    exact hi
  · intro i hi
    have hs := step (-(i : ℤ) - 1)
    have hs2 : (∑ h ∈ Finset.range n, f (-(i : ℤ) + (h : ℤ)))
        = ∑ h ∈ Finset.range n, f (-(i : ℤ) - 1 + (h : ℤ)) := by
      rw [show (∑ h ∈ Finset.range n, f (-(i : ℤ) + (h : ℤ)))
          = ∑ h ∈ Finset.range n, f (-(i : ℤ) - 1 + (h : ℤ) + 1) from
        Finset.sum_congr rfl (fun h _ => by congr 1; ring)]
      exact hs
    rw [← hs2]
    exact hi

/-- Single-step Weyl differencing for a complete residue system: if `f : ℤ → ℂ` is periodic of
period `n > 0` then the squared modulus of the complete sum is bounded by the sum of the moduli of
the shifted autocorrelation sums. -/
theorem norm_sum_sq_le_shift_conj (n : ℕ) (hn : 0 < n) (f : ℤ → ℂ)
    (hf : ∀ x : ℤ, f (x + n) = f x) :
    ‖∑ x ∈ Finset.range n, f x‖ ^ 2
      ≤ ∑ h ∈ Finset.range n, ‖∑ x ∈ Finset.range n, f (x + h) * conj (f x)‖ := by
  have _ := hn
  set S : ℂ := ∑ y ∈ Finset.range n, f y with hS
  -- Every shifted complete sum equals the unshifted one.
  have hshift : ∀ m : ℕ, (∑ h ∈ Finset.range n, f (m + h)) = S := by
    intro m
    rw [hS]
    exact sum_range_add_eq_sum_range_of_periodic n f hf (m : ℤ)
  have hA : ∀ m : ℕ, (∑ h ∈ Finset.range n, f (m + h) * conj (f m)) = S * conj (f m) := by
    intro m
    rw [← Finset.sum_mul, hshift m]
  -- The sum of the autocorrelations equals `S * conj S`.
  have hsum : ∑ h ∈ Finset.range n, (∑ x ∈ Finset.range n, f (x + h) * conj (f x))
      = S * conj S := by
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun x _ => hA x)]
    rw [← Finset.mul_sum]
    congr 1
    rw [hS]
    exact (map_sum (starRingEnd ℂ) (fun y : ℕ => f y) (Finset.range n)).symm
  have hkey : ‖S‖ ^ 2
      = ‖∑ h ∈ Finset.range n, ∑ x ∈ Finset.range n, f (x + h) * conj (f x)‖ := by
    rw [hsum, norm_mul, Complex.norm_conj, sq]
  calc ‖∑ x ∈ Finset.range n, f x‖ ^ 2
      = ‖S‖ ^ 2 := by rw [hS]
    _ = ‖∑ h ∈ Finset.range n, ∑ x ∈ Finset.range n, f (x + h) * conj (f x)‖ := hkey
    _ ≤ ∑ h ∈ Finset.range n, ‖∑ x ∈ Finset.range n, f (x + h) * conj (f x)‖ := norm_sum_le _ _

end Commons.Analysis.ExponentialSums