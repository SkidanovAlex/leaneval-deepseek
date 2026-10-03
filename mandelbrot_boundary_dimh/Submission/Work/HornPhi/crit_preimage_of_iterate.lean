import Mathlib
import Submission.Work.Interfaces.HornParts
import Submission.Work.Horn.pushdown_critval_unique

/-!
# Critical preimages of an iterate

If `f` is a parabolic germ, `B` an immediate basin in which the critical point is unique (`c`),
and `deriv (f^[N]) w = 0` at a point `w ∈ B`, then some orbit point `f^[j] w` with `j < N`
already equals the critical point `c`.

The proof is the chain rule for iterates: `deriv (f^[N]) w = ∏_{j<N} deriv f (f^[j] w)` as soon
as `f` is differentiable at all the orbit points `f^[j] w`, `j < N`; and if `f` is *not*
differentiable at such a point then `deriv f` vanishes there, and `huniq` forces that point to be
`c`.
-/

namespace Work.HornPhi

open scoped BigOperators

/-- **Chain rule for iterates, differentiability part.**  If `f` is differentiable at all the
orbit points `f^[j] x`, `j < n`, then `f^[n]` is differentiable at `x`. -/
theorem differentiableAt_iterate {f : ℂ → ℂ} {x : ℂ} (n : ℕ)
    (h : ∀ j < n, DifferentiableAt ℂ f (f^[j] x)) : DifferentiableAt ℂ (f^[n]) x := by
  induction n with
  | zero => simpa [Function.iterate_zero] using differentiableAt_id (x := x)
  | succ n ih =>
      rw [Function.iterate_succ']
      exact DifferentiableAt.comp x (h n (Nat.lt_succ_self n))
        (ih fun j hj => h j (Nat.lt_trans hj (Nat.lt_succ_self n)))

/-- **Chain rule for iterates.**  If `f` is differentiable at all the orbit points `f^[j] x`,
`j < n`, then `deriv (f^[n]) x = ∏_{j<n} deriv f (f^[j] x)`. -/
theorem deriv_iterate_eq_prod {f : ℂ → ℂ} {x : ℂ} (n : ℕ)
    (h : ∀ j < n, DifferentiableAt ℂ f (f^[j] x)) :
    deriv (f^[n]) x = ∏ j ∈ Finset.range n, deriv f (f^[j] x) := by
  induction n with
  | zero => simpa [Function.iterate_zero] using deriv_id (x := x)
  | succ n ih =>
      have hlt : ∀ j < n, DifferentiableAt ℂ f (f^[j] x) :=
        fun j hj => h j (Nat.lt_trans hj (Nat.lt_succ_self n))
      rw [Function.iterate_succ', deriv_comp x (h n (Nat.lt_succ_self n))
        (differentiableAt_iterate n hlt), ih hlt, Finset.prod_range_succ]
      ring

/-- Nonvanishing `deriv` forces differentiability (`deriv` is `0` off the differentiability set). -/
theorem differentiableAt_of_deriv_ne_zero {f : ℂ → ℂ} {x : ℂ} (h : deriv f x ≠ 0) :
    DifferentiableAt ℂ f x := by
  by_contra hx
  exact h (deriv_zero_of_not_differentiableAt hx)

theorem crit_preimage_of_iterate {f : ℂ → ℂ} {D B : Set ℂ} {c : ℂ}
    (hgerm : MandelDim.IsParabolicGerm f D) (hB : MandelDim.IsImmediateBasin f D B)
    (huniq : ∀ c' ∈ B, deriv f c' = 0 → c' = c)
    {N : ℕ} {w : ℂ} (hw : w ∈ B) (hcrit : deriv (f^[N]) w = 0) :
    ∃ j : ℕ, j < N ∧ f^[j] w = c := by
  by_cases h : ∃ j, j < N ∧ deriv f (f^[j] w) = 0
  · obtain ⟨j, hjN, hj0⟩ := h
    exact ⟨j, hjN, huniq _ (hB.2.2.2.2.1.iterate j hw) hj0⟩
  · simp only [not_exists, not_and] at h
    have hdiff : ∀ j < N, DifferentiableAt ℂ f (f^[j] w) :=
      fun j hj => differentiableAt_of_deriv_ne_zero (h j hj)
    rw [deriv_iterate_eq_prod N hdiff] at hcrit
    refine absurd hcrit ?_
    exact Finset.prod_ne_zero_iff.mpr fun j hj => h j (Finset.mem_range.mp hj)

end Work.HornPhi
