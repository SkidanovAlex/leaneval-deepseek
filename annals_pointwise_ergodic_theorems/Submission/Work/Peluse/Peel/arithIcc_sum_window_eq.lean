/-
Copyright (c) 2026 The AnnalsChallenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AnnalsChallenge team
-/
import Mathlib
import Submission.Work.Peluse.Basic

/-!
# The window sum of an arithmetic-progression shift set

For `c ≠ 0` the set `c[L] = {c, 2c, …, Lc}` of `Work.Peluse.arithIcc c L` is a genuine
arithmetic progression (the map `y ↦ c * y` is injective on `{1, …, L}`), so

`∑_{a ∈ c[L]} ‖F (x + a)‖ = ∑_{y ∈ [L]} ‖F (x + c y)‖`.

Since every summand `‖F (x + a)‖` is a nonnegative real, the norm of the complex sum
`∑_{a ∈ c[L]} ((‖F (x + a)‖ : ℝ) : ℂ)` is exactly that sum of norms; squaring gives the pointwise
identity of the two window sums, and summing over `x ∈ ℤ` gives the statement.

`hL` and `hsupp` are not needed for the identity: both sides are `0` unless `L ≥ 1`, and the
equality is pointwise in `x`.  They are kept because the caller states the lemma in that form.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped BigOperators

namespace Work.Peluse.Peel

noncomputable section

/-- The norm of a finite sum of nonnegative reals, read in `ℂ`. -/
lemma norm_ofReal_sum_eq {ι : Type*} (s : Finset ι) (r : ι → ℝ) (hr : ∀ i ∈ s, 0 ≤ r i) :
    ‖∑ i ∈ s, ((r i : ℝ) : ℂ)‖ = ∑ i ∈ s, r i := by
  rw [← Complex.ofReal_sum]
  have h2 : ‖(((((∑ i ∈ s, r i : ℝ)) : ℂ)))‖ ^ 2 = (∑ i ∈ s, r i) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]; ring
  have hnn : 0 ≤ (∑ i ∈ s, r i : ℝ) := Finset.sum_nonneg hr
  nlinarith [norm_nonneg ((((∑ i ∈ s, r i : ℝ)) : ℂ))]

/-- The map `y ↦ c y` is injective on `[1, L]` when `c ≠ 0`. -/
lemma injOn_arithIcc {L : ℕ} {c : ℤ} (hc : c ≠ 0) :
    Set.InjOn (fun y : ℕ => c * (y : ℤ)) ↑(Finset.Icc 1 L) := by
  intro m _ n _ hmn
  exact Nat.cast_injective (mul_left_cancel₀ hc hmn)

/-- **The window sum of an arithmetic-progression shift set.**  For `c ≠ 0`, summing
`‖F (· + a)‖²` as a complex norm over `a ∈ c[L]` is the same as summing `‖F (· + c y)‖²`
over `y ∈ [L]`. -/
theorem arithIcc_sum_window_eq {N L : ℕ} (hL : 1 ≤ L) {c : ℤ} (hc : c ≠ 0) {F : ℤ → ℂ}
    (hsupp : Work.Peluse.SupportIn F N) :
    ∑' x : ℤ, ‖∑ a ∈ Work.Peluse.arithIcc c L, ((‖F (x + a)‖ : ℝ) : ℂ)‖ ^ 2
      = ∑' x : ℤ, (∑ y ∈ Finset.Icc 1 L, ‖F (x + c * (y : ℤ))‖) ^ 2 := by
  refine tsum_congr fun x => ?_
  have hnorm : ‖∑ a ∈ Work.Peluse.arithIcc c L, ((‖F (x + a)‖ : ℝ) : ℂ)‖
      = ∑ y ∈ Finset.Icc 1 L, ‖F (x + c * (y : ℤ))‖ := by
    rw [Work.Peluse.arithIcc, Finset.sum_image (injOn_arithIcc hc)]
    exact norm_ofReal_sum_eq _ _ (fun i _ => norm_nonneg _)
  rw [hnorm]

end

end Work.Peluse.Peel
