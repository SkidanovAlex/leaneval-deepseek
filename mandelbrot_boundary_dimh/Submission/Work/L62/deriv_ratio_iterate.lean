import Mathlib

namespace Work.L62

/-- **Differentiability of iterates.**  If `f` is complex-differentiable at `f^[k] z` for every
`k < j`, then the `j`-th iterate `f^[j]` is complex-differentiable at `z`. -/
lemma differentiableAt_iterate {f : ℂ → ℂ} {z : ℂ} (j : ℕ)
    (hdiff : ∀ k < j, DifferentiableAt ℂ f (f^[k] z)) :
    DifferentiableAt ℂ (f^[j]) z := by
  induction j with
  | zero => exact differentiableAt_id
  | succ n ih =>
    have h1 : DifferentiableAt ℂ (f^[n]) z :=
      ih (fun k hk => hdiff k (Nat.lt_succ_of_lt hk))
    have h2 : DifferentiableAt ℂ f (f^[n] z) := hdiff n (Nat.lt_succ_self n)
    rw [Function.iterate_succ']
    exact h2.comp z h1

/-- **Chain rule for iterates.**  If `f` is complex-differentiable at `f^[k] z` for every `k < j`,
then `deriv (f^[j]) z = ∏_{k < j} deriv f (f^[k] z)`. -/
lemma deriv_iterate_eq_prod {f : ℂ → ℂ} {z : ℂ} (j : ℕ)
    (hdiff : ∀ k < j, DifferentiableAt ℂ f (f^[k] z)) :
    deriv (f^[j]) z = ∏ k ∈ Finset.range j, deriv f (f^[k] z) := by
  induction j with
  | zero => simp
  | succ n ih =>
    have hd : DifferentiableAt ℂ (f^[n]) z :=
      differentiableAt_iterate n (fun k hk => hdiff k (Nat.lt_succ_of_lt hk))
    have hf : DifferentiableAt ℂ f (f^[n] z) := hdiff n (Nat.lt_succ_self n)
    rw [Function.iterate_succ', deriv_comp z hf hd,
      ih (fun k hk => hdiff k (Nat.lt_succ_of_lt hk)), Finset.prod_range_succ]
    ring

/-- **Telescoping product of ratios.**  In a field, a product of consecutive ratios `a k / a (k+1)`
telescopes to `a 0 / a j`, provided the `a k` for `k ≤ j` do not vanish. -/
lemma prod_range_div_of_ne {a : ℕ → ℂ} {j : ℕ} (h : ∀ k ≤ j, a k ≠ 0) :
    ∏ k ∈ Finset.range j, (a k / a (k + 1)) = a 0 / a j := by
  induction j with
  | zero => simp [div_self (h 0 le_rfl)]
  | succ n ih =>
    rw [Finset.prod_range_succ, ih (fun k hk => h k (Nat.le_succ_of_le hk))]
    have hn : a n ≠ 0 := h n (Nat.le_succ n)
    have hn1 : a (n + 1) ≠ 0 := h (n + 1) le_rfl
    field_simp

theorem deriv_ratio_iterate {f : ℂ → ℂ} {z : ℂ} (j : ℕ)
    (hdiff : ∀ k < j, DifferentiableAt ℂ f (f^[k] z))
    (hne : ∀ k ≤ j, f^[k] z ≠ 0) :
    deriv (f^[j]) z * z / (f^[j] z)
      = ∏ k ∈ Finset.range j, (deriv f (f^[k] z) * (f^[k] z) / (f^[k + 1] z)) := by
  -- the chain rule turns the left-hand side into `(∏ deriv) * z / (f^[j] z)`
  have hd : deriv (f^[j]) z = ∏ k ∈ Finset.range j, deriv f (f^[k] z) :=
    deriv_iterate_eq_prod j hdiff
  -- the product of the ratios `f^[k] z / f^[k+1] z` telescopes to `z / f^[j] z`
  have htel : ∏ k ∈ Finset.range j, (f^[k] z / f^[k+1] z) = z / f^[j] z := by
    have := prod_range_div_of_ne (a := fun k => f^[k] z) (j := j) (fun k hk => hne k hk)
    simpa using this
  -- the right-hand side factors as `(∏ deriv) * (∏ ratios)`
  have hprod : (∏ k ∈ Finset.range j, (deriv f (f^[k] z) * (f^[k] z) / (f^[k + 1] z)))
      = (∏ k ∈ Finset.range j, deriv f (f^[k] z)) * (z / f^[j] z) := by
    simp_rw [mul_div_assoc]
    rw [Finset.prod_mul_distrib, htel]
  rw [hd, hprod, mul_div_assoc]

end Work.L62
