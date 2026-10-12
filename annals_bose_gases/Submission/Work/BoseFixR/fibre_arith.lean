import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Data.Nat.Factorial.BigOperators
import Submission.Work.BoseFixR.FibreCount
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixR

/-- **Multinomial fibre arithmetic (pure `Finset` form).**

With `N = ∑ i ∈ s, a i` the total mass and `D k = ∏ i ∈ s, (if i = k then a i - 1 else a i)!`,
this says `∑ k ∈ s, (N-1)! / D k = N! / ∏ i ∈ s, (a i)!`.

Equivalently (clearing the denominators): each summand is `(N-1)! / D k = (N-1)! * a k / N!`,
so the sum equals `(N-1)! * (∑ a i) / N! = N! / N!` in the sense of the multinomial recursion —
"remove one particle and sum over the label of the removed particle".

The hypotheses are sharp: `hN` excludes `s = ∅`, where the empty sum is `0` but the right-hand
side is `0! / 1 = 1`. -/
lemma finset_arith_aux {ι : Type*} [DecidableEq ι] (s : Finset ι) (a : ι → ℕ)
    (hpos : ∀ i ∈ s, 0 < a i) (hN : 0 < ∑ i ∈ s, a i) :
    (∑ k ∈ s, ((∑ i ∈ s, a i) - 1).factorial /
        ∏ i ∈ s, (if i = k then a i - 1 else a i).factorial)
      = (∑ i ∈ s, a i).factorial / ∏ i ∈ s, (a i).factorial := by
  classical
  set N : ℕ := ∑ i ∈ s, a i with hNdef
  set P : ℕ := ∏ i ∈ s, (a i).factorial with hPdef
  have hNpos : 0 < N := hN
  have hPpos : 0 < P := by
    rw [hPdef]; exact Finset.prod_pos (fun i _ => Nat.factorial_pos _)
  -- For each `k ∈ s`, multiply the `k`-th summand by `P`; the denominator `D k` cancels against
  -- `P = a k * D k` and `D k ∣ (N-1)!`.
  have hkey : ∀ k ∈ s,
      P * ((N - 1).factorial / ∏ i ∈ s, (if i = k then a i - 1 else a i).factorial)
        = a k * (N - 1).factorial := by
    intro k hk
    have hak : 0 < a k := hpos k hk
    -- `D k = (a k - 1)! * ∏_{i ≠ k} (a i)!`
    have hE : ∏ i ∈ s, (if i = k then a i - 1 else a i).factorial
        = (a k - 1).factorial * ∏ i ∈ s \ {k}, (a i).factorial := by
      have h1 : ∏ i ∈ s, (if i = k then a i - 1 else a i).factorial
          = ∏ i ∈ s,
              Function.update (fun i => (a i).factorial) k ((a k - 1).factorial) i := by
        apply Finset.prod_congr rfl
        intro i _
        by_cases h : i = k
        · subst h; simp
        · simp [h]
      rw [h1, Finset.prod_update_of_mem hk]
    -- `P = (a k)! * ∏_{i ≠ k} (a i)!`
    have hPk : P = (a k).factorial * ∏ i ∈ s \ {k}, (a i).factorial := by
      rw [hPdef, Finset.prod_eq_mul_prod_sdiff_singleton_of_mem hk]
    -- hence `P = a k * D k`
    have hPD : P = a k * ∏ i ∈ s, (if i = k then a i - 1 else a i).factorial := by
      rw [hE, hPk, ← Nat.mul_factorial_pred (ne_of_gt hak)]
      ring
    -- `∑ i ∈ s, (if i = k then a i - 1 else a i) = N - 1`
    have hsum_if : ∑ i ∈ s, (if i = k then a i - 1 else a i) = N - 1 := by
      have h1 : ∑ i ∈ s, (if i = k then a i - 1 else a i)
          = (a k - 1) + ∑ i ∈ s \ {k}, a i := by
        have h2 : ∑ i ∈ s, (if i = k then a i - 1 else a i)
            = ∑ i ∈ s, Function.update (fun i => a i) k (a k - 1) i := by
          apply Finset.sum_congr rfl
          intro i _
          by_cases h : i = k
          · subst h; simp
          · simp [h]
        rw [h2, Finset.sum_update_of_mem hk]
      rw [h1]
      have h3 : ∑ i ∈ s \ {k}, a i = N - a k := by
        rw [Finset.sdiff_singleton_eq_erase, hNdef]
        have h4 := Finset.add_sum_erase s a hk
        omega
      rw [h3]
      have hak_le : a k ≤ N := by
        rw [hNdef]; exact Finset.single_le_sum (fun i _ => Nat.zero_le _) hk
      omega
    -- `D k ∣ (N-1)!` since both are factorial products of a partition of `N-1`
    have hdiv : (∏ i ∈ s, (if i = k then a i - 1 else a i).factorial) ∣ (N - 1).factorial := by
      have h5 := Nat.prod_factorial_dvd_factorial_sum s
        (fun i => if i = k then a i - 1 else a i)
      simpa [hsum_if] using h5
    rw [hPD, mul_assoc, Nat.mul_div_cancel' hdiv]
  -- multiply the whole sum by `P`; the result is `N * (N-1)! = N!`
  have hsum : P * (∑ k ∈ s,
        (N - 1).factorial / ∏ i ∈ s, (if i = k then a i - 1 else a i).factorial)
      = N.factorial := by
    rw [Finset.mul_sum]
    rw [Finset.sum_congr rfl hkey]
    rw [← Finset.sum_mul, hNdef, Nat.mul_factorial_pred (ne_of_gt hNpos)]
  have hsum2 : P * (N.factorial / P) = N.factorial := by
    rw [hPdef, hNdef]
    exact Nat.mul_div_cancel' (Nat.prod_factorial_dvd_factorial_sum s a)
  exact Nat.mul_left_cancel hPpos (hsum.trans hsum2.symm)

/-- The multinomial "remove one particle" denominator: removing one of the `α k` particles of
label `k` replaces the factor `(α k)!` by `(α k - 1)!` in the factorial denominator.  Concretely
the `Finsupp` product over the *updated* support equals the `Finset` product over `α.support` of
the pointwise updated factorials. -/
lemma update_prod {ι : Type*} [Fintype ι] [DecidableEq ι] (α : ι →₀ ℕ) {k : ι}
    (hk : k ∈ α.support) :
    (α.update k (α k - 1)).prod (fun _ j => j.factorial)
      = ∏ i ∈ α.support, (if i = k then α i - 1 else α i).factorial := by
  rw [Finsupp.prod_of_support_subset (f := α.update k (α k - 1)) (s := α.support)
      (by exact (Finsupp.support_update_subset α k).trans
            (Finset.insert_subset_iff.mpr ⟨hk, fun _ hx => hx⟩))
      (fun _ j => j.factorial) (fun i _ => Nat.factorial_zero)]
  apply Finset.prod_congr rfl
  intro i _
  rw [Finsupp.update_apply]
  by_cases h : i = k
  · subst h; simp
  · simp [h]

/-- **Multinomial fibre arithmetic.**  Summing, over all labels `k` present in `α`, the number
`(N-1)! / ∏ (α.update k (α k - 1))!` of arrangements of `α` after removing one particle of label
`k` reproduces the number `N! / ∏ (α i)!` of arrangements of `α` itself.  This is the arithmetic
heart of the fibre-counting identity in `Work.BoseFixR.labelling_count`. -/
theorem fibre_arith {ι : Type*} [Fintype ι] [DecidableEq ι] (α : ι →₀ ℕ)
    (hα : 0 < α.sum (fun _ j => j)) :
    (∑ k ∈ α.support, ((α.sum fun _ j => j) - 1).factorial
        / ((α.update k (α k - 1)).prod fun _ j => j.factorial))
      = (α.sum fun _ j => j).factorial / (α.prod fun _ j => j.factorial) := by
  have hpos : ∀ i ∈ α.support, 0 < α i :=
    fun i hi => Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi)
  have hN : 0 < ∑ i ∈ α.support, α i := hα
  have key : ∀ k ∈ α.support,
      ((∑ i ∈ α.support, α i) - 1).factorial
        / ((α.update k (α k - 1)).prod fun _ j => j.factorial)
      = ((∑ i ∈ α.support, α i) - 1).factorial
        / ∏ i ∈ α.support, (if i = k then α i - 1 else α i).factorial := by
    intro k hk
    rw [update_prod α hk]
  show (∑ k ∈ α.support, ((∑ i ∈ α.support, α i) - 1).factorial
        / ((α.update k (α k - 1)).prod fun _ j => j.factorial))
      = (∑ i ∈ α.support, α i).factorial / (∏ i ∈ α.support, (α i).factorial)
  rw [Finset.sum_congr rfl key]
  exact finset_arith_aux α.support (fun i => α i) hpos hN

end Work.BoseFixR
