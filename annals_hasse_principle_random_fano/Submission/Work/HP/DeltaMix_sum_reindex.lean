import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.DiagDefs

/-!
# Reindexing `∑_a Δ_V^mix(B)` as a sum over `x ∈ Ξ_{d,n}(B)`

The mixed second-moment object `Δ_V^mix(B)` of Browning--Le Boudec--Sawin (§4) is
`DeltaMix d n a B = (1/2) (log B · W / ‖a‖) ∑_{x ∈ Ξ, f_a(x) = 0} ‖ν(x)‖^{-1}`, a sum over the
primitive coefficient vectors `a` of height `≤ A`.  Summing it over `a` and exchanging the two
finite sums shows that the total is the sum over `x ∈ Ξ_{d,n}(B)` of `‖ν(x)‖^{-1}` times the sum
over the `a` with `f_a(x) = 0` of `‖a‖^{-1}`.

The proof is pure bookkeeping: unfold `DeltaMix`, replace each `finsum` over a finite set by the
corresponding `Finset` sum (`finsum_mem_eq_finite_toFinset_sum`), rewrite the inner sum over
`{x ∈ Ξ | f_a(x) = 0}` as a sum over `Ξ` of an `if`-expression (`Finset.sum_filter`), factor out the
constants and apply `Finset.sum_comm`.
-/

set_option autoImplicit false

noncomputable section

namespace Work.HP

/-- A `finsum` over the set `{x ∈ s | P x}` is the `Finset` sum over `hs.toFinset.filter P`. -/
private lemma finsum_mem_sep_toFinset' {α M : Type*} [AddCommMonoid M] {s : Set α}
    (hs : s.Finite) (P : α → Prop) (f : α → M) [DecidablePred P] :
    (∑ᶠ x ∈ ({x ∈ s | P x} : Set α), f x) = ∑ x ∈ hs.toFinset.filter P, f x := by
  have hsub : ({x ∈ s | P x} : Set α) ⊆ s := fun x hx => hx.1
  rw [finsum_mem_eq_finite_toFinset_sum _ (hs.subset hsub)]
  congr 1
  ext x
  simp only [Set.Finite.mem_toFinset, Finset.mem_filter, Set.mem_ofPred_eq]

theorem DeltaMix_sum_reindex (d n : ℕ) (A B : ℝ) :
    (∑ᶠ a ∈ primSet d n A (fun _ => True), DeltaMix d n a B)
      = (1 / 2) * Real.log B * (bigW (wOf B) : ℝ) *
        ∑ᶠ x ∈ Xi d n B, (1 / eNorm (veronese d n x)) *
          (∑ᶠ a ∈ primSet d n A (fun _ => True),
            (if formEval d n a x = 0 then 1 / eNorm a else 0)) := by
  classical
  have hPf : (primSet d n A (fun _ => True)).Finite := primSet_finite d n A _
  have hXf : (Xi d n B).Finite := Xi_finite d n B
  -- The value of `DeltaMix` at a fixed coefficient vector, in `Finset` form.
  have hDelta : ∀ a : Mon d n → ℤ, DeltaMix d n a B =
      (1 / 2) * Real.log B * (bigW (wOf B) : ℝ) *
        ∑ x ∈ hXf.toFinset,
          (if formEval d n a x = 0 then (1 / eNorm a) * (1 / eNorm (veronese d n x)) else 0) := by
    intro a
    rw [DeltaMix]
    rw [finsum_mem_sep_toFinset' hXf (fun x => formEval d n a x = 0)
          (fun x => 1 / eNorm (veronese d n x))]
    rw [Finset.sum_filter]
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    by_cases h : formEval d n a x = 0
    · rw [ite_eq_left h, ite_eq_left h]; ring
    · rw [ite_eq_right h, ite_eq_right h]; ring
  -- The right-hand side in `Finset` form.
  have hRHS : (∑ᶠ x ∈ Xi d n B, (1 / eNorm (veronese d n x)) *
        (∑ᶠ a ∈ primSet d n A (fun _ => True),
          (if formEval d n a x = 0 then 1 / eNorm a else 0)))
      = ∑ x ∈ hXf.toFinset, ∑ a ∈ hPf.toFinset,
          (if formEval d n a x = 0 then (1 / eNorm a) * (1 / eNorm (veronese d n x)) else 0) := by
    rw [finsum_mem_eq_finite_toFinset_sum
        (fun x => (1 / eNorm (veronese d n x)) *
          (∑ᶠ a ∈ primSet d n A (fun _ => True),
            (if formEval d n a x = 0 then 1 / eNorm a else 0))) hXf]
    apply Finset.sum_congr rfl
    intro x _
    rw [finsum_mem_eq_finite_toFinset_sum
        (fun a => if formEval d n a x = 0 then 1 / eNorm a else 0) hPf]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    by_cases h : formEval d n a x = 0
    · rw [ite_eq_left h, ite_eq_left h]; ring
    · rw [ite_eq_right h, ite_eq_right h]; ring
  calc (∑ᶠ a ∈ primSet d n A (fun _ => True), DeltaMix d n a B)
      = ∑ a ∈ hPf.toFinset, DeltaMix d n a B := by
          rw [finsum_mem_eq_finite_toFinset_sum _ hPf]
    _ = (1 / 2) * Real.log B * (bigW (wOf B) : ℝ) *
          ∑ a ∈ hPf.toFinset, ∑ x ∈ hXf.toFinset,
            (if formEval d n a x = 0 then (1 / eNorm a) * (1 / eNorm (veronese d n x)) else 0) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun a _ => hDelta a
    _ = (1 / 2) * Real.log B * (bigW (wOf B) : ℝ) *
          ∑ x ∈ hXf.toFinset, ∑ a ∈ hPf.toFinset,
            (if formEval d n a x = 0 then (1 / eNorm a) * (1 / eNorm (veronese d n x)) else 0) := by
          rw [Finset.sum_comm]
    _ = (1 / 2) * Real.log B * (bigW (wOf B) : ℝ) *
        ∑ᶠ x ∈ Xi d n B, (1 / eNorm (veronese d n x)) *
          (∑ᶠ a ∈ primSet d n A (fun _ => True),
            (if formEval d n a x = 0 then 1 / eNorm a else 0)) := by
          rw [hRHS]

end Work.HP
