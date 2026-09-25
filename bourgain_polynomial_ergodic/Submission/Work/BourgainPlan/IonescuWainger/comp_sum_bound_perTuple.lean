import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.comp_sum_bound

/-!
# The core rearrangement step of `ortho-apply`(i), with the per-tuple smallness hypothesis

Source: T. Tao, *The Ionescu–Wainger multiplier theorem and the adeles*, arXiv:2008.05066, §4,
Theorem `ortho-apply`(i), first inequality.

This is the same rearrangement step as `comp_sum_bound`, but with the smallness hypothesis of `ε`
required only on the tuples of petals that are actually summed (the pairwise disjoint ones).  In
`comp_sum_bound` the hypothesis was stated with the single denominator `Q_{A₀} · Q_S`, and the
monotonicity `∏_i Q_{P_i} ≤ Q_S` for a pairwise disjoint family (proved there as
`prod_QA_le_QA_of_pairwiseDisjoint`) was used to weaken it to the "per-tuple" form
`Q_{A₀} · ∏_i Q_{P_i}` consumed by `tsum_norm_prod_union_eq_sum_tuples`.

Here the per-tuple form is *assumed*; the proof of `comp_sum_bound` goes through verbatim with the
derivation of the per-tuple hypothesis from the global one removed.  This is the form that applies
inside `ortho-apply`(i), where `(r,c)`-goodness bounds `Q_{A₀} · ∏_i Q_{A_i} = Q_{A₀ ∪ ⋃_i A_i}`
on disjoint tuples but says nothing about `Q_S`.
-/

open Finset MeasureTheory
open scoped BigOperators ENNReal lp

set_option autoImplicit false

namespace Work.BourgainPlan.IonescuWainger

/-- **The core rearrangement step with the per-tuple smallness hypothesis.**  Same conclusion as
`comp_sum_bound`, but the smallness of `ε` is required only on the tuples that are actually summed
(the pairwise disjoint ones), in the exact form consumed by
`tsum_norm_prod_union_eq_sum_tuples`.  This is the form in which it applies inside
`ortho-apply`(i): the `(r,c)`-goodness of the parameter set bounds
`Q_{A₀} · ∏_i Q_{A_i} = Q_{A₀ ∪ ⋃_i A_i} ≤ q_max^{r k}` on disjoint tuples, but not `Q_S`. -/
theorem comp_sum_bound_perTuple {S : Finset ℕ} {k r : ℕ} (hr : 1 ≤ r)
    (h2 : ∀ q ∈ S, 2 ≤ q) (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
    {A₀ : Finset ℕ} (hA₀ : A₀ ⊆ S)
    {f : Circle → ℤ → ℂ} (hf : ∀ δ, Memℓp (f δ) 2) {ε : ℝ}
    (hFreq : ∀ δ, HasFreqSupport (f δ) (hf δ) (arcSet δ ε))
    (hsmall : ∀ A : (i : Fin r) → ↥((S \ A₀).powerset.filter (fun B => B.card ≤ k - A₀.card)),
        (∀ i j : Fin r, i ≠ j → Disjoint ((A i).1) ((A j).1)) →
        2 * (r : ℝ) * ε * ((QA A₀ * (∏ i, QA ((A i).1)) : ℕ) : ℝ) < 1) :
    (∑ A : (i : Fin r) → ↥((S \ A₀).powerset.filter (fun B => B.card ≤ k - A₀.card)),
        if (∀ i j : Fin r, i ≠ j → Disjoint ((A i).1) ((A j).1))
          then ∑' x : ℤ, ∏ i, ‖(∑ δ ∈ sigmaAFinset (A₀ ∪ ((A i).1)), f δ x)‖ ^ 2
          else 0)
      ≤ ∑' x : ℤ, (∑ α ∈ ((S \ A₀).powerset.filter (fun B => B.card ≤ k - A₀.card)).biUnion sigmaAFinset,
            ‖(∑ γ ∈ sigmaAFinset A₀, f (γ + α) x)‖ ^ 2) ^ r := by
  classical
  set F := (S \ A₀).powerset.filter (fun B => B.card ≤ k - A₀.card) with hFdef
  -- every member of `F` is a subset of `S`
  have hFsub : ∀ A ∈ F, A ⊆ S := fun A hA =>
    (Finset.mem_powerset.mp (Finset.mem_filter.mp hA).1).trans Finset.sdiff_subset
  have hAsub : ∀ (A : (i : Fin r) → ↥F) (i : Fin r), (A i).1 ⊆ S \ A₀ := fun A i =>
    Finset.mem_powerset.mp (Finset.mem_filter.mp (A i).2).1
  -- step 1: expand each admissible tuple by Pythagoras
  have hstep1 : ∀ A : (i : Fin r) → ↥F,
      (if (∀ i j : Fin r, i ≠ j → Disjoint ((A i).1) ((A j).1))
        then ∑' x : ℤ, ∏ i, ‖(∑ δ ∈ sigmaAFinset (A₀ ∪ ((A i).1)), f δ x)‖ ^ 2
        else 0)
      ≤ ∑ α : (i : Fin r) → ↥(sigmaAFinset ((A i).1)),
          ∑' x : ℤ, ∏ i, ‖(∑ γ ∈ sigmaAFinset A₀, f (γ + (α i).1) x)‖ ^ 2 := by
    intro A
    by_cases hd : ∀ i j : Fin r, i ≠ j → Disjoint ((A i).1) ((A j).1)
    · rw [if_pos hd]
      have hkey := tsum_norm_prod_union_eq_sum_tuples (S := S) (A₀ := A₀) (r := r) hr h2 hS hA₀
        (P := fun i => (A i).1) (fun i => (hAsub A i).trans Finset.sdiff_subset) hd
        (fun i => Finset.disjoint_left.mpr
          (fun x hx1 hx2 => (Finset.mem_sdiff.mp (hAsub A i hx2)).2 hx1))
        hf hFreq (hsmall A hd)
      -- the two sides of the identity, written with `∏ i, ‖…‖ ^ 2` instead of `‖∏ i, …‖ ^ 2`
      have hconv : (∑' x : ℤ, ∏ i, ‖(∑ δ ∈ sigmaAFinset (A₀ ∪ ((A i).1)), f δ x)‖ ^ 2)
          = ∑' x : ℤ, ‖∏ i, (∑ δ ∈ sigmaAFinset (A₀ ∪ ((A i).1)), f δ x)‖ ^ 2 :=
        tsum_congr (fun x => by rw [norm_prod, Finset.prod_pow])
      have hconv2 : (∑ α : (i : Fin r) → ↥(sigmaAFinset ((A i).1)),
            ∑' x : ℤ, ‖∏ i, (∑ γ ∈ sigmaAFinset A₀, f (γ + (α i).1) x)‖ ^ 2)
          = ∑ α : (i : Fin r) → ↥(sigmaAFinset ((A i).1)),
            ∑' x : ℤ, ∏ i, ‖(∑ γ ∈ sigmaAFinset A₀, f (γ + (α i).1) x)‖ ^ 2 :=
        Finset.sum_congr rfl (fun α _ => tsum_congr (fun x => by rw [norm_prod, Finset.prod_pow]))
      exact le_of_eq (hconv.trans (hkey.trans hconv2))
    · rw [if_neg hd]
      refine Finset.sum_nonneg (fun α _ => ?_)
      exact tsum_nonneg (fun x => Finset.prod_nonneg (fun i _ => sq_nonneg _))
  calc
    (∑ A : (i : Fin r) → ↥F,
        if (∀ i j : Fin r, i ≠ j → Disjoint ((A i).1) ((A j).1))
          then ∑' x : ℤ, ∏ i, ‖(∑ δ ∈ sigmaAFinset (A₀ ∪ ((A i).1)), f δ x)‖ ^ 2
          else 0)
      ≤ ∑ A : (i : Fin r) → ↥F, ∑ α : (i : Fin r) → ↥(sigmaAFinset ((A i).1)),
          ∑' x : ℤ, ∏ i, ‖(∑ γ ∈ sigmaAFinset A₀, f (γ + (α i).1) x)‖ ^ 2 :=
        Finset.sum_le_sum (fun A _ => hstep1 A)
    _ = ∑ β : (i : Fin r) → ↥(F.biUnion sigmaAFinset),
          ∑' x : ℤ, ∏ i, ‖(∑ γ ∈ sigmaAFinset A₀, f (γ + (β i).1) x)‖ ^ 2 :=
        sum_pi_sigmaAFinset_eq_sum_pi_biUnion (r := r) (F := F) h2 hS hFsub
          (fun β => ∑' x : ℤ, ∏ i, ‖(∑ γ ∈ sigmaAFinset A₀, f (γ + β i) x)‖ ^ 2)
    _ = ∑' x : ℤ, (∑ α ∈ F.biUnion sigmaAFinset,
            ‖(∑ γ ∈ sigmaAFinset A₀, f (γ + α) x)‖ ^ 2) ^ r :=
        (tsum_pow_sum_eq_sum_tuples_finset (F.biUnion sigmaAFinset) hr
          (fun α => Memℓp.finsetSum (sigmaAFinset A₀) (fun γ _ => hf (γ + α)))).symm

end Work.BourgainPlan.IonescuWainger
