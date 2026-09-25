import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.tsum_norm_prod_union_eq_sum_tuples_strata
import Submission.Work.BourgainPlan.IonescuWainger.sum_pi_sigmaStrataFinset_eq_sum_pi_biUnion
import Submission.Work.BourgainPlan.IonescuWainger.comp_sum_bound_perTuple
import Submission.Work.BourgainPlan.IonescuWainger.StrataCompDefs

/-!
# The core rearrangement step of `ortho-apply`(i) in Tao's strata convention

This is `comp_sum_bound_perTuple` with the exact-denominator sets `sigmaAFinset` replaced by Tao's
strata `sigmaStrataFinset` (and the core set `Σ_{(A₀)}` by `strataCompFinset S k A₀`, which is
definitionally the corresponding `biUnion`).
-/

open Finset MeasureTheory
open scoped BigOperators ENNReal lp

set_option autoImplicit false

namespace Work.BourgainPlan.IonescuWainger

/-- **The core rearrangement step with the per-tuple smallness hypothesis, strata form.** -/
theorem comp_sum_bound_perTuple_strata {S : Finset ℕ} {k r : ℕ} (hr : 1 ≤ r)
    (h2 : ∀ q ∈ S, 2 ≤ q) (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
    {A₀ : Finset ℕ} (hA₀ : A₀ ⊆ S)
    {f : Circle → ℤ → ℂ} (hf : ∀ δ, Memℓp (f δ) 2) {ε : ℝ}
    (hFreq : ∀ δ, HasFreqSupport (f δ) (hf δ) (arcSet δ ε))
    (hsmall : ∀ A : (i : Fin r) → ↥((S \ A₀).powerset.filter (fun B => B.card ≤ k - A₀.card)),
        (∀ i j : Fin r, i ≠ j → Disjoint ((A i).1) ((A j).1)) →
        2 * (r : ℝ) * ε * ((QA A₀ * (∏ i, QA ((A i).1)) : ℕ) : ℝ) < 1) :
    (∑ A : (i : Fin r) → ↥((S \ A₀).powerset.filter (fun B => B.card ≤ k - A₀.card)),
        if (∀ i j : Fin r, i ≠ j → Disjoint ((A i).1) ((A j).1))
          then ∑' x : ℤ, ∏ i, ‖(∑ δ ∈ sigmaStrataFinset (A₀ ∪ ((A i).1)), f δ x)‖ ^ 2
          else 0)
      ≤ ∑' x : ℤ, (∑ α ∈ strataCompFinset S k A₀,
            ‖(∑ γ ∈ sigmaStrataFinset A₀, f (γ + α) x)‖ ^ 2) ^ r := by
  classical
  set F := (S \ A₀).powerset.filter (fun B => B.card ≤ k - A₀.card) with hFdef
  have hFsub : ∀ A ∈ F, A ⊆ S := fun A hA =>
    (Finset.mem_powerset.mp (Finset.mem_filter.mp hA).1).trans Finset.sdiff_subset
  have hAsub : ∀ (A : (i : Fin r) → ↥F) (i : Fin r), (A i).1 ⊆ S \ A₀ := fun A i =>
    Finset.mem_powerset.mp (Finset.mem_filter.mp (A i).2).1
  have hstep1 : ∀ A : (i : Fin r) → ↥F,
      (if (∀ i j : Fin r, i ≠ j → Disjoint ((A i).1) ((A j).1))
        then ∑' x : ℤ, ∏ i, ‖(∑ δ ∈ sigmaStrataFinset (A₀ ∪ ((A i).1)), f δ x)‖ ^ 2
        else 0)
      ≤ ∑ α : (i : Fin r) → ↥(sigmaStrataFinset ((A i).1)),
          ∑' x : ℤ, ∏ i, ‖(∑ γ ∈ sigmaStrataFinset A₀, f (γ + (α i).1) x)‖ ^ 2 := by
    intro A
    by_cases hd : ∀ i j : Fin r, i ≠ j → Disjoint ((A i).1) ((A j).1)
    · rw [if_pos hd]
      have hkey := tsum_norm_prod_union_eq_sum_tuples_strata (S := S) (A₀ := A₀) (r := r) hr h2 hS
        hA₀ (P := fun i => (A i).1) (fun i => (hAsub A i).trans Finset.sdiff_subset) hd
        (fun i => Finset.disjoint_left.mpr
          (fun x hx1 hx2 => (Finset.mem_sdiff.mp (hAsub A i hx2)).2 hx1))
        hf hFreq (hsmall A hd)
      have hconv : (∑' x : ℤ, ∏ i, ‖(∑ δ ∈ sigmaStrataFinset (A₀ ∪ ((A i).1)), f δ x)‖ ^ 2)
          = ∑' x : ℤ, ‖∏ i, (∑ δ ∈ sigmaStrataFinset (A₀ ∪ ((A i).1)), f δ x)‖ ^ 2 :=
        tsum_congr (fun x => by rw [norm_prod, Finset.prod_pow])
      have hconv2 : (∑ α : (i : Fin r) → ↥(sigmaStrataFinset ((A i).1)),
            ∑' x : ℤ, ‖∏ i, (∑ γ ∈ sigmaStrataFinset A₀, f (γ + (α i).1) x)‖ ^ 2)
          = ∑ α : (i : Fin r) → ↥(sigmaStrataFinset ((A i).1)),
            ∑' x : ℤ, ∏ i, ‖(∑ γ ∈ sigmaStrataFinset A₀, f (γ + (α i).1) x)‖ ^ 2 :=
        Finset.sum_congr rfl (fun α _ => tsum_congr (fun x => by rw [norm_prod, Finset.prod_pow]))
      exact le_of_eq (hconv.trans (hkey.trans hconv2))
    · rw [if_neg hd]
      refine Finset.sum_nonneg (fun α _ => ?_)
      exact tsum_nonneg (fun x => Finset.prod_nonneg (fun i _ => sq_nonneg _))
  calc
    (∑ A : (i : Fin r) → ↥F,
        if (∀ i j : Fin r, i ≠ j → Disjoint ((A i).1) ((A j).1))
          then ∑' x : ℤ, ∏ i, ‖(∑ δ ∈ sigmaStrataFinset (A₀ ∪ ((A i).1)), f δ x)‖ ^ 2
          else 0)
      ≤ ∑ A : (i : Fin r) → ↥F, ∑ α : (i : Fin r) → ↥(sigmaStrataFinset ((A i).1)),
          ∑' x : ℤ, ∏ i, ‖(∑ γ ∈ sigmaStrataFinset A₀, f (γ + (α i).1) x)‖ ^ 2 :=
        Finset.sum_le_sum (fun A _ => hstep1 A)
    _ = ∑ β : (i : Fin r) → ↥(F.biUnion sigmaStrataFinset),
          ∑' x : ℤ, ∏ i, ‖(∑ γ ∈ sigmaStrataFinset A₀, f (γ + (β i).1) x)‖ ^ 2 :=
        sum_pi_sigmaStrataFinset_eq_sum_pi_biUnion (r := r) (F := F) h2 hS hFsub
          (fun β => ∑' x : ℤ, ∏ i, ‖(∑ γ ∈ sigmaStrataFinset A₀, f (γ + β i) x)‖ ^ 2)
    _ = ∑' x : ℤ, (∑ α ∈ F.biUnion sigmaStrataFinset,
            ‖(∑ γ ∈ sigmaStrataFinset A₀, f (γ + α) x)‖ ^ 2) ^ r :=
        (tsum_pow_sum_eq_sum_tuples_finset (F.biUnion sigmaStrataFinset) hr
          (fun α => Memℓp.finsetSum (sigmaStrataFinset A₀) (fun γ _ => hf (γ + α)))).symm
    _ = ∑' x : ℤ, (∑ α ∈ strataCompFinset S k A₀,
            ‖(∑ γ ∈ sigmaStrataFinset A₀, f (γ + α) x)‖ ^ 2) ^ r := by
        rw [strataCompFinset]

end Work.BourgainPlan.IonescuWainger
