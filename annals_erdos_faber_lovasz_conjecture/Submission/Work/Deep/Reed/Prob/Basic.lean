import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Finite probability spaces

A minimal, self-contained layer of finite probability, designed for the
probabilistic-combinatorics arguments in this subproject (the Lovász Local
Lemma, the naive/wasteful colouring procedure, and concentration estimates).

A finite probability space is a weight function `wt : Ω → ℝ` on a finite type
with non-negative values summing to one.  Events are `Set Ω`; the probability
of an event is the sum of the weights of its points.

The main definitions are

* `FinProb Ω` — a finite probability space on `Ω`,
* `FinProb.prob μ A` — the probability of the event `A`,
* `FinProb.cprob μ A B` — the conditional probability `P(A | B)` (with the
  convention `0 / 0 = 0`, i.e. junk when `P(B) = 0`),
* `FinProb.Indep μ A B` — independence of the events `A` and `B`,
* `FinProb.uniform Ω` — the uniform distribution on a nonempty finite type.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Deep.Reed

/-- A **finite probability space**: a weight function on a finite type whose
values are non-negative and sum to one. -/
structure FinProb (Ω : Type*) [Fintype Ω] where
  /-- the weight of a point -/
  wt : Ω → ℝ
  wt_nonneg : ∀ ω, 0 ≤ wt ω
  wt_sum : ∑ ω, wt ω = 1

namespace FinProb

variable {Ω : Type*} [Fintype Ω]

/-- The **probability** of an event in a finite probability space: the total
weight of its points. -/
noncomputable def prob (μ : FinProb Ω) (A : Set Ω) : ℝ := by
  classical
  exact ∑ ω, if ω ∈ A then μ.wt ω else 0

lemma prob_nonneg (μ : FinProb Ω) (A : Set Ω) : 0 ≤ μ.prob A := by
  classical
  rw [prob]
  refine Finset.sum_nonneg fun ω _ => ?_
  by_cases h : ω ∈ A
  · simp [h, μ.wt_nonneg ω]
  · simp [h]

lemma prob_mono (μ : FinProb Ω) {A B : Set Ω} (h : A ⊆ B) : μ.prob A ≤ μ.prob B := by
  classical
  rw [prob, prob]
  exact Finset.sum_le_sum fun ω _ => by
    by_cases hA : ω ∈ A
    · simp [hA, h hA]
    · by_cases hB : ω ∈ B
      · simp [hA, hB, μ.wt_nonneg ω]
      · simp [hA, hB]

lemma prob_univ (μ : FinProb Ω) : μ.prob Set.univ = 1 := by
  classical
  rw [prob]
  simp [μ.wt_sum]

lemma prob_le_one (μ : FinProb Ω) (A : Set Ω) : μ.prob A ≤ 1 := by
  have h := prob_mono μ (Set.subset_univ A)
  rwa [prob_univ] at h

lemma prob_empty (μ : FinProb Ω) : μ.prob ∅ = 0 := by
  classical
  rw [prob]; simp

lemma prob_compl (μ : FinProb Ω) (A : Set Ω) : μ.prob Aᶜ = 1 - μ.prob A := by
  classical
  rw [prob, prob, ← μ.wt_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun ω _ => by
    by_cases hA : ω ∈ A <;> simp [Set.mem_compl_iff, hA]

lemma prob_union_add_inter (μ : FinProb Ω) (A B : Set Ω) :
    μ.prob (A ∪ B) + μ.prob (A ∩ B) = μ.prob A + μ.prob B := by
  classical
  rw [prob, prob, prob, prob, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun ω _ => by
    by_cases hA : ω ∈ A <;> by_cases hB : ω ∈ B <;> simp [hA, hB]

lemma prob_union_le (μ : FinProb Ω) (A B : Set Ω) : μ.prob (A ∪ B) ≤ μ.prob A + μ.prob B := by
  have h := prob_union_add_inter μ A B
  have h2 : 0 ≤ μ.prob (A ∩ B) := prob_nonneg μ _
  linarith

lemma prob_inter_le_left (μ : FinProb Ω) (A B : Set Ω) : μ.prob (A ∩ B) ≤ μ.prob A :=
  prob_mono μ Set.inter_subset_left

lemma prob_inter_le_right (μ : FinProb Ω) (A B : Set Ω) : μ.prob (A ∩ B) ≤ μ.prob B :=
  prob_mono μ Set.inter_subset_right

lemma prob_iUnion_le {ι : Type*} (μ : FinProb Ω) (s : Finset ι) (A : ι → Set Ω) :
    μ.prob (⋃ i ∈ s, A i) ≤ ∑ i ∈ s, μ.prob (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [prob_empty]
  | insert a s ha ih =>
      rw [Finset.set_biUnion_insert, Finset.sum_insert ha]
      calc μ.prob (A a ∪ ⋃ i ∈ s, A i) ≤ μ.prob (A a) + μ.prob (⋃ i ∈ s, A i) :=
            prob_union_le μ _ _
        _ ≤ μ.prob (A a) + ∑ i ∈ s, μ.prob (A i) := by linarith

/-- **Independence** of two events. -/
def Indep (μ : FinProb Ω) (A B : Set Ω) : Prop := μ.prob (A ∩ B) = μ.prob A * μ.prob B

/-- **Conditional probability** `P(A | B)`, with the convention that it is `0`
when `P(B) = 0` (junk value). -/
noncomputable def cprob (μ : FinProb Ω) (A B : Set Ω) : ℝ := μ.prob (A ∩ B) / μ.prob B

lemma cprob_nonneg (μ : FinProb Ω) (A B : Set Ω) : 0 ≤ μ.cprob A B :=
  div_nonneg (prob_nonneg μ _) (prob_nonneg μ _)

lemma cprob_compl (μ : FinProb Ω) {A B : Set Ω} (hB : μ.prob B ≠ 0) :
    μ.cprob Aᶜ B = 1 - μ.cprob A B := by
  have hcompl : Aᶜ ∩ B = B \ A := by
    rw [Set.diff_eq]; exact Set.inter_comm _ _
  have hdisj : (A ∩ B) ∪ (B \ A) = B := by
    ext x; simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_diff]; tauto
  have hsum : μ.prob (A ∩ B) + μ.prob (B \ A) = μ.prob B := by
    rw [← prob_union_add_inter μ (A ∩ B) (B \ A), hdisj]
    have : (A ∩ B) ∩ (B \ A) = ∅ := by
      ext x; simp only [Set.mem_inter_iff, Set.mem_diff, Set.mem_empty_iff_false, iff_false]; tauto
    rw [this, prob_empty]; ring
  rw [cprob, cprob, hcompl, div_eq_iff hB, sub_mul, one_mul, div_mul_cancel₀ _ hB]
  linarith

lemma cprob_eq_of_indep (μ : FinProb Ω) {A B : Set Ω} (h : μ.Indep A B) (hB : μ.prob B ≠ 0) :
    μ.cprob A B = μ.prob A := by
  rw [cprob, h, mul_div_cancel_right₀ _ hB]

lemma Indep.symm (μ : FinProb Ω) {A B : Set Ω} (h : μ.Indep A B) : μ.Indep B A := by
  rw [Indep] at h ⊢
  rw [Set.inter_comm, h, mul_comm]

/-- The **uniform distribution** on a nonempty finite type. -/
noncomputable def uniform (Ω : Type*) [Fintype Ω] [Nonempty Ω] : FinProb Ω where
  wt := fun _ => (Fintype.card Ω : ℝ)⁻¹
  wt_nonneg := fun _ => by positivity
  wt_sum := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp

end FinProb

end Work.Deep.Reed
