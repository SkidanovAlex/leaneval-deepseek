/-
# Work.Deep.Conc.Basic

A minimal, self-contained layer of *finite* probability theory: the uniform measure on a
finite type, its expectation and probability, and the standard API (monotonicity, complement,
finite union bound, `prob ≤ 1`, Markov, Chebyshev).

Everything is a finite sum over a `Fintype`; no measure theory is used.  The uniform
probability space of this development is

* `Ω = ∀ i : ι, π i` with all `π i` finite and nonempty — the product of uniform "coordinate"
  spaces.  The special case `π = fun _ => Fin k` is the space `ι → Fin k` of a uniformly random
  colouring, which is what the graph-colouring applications use.

`expect f = (∑ ω, f ω) / card Ω` and `prob E = expect (E.indicator 1)`.
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Set.Piecewise
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.unusedSectionVars false
open scoped BigOperators
open Finset

namespace Work.Deep.Conc

/-! ## Definitions -/

/-- **Uniform expectation** on a finite type: the average of a real-valued function. -/
noncomputable def expect {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) : ℝ :=
  (∑ ω, f ω) / (Fintype.card Ω : ℝ)

/-- **Uniform probability** of an event `E ⊆ Ω`. -/
noncomputable def prob {Ω : Type*} [Fintype Ω] (E : Set Ω) : ℝ :=
  expect (E.indicator fun _ => (1 : ℝ))

variable {Ω : Type*} [Fintype Ω]

/-! ## The indicator of an event -/

lemma indicator_one_nonneg (E : Set Ω) (ω : Ω) : 0 ≤ E.indicator (fun _ => (1 : ℝ)) ω := by
  by_cases h : ω ∈ E
  · rw [Set.indicator_of_mem h]; norm_num
  · rw [Set.indicator_of_notMem h]

lemma indicator_one_le_one (E : Set Ω) (ω : Ω) : E.indicator (fun _ => (1 : ℝ)) ω ≤ 1 := by
  by_cases h : ω ∈ E
  · rw [Set.indicator_of_mem h]
  · rw [Set.indicator_of_notMem h]; norm_num

lemma prob_eq_sum (E : Set Ω) :
    prob E = (∑ ω, E.indicator (fun _ => (1 : ℝ)) ω) / (Fintype.card Ω : ℝ) := rfl

/-! ## Basic identities for `expect` -/

@[simp] lemma expect_zero : expect (fun _ : Ω => (0 : ℝ)) = 0 := by
  simp [expect]

lemma expect_const' (c : ℝ) (h : 0 < Fintype.card Ω) :
    expect (fun _ : Ω => c) = c := by
  rw [expect, Finset.sum_const, nsmul_eq_mul, Finset.card_univ, mul_comm]
  exact mul_div_cancel_right₀ c (Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp h))

lemma expect_const [Nonempty Ω] (c : ℝ) : expect (fun _ : Ω => c) = c :=
  expect_const' c Fintype.card_pos

lemma expect_add (f g : Ω → ℝ) : expect (f + g) = expect f + expect g := by
  simp only [expect, Pi.add_apply, Finset.sum_add_distrib, add_div]

lemma expect_sub (f g : Ω → ℝ) : expect (f - g) = expect f - expect g := by
  simp only [expect, Pi.sub_apply, Finset.sum_sub_distrib, sub_div]

lemma expect_mul_const (f : Ω → ℝ) (c : ℝ) : expect (fun ω => f ω * c) = expect f * c := by
  rw [expect, expect, ← Finset.sum_mul, mul_div_assoc]
  ring

lemma expect_const_mul (f : Ω → ℝ) (c : ℝ) : expect (fun ω => c * f ω) = c * expect f := by
  rw [expect, expect, ← Finset.mul_sum, ← mul_div_assoc]

lemma expect_sum {ι : Type*} (s : Finset ι) (f : ι → Ω → ℝ) :
    expect (fun ω => ∑ i ∈ s, f i ω) = ∑ i ∈ s, expect (f i) := by
  simp only [expect, Finset.sum_div]
  rw [Finset.sum_comm]

lemma expect_congr {f g : Ω → ℝ} (h : ∀ ω, f ω = g ω) : expect f = expect g := by
  simp only [expect]
  congr 1
  exact Finset.sum_congr rfl fun ω _ => h ω

lemma expect_nonneg {f : Ω → ℝ} (h : ∀ ω, 0 ≤ f ω) : 0 ≤ expect f := by
  have hc : (0 : ℝ) ≤ (Fintype.card Ω : ℝ) := Nat.cast_nonneg _
  rw [expect]
  exact div_nonneg (Finset.sum_nonneg fun ω _ => h ω) hc

lemma expect_mono {f g : Ω → ℝ} (h : f ≤ g) : expect f ≤ expect g := by
  have hc : (0 : ℝ) ≤ (Fintype.card Ω : ℝ) := Nat.cast_nonneg _
  rw [expect, expect]
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun ω _ => h ω) hc

lemma expect_mono' {f g : Ω → ℝ} (h : ∀ ω, f ω ≤ g ω) : expect f ≤ expect g :=
  expect_mono h

lemma expect_le_of_forall_le {f : Ω → ℝ} {c : ℝ} (h : ∀ ω, f ω ≤ c)
    (hc : 0 < Fintype.card Ω) : expect f ≤ c := by
  have := expect_mono (f := f) (g := fun _ => c) h
  rwa [expect_const' c hc] at this

/-! ## Basic properties of `prob` -/

lemma prob_nonneg (E : Set Ω) : 0 ≤ prob E :=
  expect_nonneg fun _ => indicator_one_nonneg E _

lemma prob_le_one (E : Set Ω) (hc : 0 < Fintype.card Ω) : prob E ≤ 1 :=
  expect_le_of_forall_le (f := E.indicator fun _ => (1:ℝ))
    (fun ω => indicator_one_le_one E ω) hc

lemma prob_mono {A B : Set Ω} (h : A ⊆ B) : prob A ≤ prob B := by
  refine expect_mono' fun ω => ?_
  by_cases hA : ω ∈ A
  · rw [Set.indicator_of_mem hA, Set.indicator_of_mem (h hA)]
  · rw [Set.indicator_of_notMem hA]
    exact indicator_one_nonneg B ω

lemma prob_empty : prob (∅ : Set Ω) = 0 := by
  simp [prob, expect]

lemma prob_univ [Nonempty Ω] : prob (Set.univ : Set Ω) = 1 := by
  have h1 : (Set.univ : Set Ω).indicator (fun _ => (1:ℝ)) = fun _ => (1:ℝ) := by
    funext ω
    exact Set.indicator_of_mem (Set.mem_univ ω) _
  rw [prob, h1, expect_const]

lemma prob_compl [Nonempty Ω] (E : Set Ω) : prob Eᶜ = 1 - prob E := by
  have hpt : (Eᶜ).indicator (fun _ => (1:ℝ))
      = (fun _ : Ω => (1:ℝ)) - E.indicator (fun _ => (1:ℝ)) := by
    funext ω
    rw [Pi.sub_apply]
    by_cases h : ω ∈ E
    · rw [Set.indicator_of_mem h, Set.indicator_of_notMem (by simpa using h)]; ring
    · rw [Set.indicator_of_notMem h, Set.indicator_of_mem (by simpa using h)]; ring
  rw [prob, prob, hpt, expect_sub, expect_const]

lemma prob_inter_le_left (A B : Set Ω) : prob (A ∩ B) ≤ prob A :=
  prob_mono Set.inter_subset_left

lemma prob_inter_le_right (A B : Set Ω) : prob (A ∩ B) ≤ prob B :=
  prob_mono Set.inter_subset_right

lemma prob_union_le (A B : Set Ω) : prob (A ∪ B) ≤ prob A + prob B := by
  have hpt : (A ∪ B).indicator (fun _ => (1:ℝ))
      ≤ A.indicator (fun _ => (1:ℝ)) + B.indicator (fun _ => (1:ℝ)) := by
    intro ω
    by_cases hA : ω ∈ A
    · have h1 : (A ∪ B).indicator (fun _ => (1:ℝ)) ω = 1 :=
        Set.indicator_of_mem (s := A ∪ B) (Or.inl hA) _
      have h2 : A.indicator (fun _ => (1:ℝ)) ω = 1 := Set.indicator_of_mem hA _
      rw [Pi.add_apply, h1, h2]
      linarith [indicator_one_nonneg B ω]
    · by_cases hB : ω ∈ B
      · have h1 : (A ∪ B).indicator (fun _ => (1:ℝ)) ω = 1 :=
          Set.indicator_of_mem (s := A ∪ B) (Or.inr hB) _
        have h2 : B.indicator (fun _ => (1:ℝ)) ω = 1 := Set.indicator_of_mem hB _
        have h3 : A.indicator (fun _ => (1:ℝ)) ω = 0 := Set.indicator_of_notMem hA _
        rw [Pi.add_apply, h1, h2, h3]; norm_num
      · have h1 : (A ∪ B).indicator (fun _ => (1:ℝ)) ω = 0 :=
          Set.indicator_of_notMem (s := A ∪ B) (by simp [hA, hB]) _
        have h3 : A.indicator (fun _ => (1:ℝ)) ω = 0 := Set.indicator_of_notMem hA _
        rw [Pi.add_apply, h1, h3]
        linarith [indicator_one_nonneg B ω]
  have h := expect_mono hpt
  rw [expect_add] at h
  rwa [← prob, ← prob, ← prob] at h

lemma prob_iUnion_le {ι : Type*} [Fintype ι] (A : ι → Set Ω) :
    prob (⋃ i, A i) ≤ ∑ i, prob (A i) := by
  have hpt : (⋃ i, A i).indicator (fun _ => (1:ℝ))
      ≤ fun ω => ∑ i, (A i).indicator (fun _ => (1:ℝ)) ω := by
    intro ω
    by_cases h : ω ∈ ⋃ i, A i
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp h
      have h1 : (⋃ i, A i).indicator (fun _ => (1:ℝ)) ω = 1 := Set.indicator_of_mem h _
      have h2 : (A i).indicator (fun _ => (1:ℝ)) ω = 1 := Set.indicator_of_mem hi _
      have hle : (A i).indicator (fun _ => (1:ℝ)) ω
          ≤ ∑ j, (A j).indicator (fun _ => (1:ℝ)) ω :=
        Finset.single_le_sum (fun j _ => indicator_one_nonneg (A j) ω) (Finset.mem_univ i)
      calc (⋃ i, A i).indicator (fun _ => (1:ℝ)) ω = 1 := h1
        _ = (A i).indicator (fun _ => (1:ℝ)) ω := h2.symm
        _ ≤ ∑ j, (A j).indicator (fun _ => (1:ℝ)) ω := hle
    · have h1 : (⋃ i, A i).indicator (fun _ => (1:ℝ)) ω = 0 := Set.indicator_of_notMem h _
      rw [h1]
      exact Finset.sum_nonneg fun i _ => indicator_one_nonneg (A i) ω
  have h := expect_mono hpt
  rw [expect_sum] at h
  rwa [← prob] at h

/-! ## Markov and Chebyshev -/

/-- **Markov's inequality**: for a nonnegative random variable `f` and `c > 0`,
`c · P(c ≤ f) ≤ E f`. -/
theorem mul_prob_le_expect {f : Ω → ℝ} (hf : ∀ ω, 0 ≤ f ω) {c : ℝ} (hc : 0 < c) :
    c * prob {ω | c ≤ f ω} ≤ expect f := by
  have hpt : (fun ω => c * ({ω | c ≤ f ω}).indicator (fun _ => (1:ℝ)) ω) ≤ f := by
    intro ω
    change c * ({ω | c ≤ f ω}).indicator (fun _ => (1:ℝ)) ω ≤ f ω
    by_cases h : c ≤ f ω
    · have h1 : ({ω | c ≤ f ω}).indicator (fun _ => (1:ℝ)) ω = 1 :=
        Set.indicator_of_mem (s := {ω | c ≤ f ω}) h _
      rw [h1, mul_one]; exact h
    · have h1 : ({ω | c ≤ f ω}).indicator (fun _ => (1:ℝ)) ω = 0 :=
        Set.indicator_of_notMem (s := {ω | c ≤ f ω}) h _
      rw [h1, mul_zero]; exact hf ω
  have h := expect_mono hpt
  rw [expect_const_mul] at h
  rwa [← prob] at h

theorem prob_le_expect_div {f : Ω → ℝ} (hf : ∀ ω, 0 ≤ f ω) {c : ℝ} (hc : 0 < c) :
    prob {ω | c ≤ f ω} ≤ expect f / c := by
  rw [le_div_iff₀ hc]
  linarith [mul_prob_le_expect hf hc]

/-- **Chebyshev's inequality**. -/
theorem sq_mul_prob_le_expect_sq (f : Ω → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    t ^ 2 * prob {ω | t ≤ |f ω - expect f|} ≤ expect (fun ω => (f ω - expect f) ^ 2) := by
  have hset : {ω | t ≤ |f ω - expect f|} = {ω | t ^ 2 ≤ (f ω - expect f) ^ 2} := by
    ext ω
    rw [Set.mem_setOf_eq, Set.mem_setOf_eq, sq_le_sq, abs_of_nonneg ht]
  rw [hset]
  rcases eq_or_lt_of_le ht with h0 | ht0
  · subst h0
    have hle : (0:ℝ) ^ 2 * prob {ω | (0:ℝ) ^ 2 ≤ (f ω - expect f) ^ 2} ≤ 0 := by simp
    exact le_trans hle
      (expect_nonneg (f := fun ω : Ω => (f ω - expect f) ^ 2) (fun ω => sq_nonneg _))
  · exact mul_prob_le_expect (f := fun ω => (f ω - expect f) ^ 2)
      (fun ω => sq_nonneg _) (by positivity)

end Work.Deep.Conc
