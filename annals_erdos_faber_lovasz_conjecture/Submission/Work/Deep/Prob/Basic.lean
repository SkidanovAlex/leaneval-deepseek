/-
# Finite probability spaces

This module sets up the real-valued finite-probability-space layer used throughout
`Submission/Work/Deep/Prob/`.  All later modules (`Spaces`, `Indep`, `Chernoff`, `LLL`,
`Nibble`) build on the definitions here and on the basic `Finset`-level API proved in this
file.

## Design

* A finite probability space is a structure `FinProbSpace Ω` on a `Fintype Ω`, carrying a
  mass function `mass : Ω → ℝ` with `0 ≤ mass ω` and `∑ ω, mass ω = 1`.
* Events are `Set Ω`: this makes complements, intersections and the union bound frictionless
  (`Set.indicator` is used internally, so no `DecidablePred` hypotheses ever appear).
  `probBool` is a Boolean-event variant for callers who prefer `Ω → Bool`.
* `P.prob A` is the total mass of `A` and `P.expect X` is the expectation of `X : Ω → ℝ`.
* `pattern A : Ω → (ι → Bool)` is the outcome vector of an event family, `IndepEvents P A`
  says that the joint law of `pattern A` is the product of the marginals, and `IndepFun P X`
  is the analogous notion for real-valued random variables.

Everything is stated with explicit finite sums, so the proofs reduce to real arithmetic on
`Finset`s and pointwise case analysis.
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Set.Piecewise
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

set_option autoImplicit false

open scoped BigOperators
open Finset

namespace Work.Deep.Prob

/-- A **finite probability space**: a finite sample space `Ω` (a `Fintype`) together with a
real-valued probability mass function which is nonnegative and has total mass one. -/
structure FinProbSpace (Ω : Type*) [Fintype Ω] where
  /-- The probability mass of a sample point. -/
  mass : Ω → ℝ
  /-- Masses are nonnegative. -/
  mass_nonneg : ∀ ω, 0 ≤ mass ω
  /-- The masses sum to one. -/
  mass_sum : ∑ ω, mass ω = 1

namespace FinProbSpace

variable {Ω : Type*} [Fintype Ω]

/-- The probability of an event, as the total mass of its elements. -/
noncomputable def prob (P : FinProbSpace Ω) (A : Set Ω) : ℝ :=
  ∑ ω, A.indicator P.mass ω

/-- The probability of a Boolean event. -/
noncomputable def probBool (P : FinProbSpace Ω) (A : Ω → Bool) : ℝ :=
  P.prob {ω | A ω = true}

/-- The expectation of a real-valued random variable. -/
noncomputable def expect (P : FinProbSpace Ω) (X : Ω → ℝ) : ℝ :=
  ∑ ω, P.mass ω * X ω

theorem ind_of_mem (P : FinProbSpace Ω) {A : Set Ω} {ω : Ω} (h : ω ∈ A) :
    A.indicator P.mass ω = P.mass ω :=
  Set.indicator_of_mem h P.mass

theorem ind_of_notMem (P : FinProbSpace Ω) {A : Set Ω} {ω : Ω} (h : ω ∉ A) :
    A.indicator P.mass ω = 0 :=
  Set.indicator_of_notMem h P.mass

/-! ## Pointwise indicator lemmas -/

theorem ind_nonneg (P : FinProbSpace Ω) (A : Set Ω) (ω : Ω) : 0 ≤ A.indicator P.mass ω := by
  by_cases h : ω ∈ A
  · rw [ind_of_mem P h]; exact P.mass_nonneg ω
  · rw [ind_of_notMem P h]

theorem ind_le_mass (P : FinProbSpace Ω) (A : Set Ω) (ω : Ω) :
    A.indicator P.mass ω ≤ P.mass ω := by
  by_cases h : ω ∈ A
  · rw [ind_of_mem P h]
  · rw [ind_of_notMem P h]; exact P.mass_nonneg ω

theorem ind_compl_add (P : FinProbSpace Ω) (A : Set Ω) (ω : Ω) :
    A.indicator P.mass ω + Aᶜ.indicator P.mass ω = P.mass ω := by
  by_cases h : ω ∈ A
  · rw [ind_of_mem P h, ind_of_notMem P (by simpa using h)]; ring
  · rw [ind_of_notMem P h, ind_of_mem P (by simpa using h)]; ring

theorem ind_mono (P : FinProbSpace Ω) {A B : Set Ω} (h : A ⊆ B) (ω : Ω) :
    A.indicator P.mass ω ≤ B.indicator P.mass ω := by
  by_cases hA : ω ∈ A
  · rw [ind_of_mem P hA, ind_of_mem P (h hA)]
  · by_cases hB : ω ∈ B
    · rw [ind_of_notMem P hA, ind_of_mem P hB]; exact P.mass_nonneg ω
    · rw [ind_of_notMem P hA, ind_of_notMem P hB]

theorem ind_union_le (P : FinProbSpace Ω) (A B : Set Ω) (ω : Ω) :
    (A ∪ B).indicator P.mass ω ≤ A.indicator P.mass ω + B.indicator P.mass ω := by
  by_cases hA : ω ∈ A
  · rw [ind_of_mem P (Or.inl hA), ind_of_mem P hA]; linarith [P.mass_nonneg ω, ind_nonneg P B ω]
  · by_cases hB : ω ∈ B
    · rw [ind_of_mem P (Or.inr hB), ind_of_mem P hB]; linarith [P.mass_nonneg ω, ind_nonneg P A ω]
    · rw [ind_of_notMem P (by simp [hA, hB]), ind_of_notMem P hA, ind_of_notMem P hB]
      norm_num

theorem ind_inter_compl (P : FinProbSpace Ω) (A B : Set Ω) (ω : Ω) :
    (B ∩ Aᶜ).indicator P.mass ω = B.indicator P.mass ω - (B ∩ A).indicator P.mass ω := by
  by_cases hB : ω ∈ B
  · by_cases hA : ω ∈ A
    · rw [ind_of_notMem P (by simp [hA]), ind_of_mem P hB,
        ind_of_mem P (show ω ∈ B ∩ A from ⟨hB, hA⟩)]; ring
    · rw [ind_of_mem P (show ω ∈ B ∩ Aᶜ from ⟨hB, hA⟩), ind_of_mem P hB,
        ind_of_notMem P (by simp [hA])]; ring
  · rw [ind_of_notMem P (by simp [hB]), ind_of_notMem P hB,
      ind_of_notMem P (by simp [hB])]; ring

theorem ind_iUnion_le_sum (P : FinProbSpace Ω) {ι : Type*} (s : Finset ι) (A : ι → Set Ω)
    (ω : Ω) : (⋃ i ∈ s, A i).indicator P.mass ω ≤ ∑ i ∈ s, (A i).indicator P.mass ω := by
  by_cases h : ω ∈ ⋃ i ∈ s, A i
  · rw [ind_of_mem P h]
    obtain ⟨i, hi, hiω⟩ := Set.mem_iUnion₂.mp h
    rw [← ind_of_mem P hiω (A := A i)]
    exact Finset.single_le_sum (f := fun i => (A i).indicator P.mass ω)
      (fun i _ => ind_nonneg P (A i) ω) hi
  · rw [ind_of_notMem P h]
    exact Finset.sum_nonneg fun i _ => ind_nonneg P (A i) ω

/-! ## The API for `prob` -/

theorem prob_nonneg (P : FinProbSpace Ω) (A : Set Ω) : 0 ≤ P.prob A :=
  Finset.sum_nonneg fun ω _ => ind_nonneg P A ω

theorem prob_mono (P : FinProbSpace Ω) {A B : Set Ω} (h : A ⊆ B) : P.prob A ≤ P.prob B :=
  Finset.sum_le_sum fun ω _ => ind_mono P h ω

theorem prob_univ (P : FinProbSpace Ω) : P.prob Set.univ = 1 := by
  rw [prob]
  simp only [Set.indicator_univ]
  exact P.mass_sum

theorem prob_empty (P : FinProbSpace Ω) : P.prob (∅ : Set Ω) = 0 := by
  rw [prob]
  simp

theorem prob_le_one (P : FinProbSpace Ω) (A : Set Ω) : P.prob A ≤ 1 := by
  calc P.prob A ≤ P.prob Set.univ := prob_mono P (Set.subset_univ A)
    _ = 1 := prob_univ P

theorem prob_compl (P : FinProbSpace Ω) (A : Set Ω) : P.prob Aᶜ = 1 - P.prob A := by
  have h : P.prob A + P.prob Aᶜ = 1 := by
    rw [prob, prob, ← Finset.sum_add_distrib]
    rw [← P.mass_sum]
    exact Finset.sum_congr rfl fun ω _ => ind_compl_add P A ω
  linarith

theorem prob_inter_compl (P : FinProbSpace Ω) (A B : Set Ω) :
    P.prob (B ∩ Aᶜ) = P.prob B - P.prob (B ∩ A) := by
  rw [prob, prob, prob, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun ω _ => ind_inter_compl P A B ω

theorem prob_sdiff (P : FinProbSpace Ω) {A B : Set Ω} (h : B ⊆ A) :
    P.prob (A \ B) = P.prob A - P.prob B := by
  have hset : A \ B = A ∩ Bᶜ := rfl
  rw [hset, prob_inter_compl P B A, Set.inter_eq_right.mpr h]

theorem prob_union_le (P : FinProbSpace Ω) (A B : Set Ω) :
    P.prob (A ∪ B) ≤ P.prob A + P.prob B := by
  rw [prob, prob, prob, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun ω _ => ind_union_le P A B ω

/-- **Union bound** (Finset-indexed form). -/
theorem prob_biUnion_le_sum (P : FinProbSpace Ω) {ι : Type*} (s : Finset ι) (A : ι → Set Ω) :
    P.prob (⋃ i ∈ s, A i) ≤ ∑ i ∈ s, P.prob (A i) := by
  calc P.prob (⋃ i ∈ s, A i) ≤ ∑ ω, ∑ i ∈ s, (A i).indicator P.mass ω :=
        Finset.sum_le_sum fun ω _ => ind_iUnion_le_sum P s A ω
    _ = ∑ i ∈ s, ∑ ω, (A i).indicator P.mass ω := Finset.sum_comm
    _ = ∑ i ∈ s, P.prob (A i) := by simp only [prob]

/-- **Union bound** (Fintype-indexed form). -/
theorem prob_iUnion_le_sum (P : FinProbSpace Ω) {ι : Type*} [Fintype ι] (A : ι → Set Ω) :
    P.prob (⋃ i, A i) ≤ ∑ i, P.prob (A i) := by
  simpa using prob_biUnion_le_sum P (Finset.univ : Finset ι) A

theorem prob_iInter_compl (P : FinProbSpace Ω) {ι : Type*} [Fintype ι] (A : ι → Set Ω) :
    P.prob (⋂ i, (A i)ᶜ) = 1 - P.prob (⋃ i, A i) := by
  rw [← Set.compl_iUnion, prob_compl]

theorem probBool_eq_prob (P : FinProbSpace Ω) (A : Ω → Bool) :
    P.probBool A = P.prob {ω | A ω = true} := rfl

theorem probBool_eq_sum (P : FinProbSpace Ω) (A : Ω → Bool) :
    P.probBool A = ∑ ω, ({ω | A ω = true} : Set Ω).indicator P.mass ω := rfl

/-! ## The API for `expect` -/

theorem expect_indicator (P : FinProbSpace Ω) (A : Set Ω) :
    P.expect (fun ω => A.indicator (fun _ => (1 : ℝ)) ω) = P.prob A := by
  rw [expect, prob]
  exact Finset.sum_congr rfl fun ω _ => by
    by_cases h : ω ∈ A <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]

theorem expect_nonneg (P : FinProbSpace Ω) {X : Ω → ℝ} (h : ∀ ω, 0 ≤ X ω) :
    0 ≤ P.expect X :=
  Finset.sum_nonneg fun ω _ => mul_nonneg (P.mass_nonneg ω) (h ω)

theorem expect_mono (P : FinProbSpace Ω) {X Y : Ω → ℝ} (h : ∀ ω, X ω ≤ Y ω) :
    P.expect X ≤ P.expect Y :=
  Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (h ω) (P.mass_nonneg ω)

theorem expect_const (P : FinProbSpace Ω) (c : ℝ) : P.expect (fun _ => c) = c := by
  rw [expect, ← Finset.sum_mul, P.mass_sum, one_mul]

theorem expect_add (P : FinProbSpace Ω) (X Y : Ω → ℝ) :
    P.expect (fun ω => X ω + Y ω) = P.expect X + P.expect Y := by
  rw [expect, expect, expect, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun ω _ => by ring

theorem expect_sub (P : FinProbSpace Ω) (X Y : Ω → ℝ) :
    P.expect (fun ω => X ω - Y ω) = P.expect X - P.expect Y := by
  rw [expect, expect, expect, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun ω _ => by ring

theorem expect_smul (P : FinProbSpace Ω) (c : ℝ) (X : Ω → ℝ) :
    P.expect (fun ω => c * X ω) = c * P.expect X := by
  rw [expect, expect, Finset.mul_sum]
  exact Finset.sum_congr rfl fun ω _ => by ring

theorem expect_sum (P : FinProbSpace Ω) {ι : Type*} [Fintype ι] (X : ι → Ω → ℝ) :
    P.expect (fun ω => ∑ i, X i ω) = ∑ i, P.expect (X i) := by
  simp only [expect, Finset.mul_sum]
  exact Finset.sum_comm

theorem expect_sum_finset (P : FinProbSpace Ω) {ι : Type*} (s : Finset ι) (X : ι → Ω → ℝ) :
    P.expect (fun ω => ∑ i ∈ s, X i ω) = ∑ i ∈ s, P.expect (X i) := by
  simp only [expect, Finset.mul_sum]
  exact Finset.sum_comm

/-- `∑ ω, mass ω = 1` forces some sample point to have positive mass. -/
theorem exists_mass_pos (P : FinProbSpace Ω) : ∃ ω, 0 < P.mass ω := by
  by_contra h
  push Not at h
  have hzero : ∑ ω, P.mass ω = 0 :=
    Finset.sum_eq_zero fun ω _ => le_antisymm (h ω) (P.mass_nonneg ω)
  rw [P.mass_sum] at hzero
  norm_num at hzero

/-- **Markov's inequality**: for a nonnegative random variable `X` and `t > 0`,
`ℙ[X ≥ t] ≤ E X / t`. -/
theorem markov (P : FinProbSpace Ω) {X : Ω → ℝ} (hX : ∀ ω, 0 ≤ X ω) {t : ℝ} (ht : 0 < t) :
    P.prob {ω | t ≤ X ω} ≤ P.expect X / t := by
  have h : ∀ ω, ({ω | t ≤ X ω} : Set Ω).indicator P.mass ω ≤ P.mass ω * X ω / t := by
    intro ω
    by_cases hmem : t ≤ X ω
    · rw [ind_of_mem P hmem, le_div_iff₀ ht]
      nlinarith [P.mass_nonneg ω, hmem]
    · rw [ind_of_notMem P hmem]
      exact div_nonneg (mul_nonneg (P.mass_nonneg ω) (hX ω)) ht.le
  calc P.prob {ω | t ≤ X ω} ≤ ∑ ω, P.mass ω * X ω / t := Finset.sum_le_sum fun ω _ => h ω
    _ = P.expect X / t := by rw [expect, Finset.sum_div]

/-- Some sample point has `X ω ≤ E X`. -/
theorem exists_le_expect (P : FinProbSpace Ω) (X : Ω → ℝ) : ∃ ω, X ω ≤ P.expect X := by
  by_contra h
  push Not at h
  obtain ⟨ω₀, hω₀⟩ := P.exists_mass_pos
  have hlt : (∑ ω, P.mass ω * P.expect X) < (∑ ω, P.mass ω * X ω) :=
    Finset.sum_lt_sum (fun ω _ => mul_le_mul_of_nonneg_left (le_of_lt (h ω)) (P.mass_nonneg ω))
      ⟨ω₀, Finset.mem_univ ω₀, mul_lt_mul_of_pos_left (h ω₀) hω₀⟩
  have hEq1 : (∑ ω, P.mass ω * P.expect X) = P.expect X := by
    rw [← Finset.sum_mul, P.mass_sum, one_mul]
  have hEq2 : (∑ ω, P.mass ω * X ω) = P.expect X := rfl
  rw [hEq1, hEq2] at hlt
  exact lt_irrefl _ hlt

/-- If `E X < b` then some sample point has `X ω < b`. -/
theorem exists_lt_of_expect_lt (P : FinProbSpace Ω) (X : Ω → ℝ) {b : ℝ} (h : P.expect X < b) :
    ∃ ω, X ω < b := by
  by_contra hc
  push Not at hc
  have hb : b ≤ P.expect X := by
    have : (∑ ω, P.mass ω * b) ≤ P.expect X :=
      Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hc ω) (P.mass_nonneg ω)
    rwa [← Finset.sum_mul, P.mass_sum, one_mul] at this
  linarith

/-- A positive-probability event contains a sample point. -/
theorem exists_of_prob_pos (P : FinProbSpace Ω) {A : Set Ω} (h : 0 < P.prob A) :
    ∃ ω, ω ∈ A := by
  by_contra hc
  push Not at hc
  have hzero : P.prob A = 0 := by
    rw [prob]
    exact Finset.sum_eq_zero fun ω _ => by
      rw [Set.indicator_of_notMem (hc ω)]
  linarith

theorem prob_pos_iff (P : FinProbSpace Ω) {A : Set Ω} :
    0 < P.prob A ↔ ∃ ω ∈ A, 0 < P.mass ω := by
  constructor
  · intro h
    by_contra hc
    push Not at hc
    have hzero : P.prob A = 0 := by
      rw [prob]
      exact Finset.sum_eq_zero fun ω _ => by
        by_cases hmem : ω ∈ A
        · rw [Set.indicator_of_mem hmem]
          exact le_antisymm (hc ω hmem) (P.mass_nonneg ω)
        · rw [Set.indicator_of_notMem hmem]
    linarith
  · rintro ⟨ω, hωA, hω⟩
    have hle : A.indicator P.mass ω ≤ P.prob A :=
      Finset.single_le_sum (f := fun ω => A.indicator P.mass ω)
        (fun ω _ => ind_nonneg P A ω) (Finset.mem_univ ω)
    rw [Set.indicator_of_mem hωA] at hle
    exact lt_of_lt_of_le hω hle

/-! ## First moment / alteration -/

/-- **First moment (alteration) principle.** If the expected number of `A i` occurring is
less than one, then some sample point avoids every `A i`. -/
theorem alteration (P : FinProbSpace Ω) {ι : Type*} [Fintype ι] (A : ι → Set Ω)
    (h : ∑ i, P.prob (A i) < 1) : ∃ ω, ∀ i, ω ∉ A i := by
  have hbad : P.prob (⋃ i, A i) < 1 := lt_of_le_of_lt (P.prob_iUnion_le_sum A) h
  have hpos : 0 < P.prob (⋂ i, (A i)ᶜ) := by
    rw [prob_iInter_compl]; linarith
  obtain ⟨ω, hω⟩ := P.exists_of_prob_pos hpos
  exact ⟨ω, fun i => Set.mem_iInter.mp hω i⟩

/-- **First moment principle, Finset-indexed form.** -/
theorem alteration_finset (P : FinProbSpace Ω) {ι : Type*} (s : Finset ι) (A : ι → Set Ω)
    (h : ∑ i ∈ s, P.prob (A i) < 1) : ∃ ω, ∀ i ∈ s, ω ∉ A i := by
  have hbad : P.prob (⋃ i ∈ s, A i) < 1 := lt_of_le_of_lt (P.prob_biUnion_le_sum s A) h
  have hpos : 0 < P.prob (⋃ i ∈ s, A i)ᶜ := by
    rw [prob_compl]; linarith
  obtain ⟨ω, hω⟩ := P.exists_of_prob_pos hpos
  exact ⟨ω, fun i hi hiA => hω (Set.mem_iUnion₂.mpr ⟨i, hi, hiA⟩)⟩

/-- **Delete-and-repair, cost form.** If the cost of the cleanup is bounded by `c` times the
number of bad events, and the expected number of bad events is so small that `c · ∑ ℙ[A i] < b`,
then there is a sample point whose cleanup cost is less than `b`. -/
theorem delete_repair_cost (P : FinProbSpace Ω) {ι : Type*} [Fintype ι] (A : ι → Set Ω)
    (cost : Ω → ℝ) (c b : ℝ)
    (hcost : ∀ ω, cost ω ≤ c * ∑ i, (A i).indicator (fun _ => (1 : ℝ)) ω)
    (hbad : c * ∑ i, P.prob (A i) < b) : ∃ ω, cost ω < b := by
  have h1 : P.expect cost ≤ P.expect (fun ω => c * ∑ i, (A i).indicator (fun _ => (1 : ℝ)) ω) :=
    P.expect_mono hcost
  have h2 : P.expect (fun ω => c * ∑ i, (A i).indicator (fun _ => (1 : ℝ)) ω)
      = c * ∑ i, P.prob (A i) := by
    rw [P.expect_smul, P.expect_sum]
    exact congrArg _ (Finset.sum_congr rfl fun i _ => P.expect_indicator (A i))
  exact P.exists_lt_of_expect_lt cost (lt_of_le_of_lt (h2 ▸ h1) hbad)

/-! ## Independence -/

/-- The **outcome pattern** of a family of events: `pattern A ω i` is `true` iff `ω ∈ A i`. -/
noncomputable def pattern {ι : Type*} (A : ι → Set Ω) : Ω → (ι → Bool) :=
  fun ω i => (A i).boolIndicator ω

omit [Fintype Ω] in
theorem pattern_eq_true_iff {ι : Type*} (A : ι → Set Ω) (ω : Ω) (i : ι) :
    pattern A ω i = true ↔ ω ∈ A i :=
  ((A i).mem_iff_boolIndicator ω).symm

omit [Fintype Ω] in
theorem pattern_eq_false_iff {ι : Type*} (A : ι → Set Ω) (ω : Ω) (i : ι) :
    pattern A ω i = false ↔ ω ∉ A i :=
  ((A i).notMem_iff_boolIndicator ω).symm

/-- A family of events is **independent** if the joint law of the outcome pattern is the
product of the marginals. -/
def IndepEvents (P : FinProbSpace Ω) {ι : Type*} [Fintype ι] (A : ι → Set Ω) : Prop :=
  ∀ s : ι → Bool,
    P.prob (⋂ i, if s i then A i else (A i)ᶜ) = ∏ i, P.prob (if s i then A i else (A i)ᶜ)

/-- A family of real-valued random variables is **independent** if every joint atom
probability factorizes. -/
def IndepFun (P : FinProbSpace Ω) {ι : Type*} [Fintype ι] (X : ι → Ω → ℝ) : Prop :=
  ∀ s : ι → ℝ, P.prob {ω | ∀ i, X i ω = s i} = ∏ i, P.prob {ω | X i ω = s i}

/-- `B` is independent of the conjunction of the complements of `A` over `T`. -/
def indepOfCompls (P : FinProbSpace Ω) {ι : Type*} (B : Set Ω) (A : ι → Set Ω)
    (T : Finset ι) : Prop :=
  P.prob (B ∩ ⋂ j ∈ T, (A j)ᶜ) = P.prob B * P.prob (⋂ j ∈ T, (A j)ᶜ)

/-- The **lopsided** dependence hypothesis: `B` is negatively correlated with the conjunction
of the complements of `A` over `T`. -/
def LopsidedIndep (P : FinProbSpace Ω) {ι : Type*} (B : Set Ω) (A : ι → Set Ω)
    (T : Finset ι) : Prop :=
  P.prob (B ∩ ⋂ j ∈ T, (A j)ᶜ) ≤ P.prob B * P.prob (⋂ j ∈ T, (A j)ᶜ)

theorem indepOfCompls.lopsided (P : FinProbSpace Ω) {ι : Type*} {B : Set Ω} {A : ι → Set Ω}
    {T : Finset ι} (h : indepOfCompls P B A T) : LopsidedIndep P B A T := le_of_eq h

end FinProbSpace

end Work.Deep.Prob
