/-
# A minimal finite probability layer, and the product law of random colourings

This module is the probabilistic foundation of the proof of `SparseGraphStatement`
(`Submission/Deep/Reed.lean`) carried out under `Submission/Work/Deep/Sparse/`.

* `FinSpace Ω` — a finite probability space on a `Fintype Ω`, given by a mass function.
  Events are `Set Ω`, `prob` is the total mass, `expect` the mean.
* `FinSpace.uniform` — the uniform measure on a nonempty finite type.
* `colSpace V k` — the uniform measure on the colourings `V → Fin k` (one colour per vertex,
  chosen independently and uniformly).  This is the sample space of the *naive colouring
  procedure* (Molloy–Reed, Chapter 10; Bruhn–Joos; Bonamy–Perrett–Postle, Section 3).
* `colSpace_prob_pi` — **the product law**: the probability that each coordinate `v` of the
  random colouring lies in a prescribed set `A v` is `∏ v, |A v| / k`.  Every probability
  computation of the naive colouring procedure is a corollary of this single identity.
* `prob_single_and_avoid`, `prob_two_and_avoid` — the two consequences used in the
  expectation computations: the probability that prescribed vertices take a prescribed
  colour `c` while a specified set `T` of other vertices avoids the colour `c`.

Later modules of the directory (`ProbModel`, `ProbExpect`, …) build the naive colouring
procedure on top of this file.
-/
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Set.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped BigOperators

namespace Work.Deep.Sparse

/-! ## 1. Finite probability spaces -/

/-- A **finite probability space**: a finite sample space with a real mass function which is
nonnegative and has total mass one. -/
structure FinSpace (Ω : Type*) [Fintype Ω] where
  /-- The probability mass of a sample point. -/
  mass : Ω → ℝ
  mass_nonneg : ∀ ω, 0 ≤ mass ω
  mass_sum : ∑ ω, mass ω = 1

namespace FinSpace

variable {Ω : Type*} [Fintype Ω]

/-- The probability of an event. -/
noncomputable def prob (P : FinSpace Ω) (A : Set Ω) : ℝ := ∑ ω, A.indicator P.mass ω

/-- The expectation of a real-valued random variable. -/
noncomputable def expect (P : FinSpace Ω) (X : Ω → ℝ) : ℝ := ∑ ω, P.mass ω * X ω

theorem ind_nonneg (P : FinSpace Ω) (A : Set Ω) (ω : Ω) : 0 ≤ A.indicator P.mass ω := by
  by_cases h : ω ∈ A
  · rw [Set.indicator_of_mem h]; exact P.mass_nonneg ω
  · rw [Set.indicator_of_notMem h]

theorem ind_le_mass (P : FinSpace Ω) (A : Set Ω) (ω : Ω) :
    A.indicator P.mass ω ≤ P.mass ω := by
  by_cases h : ω ∈ A
  · rw [Set.indicator_of_mem h]
  · rw [Set.indicator_of_notMem h]; exact P.mass_nonneg ω

theorem ind_compl_add (P : FinSpace Ω) (A : Set Ω) (ω : Ω) :
    A.indicator P.mass ω + Aᶜ.indicator P.mass ω = P.mass ω := by
  by_cases h : ω ∈ A
  · rw [Set.indicator_of_mem h, Set.indicator_of_notMem (by simpa using h)]; ring
  · rw [Set.indicator_of_notMem h, Set.indicator_of_mem (by simpa using h)]; ring

theorem prob_nonneg (P : FinSpace Ω) (A : Set Ω) : 0 ≤ P.prob A :=
  Finset.sum_nonneg fun ω _ => ind_nonneg P A ω

theorem prob_univ (P : FinSpace Ω) : P.prob Set.univ = 1 := by
  rw [prob, Set.indicator_univ]; exact P.mass_sum

theorem prob_mono (P : FinSpace Ω) {A B : Set Ω} (h : A ⊆ B) : P.prob A ≤ P.prob B := by
  refine Finset.sum_le_sum fun ω _ => ?_
  by_cases hA : ω ∈ A
  · rw [Set.indicator_of_mem hA, Set.indicator_of_mem (h hA)]
  · rw [Set.indicator_of_notMem hA]
    exact ind_nonneg P B ω

theorem prob_le_one (P : FinSpace Ω) (A : Set Ω) : P.prob A ≤ 1 := by
  calc P.prob A ≤ P.prob Set.univ := prob_mono P (Set.subset_univ A)
    _ = 1 := prob_univ P

theorem prob_compl (P : FinSpace Ω) (A : Set Ω) : P.prob Aᶜ = 1 - P.prob A := by
  have h : P.prob A + P.prob Aᶜ = 1 := by
    rw [prob, prob, ← Finset.sum_add_distrib, ← P.mass_sum]
    exact Finset.sum_congr rfl fun ω _ => ind_compl_add P A ω
  linarith

/-- Additivity of `prob` over two disjoint events. -/
theorem prob_union_of_disjoint (P : FinSpace Ω) {A B : Set Ω} (h : Disjoint A B) :
    P.prob (A ∪ B) = P.prob A + P.prob B := by
  rw [prob, prob, prob, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun ω _ => by rw [Set.indicator_union_of_disjoint h]

/-- Additivity of `prob` over a family of pairwise disjoint events, indexed by a `Finset`. -/
theorem prob_biUnion_disjoint (P : FinSpace Ω) {ι : Type*} (s : Finset ι) (A : ι → Set Ω)
    (h : (s : Set ι).PairwiseDisjoint A) :
    P.prob (⋃ i ∈ s, A i) = ∑ i ∈ s, P.prob (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [prob]
  | insert a s ha ih =>
      have hdisj : Disjoint (A a) (⋃ i ∈ s, A i) := by
        rw [Set.disjoint_left]
        intro x hxa hxs
        obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hxs
        have hne : (a : ι) ≠ i := by rintro rfl; exact ha hi
        have hd : Disjoint (A a) (A i) :=
          h (Finset.mem_insert_self a s) (Finset.mem_insert.mpr (Or.inr hi)) hne
        rw [Set.disjoint_left] at hd
        exact hd hxa hxi
      have hpair' : ((s : Finset ι) : Set ι).PairwiseDisjoint A := by
        intro i hi j hj hij
        exact h (Finset.mem_insert.mpr (Or.inr hi)) (Finset.mem_insert.mpr (Or.inr hj)) hij
      rw [Finset.set_biUnion_insert, prob_union_of_disjoint P hdisj, ih hpair',
        Finset.sum_insert ha]

theorem prob_sdiff (P : FinSpace Ω) {A B : Set Ω} (h : B ⊆ A) :
    P.prob (A \ B) = P.prob A - P.prob B := by
  have hdisj : Disjoint (A \ B) B := by
    rw [Set.disjoint_left]
    exact fun x hx hxB => hx.2 hxB
  have hunion : A \ B ∪ B = A := by
    ext x
    constructor
    · rintro (⟨hxA, _⟩ | hxB)
      · exact hxA
      · exact h hxB
    · intro hxA
      by_cases hxB : x ∈ B
      · exact Or.inr hxB
      · exact Or.inl ⟨hxA, hxB⟩
  have hh := prob_union_of_disjoint P hdisj
  rw [hunion] at hh
  linarith

/-! ## The API for `expect` -/

theorem expect_add (P : FinSpace Ω) (X Y : Ω → ℝ) :
    P.expect (fun ω => X ω + Y ω) = P.expect X + P.expect Y := by
  rw [expect, expect, expect, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun ω _ => by ring

theorem expect_sub (P : FinSpace Ω) (X Y : Ω → ℝ) :
    P.expect (fun ω => X ω - Y ω) = P.expect X - P.expect Y := by
  rw [expect, expect, expect, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun ω _ => by ring

theorem expect_const (P : FinSpace Ω) (c : ℝ) : P.expect (fun _ => c) = c := by
  rw [expect, ← Finset.sum_mul, P.mass_sum, one_mul]

theorem expect_sum {ι : Type*} [Fintype ι] (P : FinSpace Ω) (X : ι → Ω → ℝ) :
    P.expect (fun ω => ∑ i, X i ω) = ∑ i, P.expect (X i) := by
  simp only [expect, Finset.mul_sum]
  exact Finset.sum_comm

theorem expect_nonneg (P : FinSpace Ω) {X : Ω → ℝ} (h : ∀ ω, 0 ≤ X ω) : 0 ≤ P.expect X :=
  Finset.sum_nonneg fun ω _ => mul_nonneg (P.mass_nonneg ω) (h ω)

theorem expect_mono (P : FinSpace Ω) {X Y : Ω → ℝ} (h : ∀ ω, X ω ≤ Y ω) :
    P.expect X ≤ P.expect Y :=
  Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (h ω) (P.mass_nonneg ω)

/-- Some sample point has positive mass. -/
theorem exists_mass_pos (P : FinSpace Ω) : ∃ ω, 0 < P.mass ω := by
  by_contra h
  push Not at h
  have hzero : ∑ ω, P.mass ω = 0 :=
    Finset.sum_eq_zero fun ω _ => le_antisymm (h ω) (P.mass_nonneg ω)
  rw [P.mass_sum] at hzero
  norm_num at hzero

/-- A positive-probability event contains a sample point. -/
theorem exists_of_prob_pos (P : FinSpace Ω) {A : Set Ω} (h : 0 < P.prob A) : ∃ ω, ω ∈ A := by
  by_contra hc
  push Not at hc
  have hzero : P.prob A = 0 := by
    rw [prob]
    exact Finset.sum_eq_zero fun ω _ => by
      rw [Set.indicator_of_notMem (hc ω)]
  linarith

/-- If `E X < b` then some sample point has `X ω < b`. -/
theorem exists_lt_of_expect_lt (P : FinSpace Ω) (X : Ω → ℝ) {b : ℝ} (h : P.expect X < b) :
    ∃ ω, X ω < b := by
  by_contra hc
  push Not at hc
  have hb : b ≤ P.expect X := by
    have : (∑ ω, P.mass ω * b) ≤ P.expect X :=
      Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hc ω) (P.mass_nonneg ω)
    rwa [← Finset.sum_mul, P.mass_sum, one_mul] at this
  linarith

end FinSpace

/-! ## 2. The uniform measure and counting -/

namespace FinSpace

variable {Ω : Type*} [Fintype Ω]

/-- The uniform probability measure on a nonempty finite type. -/
noncomputable def uniform (Ω : Type*) [Fintype Ω] [Nonempty Ω] : FinSpace Ω where
  mass _ := (Fintype.card Ω : ℝ)⁻¹
  mass_nonneg _ := by positivity
  mass_sum := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have h : (Fintype.card Ω : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    field_simp

@[simp] theorem uniform_mass [Nonempty Ω] (ω : Ω) :
    (uniform Ω).mass ω = (Fintype.card Ω : ℝ)⁻¹ := rfl

@[simp] theorem uniform_mass' [Nonempty Ω] : (uniform Ω).mass = fun _ => (Fintype.card Ω : ℝ)⁻¹ :=
  rfl

/-- On a space of constant mass `m`, the probability of an event given by a `Finset` is its
cardinality times `m`. -/
theorem prob_of_const_mass (P : FinSpace Ω) {m : ℝ} (h : P.mass = fun _ => m) (s : Finset Ω) :
    P.prob (↑s : Set Ω) = (s.card : ℝ) * m := by
  classical
  have hterm : ∀ ω : Ω, (↑s : Set Ω).indicator P.mass ω = if ω ∈ s then m else 0 := by
    intro ω
    by_cases hω : ω ∈ s
    · rw [Set.indicator_of_mem (by simpa using hω), congrFun h ω, if_pos hω]
    · rw [Set.indicator_of_notMem (by simpa using hω), if_neg hω]
  calc P.prob (↑s : Set Ω) = ∑ ω, (if ω ∈ s then m else 0) := by
        rw [prob]; exact Finset.sum_congr rfl fun ω _ => hterm ω
    _ = ∑ _ω ∈ s, m := by
        rw [← Finset.sum_filter]
        exact Finset.sum_congr (by rw [Finset.filter_mem_eq_inter, Finset.univ_inter])
          (fun _ _ => rfl)
    _ = (s.card : ℝ) * m := by rw [Finset.sum_const, nsmul_eq_mul]

end FinSpace

/-! ## 3. The random colouring of a finite vertex set -/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The uniform measure on the colourings `V → Fin k`: the sample space of the naive
colouring procedure. -/
noncomputable def colSpace (k : ℕ) [Nonempty (V → Fin k)] : FinSpace (V → Fin k) :=
  FinSpace.uniform (V → Fin k)

@[simp] theorem colSpace_mass {k : ℕ} [Nonempty (V → Fin k)] :
    (colSpace (V := V) k).mass = fun _ => (Fintype.card (V → Fin k) : ℝ)⁻¹ := rfl

theorem card_colSpace {k : ℕ} : Fintype.card (V → Fin k) = k ^ Fintype.card V := by
  rw [Fintype.card_pi]
  simp [Fintype.card_fin]

/-- **The product law of the random colouring.**  For prescribed sets `A v` of allowed colours,
the probability that the random colouring takes its value at `v` inside `A v` for every `v` is
the product of the marginal probabilities `|A v| / k`. -/
theorem colSpace_prob_pi {k : ℕ} [Nonempty (V → Fin k)] (A : V → Finset (Fin k)) :
    (colSpace k).prob (↑(Fintype.piFinset A) : Set (V → Fin k))
      = ∏ v, ((A v).card : ℝ) / (k : ℝ) := by
  classical
  rw [FinSpace.prob_of_const_mass (colSpace (V := V) k) colSpace_mass, Fintype.card_piFinset,
    card_colSpace, Finset.prod_div_distrib, Nat.cast_prod, Finset.prod_const, Finset.card_univ,
    Nat.cast_pow]
  field_simp

/-- The complement of a colour in `Fin k`, as a `Finset`. -/
def colourCompl {k : ℕ} (c : Fin k) : Finset (Fin k) := Finset.univ.erase c

@[simp] theorem mem_colourCompl {k : ℕ} {c c' : Fin k} :
    c' ∈ colourCompl c ↔ c' ≠ c := by
  simp [colourCompl]

theorem card_colourCompl {k : ℕ} (c : Fin k) : (colourCompl c).card = k - 1 := by
  rw [colourCompl, Finset.card_erase_of_mem (Finset.mem_univ c), Finset.card_univ,
    Fintype.card_fin]

theorem card_colourCompl_cast {k : ℕ} (hk : 0 < k) (c : Fin k) :
    ((colourCompl c).card : ℝ) = (k : ℝ) - 1 := by
  rw [card_colourCompl, Nat.cast_sub hk, Nat.cast_one]

/-- The event "the colouring assigns the colour `c` to `x` and avoids the colour `c` on the
set `T`" has probability `(1/k)·((k-1)/k)^{|T|}`. -/
theorem prob_single_and_avoid {k : ℕ} [Nonempty (V → Fin k)] (hk : 0 < k)
    {x : V} {T : Finset V} (hxT : x ∉ T) (c : Fin k) :
    (colSpace k).prob {f | f x = c ∧ ∀ w ∈ T, f w ≠ c}
      = (1 / (k : ℝ)) * (((k : ℝ) - 1) / (k : ℝ)) ^ T.card := by
  classical
  have hset : {f : V → Fin k | f x = c ∧ ∀ w ∈ T, f w ≠ c}
      = (↑(Fintype.piFinset (fun v : V =>
          if v = x then {c} else if v ∈ T then colourCompl c else Finset.univ)) :
            Set (V → Fin k)) := by
    ext f
    simp only [Set.mem_setOf_eq, Finset.mem_coe, Fintype.mem_piFinset]
    constructor
    · intro hf v
      by_cases hvx : v = x
      · rw [if_pos hvx, hvx, Finset.mem_singleton]; exact hf.1
      · rw [if_neg hvx]
        by_cases hvT : v ∈ T
        · rw [if_pos hvT, mem_colourCompl]; exact hf.2 v hvT
        · rw [if_neg hvT]; exact Finset.mem_univ _
    · intro hf
      refine ⟨?_, fun w hw => ?_⟩
      · have h := hf x
        rwa [if_pos rfl, Finset.mem_singleton] at h
      · have h := hf w
        rw [if_neg (by rintro rfl; exact hxT hw), if_pos hw, mem_colourCompl] at h
        exact h
  rw [hset, colSpace_prob_pi]
  have hprod : (∏ v : V, ((if v = x then ({c} : Finset (Fin k))
        else if v ∈ T then colourCompl c else Finset.univ).card : ℝ) / (k : ℝ))
      = ∏ v : V, (if v = x then (1 / (k : ℝ))
        else if v ∈ T then (((k : ℝ) - 1) / (k : ℝ)) else 1) :=
    Finset.prod_congr rfl fun v _ => by
      by_cases hvx : v = x
      · rw [if_pos hvx, if_pos hvx, Finset.card_singleton, Nat.cast_one]
      · rw [if_neg hvx, if_neg hvx]
        by_cases hvT : v ∈ T
        · rw [if_pos hvT, if_pos hvT, card_colourCompl_cast hk]
        · rw [if_neg hvT, if_neg hvT, Finset.card_univ, Fintype.card_fin]
          field_simp
  rw [hprod]
  rw [Finset.prod_ite (f := fun _ : V => (1 / (k : ℝ)))
    (g := fun v : V => if v ∈ T then (((k : ℝ) - 1) / (k : ℝ)) else 1)]
  have h1 : (Finset.univ.filter (fun v : V => v = x)) = {x} := by ext v; simp
  rw [h1, Finset.prod_singleton]
  have h2 : (Finset.univ.filter (fun v : V => ¬ v = x)) = Finset.univ.erase x := by
    ext v; simp [Finset.mem_erase]
  rw [h2]
  rw [Finset.prod_ite (f := fun _ : V => (((k : ℝ) - 1) / (k : ℝ))) (g := fun _ : V => (1 : ℝ))]
  have h3 : ((Finset.univ.erase x).filter (fun v : V => v ∈ T)) = T := by
    ext v
    constructor
    · intro hv
      rw [Finset.mem_filter] at hv
      exact hv.2
    · intro hv
      rw [Finset.mem_filter, Finset.mem_erase]
      exact ⟨⟨by rintro rfl; exact hxT hv, Finset.mem_univ v⟩, hv⟩
  rw [h3, Finset.prod_const, Finset.prod_const]
  simp

/-- The event "the colouring assigns the colour `c` to both `x` and `y` and avoids the colour
`c` on the set `T`" has probability `(1/k)²·((k-1)/k)^{|T|}`. -/
theorem prob_two_and_avoid {k : ℕ} [Nonempty (V → Fin k)] (hk : 0 < k)
    {x y : V} (hxy : x ≠ y) {T : Finset V} (hxT : x ∉ T) (hyT : y ∉ T) (c : Fin k) :
    (colSpace k).prob {f | f x = c ∧ f y = c ∧ ∀ w ∈ T, f w ≠ c}
      = (1 / (k : ℝ)) * (1 / (k : ℝ)) * (((k : ℝ) - 1) / (k : ℝ)) ^ T.card := by
  classical
  have hset : {f : V → Fin k | f x = c ∧ f y = c ∧ ∀ w ∈ T, f w ≠ c}
      = (↑(Fintype.piFinset (fun v : V => if v = x then {c} else if v = y then {c}
          else if v ∈ T then colourCompl c else Finset.univ)) : Set (V → Fin k)) := by
    ext f
    simp only [Set.mem_setOf_eq, Finset.mem_coe, Fintype.mem_piFinset]
    constructor
    · intro hf v
      by_cases hvx : v = x
      · rw [if_pos hvx, hvx, Finset.mem_singleton]; exact hf.1
      · rw [if_neg hvx]
        by_cases hvy : v = y
        · rw [if_pos hvy, hvy, Finset.mem_singleton]; exact hf.2.1
        · rw [if_neg hvy]
          by_cases hvT : v ∈ T
          · rw [if_pos hvT, mem_colourCompl]; exact hf.2.2 v hvT
          · rw [if_neg hvT]; exact Finset.mem_univ _
    · intro hf
      refine ⟨?_, ?_, fun w hw => ?_⟩
      · have h := hf x
        rwa [if_pos rfl, Finset.mem_singleton] at h
      · have h := hf y
        rwa [if_neg (Ne.symm hxy), if_pos rfl, Finset.mem_singleton] at h
      · have h := hf w
        rw [if_neg (by rintro rfl; exact hxT hw), if_neg (by rintro rfl; exact hyT hw),
          if_pos hw, mem_colourCompl] at h
        exact h
  rw [hset, colSpace_prob_pi]
  have hprod : (∏ v : V, ((if v = x then ({c} : Finset (Fin k)) else if v = y then {c}
        else if v ∈ T then colourCompl c else Finset.univ).card : ℝ) / (k : ℝ))
      = ∏ v : V, (if v = x then (1 / (k : ℝ)) else if v = y then (1 / (k : ℝ))
        else if v ∈ T then (((k : ℝ) - 1) / (k : ℝ)) else 1) :=
    Finset.prod_congr rfl fun v _ => by
      by_cases hvx : v = x
      · rw [if_pos hvx, if_pos hvx, Finset.card_singleton, Nat.cast_one]
      · rw [if_neg hvx, if_neg hvx]
        by_cases hvy : v = y
        · rw [if_pos hvy, if_pos hvy, Finset.card_singleton, Nat.cast_one]
        · rw [if_neg hvy, if_neg hvy]
          by_cases hvT : v ∈ T
          · rw [if_pos hvT, if_pos hvT, card_colourCompl_cast hk]
          · rw [if_neg hvT, if_neg hvT, Finset.card_univ, Fintype.card_fin]
            field_simp
  rw [hprod]
  rw [Finset.prod_ite (f := fun _ : V => (1 / (k : ℝ)))
    (g := fun v : V => if v = y then (1 / (k : ℝ))
      else if v ∈ T then (((k : ℝ) - 1) / (k : ℝ)) else 1)]
  have h1 : (Finset.univ.filter (fun v : V => v = x)) = {x} := by ext v; simp
  rw [h1, Finset.prod_singleton]
  have h2 : (Finset.univ.filter (fun v : V => ¬ v = x)) = Finset.univ.erase x := by
    ext v; simp [Finset.mem_erase]
  rw [h2]
  rw [Finset.prod_ite (f := fun _ : V => (1 / (k : ℝ)))
    (g := fun v : V => if v ∈ T then (((k : ℝ) - 1) / (k : ℝ)) else 1)]
  have h3 : ((Finset.univ.erase x).filter (fun v : V => v = y)) = {y} := by
    ext v
    rw [Finset.mem_filter, Finset.mem_erase, Finset.mem_singleton]
    simp only [Finset.mem_univ, and_true]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨by rw [h]; exact Ne.symm hxy, h⟩
  have h4 : ((Finset.univ.erase x).filter (fun v : V => ¬ v = y)) = (Finset.univ.erase x).erase y := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and]
    tauto
  rw [h3, h4, Finset.prod_singleton]
  rw [Finset.prod_ite (f := fun _ : V => (((k : ℝ) - 1) / (k : ℝ))) (g := fun _ : V => (1 : ℝ))]
  have h5 : (((Finset.univ.erase x).erase y).filter (fun v : V => v ∈ T)) = T := by
    ext v
    constructor
    · intro hv
      rw [Finset.mem_filter] at hv
      exact hv.2
    · intro hvT
      rw [Finset.mem_filter, Finset.mem_erase, Finset.mem_erase]
      exact ⟨⟨by rintro rfl; exact hyT hvT, by rintro rfl; exact hxT hvT, Finset.mem_univ v⟩, hvT⟩
  rw [h5, Finset.prod_const, Finset.prod_const]
  ring

end Work.Deep.Sparse
