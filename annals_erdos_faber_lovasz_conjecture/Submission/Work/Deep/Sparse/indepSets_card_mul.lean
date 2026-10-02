/-
# Counting independent j-subsets through non-adjacent pairs

`indepSets_card_mul`: the number of independent `j`-element subsets of the neighbourhood of `v`,
multiplied by `j (j-1)`, is at most the number of ordered non-adjacent pairs of neighbours
multiplied by `C(d-2, j-2)`, where `d = |N(v)|`.

The proof is the double count of the pairs `(S, x)` with `S` an independent `j`-subset of `N(v)`
and `x ∈ S.offDiag` an ordered pair of distinct elements of `S`: each `S` contributes `j (j-1)`
(for an independent set every ordered pair of distinct elements is non-adjacent), while an
ordered pair `x` of distinct elements of `N(v)` lies in at most `C(d-2, j-2)` independent
`j`-subsets (counted by `Finset.card_filter_powersetCard_subset`).  Ordered pairs that are
adjacent lie in no independent set at all, so only `nonAdjPairs G v` contributes.
-/
import Submission.Work.Deep.Sparse.Prelude
import Submission.Work.Deep.Sparse.ncpTailDefs
import Submission.Work.Deep.Sparse.NcpDefs
import Submission.Work.Deep.Sparse.ProbModel

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open scoped BigOperators

namespace Work.Deep.Sparse

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The number of independent `j`-subsets `S` of `A` containing a fixed ordered pair `x` of
distinct elements of `A` is at most `C(|A| - 2, j - 2)`. -/
private lemma indepSets_filter_pair_card_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) {j : ℕ} (hj : 2 ≤ j) {x : V × V} (hx1 : x.1 ∈ A) (hx2 : x.2 ∈ A)
    (hne : x.1 ≠ x.2) :
    ((indepSets G A j).filter (fun S => x ∈ S.offDiag)).card
      ≤ (A.card - 2).choose (j - 2) := by
  classical
  set P : Finset (Finset V) := A.powersetCard j with hP
  have hsub : (indepSets G A j).filter (fun S => x ∈ S.offDiag)
      ⊆ P.filter (fun S => ({x.1, x.2} : Finset V) ⊆ S) := by
    intro S hS
    rw [Finset.mem_filter] at hS ⊢
    obtain ⟨hS1, hS2⟩ := hS
    rw [indepSets, Finset.mem_filter] at hS1
    refine ⟨?_, ?_⟩
    · rw [hP]; exact hS1.1
    · rw [Finset.mem_offDiag] at hS2
      intro y hy
      rw [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact hS2.1
      · exact hS2.2.1
  have hcard2 : ({x.1, x.2} : Finset V).card = 2 := Finset.card_pair hne
  have hsub2 : ({x.1, x.2} : Finset V) ⊆ A := by
    intro y hy
    rw [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl
    · exact hx1
    · exact hx2
  calc ((indepSets G A j).filter (fun S => x ∈ S.offDiag)).card
      ≤ (P.filter (fun S => ({x.1, x.2} : Finset V) ⊆ S)).card := Finset.card_le_card hsub
    _ = (A.card - 2).choose (j - 2) := by
        rw [hP, Finset.card_filter_powersetCard_subset ({x.1, x.2} : Finset V) A j hsub2
          (by rw [hcard2]; exact hj), hcard2]

set_option maxHeartbeats 2000000 in
theorem indepSets_card_mul {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) {j : ℕ} (hj : 2 ≤ j) :
    ((indepSets G (G.neighborFinset v) j).card : ℝ) * ((j : ℝ) * ((j : ℝ) - 1))
      ≤ ((nonAdjPairs G v).card : ℝ) * (((G.neighborFinset v).card - 2).choose (j - 2) : ℝ) := by
  classical
  set A : Finset V := G.neighborFinset v with hA
  set IS : Finset (Finset V) := indepSets G A j with hIS
  have hmem : ∀ S ∈ IS, S ⊆ A ∧ S.card = j ∧ (∀ x ∈ S, ∀ y ∈ S, G.Adj x y → x = y) := by
    intro S hS
    rw [hIS, mem_indepSets] at hS
    exact hS
  have hcard : ∀ S ∈ IS, S.card = j := fun S hS => (hmem S hS).2.1
  have hindep : ∀ S ∈ IS, ∀ x ∈ S, ∀ y ∈ S, G.Adj x y → x = y := fun S hS => (hmem S hS).2.2
  have hsubA : ∀ S ∈ IS, S ⊆ A := fun S hS => (hmem S hS).1
  -- Step 1: the left-hand side is `∑_{S ∈ IS} |S.offDiag|`.
  have step1 : ((IS.card : ℕ) : ℝ) * ((j : ℝ) * ((j : ℝ) - 1))
      = ∑ S ∈ IS, ((S.offDiag).card : ℝ) := by
    rw [Finset.sum_congr rfl (fun S hS => ?_), Finset.sum_const, nsmul_eq_mul]
    rw [Finset.offDiag_card, hcard S hS, Nat.cast_sub (Nat.le_mul_self j), Nat.cast_mul]
    ring
  -- Step 2: expand each `|S.offDiag|` as a sum of indicators over `A.offDiag`.
  have step2 : ∑ S ∈ IS, ((S.offDiag).card : ℝ)
      = ∑ x ∈ A.offDiag, ∑ S ∈ IS, (if x ∈ S.offDiag then (1 : ℝ) else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun S hS => ?_)
    have hsub : S.offDiag ⊆ A.offDiag := Finset.offDiag_mono (hsubA S hS)
    have hfilt : A.offDiag.filter (fun x => x ∈ S.offDiag) = S.offDiag := by
      ext y
      rw [Finset.mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨hsub h, h⟩⟩
    conv_lhs => rw [← hfilt]
    exact (Finset.sum_boole (R := ℝ) (fun x => x ∈ S.offDiag) A.offDiag).symm
  -- Step 3: identify the inner sum with the cardinality of a filter, and bound it.
  have step3 : ∀ x ∈ A.offDiag, (∑ S ∈ IS, (if x ∈ S.offDiag then (1 : ℝ) else 0))
      ≤ (((A.card - 2).choose (j - 2) : ℕ) : ℝ) ∧
      (G.Adj x.1 x.2 → (∑ S ∈ IS, (if x ∈ S.offDiag then (1 : ℝ) else 0)) = 0) := by
    intro x hx
    rw [Finset.mem_offDiag] at hx
    obtain ⟨hx1, hx2, hne⟩ := hx
    have hsum : (∑ S ∈ IS, (if x ∈ S.offDiag then (1 : ℝ) else 0))
        = (((IS.filter (fun S => x ∈ S.offDiag)).card : ℕ) : ℝ) := by
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
        mul_one]
    constructor
    · rw [hsum]
      have hb := indepSets_filter_pair_card_le G A hj hx1 hx2 hne
      rw [← hIS] at hb
      exact_mod_cast hb
    · intro hadj
      rw [hsum]
      have hempty : (IS.filter (fun S => x ∈ S.offDiag)) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro S hS
        rw [Finset.mem_filter, Finset.mem_offDiag] at hS
        obtain ⟨hS1, hS2⟩ := hS
        exact hne (hindep S hS1 x.1 hS2.1 x.2 hS2.2.1 hadj)
      rw [hempty, Finset.card_empty, Nat.cast_zero]
  -- Step 4: restrict the sum to the non-adjacent ordered pairs.
  have hfilterEq : A.offDiag.filter (fun x : V × V => ¬ G.Adj x.1 x.2) = nonAdjPairs G v := by
    ext x
    rw [Finset.mem_filter, Finset.mem_offDiag, mem_nonAdjPairs]
    constructor
    · rintro ⟨⟨h1, h2, h3⟩, h4⟩
      exact ⟨h1, h2, h3, h4⟩
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨⟨h1, h2, h3⟩, h4⟩
  calc ((indepSets G (G.neighborFinset v) j).card : ℝ) * ((j : ℝ) * ((j : ℝ) - 1))
      = ((IS.card : ℕ) : ℝ) * ((j : ℝ) * ((j : ℝ) - 1)) := by rw [hIS, hA]
    _ = ∑ S ∈ IS, ((S.offDiag).card : ℝ) := step1
    _ = ∑ x ∈ A.offDiag, ∑ S ∈ IS, (if x ∈ S.offDiag then (1 : ℝ) else 0) := step2
    _ = ∑ x ∈ A.offDiag.filter (fun x : V × V => ¬ G.Adj x.1 x.2),
          ∑ S ∈ IS, (if x ∈ S.offDiag then (1 : ℝ) else 0) := by
        rw [Finset.sum_filter_of_ne]
        intro x hx hne0
        exact fun hadj => hne0 ((step3 x hx).2 hadj)
    _ = ∑ x ∈ nonAdjPairs G v, ∑ S ∈ IS, (if x ∈ S.offDiag then (1 : ℝ) else 0) := by
        rw [hfilterEq]
    _ ≤ ∑ x ∈ nonAdjPairs G v, (((A.card - 2).choose (j - 2) : ℕ) : ℝ) := by
        refine Finset.sum_le_sum (fun x hx => (step3 x ?_).1)
        have hx' : x ∈ A.offDiag.filter (fun x : V × V => ¬ G.Adj x.1 x.2) := by
          rw [hfilterEq]; exact hx
        exact (Finset.mem_filter.mp hx').1
    _ = ((nonAdjPairs G v).card : ℝ) * (((A.card - 2).choose (j - 2) : ℕ) : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = ((nonAdjPairs G v).card : ℝ) * (((G.neighborFinset v).card - 2).choose (j - 2) : ℝ) := by
        rw [hA]

end Work.Deep.Sparse
