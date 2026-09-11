import Mathlib.Probability.Distributions.SetBernoulli
import ChallengeDeps
import Submission.SelCore
import Submission.Deep

/-!
PROVE: `Submission.ObsTPrime.theorem_obsTp` (Proposition obs.T' of Park--Pham 2024, §2.2,
adapted to our natural-index fragments: the paper's index -1 is excluded by the hypothesis that
W is BAD; do not import Submission.ObsT).

Definitions in Submission/Deep.lean; `S' ∈ FPartial S b` means COUNT equality of level sets on
levels ≤ b.  `IsFragment N S W U b S'`, `MinFragmentAt N S W U b hS hB` as in Submission/ObsT.lean.

THEOREM: hypotheses:
- hS : S ∈ N.F, hB : N.LevelBounded
- hTot : ∀ T ∈ N.F, 10^{-8} ≤ N.totalWeight T   (=(10^8)^{-1} ≤ totalWeight T)
- hbad : N.Bad (10^{-10}) W   i.e. procVal N W < 10^{-10}
        (procVal N W = famSup over T∈F of N.weight T (W∩T); use le_famSup to bound any
         weightAbove S' W b ≤ procVal W)
- hmin : N.MinFragmentAt S W U b hS hB, hfr : N.IsFragment S W U b S'
CONCLUSION:  (9/10) * (prefixCount S b : ℝ) ≤ (U.ncard : ℝ).

Proof outline (paper obs.T'): write s_j := sCount S' j (j ≤ b), t_j := |levelSet S' j ∩ U|,
n_b := prefixCount S b, t := |U|.  From obs.T (reprove it here if needed under a different name)
t = Σ_{j≤b} t_j.  Assume t < 0.9·n_b for contradiction.
1. (telescoping) ∃ b' ≤ b with Σ_{b'≤j≤b} wlev j·(t_j - 0.9·s_j) < 0.  Prove: for
   u_i := Σ_{i≤j≤b} wlev j (t_j - 0.9 s_j) (u_{b+1} := 0): Σ_{j≤b}(t_j - 0.9 s_j) =
   Σ_{i≤b} (100^i - 100^{i-1})·u_i with 100^{-1}:=0; coefficients are ≥ 0.
2. Then Σ_{b'≤j≤b} wlev j·(s_j - t_j) > (1/10)·Σ_{b'≤j≤b} wlev j·s_j.     (**)
   Reason: levelSet S' j ⊆ W ∪ U (fragment1) and levelSet S' j ∩ U has t_j elements, so
   |levelSet S' j ∩ W| = s_j - t_j.
Case b' ≥ 1: U' := unionBelow S' (b'-1) ∩ U is a fragment at index b'-1 with witness S',
contradicting minimality of the index (use minIndex_min: any fragment at index c has
MinIndex ≤ c, and b'-1 < b = MinIndex).
   Fragment2 for U' follows by the paper's displayed computation; the extra inequalities:
   0.09·Σ_{b'≤j≤b} wlev j·s_j ≥ wlev (b+1)·Σ_{b'≤j≤b} s_j  (since 0.09·wlev j ≥ wlev(b+1) for
   j ≤ b: use wlev (b+1) = (1/100)·wlev b and j ≤ b)
   and  (wlev (b'-1) - wlev b)·Σ_{j < b'} s_j ≥ wlev (b'-1)·t' - wlev b·t with t' := |U'|,
   using Σ_{j<b'} s_j ≥ t' and t' ≤ t ≤ n_b; adapt as needed (you may replace (b'-1) arithmetic
   by proving a fragment at index b'-1 directly).
Case b' = 0: derive the fragment2 inequality for U' := ∅ "at index -1" which reduces to
   weight S' (S'∩W) ≥ (1/100) · weight S' S'  (all levels; prefixCount at -1 = 0, |U'|=0)
   [derive it by the same algebra as case b' ≥ 1 with b' := 0: the middle sum Σ_{0≤j≤b}... and
    the paper's dagger inequalities], contradicting hbad + hTot:
   weight S' (S'∩W) ≤ procVal N W < 10^{-10} ≤ (1/100)·weight S' S'   (weight S' S' ≥ 10^{-8}).

Work only in this file (namespace Submission.ObsTPrime); add helpers as needed.  The final file must be free of gaps.
-/

set_option autoImplicit false
open Classical
open MeasureTheory ProbabilityTheory Measure unitInterval Finset
open scoped NNReal ENNReal BigOperators

namespace Submission

open _root_.SupremumOfSelectorProcesses

namespace ObsTPrime

open Frame
open Sel.Deep
open Sel.Deep.Sys

variable {X : Type*} [Fintype X]

/-! ## minimality lemmas (reproduced from the framework file so this module is self-contained) -/

/-! ## weightAbove facts -/

/-- weightAbove depends only on the level-set intersections -/
lemma weightAbove_congr_of_inter (N : Sys X) {S' A B : Set X} {b : ℕ}
    (h : ∀ j, A ∩ N.levelSet S' j = B ∩ N.levelSet S' j) :
    N.weightAbove S' A b = N.weightAbove S' B b := by
  unfold Sys.weightAbove
  apply Finset.sum_congr rfl
  intro j hj
  rw [h j]

/-- Removing one element of level j0 from A decreases weightAbove by at most wlev j0 -/
lemma weightAbove_erase_le (N : Sys X) {S' A : Set X} {b : ℕ} {x : X} {j0 : ℕ}
    (hxlev : x ∈ N.levelSet S' j0) :
    N.weightAbove S' A b ≤ N.weightAbove S' (A \ {x}) b + wlev j0 := by
  classical
  have hxnot : ∀ j, j ≠ j0 → x ∉ N.levelSet S' j := by
    intro j hne hxL
    apply hne
    calc
      j = N.lv S' x := hxL.2.symm
      _ = j0 := hxlev.2
  have hpt : ∀ j, j ∈ Finset.Icc (b + 1) N.τ →
      ((A ∩ N.levelSet S' j).ncard : ℝ) * wlev j ≤
        (((A \ {x}) ∩ N.levelSet S' j).ncard : ℝ) * wlev j +
          (if j = j0 then wlev j else 0) := by
    intro j hj
    by_cases hjj0 : j = j0
    · subst j
      by_cases hxAj : x ∈ A ∩ N.levelSet S' j0
      · have hcard : (A ∩ N.levelSet S' j0).ncard ≤ ((A \ {x}) ∩ N.levelSet S' j0).ncard + 1 := by
          have hc' : (A ∩ N.levelSet S' j0).ncard ≤ ((A ∩ N.levelSet S' j0) \ {x}).ncard + 1 := by
            have hsc : ((A ∩ N.levelSet S' j0) \ {x}).ncard + 1 = (A ∩ N.levelSet S' j0).ncard :=
              Set.ncard_sdiff_singleton_add_one hxAj
            omega
          have hset : (A \ {x}) ∩ N.levelSet S' j0 = (A ∩ N.levelSet S' j0) \ {x} := by
            ext y
            constructor <;> intro hy <;> simp at hy ⊢ <;> tauto
          rwa [← hset] at hc'
        have hcr : ((A ∩ N.levelSet S' j0).ncard : ℝ) ≤
            (((A \ {x}) ∩ N.levelSet S' j0).ncard : ℝ) + 1 := by
          exact_mod_cast hcard
        have hmul := mul_le_mul_of_nonneg_right hcr (wlev_nonneg j0)
        simpa [add_mul, one_mul] using hmul
      · have hset : A ∩ N.levelSet S' j0 = (A \ {x}) ∩ N.levelSet S' j0 := by
          ext y
          constructor
          · intro hy
            rcases hy with ⟨hyA, hyL⟩
            refine ⟨⟨hyA, ?_⟩, hyL⟩
            intro hxy
            have hyx : y = x := Set.mem_singleton_iff.mp hxy
            apply hxAj
            constructor
            · simpa [hyx] using hyA
            · simpa [hyx] using hyL
          · intro hy
            exact ⟨hy.1.1, hy.2⟩
        have hcr : ((A ∩ N.levelSet S' j0).ncard : ℝ) =
            (((A \ {x}) ∩ N.levelSet S' j0).ncard : ℝ) := by
          exact_mod_cast (congrArg Set.ncard hset)
        rw [hcr]
        simp
        linarith [wlev_nonneg j0]
    · have hset : A ∩ N.levelSet S' j = (A \ {x}) ∩ N.levelSet S' j := by
        ext y
        constructor
        · intro hy
          rcases hy with ⟨hyA, hyL⟩
          refine ⟨⟨hyA, ?_⟩, hyL⟩
          intro hxy
          have hyx : y = x := Set.mem_singleton_iff.mp hxy
          exact hxnot j hjj0 (by simpa [hyx] using hyL)
        · intro hy
          exact ⟨hy.1.1, hy.2⟩
      have hcr : ((A ∩ N.levelSet S' j).ncard : ℝ) =
          (((A \ {x}) ∩ N.levelSet S' j).ncard : ℝ) := by
        exact_mod_cast (congrArg Set.ncard hset)
      rw [hcr, if_neg hjj0]
      simp
  have h1 :
      (∑ j ∈ Finset.Icc (b + 1) N.τ, ((A ∩ N.levelSet S' j).ncard : ℝ) * wlev j) ≤
        (∑ j ∈ Finset.Icc (b + 1) N.τ,
          ((((A \ {x}) ∩ N.levelSet S' j).ncard : ℝ) * wlev j +
            (if j = j0 then wlev j else 0))) := by
    exact Finset.sum_le_sum hpt
  have hind :
      (∑ j ∈ Finset.Icc (b + 1) N.τ, (if j = j0 then wlev j else 0)) ≤ wlev j0 := by
    calc
      (∑ j ∈ Finset.Icc (b + 1) N.τ, (if j = j0 then wlev j else 0))
          ≤ (∑ j ∈ Finset.Icc (b + 1) N.τ, (if j = j0 then wlev j0 else 0)) := by
            exact Finset.sum_le_sum (fun j hj => by by_cases h : j = j0 <;> simp [h])
      _ = (if j0 ∈ Finset.Icc (b + 1) N.τ then wlev j0 else 0) := by
            exact Finset.sum_ite_eq' (Finset.Icc (b + 1) N.τ) j0 (fun _ => wlev j0)
      _ ≤ wlev j0 := by
            by_cases hj0 : j0 ∈ Finset.Icc (b + 1) N.τ <;> simp [hj0, wlev_nonneg j0]
  have h2 :
      (∑ j ∈ Finset.Icc (b + 1) N.τ,
          ((((A \ {x}) ∩ N.levelSet S' j).ncard : ℝ) * wlev j + (if j = j0 then wlev j else 0)))
        = (∑ j ∈ Finset.Icc (b + 1) N.τ, (((A \ {x}) ∩ N.levelSet S' j).ncard : ℝ) * wlev j)
          + (∑ j ∈ Finset.Icc (b + 1) N.τ, (if j = j0 then wlev j else 0)) := by
    rw [Finset.sum_add_distrib]
  have h3 :
      (∑ j ∈ Finset.Icc (b + 1) N.τ, (((A \ {x}) ∩ N.levelSet S' j).ncard : ℝ) * wlev j)
          + (∑ j ∈ Finset.Icc (b + 1) N.τ, (if j = j0 then wlev j else 0)) ≤
        (∑ j ∈ Finset.Icc (b + 1) N.τ, (((A \ {x}) ∩ N.levelSet S' j).ncard : ℝ) * wlev j)
          + wlev j0 := by
    exact add_le_add_right hind _
  have hfin : N.weightAbove S' A b ≤ N.weightAbove S' (A \ {x}) b + wlev j0 := by
    unfold Sys.weightAbove
    exact h1.trans (h2.trans_le h3)
  exact hfin

/-- An element of level j0 with j0 > b lies in no level set with index ≤ b -/
lemma not_mem_levelSet_of_level_gt (N : Sys X) {S' : Set X} {x : X} {j0 b : ℕ}
    (hxlev : x ∈ N.levelSet S' j0) (hbj : b < j0) {j : ℕ} (hj : j ≤ b) :
    x ∉ N.levelSet S' j := by
  intro hxj
  have hne : j ≠ j0 := by omega
  have hdisj : Disjoint (N.levelSet S' j) (N.levelSet S' j0) := N.levelSet_disjoint S' hne
  have hxnotj0 : x ∉ N.levelSet S' j0 := (Set.disjoint_left.mp hdisj) hxj
  exact hxnotj0 hxlev

/-! ## the weight inequality when erasing an element -/

/-- fragment2 for U plus smallness of the loss gives fragment2 for U\{x} -/
lemma frag_weight_erase (N : Sys X) {S S' W U : Set X} {b : ℕ} {x : X} (hxU : x ∈ U)
    (hfr2 : N.weightAbove S' (W ∪ U) b ≥ (100 : ℝ)⁻¹ *
        (N.weightAbove S' S' b - wlev b * ((N.prefixCount S b : ℝ) - (U.ncard : ℝ))))
    (hloss : N.weightAbove S' (W ∪ U) b - N.weightAbove S' (W ∪ (U \ {x})) b ≤ wlev (b + 1)) :
    N.weightAbove S' (W ∪ (U \ {x})) b ≥ (100 : ℝ)⁻¹ *
        (N.weightAbove S' S' b - wlev b * ((N.prefixCount S b : ℝ) - ((U \ {x}).ncard : ℝ))) := by
  classical
  have hcard : ((U \ {x}).ncard : ℝ) + 1 = (U.ncard : ℝ) := by
    exact_mod_cast (Set.ncard_sdiff_singleton_add_one hxU)
  have hws : wlev (b + 1) = (100 : ℝ)⁻¹ * wlev b := by
    rw [wlev_succ]
    norm_num
  have hsub : (N.prefixCount S b : ℝ) - ((U \ {x}).ncard : ℝ) =
      (N.prefixCount S b : ℝ) - (U.ncard : ℝ) + 1 := by
    linarith
  have hA : (100 : ℝ)⁻¹ * (N.weightAbove S' S' b - wlev b *
        ((N.prefixCount S b : ℝ) - (U.ncard : ℝ))) - wlev (b + 1) ≤
      N.weightAbove S' (W ∪ U) b - wlev (b + 1) := by
    exact sub_le_sub_right hfr2 (wlev (b + 1))
  have hB : N.weightAbove S' (W ∪ U) b - wlev (b + 1) ≤
      N.weightAbove S' (W ∪ (U \ {x})) b := by
    linarith
  calc
    N.weightAbove S' (W ∪ (U \ {x})) b ≥
        (100 : ℝ)⁻¹ * (N.weightAbove S' S' b - wlev b *
          ((N.prefixCount S b : ℝ) - (U.ncard : ℝ))) - wlev (b + 1) := by
          exact le_trans hA hB
    _ = (100 : ℝ)⁻¹ * (N.weightAbove S' S' b - wlev b *
          ((N.prefixCount S b : ℝ) - ((U \ {x}).ncard : ℝ))) := by
          rw [hws, hsub]
          ring

/-! ## erasing an element from a fragment -/

/-- A fragment with x removed stays a fragment (x must be out of all level sets ≤ b,
    and the weight loss must be bounded by wlev (b+1)) -/
lemma isFragment_erase (N : Sys X) {S W U S' : Set X} {b : ℕ} {x : X}
    (hfr : N.IsFragment S W U b S') (hxU : x ∈ U)
    (hxnotbelow : ∀ j, j ≤ b → x ∉ N.levelSet S' j)
    (hloss : N.weightAbove S' (W ∪ U) b - N.weightAbove S' (W ∪ (U \ {x})) b ≤ wlev (b + 1)) :
    N.IsFragment S W (U \ {x}) b S' := by
  constructor
  · exact hfr.1
  · constructor
    · intro y hy
      exact hfr.2.1 hy.1
    · constructor
      · apply Set.disjoint_left.mpr
        intro y hyUx hyW
        exact (Set.disjoint_left.mp hfr.2.2.1) hyUx.1 hyW
      · constructor
        · intro j hj y hyL
          rcases hfr.2.2.2.1 j hj hyL with hyW | hyU
          · exact Or.inl hyW
          · refine Or.inr ⟨hyU, ?_⟩
            intro hyx
            have hxy : y = x := Set.mem_singleton_iff.mp hyx
            exact hxnotbelow j hj (by simpa [hxy] using hyL)
        · exact frag_weight_erase N hxU hfr.2.2.2.2 hloss

/-- Removing x ∉ S' from a fragment gives a fragment -/
lemma isFragment_erase_of_not_mem (N : Sys X) {S W U S' : Set X} {b : ℕ} {x : X}
    (hfr : N.IsFragment S W U b S') (hxU : x ∈ U) (hxS' : x ∉ S') :
    N.IsFragment S W (U \ {x}) b S' := by
  have hxnotbelow : ∀ j, j ≤ b → x ∉ N.levelSet S' j := by
    intro j hj hxj
    exact hxS' hxj.1
  have hEq : N.weightAbove S' (W ∪ U) b = N.weightAbove S' (W ∪ (U \ {x})) b := by
    apply weightAbove_congr_of_inter
    intro j
    ext y
    constructor
    · intro hy
      rcases hy with ⟨hyWU, hyL⟩
      rcases hyWU with hyW | hyU
      · exact ⟨Or.inl hyW, hyL⟩
      · refine ⟨Or.inr ⟨hyU, ?_⟩, hyL⟩
        intro hyx
        have hxy : y = x := Set.mem_singleton_iff.mp hyx
        have hxL' : x ∈ N.levelSet S' j := by simpa [hxy] using hyL
        exact hxS' hxL'.1
    · intro hy
      rcases hy with ⟨hyWU, hyL⟩
      rcases hyWU with hyW | hyUx
      · exact ⟨Or.inl hyW, hyL⟩
      · exact ⟨Or.inr hyUx.1, hyL⟩
  have hloss : N.weightAbove S' (W ∪ U) b - N.weightAbove S' (W ∪ (U \ {x})) b ≤ wlev (b + 1) := by
    rw [hEq]
    simpa using (wlev_nonneg (b + 1))
  exact isFragment_erase N hfr hxU hxnotbelow hloss

/-- Removing an element of level > b from a fragment gives a fragment -/
lemma isFragment_erase_of_high_level (N : Sys X) {S W U S' : Set X} {b : ℕ} {x : X} {j0 : ℕ}
    (hfr : N.IsFragment S W U b S') (hxU : x ∈ U) (hxlev : x ∈ N.levelSet S' j0)
    (hbj : b < j0) :
    N.IsFragment S W (U \ {x}) b S' := by
  have hxnotbelow : ∀ j, j ≤ b → x ∉ N.levelSet S' j := by
    intro j hj hxj
    exact not_mem_levelSet_of_level_gt N hxlev hbj hj hxj
  have hxW : x ∉ W := (Set.disjoint_left.mp hfr.2.2.1) hxU
  have hEq : (W ∪ U) \ {x} = W ∪ (U \ {x}) := by
    ext y
    constructor
    · intro hy
      rcases hy with ⟨hyWU, hyx⟩
      rcases hyWU with hyW | hyU
      · exact Or.inl hyW
      · exact Or.inr ⟨hyU, hyx⟩
    · intro hy
      rcases hy with hyW | hyUx
      · refine ⟨Or.inl hyW, ?_⟩
        intro hyx
        have hxy : y = x := Set.mem_singleton_iff.mp hyx
        exact hxW (by simpa [hxy] using hyW)
      · refine ⟨Or.inr hyUx.1, hyUx.2⟩
  have hloss' : N.weightAbove S' (W ∪ U) b ≤ N.weightAbove S' (W ∪ (U \ {x})) b + wlev j0 := by
    have hl := weightAbove_erase_le (N := N) (S' := S') (A := W ∪ U) (b := b) (x := x)
      (j0 := j0) hxlev
    simpa [hEq] using hl
  have hwj0 : wlev j0 ≤ wlev (b + 1) := wlev_le_of_le (by omega : b + 1 ≤ j0)
  have hloss : N.weightAbove S' (W ∪ U) b - N.weightAbove S' (W ∪ (U \ {x})) b ≤ wlev (b + 1) := by
    linarith
  exact isFragment_erase N hfr hxU hxnotbelow hloss

/-! ## minimality of U -/

/-- Elements of a minimal fragment at index b lie in the witness S' -/
lemma mem_S'_of_minimal (N : Sys X) (S W U : Set X) (b : ℕ) (hS : S ∈ N.F)
    (hB : N.LevelBounded) (hmin : N.MinFragmentAt S W U b hS hB) {S' : Set X}
    (hfr : N.IsFragment S W U b S') {x : X} (hxU : x ∈ U) : x ∈ S' := by
  by_contra hxS'
  have hfrx : N.IsFragment S W (U \ {x}) b S' :=
    isFragment_erase_of_not_mem N hfr hxU hxS'
  have hU' : N.HasFragmentAt S W (U \ {x}) b := ⟨S', hfrx⟩
  have hle : U.ncard ≤ (U \ {x}).ncard := hmin.2.2 (U \ {x}) hU'
  have hlt : (U \ {x}).ncard < U.ncard := Set.ncard_sdiff_singleton_lt_of_mem hxU
  omega

/-- Elements of a minimal fragment at index b have level ≤ b in S' -/
lemma level_le_b_of_minimal (N : Sys X) (S W U : Set X) (b : ℕ) (hS : S ∈ N.F)
    (hB : N.LevelBounded) (hmin : N.MinFragmentAt S W U b hS hB) {S' : Set X}
    (hfr : N.IsFragment S W U b S') {x : X} (hxU : x ∈ U) : N.lv S' x ≤ b := by
  by_contra hnot
  have hbj : b < N.lv S' x := Nat.lt_of_not_ge hnot
  have hxS' : x ∈ S' := mem_S'_of_minimal N S W U b hS hB hmin hfr hxU
  have hxlev : x ∈ N.levelSet S' (N.lv S' x) := ⟨hxS', rfl⟩
  have hfrx : N.IsFragment S W (U \ {x}) b S' :=
    isFragment_erase_of_high_level N hfr hxU hxlev hbj
  have hU' : N.HasFragmentAt S W (U \ {x}) b := ⟨S', hfrx⟩
  have hle : U.ncard ≤ (U \ {x}).ncard := hmin.2.2 (U \ {x}) hU'
  have hlt : (U \ {x}).ncard < U.ncard := Set.ncard_sdiff_singleton_lt_of_mem hxU
  omega

/-! ## subset inclusions -/

lemma unionBelow_diff_subset_U (N : Sys X) {S W U S' : Set X} {b : ℕ}
    (hfr : N.IsFragment S W U b S') : N.unionBelow S' b \ W ⊆ U := by
  intro x hx
  rcases hx with ⟨hxub, hxW⟩
  rcases (N.mem_unionBelow).1 hxub with ⟨j, hj, hxL⟩
  have hxWU : x ∈ W ∪ U := hfr.2.2.2.1 j hj hxL
  rcases hxWU with hxW' | hxU
  · exact False.elim (hxW hxW')
  · exact hxU

lemma U_subset_unionBelow_diff (N : Sys X) (S W U : Set X) (b : ℕ) (hS : S ∈ N.F)
    (hB : N.LevelBounded) (hmin : N.MinFragmentAt S W U b hS hB) {S' : Set X}
    (hfr : N.IsFragment S W U b S') : U ⊆ N.unionBelow S' b \ W := by
  intro x hxU
  constructor
  · exact ⟨N.lv S' x, level_le_b_of_minimal N S W U b hS hB hmin hfr hxU,
      ⟨mem_S'_of_minimal N S W U b hS hB hmin hfr hxU, rfl⟩⟩
  · exact (Set.disjoint_left.mp hfr.2.2.1) hxU

lemma obsT (N : Sys X) (S W U : Set X) (b : ℕ) (hS : S ∈ N.F) (hB : N.LevelBounded)
    (hmin : N.MinFragmentAt S W U b hS hB) {S' : Set X} (hfr : N.IsFragment S W U b S') :
    N.unionBelow S' b \ W = U := by
  exact le_antisymm (unionBelow_diff_subset_U N hfr)
    (U_subset_unionBelow_diff N S W U b hS hB hmin hfr)



/-! ## finite sums over level ranges: splitting, telescoping -/

/-- Σ_{j∈range(b+1)} f (j+1) = Σ_{j∈Icc 1 (b+1)} f j -/
lemma sum_range_succ_fun (b : ℕ) (f : ℕ → ℝ) :
    (∑ j ∈ Finset.range (b + 1), f (j + 1)) = (∑ j ∈ Finset.Icc 1 (b + 1), f j) := by
  symm
  refine Finset.sum_bij (fun a ha => a - 1) ?hi ?hinj ?hsurj ?hval
  · intro a ha
    rw [Finset.mem_range]
    have h1 : 1 ≤ a := (Finset.mem_Icc.mp ha).1
    have h2 : a ≤ b + 1 := (Finset.mem_Icc.mp ha).2
    omega
  · intro a1 ha1 a2 ha2 h
    have h1 : 1 ≤ a1 := (Finset.mem_Icc.mp ha1).1
    have h2 : 1 ≤ a2 := (Finset.mem_Icc.mp ha2).1
    omega
  · intro x hx
    have hxb : x < b + 1 := (Finset.mem_range.mp hx)
    refine ⟨x + 1, ?_, ?_⟩
    · rw [Finset.mem_Icc]
      exact ⟨by omega, by omega⟩
    · omega
  · intro a ha
    have hge : 1 ≤ a := (Finset.mem_Icc.mp ha).1
    rw [Nat.sub_add_cancel hge]

/-- Icc j b = insert j (Icc (j+1) b) for j ≤ b -/
lemma Icc_eq_insert {j b : ℕ} (hj : j ≤ b) :
    Finset.Icc j b = insert j (Finset.Icc (j + 1) b) := by
  apply Finset.ext
  intro x
  rw [Finset.mem_insert]
  constructor
  · intro hx
    rcases (Finset.mem_Icc.mp hx) with ⟨hjx, hxb⟩
    by_cases hxeq : x = j
    · exact Or.inl hxeq
    · refine Or.inr ?_
      exact Finset.mem_Icc.mpr ⟨by omega, hxb⟩
  · intro hx
    rcases hx with hxj | hx
    · rw [hxj]
      exact Finset.mem_Icc.mpr ⟨le_rfl, hj⟩
    · have hxI := Finset.mem_Icc.mp hx
      exact Finset.mem_Icc.mpr ⟨le_trans (by omega : j ≤ j + 1) hxI.1, hxI.2⟩

/-- u_j - u_{j+1} = d_j -/
lemma u_diff {b j : ℕ} (hj : j ≤ b) (d : ℕ → ℝ) :
    (∑ k ∈ Finset.Icc j b, d k) - (∑ k ∈ Finset.Icc (j + 1) b, d k) = d j := by
  rw [Icc_eq_insert hj]
  have hnot : j ∉ Finset.Icc (j + 1) b := by
    intro hx
    have : j + 1 ≤ j := (Finset.mem_Icc.mp hx).1
    omega
  rw [Finset.sum_insert hnot]
  ring

/-- Icc a c splits at b (b strictly between) -/
lemma sum_Icc_split {a b c : ℕ} (hab : a ≤ b) (hbc : b < c) (f : ℕ → ℝ) :
    (∑ j ∈ Finset.Icc a c, f j) = (∑ j ∈ Finset.Icc a b, f j) + (∑ j ∈ Finset.Icc (b + 1) c, f j) := by
  have hdisj : Disjoint (Finset.Icc a b) (Finset.Icc (b + 1) c) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    have hx1b : x ≤ b := (Finset.mem_Icc.mp hx1).2
    have hx2b : b + 1 ≤ x := (Finset.mem_Icc.mp hx2).1
    omega
  have hunion : Finset.Icc a c = Finset.Icc a b ∪ Finset.Icc (b + 1) c := by
    apply Finset.ext
    intro x
    rw [Finset.mem_union, Finset.mem_Icc, Finset.mem_Icc, Finset.mem_Icc]
    constructor
    · intro hx
      rcases hx with ⟨hxa, hxc⟩
      by_cases hxb : x ≤ b
      · exact Or.inl ⟨hxa, hxb⟩
      · exact Or.inr ⟨by omega, hxc⟩
    · intro hx
      rcases hx with ⟨hxa, hxb⟩ | ⟨hxb, hxc⟩
      · exact ⟨hxa, le_trans hxb (by omega)⟩
      · exact ⟨by omega, hxc⟩
  rw [hunion, Finset.sum_union hdisj]

/-- Icc a c splits at b (b between, inclusive case allowed) -/
lemma sum_Icc_split_at {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) (f : ℕ → ℝ) :
    (∑ j ∈ Finset.Icc a c, f j) = (∑ j ∈ Finset.Icc a b, f j) + (∑ j ∈ Finset.Icc (b + 1) c, f j) := by
  by_cases hbc' : b < c
  · exact sum_Icc_split hab hbc' f
  · have hcb : c ≤ b := le_of_not_gt hbc'
    have hbceq : b = c := le_antisymm hbc hcb
    have hsum2 : (∑ j ∈ Finset.Icc (b + 1) c, f j) = 0 := by
      subst c
      simp
    calc
      (∑ j ∈ Finset.Icc a c, f j) = (∑ j ∈ Finset.Icc a b, f j) := by rw [hbceq]
      _ = (∑ j ∈ Finset.Icc a b, f j) + (∑ j ∈ Finset.Icc (b + 1) c, f j) := by rw [hsum2]; ring

/-- Σ_{i∈Icc 1 b} g i = Σ_{j∈range b} g (j+1) -/
lemma sum_Icc1_eq_range_pred (b : ℕ) (g : ℕ → ℝ) :
    (∑ i ∈ Finset.Icc 1 b, g i) = (∑ j ∈ Finset.range b, g (j + 1)) := by
  refine Finset.sum_bij (fun a ha => a - 1) ?hi ?hinj ?hsurj ?hval
  · intro a ha
    rw [Finset.mem_range]
    have h1 : 1 ≤ a := (Finset.mem_Icc.mp ha).1
    have h2 : a ≤ b := (Finset.mem_Icc.mp ha).2
    omega
  · intro a1 ha1 a2 ha2 h
    have h1 : 1 ≤ a1 := (Finset.mem_Icc.mp ha1).1
    have h2 : 1 ≤ a2 := (Finset.mem_Icc.mp ha2).1
    omega
  · intro x hx
    have hxb : x < b := (Finset.mem_range.mp hx)
    refine ⟨x + 1, ?_, ?_⟩
    · rw [Finset.mem_Icc]
      exact ⟨by omega, by omega⟩
    · omega
  · intro a ha
    have hge : 1 ≤ a := (Finset.mem_Icc.mp ha).1
    rw [Nat.sub_add_cancel hge]

/-- telescoping coefficients: Σ_{i∈Icc1b}(100^i-100^{i-1}) = 100^b - 1 -/
lemma coef_tel (b : ℕ) : (∑ i ∈ Finset.Icc 1 b, ((100 : ℝ) ^ i - (100 : ℝ) ^ (i - 1))) = (100 : ℝ) ^ b - 1 := by
  rw [sum_Icc1_eq_range_pred b (fun i => (100 : ℝ) ^ i - (100 : ℝ) ^ (i - 1))]
  have h := Finset.sum_range_sub (fun j : ℕ => (100 : ℝ) ^ j) b
  simpa using h

/-- Abel summation identity: Σ_j 100^j d_j = u_0 + Σ_i (100^i-100^{i-1}) u_i,
    u_i := Σ_{j∈Icc i b} d_j -/
lemma abel_identity (b : ℕ) (d : ℕ → ℝ) :
    (∑ j ∈ Finset.range (b + 1), (100 : ℝ) ^ j * d j)
      = (∑ j ∈ Finset.Icc 0 b, d j)
        + ∑ i ∈ Finset.Icc 1 b,
            (((100 : ℝ) ^ i - (100 : ℝ) ^ (i - 1)) * (∑ j ∈ Finset.Icc i b, d j)) := by
  induction b with
  | zero =>
      simp
  | succ b ih =>
      have hA : (∑ j ∈ Finset.range (b + 2), (100 : ℝ) ^ j * d j)
          = (∑ j ∈ Finset.range (b + 1), (100 : ℝ) ^ j * d j) + (100 : ℝ) ^ (b + 1) * d (b + 1) := by
        rw [Finset.sum_range_succ]
      have h1 : (∑ j ∈ Finset.Icc 0 (b + 1), d j) = (∑ j ∈ Finset.Icc 0 b, d j) + d (b + 1) := by
        simpa using (Finset.sum_Icc_succ_top (a := 0) (b := b) (by omega : 0 ≤ b + 1) d)
      have hsplit :
          (∑ i ∈ Finset.Icc 1 (b + 1), (((100 : ℝ) ^ i - (100 : ℝ) ^ (i - 1)) *
              (∑ j ∈ Finset.Icc i (b + 1), d j)))
          = (∑ i ∈ Finset.Icc 1 b, (((100 : ℝ) ^ i - (100 : ℝ) ^ (i - 1)) *
                (∑ j ∈ Finset.Icc i (b + 1), d j)))
            + (((100 : ℝ) ^ (b + 1) - (100 : ℝ) ^ b) * (∑ j ∈ Finset.Icc (b + 1) (b + 1), d j)) := by
        simpa using (Finset.sum_Icc_succ_top (a := 1) (b := b) (by omega : 1 ≤ b + 1)
          (fun i => (((100 : ℝ) ^ i - (100 : ℝ) ^ (i - 1)) * (∑ j ∈ Finset.Icc i (b + 1), d j))))
      have hmid : (∑ i ∈ Finset.Icc 1 b, (((100 : ℝ) ^ i - (100 : ℝ) ^ (i - 1)) *
              (∑ j ∈ Finset.Icc i (b + 1), d j)))
          = (∑ i ∈ Finset.Icc 1 b, (((100 : ℝ) ^ i - (100 : ℝ) ^ (i - 1)) *
                ((∑ j ∈ Finset.Icc i b, d j) + d (b + 1)))) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hiL : i ≤ b + 1 := by
          have hb' := (Finset.mem_Icc.mp hi).2
          omega
        have hsub := Finset.sum_Icc_succ_top (a := i) (b := b) hiL d
        rw [hsub]
      have hsing : (∑ j ∈ Finset.Icc (b + 1) (b + 1), d j) = d (b + 1) := by
        simp [Finset.Icc_self]
      calc
        (∑ j ∈ Finset.range (b + 2), (100 : ℝ) ^ j * d j)
            = (∑ j ∈ Finset.range (b + 1), (100 : ℝ) ^ j * d j) + (100 : ℝ) ^ (b + 1) * d (b + 1) := hA
        _ = ((∑ j ∈ Finset.Icc 0 b, d j)
              + ∑ i ∈ Finset.Icc 1 b,
                  (((100 : ℝ) ^ i - (100 : ℝ) ^ (i - 1)) * (∑ j ∈ Finset.Icc i b, d j)))
            + (100 : ℝ) ^ (b + 1) * d (b + 1) := by rw [ih]
        _ = (∑ j ∈ Finset.Icc 0 (b + 1), d j)
              + ∑ i ∈ Finset.Icc 1 (b + 1),
                  (((100 : ℝ) ^ i - (100 : ℝ) ^ (i - 1)) * (∑ j ∈ Finset.Icc i (b + 1), d j)) := by
              rw [h1]
              rw [hsplit, hmid, hsing]
              simp_rw [mul_add]
              rw [Finset.sum_add_distrib]
              rw [← Finset.sum_mul]
              rw [coef_tel]
              ring

/-- If the plain sum is negative, some weighted suffix tail is negative. -/
lemma exists_neg_tail (b : ℕ) (d : ℕ → ℝ)
    (hneg : (∑ j ∈ Finset.range (b + 1), (100 : ℝ) ^ j * d j) < 0) :
    ∃ i, i ≤ b ∧ (∑ j ∈ Finset.Icc i b, d j) < 0 := by
  by_contra hne
  have hall : ∀ i, i ≤ b → 0 ≤ ∑ j ∈ Finset.Icc i b, d j := by
    intro i hi
    by_contra hlt
    exact hne ⟨i, hi, (lt_of_not_ge hlt)⟩
  have hnon : 0 ≤ (∑ j ∈ Finset.range (b + 1), (100 : ℝ) ^ j * d j) := by
    rw [abel_identity b d]
    have hu0 : 0 ≤ ∑ j ∈ Finset.Icc 0 b, d j := hall 0 (by omega)
    have hsum : 0 ≤ ∑ i ∈ Finset.Icc 1 b,
        (((100 : ℝ) ^ i - (100 : ℝ) ^ (i - 1)) * (∑ j ∈ Finset.Icc i b, d j)) := by
      apply Finset.sum_nonneg
      intro i hi
      apply mul_nonneg
      · have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
        have hpow : (100 : ℝ) ^ i = (100 : ℝ) * (100 : ℝ) ^ (i - 1) := by
          calc
            (100 : ℝ) ^ i = (100 : ℝ) ^ (1 + (i - 1)) := by congr 1; omega
            _ = (100 : ℝ) ^ 1 * (100 : ℝ) ^ (i - 1) := by rw [pow_add]
            _ = (100 : ℝ) * (100 : ℝ) ^ (i - 1) := by norm_num
        rw [hpow]
        have hpos : 0 ≤ 99 * (100 : ℝ) ^ (i - 1) := by positivity
        nlinarith
      · exact hall i ((Finset.mem_Icc.mp hi).2)
    linarith
  linarith

/-! ## weight bounds -/

/-- (100 : ℝ)^j · wlev j = 1 -/
lemma wlev_mul_pow (j : ℕ) : (100 : ℝ) ^ j * wlev j = 1 := by
  unfold wlev
  exact mul_inv_cancel₀ (by positivity)

/-- wlev (b+1) ≤ (9/100)·wlev j for j ≤ b -/
lemma wlev_bound (b j : ℕ) (hj : j ≤ b) : wlev (b + 1) ≤ (9 / 100) * wlev j := by
  calc
    wlev (b + 1) ≤ wlev (j + 1) := wlev_le_of_le (by omega)
    _ = (1 / 100 : ℝ) * wlev j := by
      rw [wlev_succ]
      norm_num [q]
    _ ≤ (9 / 100) * wlev j := by
      exact mul_le_mul_of_nonneg_right (by norm_num) (wlev_nonneg j)


/-- wlev (b+1) = (1/100)·wlev b -/
lemma wlev_succ_hundred (b : ℕ) : wlev (b + 1) = (1 / 100 : ℝ) * wlev b := by
  rw [wlev_succ]
  norm_num [q]

/-! ## counting in level sets -/

/-- |A ∩ unionBelow S' b| = Σ_{j≤b} |A ∩ levelSet S' j| -/
lemma ncard_inter_unionBelow (N : Sys X) (A S' : Set X) (b : ℕ) :
    ((A ∩ N.unionBelow S' b).ncard : ℝ) = ∑ j ∈ Finset.range (b + 1), ((A ∩ N.levelSet S' j).ncard : ℝ) := by
  classical
  induction b with
  | zero =>
      have hsub : N.unionBelow S' 0 = N.levelSet S' 0 := by
        ext x
        rw [N.mem_unionBelow]
        constructor
        · rintro ⟨j, hj, hx⟩
          have : j = 0 := by omega
          subst j
          exact hx
        · intro hx
          exact ⟨0, by omega, hx⟩
      calc
        ((A ∩ N.unionBelow S' 0).ncard : ℝ) = ((A ∩ N.levelSet S' 0).ncard : ℝ) := by rw [hsub]
        _ = ∑ j ∈ Finset.range 1, ((A ∩ N.levelSet S' j).ncard : ℝ) := by
          simp
  | succ b ih =>
      have hsub : N.unionBelow S' (b + 1) = N.unionBelow S' b ∪ N.levelSet S' (b + 1) := by
        ext x
        rw [N.mem_unionBelow, Set.mem_union]
        constructor
        · rintro ⟨j, hj, hx⟩
          by_cases h : j ≤ b
          · exact Or.inl ⟨j, h, hx⟩
          · refine Or.inr ?_
            have : j = b + 1 := by omega
            subst j
            exact hx
        · intro hx
          rcases hx with ⟨j, hj, hx⟩ | hx
          · exact ⟨j, by omega, hx⟩
          · exact ⟨b + 1, by omega, hx⟩
      have hdisj : Disjoint (A ∩ N.unionBelow S' b) (A ∩ N.levelSet S' (b + 1)) := by
        rw [Set.disjoint_left]
        intro x hx1 hx2
        rcases hx1 with ⟨hxA, hxub⟩
        rcases (N.mem_unionBelow).1 hxub with ⟨j, hj, hxL'⟩
        have hxL : x ∈ N.levelSet S' (b + 1) := hx2.2
        have hne : j ≠ b + 1 := by omega
        exact ((Set.disjoint_left).mp (N.levelSet_disjoint S' hne)) hxL' hxL
      calc
        ((A ∩ N.unionBelow S' (b + 1)).ncard : ℝ)
            = ((A ∩ (N.unionBelow S' b ∪ N.levelSet S' (b + 1))).ncard : ℝ) := by rw [hsub]
        _ = (((A ∩ N.unionBelow S' b) ∪ (A ∩ N.levelSet S' (b + 1))).ncard : ℝ) := by
            congr 1
            rw [Set.inter_union_distrib_left]
        _ = ((A ∩ N.unionBelow S' b).ncard : ℝ) + ((A ∩ N.levelSet S' (b + 1)).ncard : ℝ) := by
            have hc := Set.ncard_union_eq hdisj
            exact_mod_cast hc
        _ = (∑ j ∈ Finset.range (b + 1), ((A ∩ N.levelSet S' j).ncard : ℝ))
            + ((A ∩ N.levelSet S' (b + 1)).ncard : ℝ) := by rw [ih]
        _ = ∑ j ∈ Finset.range (b + 2), ((A ∩ N.levelSet S' j).ncard : ℝ) := by
            have hs := Finset.sum_range_succ (fun j => ((A ∩ N.levelSet S' j).ncard : ℝ)) (b + 1)
            rw [show b + 2 = (b + 1) + 1 by omega]
            exact hs.symm

/-- If A lies in the union of level sets 0..b, its size is the sum of the A-part counts. -/
lemma ncard_eq_sum_levels (N : Sys X) (A S' : Set X) (b : ℕ) (hA : A ⊆ N.unionBelow S' b) :
    (A.ncard : ℝ) = ∑ j ∈ Finset.range (b + 1), ((A ∩ N.levelSet S' j).ncard : ℝ) := by
  have h1 := ncard_inter_unionBelow N A S' b
  have hEq : A ∩ N.unionBelow S' b = A := by
    ext x
    constructor
    · intro hx
      exact hx.1
    · intro hx
      exact ⟨hx, hA hx⟩
  calc
    (A.ncard : ℝ) = ((A ∩ N.unionBelow S' b).ncard : ℝ) := by
      exact congrArg (fun s : Set X => (s.ncard : ℝ)) hEq.symm
    _ = ∑ j ∈ Finset.range (b + 1), ((A ∩ N.levelSet S' j).ncard : ℝ) := h1


/-- split a range sum into a prefix and an Icc tail -/
lemma sum_range_split (c b : ℕ) (h : c + 1 ≤ b) (f : ℕ → ℝ) :
    (∑ j ∈ Finset.range (b + 1), f j) = (∑ j ∈ Finset.range (c + 1), f j) + (∑ j ∈ Finset.Icc (c + 1) b, f j) := by
  have hdisj : Disjoint (Finset.range (c + 1)) (Finset.Icc (c + 1) b) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    have hx1' : x < c + 1 := (Finset.mem_range).1 hx1
    have hx2' : c + 1 ≤ x := (Finset.mem_Icc.mp hx2).1
    omega
  have hunion : Finset.range (b + 1) = Finset.range (c + 1) ∪ Finset.Icc (c + 1) b := by
    apply Finset.ext
    intro x
    rw [Finset.mem_union, Finset.mem_range, Finset.mem_range, Finset.mem_Icc]
    constructor
    · intro hx
      by_cases hxc : x < c + 1
      · exact Or.inl hxc
      · refine Or.inr ?_
        constructor
        · omega
        · omega
    · intro hx
      rcases hx with hx | hx
      · omega
      · omega
  rw [hunion, Finset.sum_union hdisj]

/-- level sets above the bound are empty -/
lemma levelSet_eq_empty_of_gt_tau (N : Sys X) {S' : Set X} (hS' : S' ∈ N.F)
    (hB : N.LevelBounded) {j : ℕ} (hj : N.τ < j) : N.levelSet S' j = ∅ := by
  exact N.levelSet_eq_empty_of_gt (hB S' hS') hj

/-- weightAbove splits at an intermediate index -/
lemma weightAbove_split_index (N : Sys X) (A S' : Set X) {b c b' : ℕ}
    (hbc : c + 1 = b') (hb'le : b' ≤ b) (hbτ : b ≤ N.τ) :
    N.weightAbove S' A c = (∑ j ∈ Finset.Icc b' b, ((A ∩ N.levelSet S' j).ncard : ℝ) * wlev j)
      + N.weightAbove S' A b := by
  unfold Sys.weightAbove
  calc
    (∑ j ∈ Finset.Icc (c + 1) N.τ, ((A ∩ N.levelSet S' j).ncard : ℝ) * wlev j)
        = (∑ j ∈ Finset.Icc b' N.τ, ((A ∩ N.levelSet S' j).ncard : ℝ) * wlev j) := by rw [hbc]
    _ = (∑ j ∈ Finset.Icc b' b, ((A ∩ N.levelSet S' j).ncard : ℝ) * wlev j)
        + (∑ j ∈ Finset.Icc (b + 1) N.τ, ((A ∩ N.levelSet S' j).ncard : ℝ) * wlev j) :=
          sum_Icc_split_at (a := b') (b := b) (c := N.τ)
            (by omega : b' ≤ b) hbτ (fun j => ((A ∩ N.levelSet S' j).ncard : ℝ) * wlev j)

/-- algebra: D ≥ 0 for the new-fragment weight inequality -/
lemma frag2_aux (Gb Sc nB tU n_c tT wB wC : ℝ)
    (hG1 : (1 / 100 : ℝ) * wB * Sc ≤ (9 / 100) * Gb)
    (hNB : nB = n_c + Sc)
    (hwB : 0 ≤ wB)
    (htU : tT ≤ tU)
    (hnc : tT ≤ n_c)
    (hwle : wB ≤ wC) :
    0 ≤ (9 / 100) * Gb - (1 / 100) * wB * (nB - tU) + (1 / 100) * wC * (n_c - tT) := by
  have hA : 0 ≤ (9 / 100) * Gb - (1 / 100) * wB * Sc := by linarith
  have h1 : 0 ≤ wB * (tU - tT) := mul_nonneg hwB (by linarith)
  have h2 : 0 ≤ (wC - wB) * (n_c - tT) := mul_nonneg (by linarith) (by linarith)
  have hrest : 0 ≤ wB * (tU - tT) + (wC - wB) * (n_c - tT) := by linarith
  rw [hNB]
  have hmain : (9 / 100) * Gb - (1 / 100) * wB * (n_c + Sc - tU) + (1 / 100) * wC * (n_c - tT)
      = ((9 / 100) * Gb - (1 / 100) * wB * Sc) + (1 / 100) * (wB * (tU - tT) + (wC - wB) * (n_c - tT)) := by
    ring
  rw [hmain]
  have h3 : 0 ≤ (1 / 100 : ℝ) * (wB * (tU - tT) + (wC - wB) * (n_c - tT)) := by
    exact mul_nonneg (by norm_num) hrest
  linarith

/-- range (b+1) as an Icc starting at 0 -/
lemma sum_range_eq_sum_Icc0 (b : ℕ) (f : ℕ → ℝ) :
    (∑ j ∈ Finset.range (b + 1), f j) = (∑ j ∈ Finset.Icc 0 b, f j) := by
  congr 1
  apply Finset.ext
  intro x
  simp

/-- weight (all levels 0..τ) splits at b -/
lemma weight_eq_above_split (N : Sys X) (A S' : Set X) {b : ℕ} (hb : b ≤ N.τ) :
    N.weight S' A = (∑ j ∈ Finset.Icc 0 b, ((A ∩ N.levelSet S' j).ncard : ℝ) * wlev j)
      + N.weightAbove S' A b := by
  unfold Sys.weight Sys.weightAbove
  calc
    (∑ j ∈ Finset.range (N.τ + 1), ((A ∩ N.levelSet S' j).ncard : ℝ) * wlev j)
        = (∑ j ∈ Finset.Icc 0 N.τ, ((A ∩ N.levelSet S' j).ncard : ℝ) * wlev j) := sum_range_eq_sum_Icc0 N.τ _
    _ = (∑ j ∈ Finset.Icc 0 b, ((A ∩ N.levelSet S' j).ncard : ℝ) * wlev j)
        + (∑ j ∈ Finset.Icc (b + 1) N.τ, ((A ∩ N.levelSet S' j).ncard : ℝ) * wlev j) :=
          sum_Icc_split_at (a := 0) (b := b) (c := N.τ) (by omega) hb
            (fun j => ((A ∩ N.levelSet S' j).ncard : ℝ) * wlev j)

theorem theorem_obsTp (N : Sys X) (S : Set X) (W U : Set X) (b : ℕ) (hS : S ∈ N.F)
    (hB : N.LevelBounded) (hTot : ∀ T ∈ N.F, ((10 : ℝ) ^ 8)⁻¹ ≤ N.totalWeight T)
    (hbad : N.Bad ((10 : ℝ) ^ 10)⁻¹ W)
    (hmin : N.MinFragmentAt S W U b hS hB)
    {S' : Set X} (hfr : N.IsFragment S W U b S') :
    (9 / 10 : ℝ) * (N.prefixCount S b : ℝ) ≤ (U.ncard : ℝ) := by
  classical
  let sCnt : ℕ → ℝ := fun j => (N.sCount S' j : ℝ)
  let uCnt : ℕ → ℝ := fun j => ((U ∩ N.levelSet S' j).ncard : ℝ)
  have hS'F : S' ∈ N.F := hfr.1.1
  have hprof : ∀ j, j ≤ b → N.sCount S j = N.sCount S' j := hfr.1.2
  have hfrag1 : ∀ j ≤ b, N.levelSet S' j ⊆ W ∪ U := hfr.2.2.2.1
  have hdisjWU : Disjoint U W := hfr.2.2.1
  have hfr2 : N.weightAbove S' (W ∪ U) b ≥ (100 : ℝ)⁻¹ *
      (N.weightAbove S' S' b - wlev b * ((N.prefixCount S b : ℝ) - (U.ncard : ℝ))) := hfr.2.2.2.2
  have hbτ : b ≤ N.τ := by
    have hminle : N.MinIndex S W hS hB ≤ N.τ :=
      minIndex_min N S W hS hB (S \ W) S (N.sdiff_isFragment S W hS hB)
    rw [hmin.1]
    exact hminle
  -- every element of the minimal fragment U has level ≤ b in the witness S'
  have hUbelow : U ⊆ N.unionBelow S' b := by
    intro x hxU
    refine ⟨N.lv S' x, level_le_b_of_minimal N S W U b hS hB hmin hfr hxU,
      ⟨mem_S'_of_minimal N S W U b hS hB hmin hfr hxU, rfl⟩⟩
  have hs_count : (∑ j ∈ Finset.range (b + 1), sCnt j) = (N.prefixCount S b : ℝ) := by
    unfold sCnt Sys.prefixCount
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hprof j (by simpa using hj)]
  have ht_count : (∑ j ∈ Finset.range (b + 1), uCnt j) = (U.ncard : ℝ) := by
    have h1 := ncard_eq_sum_levels N U S' b hUbelow
    unfold uCnt
    exact h1.symm
  have hs_nonneg : ∀ j, 0 ≤ sCnt j := by
    intro j
    unfold sCnt
    positivity
  have hu_le_s : ∀ j, uCnt j ≤ sCnt j := by
    intro j
    unfold uCnt sCnt
    have hle : (U ∩ N.levelSet S' j).ncard ≤ (N.levelSet S' j).ncard := by
      exact Set.ncard_le_ncard (by intro x hx; exact hx.2)
    exact_mod_cast hle
  by_contra hnot
  have htlt : (U.ncard : ℝ) < (9 / 10) * (N.prefixCount S b : ℝ) := lt_of_not_ge hnot
  have hC : (∑ j ∈ Finset.range (b + 1), (uCnt j - (9 / 10) * sCnt j)) < 0 := by
    have hsum : (∑ j ∈ Finset.range (b + 1), (uCnt j - (9 / 10) * sCnt j))
        = (∑ j ∈ Finset.range (b + 1), uCnt j) - (9 / 10) * (∑ j ∈ Finset.range (b + 1), sCnt j) := by
      calc
        (∑ j ∈ Finset.range (b + 1), (uCnt j - (9 / 10) * sCnt j))
            = (∑ j ∈ Finset.range (b + 1), uCnt j) - (∑ j ∈ Finset.range (b + 1), (9 / 10) * sCnt j) := by
              rw [Finset.sum_sub_distrib]
        _ = (∑ j ∈ Finset.range (b + 1), uCnt j) - (9 / 10) * (∑ j ∈ Finset.range (b + 1), sCnt j) := by
              rw [← Finset.mul_sum]
    rw [hsum, ht_count, hs_count]
    linarith
  have hsumneg : (∑ j ∈ Finset.range (b + 1), (100 : ℝ) ^ j * (wlev j * (uCnt j - (9 / 10) * sCnt j))) < 0 := by
    have hterm : ∀ j, j ∈ Finset.range (b + 1) →
        (100 : ℝ) ^ j * (wlev j * (uCnt j - (9 / 10) * sCnt j)) = uCnt j - (9 / 10) * sCnt j := by
      intro j hj
      calc
        (100 : ℝ) ^ j * (wlev j * (uCnt j - (9 / 10) * sCnt j))
            = ((100 : ℝ) ^ j * wlev j) * (uCnt j - (9 / 10) * sCnt j) := by ring
        _ = uCnt j - (9 / 10) * sCnt j := by rw [wlev_mul_pow j]; ring
    calc
      (∑ j ∈ Finset.range (b + 1), (100 : ℝ) ^ j * (wlev j * (uCnt j - (9 / 10) * sCnt j)))
          = (∑ j ∈ Finset.range (b + 1), (uCnt j - (9 / 10) * sCnt j)) := by
            exact Finset.sum_congr rfl hterm
      _ < 0 := hC
  rcases exists_neg_tail b (fun j => wlev j * (uCnt j - (9 / 10) * sCnt j)) hsumneg with ⟨b', hb'le, hneg_b'⟩
  by_cases hb'pos : 0 < b'
  · -- case b' ≥ 1 : the tail produces a fragment at the smaller index c = b'-1
    let c : ℕ := b' - 1
    let T' : Set X := N.unionBelow S' c ∩ U
    let Gb : ℝ := ∑ j ∈ Finset.Icc b' b, sCnt j * wlev j
    let Sc : ℝ := ∑ j ∈ Finset.Icc b' b, sCnt j
    let nB : ℝ := (N.prefixCount S b : ℝ)
    let nC : ℝ := (N.prefixCount S c : ℝ)
    let tU : ℝ := (U.ncard : ℝ)
    let tT : ℝ := (T'.ncard : ℝ)
    have hc1 : c + 1 = b' := by
      unfold c
      omega
    have hcle : c ≤ b := by omega
    have hc_lt : c < b := by omega
    have hT'subU : T' ⊆ U := by
      intro x hx
      exact hx.2
    have hT'below : T' ⊆ N.unionBelow S' c := by
      intro x hx
      exact hx.1
    have htT_le_tU : tT ≤ tU := by
      unfold tT tU
      have hle : (T'.ncard) ≤ (U.ncard) := Set.ncard_le_ncard hT'subU
      exact_mod_cast hle
    have hnc_count : (∑ j ∈ Finset.range (c + 1), sCnt j) = (N.prefixCount S c : ℝ) := by
      unfold sCnt Sys.prefixCount
      rw [Nat.cast_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [hprof j (by have hj' := (Finset.mem_range.mp hj); omega)]
    have htT_count : (T'.ncard : ℝ) = ∑ j ∈ Finset.range (c + 1), uCnt j := by
      have h1 := ncard_eq_sum_levels N T' S' c hT'below
      calc
        (T'.ncard : ℝ) = ∑ j ∈ Finset.range (c + 1), ((T' ∩ N.levelSet S' j).ncard : ℝ) := h1
        _ = ∑ j ∈ Finset.range (c + 1), uCnt j := by
          apply Finset.sum_congr rfl
          intro j hj
          have hjc : j ≤ c := by
            have hj' := (Finset.mem_range.mp hj)
            omega
          have hset : T' ∩ N.levelSet S' j = U ∩ N.levelSet S' j := by
            ext x
            constructor
            · intro hx
              rcases hx with ⟨hx1, hxL⟩
              rcases hx1 with ⟨hxub, hxU⟩
              exact ⟨hxU, hxL⟩
            · intro hx
              rcases hx with ⟨hxU, hxL⟩
              exact ⟨⟨⟨j, hjc, hxL⟩, hxU⟩, hxL⟩
          have hc : (T' ∩ N.levelSet S' j).ncard = (U ∩ N.levelSet S' j).ncard := congrArg Set.ncard hset
          unfold T' uCnt
          exact_mod_cast hc
    have htT_le_nc : tT ≤ nC := by
      calc
        tT = ∑ j ∈ Finset.range (c + 1), uCnt j := htT_count
        _ ≤ ∑ j ∈ Finset.range (c + 1), sCnt j := by
          apply Finset.sum_le_sum
          intro j hj
          exact hu_le_s j
        _ = nC := by
          unfold nC
          exact hnc_count
    have hnB : nB = nC + Sc := by
      unfold nB nC Sc
      calc
        (N.prefixCount S b : ℝ) = (∑ j ∈ Finset.range (b + 1), sCnt j) := by rw [hs_count]
        _ = (∑ j ∈ Finset.range (c + 1), sCnt j) + (∑ j ∈ Finset.Icc (c + 1) b, sCnt j) :=
              sum_range_split c b (by omega : c + 1 ≤ b) sCnt
        _ = (∑ j ∈ Finset.range (c + 1), sCnt j) + (∑ j ∈ Finset.Icc b' b, sCnt j) := by rw [hc1]
        _ = (N.prefixCount S c : ℝ) + (∑ j ∈ Finset.Icc b' b, sCnt j) := by rw [hnc_count]
    -- T' lies in no level set of S' with index ≥ b'
    have hT'high : ∀ j, b' ≤ j → Disjoint T' (N.levelSet S' j) := by
      intro j hj
      rw [Set.disjoint_left]
      intro x hxT' hxL
      rcases hxT' with ⟨hxub, hxU⟩
      rcases (N.mem_unionBelow).1 hxub with ⟨j', hj', hxL'⟩
      have hne : j' ≠ j := by omega
      exact (Set.disjoint_left.mp (N.levelSet_disjoint S' hne)) hxL' hxL
    -- U lies in no level set of S' with index ≥ b+1
    have hUhigh : ∀ j, b + 1 ≤ j → Disjoint U (N.levelSet S' j) := by
      intro j hj
      rw [Set.disjoint_left]
      intro x hxU hxL
      rcases (N.mem_unionBelow).1 (hUbelow hxU) with ⟨j', hj', hxL'⟩
      have hne : j' ≠ j := by omega
      exact (Set.disjoint_left.mp (N.levelSet_disjoint S' hne)) hxL' hxL
    -- new fragment: level sets ≤ c are covered by W ∪ T'
    have hnew1 : ∀ j ≤ c, N.levelSet S' j ⊆ W ∪ T' := by
      intro j hj x hxL
      have hxWU := hfrag1 j (by omega) hxL
      rcases hxWU with hxW | hxU
      · exact Or.inl hxW
      · exact Or.inr ⟨⟨j, hj, hxL⟩, hxU⟩
    -- W-part of the level sets b'..b dominates (1/10) of their full weight
    have hWcount : ∀ j, j ∈ Finset.Icc b' b → ((W ∩ N.levelSet S' j).ncard : ℝ) = sCnt j - uCnt j := by
      intro j hj
      have hjb : j ≤ b := (Finset.mem_Icc.mp hj).2
      have hle : N.levelSet S' j ⊆ W ∪ U := hfrag1 j hjb
      have hEq : N.levelSet S' j = (W ∩ N.levelSet S' j) ∪ (U ∩ N.levelSet S' j) := by
        apply Set.ext
        intro x
        constructor
        · intro hx
          have hwU := hle hx
          rcases hwU with hxW | hxU
          · exact Or.inl ⟨hxW, hx⟩
          · exact Or.inr ⟨hxU, hx⟩
        · intro hx
          rcases hx with ⟨hxW, hxL⟩ | ⟨hxU, hxL⟩ <;> exact hxL
      have hdisj : Disjoint (W ∩ N.levelSet S' j) (U ∩ N.levelSet S' j) := by
        rw [Set.disjoint_left]
        intro x hx1 hx2
        exact (Set.disjoint_left.mp hdisjWU) hx2.1 hx1.1
      have hc : N.sCount S' j = (W ∩ N.levelSet S' j).ncard + (U ∩ N.levelSet S' j).ncard := by
        unfold Sys.sCount
        have h1 : (N.levelSet S' j).ncard = ((W ∩ N.levelSet S' j) ∪ (U ∩ N.levelSet S' j)).ncard := congrArg Set.ncard hEq
        rw [h1, Set.ncard_union_eq hdisj]
      have hcR : (N.sCount S' j : ℝ) = ((W ∩ N.levelSet S' j).ncard : ℝ) + ((U ∩ N.levelSet S' j).ncard : ℝ) := by
        rw [← Nat.cast_add]
        exact_mod_cast hc
      unfold sCnt uCnt
      linarith
    have hWb_ge : (1 / 10 : ℝ) * Gb ≤ ∑ j ∈ Finset.Icc b' b, ((W ∩ N.levelSet S' j).ncard : ℝ) * wlev j := by
      -- hneg_b' : Σ wlev_j (uCnt_j - (9/10)sCnt_j) < 0
      have h1 : (∑ j ∈ Finset.Icc b' b, (sCnt j - uCnt j) * wlev j)
          = (∑ j ∈ Finset.Icc b' b, ((W ∩ N.levelSet S' j).ncard : ℝ) * wlev j) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hWcount j hj]
      have h2 : (1 / 10 : ℝ) * Gb ≤ (∑ j ∈ Finset.Icc b' b, (sCnt j - uCnt j) * wlev j) := by
        unfold Gb
        -- from hneg_b'
        have hneg' : (∑ j ∈ Finset.Icc b' b, wlev j * (uCnt j - (9 / 10) * sCnt j)) < 0 := hneg_b'
        have heq : (∑ j ∈ Finset.Icc b' b, wlev j * (uCnt j - (9 / 10) * sCnt j))
            = (∑ j ∈ Finset.Icc b' b, uCnt j * wlev j) - (9 / 10) * (∑ j ∈ Finset.Icc b' b, sCnt j * wlev j) := by
          calc
            (∑ j ∈ Finset.Icc b' b, wlev j * (uCnt j - (9 / 10) * sCnt j))
                = (∑ j ∈ Finset.Icc b' b, (uCnt j * wlev j - (9 / 10) * (sCnt j * wlev j))) := by
                  apply Finset.sum_congr rfl
                  intro j hj
                  ring
            _ = (∑ j ∈ Finset.Icc b' b, uCnt j * wlev j) - (∑ j ∈ Finset.Icc b' b, (9 / 10) * (sCnt j * wlev j)) := by
                  rw [Finset.sum_sub_distrib]
            _ = (∑ j ∈ Finset.Icc b' b, uCnt j * wlev j) - (9 / 10) * (∑ j ∈ Finset.Icc b' b, sCnt j * wlev j) := by
                  congr 1
                  rw [← Finset.mul_sum]
        have heq2 : (∑ j ∈ Finset.Icc b' b, (sCnt j - uCnt j) * wlev j)
            = (∑ j ∈ Finset.Icc b' b, sCnt j * wlev j) - (∑ j ∈ Finset.Icc b' b, uCnt j * wlev j) := by
          calc
            (∑ j ∈ Finset.Icc b' b, (sCnt j - uCnt j) * wlev j)
                = (∑ j ∈ Finset.Icc b' b, (sCnt j * wlev j - uCnt j * wlev j)) := by
                  apply Finset.sum_congr rfl
                  intro j hj
                  ring
            _ = (∑ j ∈ Finset.Icc b' b, sCnt j * wlev j) - (∑ j ∈ Finset.Icc b' b, uCnt j * wlev j) := by
                  rw [Finset.sum_sub_distrib]
        have hneg'' : (∑ j ∈ Finset.Icc b' b, uCnt j * wlev j) < (9 / 10) * (∑ j ∈ Finset.Icc b' b, sCnt j * wlev j) := by
          rw [heq] at hneg'
          linarith
        nlinarith
      rw [← h1]
      exact h2
    -- weight-above decompositions
    have hWAc : N.weightAbove S' S' c = Gb + N.weightAbove S' S' b := by
      have hsplit := weightAbove_split_index N S' S' (b := b) (c := c) (b' := b') hc1 hb'le hbτ
      -- hsplit : weightAbove S' S' c = Σ_{Icc b'b}((S'∩lvl).ncard)*wlev + weightAbove S' S' b
      unfold Gb
      rw [hsplit]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      congr 1
      -- (S' ∩ lvl_j) = lvl_j
      have hlvl : N.levelSet S' j ⊆ S' := N.levelSet_subset S' j
      have hEqS : S' ∩ N.levelSet S' j = N.levelSet S' j := by
        ext x
        constructor
        · intro hx; exact hx.2
        · intro hx; exact ⟨hlvl hx, hx⟩
      rw [hEqS]
      rfl
    have hunion_erase : ∀ {A : Set X} {j : ℕ}, Disjoint A (N.levelSet S' j) →
        (W ∪ A) ∩ N.levelSet S' j = W ∩ N.levelSet S' j := by
      intro A j hA
      ext x
      constructor
      · intro hx
        rcases hx with ⟨hxWU, hxL⟩
        rcases hxWU with hxW | hxA
        · exact ⟨hxW, hxL⟩
        · exfalso
          exact (Set.disjoint_left.mp hA) hxA hxL
      · intro hx
        exact ⟨Or.inl hx.1, hx.2⟩
    have hG1 : (1 / 100 : ℝ) * wlev b * Sc ≤ (9 / 100) * Gb := by
      calc
        (1 / 100 : ℝ) * wlev b * Sc = (∑ j ∈ Finset.Icc b' b, ((1 / 100 : ℝ) * wlev b) * sCnt j) := by
          unfold Sc
          rw [Finset.mul_sum]
        _ ≤ (∑ j ∈ Finset.Icc b' b, (9 / 100) * (sCnt j * wlev j)) := by
          apply Finset.sum_le_sum
          intro j hj
          have hjb : j ≤ b := (Finset.mem_Icc.mp hj).2
          have hb1 := wlev_bound b j hjb
          have hb2 : (1 / 100 : ℝ) * wlev b ≤ (9 / 100) * wlev j := by
            rw [← wlev_succ_hundred b]
            exact hb1
          have hs : 0 ≤ sCnt j := hs_nonneg j
          calc
            ((1 / 100 : ℝ) * wlev b) * sCnt j ≤ ((9 / 100) * wlev j) * sCnt j := mul_le_mul_of_nonneg_right hb2 hs
            _ = (9 / 100) * (sCnt j * wlev j) := by ring
        _ = (9 / 100) * Gb := by
          unfold Gb
          rw [Finset.mul_sum]
    have hMid : (∑ j ∈ Finset.Icc b' b, (((W ∪ T') ∩ N.levelSet S' j).ncard : ℝ) * wlev j)
        = (∑ j ∈ Finset.Icc b' b, ((W ∩ N.levelSet S' j).ncard : ℝ) * wlev j) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjge : b' ≤ j := (Finset.mem_Icc.mp hj).1
      rw [hunion_erase (hT'high j hjge)]
    have hTop1 : (∑ j ∈ Finset.Icc (b + 1) N.τ, (((W ∪ T') ∩ N.levelSet S' j).ncard : ℝ) * wlev j)
        = (∑ j ∈ Finset.Icc (b + 1) N.τ, ((W ∩ N.levelSet S' j).ncard : ℝ) * wlev j) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjge : b' ≤ j := by
        have hj' := (Finset.mem_Icc.mp hj).1
        omega
      rw [hunion_erase (hT'high j hjge)]
    have hTop2 : N.weightAbove S' (W ∪ U) b
        = (∑ j ∈ Finset.Icc (b + 1) N.τ, ((W ∩ N.levelSet S' j).ncard : ℝ) * wlev j) := by
      unfold Sys.weightAbove
      apply Finset.sum_congr rfl
      intro j hj
      have hjge : b + 1 ≤ j := (Finset.mem_Icc.mp hj).1
      rw [hunion_erase (hUhigh j hjge)]
    have hWA_eq : N.weightAbove S' (W ∪ T') c =
        (∑ j ∈ Finset.Icc b' b, ((W ∩ N.levelSet S' j).ncard : ℝ) * wlev j)
          + N.weightAbove S' (W ∪ U) b := by
      unfold Sys.weightAbove
      calc
        (∑ j ∈ Finset.Icc (c + 1) N.τ, (((W ∪ T') ∩ N.levelSet S' j).ncard : ℝ) * wlev j)
            = (∑ j ∈ Finset.Icc b' N.τ, (((W ∪ T') ∩ N.levelSet S' j).ncard : ℝ) * wlev j) := by rw [hc1]
        _ = (∑ j ∈ Finset.Icc b' b, (((W ∪ T') ∩ N.levelSet S' j).ncard : ℝ) * wlev j)
            + (∑ j ∈ Finset.Icc (b + 1) N.τ, (((W ∪ T') ∩ N.levelSet S' j).ncard : ℝ) * wlev j) :=
              sum_Icc_split_at (a := b') (b := b) (c := N.τ) hb'le hbτ
                (fun j => (((W ∪ T') ∩ N.levelSet S' j).ncard : ℝ) * wlev j)
        _ = (∑ j ∈ Finset.Icc b' b, ((W ∩ N.levelSet S' j).ncard : ℝ) * wlev j)
            + (∑ j ∈ Finset.Icc (b + 1) N.τ, (((W ∪ T') ∩ N.levelSet S' j).ncard : ℝ) * wlev j) := by rw [hMid]
        _ = (∑ j ∈ Finset.Icc b' b, ((W ∩ N.levelSet S' j).ncard : ℝ) * wlev j)
            + (∑ j ∈ Finset.Icc (b + 1) N.τ, ((W ∩ N.levelSet S' j).ncard : ℝ) * wlev j) := by rw [hTop1]
        _ = (∑ j ∈ Finset.Icc b' b, ((W ∩ N.levelSet S' j).ncard : ℝ) * wlev j)
            + N.weightAbove S' (W ∪ U) b := by rw [hTop2]
    have hnew2 : N.weightAbove S' (W ∪ T') c ≥ (100 : ℝ)⁻¹ *
        (N.weightAbove S' S' c - wlev c * ((N.prefixCount S c : ℝ) - (T'.ncard : ℝ))) := by
      have hchain1 : (1 / 10 : ℝ) * Gb + (100 : ℝ)⁻¹ *
            (N.weightAbove S' S' b - wlev b * (nB - tU)) ≤ N.weightAbove S' (W ∪ T') c := by
        rw [hWA_eq]
        have h2 : (100 : ℝ)⁻¹ * (N.weightAbove S' S' b - wlev b * (nB - tU)) ≤
            N.weightAbove S' (W ∪ U) b := by
          simpa [nB, tU] using hfr2
        exact add_le_add hWb_ge h2
      have hD : 0 ≤ (9 / 100) * Gb - (1 / 100) * wlev b * (nB - tU)
          + (1 / 100) * wlev c * (nC - tT) := by
        exact frag2_aux Gb Sc nB tU nC tT (wlev b) (wlev c) hG1 hnB (wlev_nonneg b)
          htT_le_tU htT_le_nc (wlev_le_of_le hcle)
      have hdiff : (1 / 10 : ℝ) * Gb + (100 : ℝ)⁻¹ * (N.weightAbove S' S' b - wlev b * (nB - tU))
            - (100 : ℝ)⁻¹ * (N.weightAbove S' S' c - wlev c * (nC - tT))
          = (9 / 100) * Gb - (1 / 100) * wlev b * (nB - tU) + (1 / 100) * wlev c * (nC - tT) := by
        rw [hWAc]
        have hinv : (100 : ℝ)⁻¹ = (1 / 100 : ℝ) := by norm_num
        rw [hinv]
        ring_nf
      have hBleA : (100 : ℝ)⁻¹ * (N.weightAbove S' S' c - wlev c * (nC - tT)) ≤
          (1 / 10 : ℝ) * Gb + (100 : ℝ)⁻¹ * (N.weightAbove S' S' b - wlev b * (nB - tU)) := by
        exact (sub_nonneg.mp (by rw [hdiff]; exact hD))
      exact le_trans hBleA hchain1
    have hTfrag : N.IsFragment S W T' c S' := by
      constructor
      · constructor
        · exact hS'F
        · intro j hj
          exact hprof j (by omega)
      · constructor
        · intro x hx
          exact hfr.2.1 hx.2
        · constructor
          · apply Set.disjoint_left.mpr
            intro x hxT' hxW
            exact (Set.disjoint_left.mp hdisjWU) hxT'.2 hxW
          · constructor
            · exact hnew1
            · exact hnew2
    have hminle : N.MinIndex S W hS hB ≤ c := minIndex_min N S W hS hB T' S' hTfrag
    have hcmin : c < N.MinIndex S W hS hB := by
      rw [← hmin.1]
      exact hc_lt
    omega
  · -- case b' = 0 : U would have to be so small that W∩S' alone carries 1% of the weight of S'
    have hb'0 : b' = 0 := by omega
    let tU : ℝ := (U.ncard : ℝ)
    let nB : ℝ := (N.prefixCount S b : ℝ)
    let G0 : ℝ := ∑ j ∈ Finset.Icc 0 b, sCnt j * wlev j
    let S0 : ℝ := ∑ j ∈ Finset.Icc 0 b, sCnt j
    have htU_nonneg : 0 ≤ tU := by
      unfold tU
      positivity
    have hUhigh0 : ∀ j, b + 1 ≤ j → Disjoint U (N.levelSet S' j) := by
      intro j hj
      rw [Set.disjoint_left]
      intro x hxU hxL
      rcases (N.mem_unionBelow).1 (hUbelow hxU) with ⟨j', hj', hxL'⟩
      have hne : j' ≠ j := by omega
      exact (Set.disjoint_left.mp (N.levelSet_disjoint S' hne)) hxL' hxL
    have hunion_erase0 : ∀ {A : Set X} {j : ℕ}, Disjoint A (N.levelSet S' j) →
        (W ∪ A) ∩ N.levelSet S' j = W ∩ N.levelSet S' j := by
      intro A j hA
      ext x
      constructor
      · intro hx
        rcases hx with ⟨hxWU, hxL⟩
        rcases hxWU with hxW | hxA
        · exact ⟨hxW, hxL⟩
        · exfalso
          exact (Set.disjoint_left.mp hA) hxA hxL
      · intro hx
        exact ⟨Or.inl hx.1, hx.2⟩
    have hWcount0 : ∀ j, j ∈ Finset.Icc 0 b → ((W ∩ N.levelSet S' j).ncard : ℝ) = sCnt j - uCnt j := by
      intro j hj
      have hjb : j ≤ b := (Finset.mem_Icc.mp hj).2
      have hle : N.levelSet S' j ⊆ W ∪ U := hfrag1 j hjb
      have hEq : N.levelSet S' j = (W ∩ N.levelSet S' j) ∪ (U ∩ N.levelSet S' j) := by
        apply Set.ext
        intro x
        constructor
        · intro hx
          have hwU := hle hx
          rcases hwU with hxW | hxU
          · exact Or.inl ⟨hxW, hx⟩
          · exact Or.inr ⟨hxU, hx⟩
        · intro hx
          rcases hx with ⟨hxW, hxL⟩ | ⟨hxU, hxL⟩ <;> exact hxL
      have hdisj : Disjoint (W ∩ N.levelSet S' j) (U ∩ N.levelSet S' j) := by
        rw [Set.disjoint_left]
        intro x hx1 hx2
        exact (Set.disjoint_left.mp hdisjWU) hx2.1 hx1.1
      have hc : N.sCount S' j = (W ∩ N.levelSet S' j).ncard + (U ∩ N.levelSet S' j).ncard := by
        unfold Sys.sCount
        have h1 : (N.levelSet S' j).ncard = ((W ∩ N.levelSet S' j) ∪ (U ∩ N.levelSet S' j)).ncard := congrArg Set.ncard hEq
        rw [h1, Set.ncard_union_eq hdisj]
      have hcR : (N.sCount S' j : ℝ) = ((W ∩ N.levelSet S' j).ncard : ℝ) + ((U ∩ N.levelSet S' j).ncard : ℝ) := by
        rw [← Nat.cast_add]
        exact_mod_cast hc
      unfold sCnt uCnt
      linarith
    have hneg0 : (∑ j ∈ Finset.Icc 0 b, wlev j * (uCnt j - (9 / 10) * sCnt j)) < 0 := by
      simpa [hb'0] using hneg_b'
    have hW0_ge : (1 / 10 : ℝ) * G0 ≤ ∑ j ∈ Finset.Icc 0 b, ((W ∩ N.levelSet S' j).ncard : ℝ) * wlev j := by
      have h1 : (∑ j ∈ Finset.Icc 0 b, (sCnt j - uCnt j) * wlev j)
          = (∑ j ∈ Finset.Icc 0 b, ((W ∩ N.levelSet S' j).ncard : ℝ) * wlev j) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hWcount0 j hj]
      have h2 : (1 / 10 : ℝ) * G0 ≤ (∑ j ∈ Finset.Icc 0 b, (sCnt j - uCnt j) * wlev j) := by
        unfold G0
        have heq : (∑ j ∈ Finset.Icc 0 b, wlev j * (uCnt j - (9 / 10) * sCnt j))
            = (∑ j ∈ Finset.Icc 0 b, uCnt j * wlev j) - (9 / 10) * (∑ j ∈ Finset.Icc 0 b, sCnt j * wlev j) := by
          calc
            (∑ j ∈ Finset.Icc 0 b, wlev j * (uCnt j - (9 / 10) * sCnt j))
                = (∑ j ∈ Finset.Icc 0 b, (uCnt j * wlev j - (9 / 10) * (sCnt j * wlev j))) := by
                  apply Finset.sum_congr rfl
                  intro j hj
                  ring
            _ = (∑ j ∈ Finset.Icc 0 b, uCnt j * wlev j) - (∑ j ∈ Finset.Icc 0 b, (9 / 10) * (sCnt j * wlev j)) := by
                  rw [Finset.sum_sub_distrib]
            _ = (∑ j ∈ Finset.Icc 0 b, uCnt j * wlev j) - (9 / 10) * (∑ j ∈ Finset.Icc 0 b, sCnt j * wlev j) := by
                  congr 1
                  rw [← Finset.mul_sum]
        have heq2 : (∑ j ∈ Finset.Icc 0 b, (sCnt j - uCnt j) * wlev j)
            = (∑ j ∈ Finset.Icc 0 b, sCnt j * wlev j) - (∑ j ∈ Finset.Icc 0 b, uCnt j * wlev j) := by
          calc
            (∑ j ∈ Finset.Icc 0 b, (sCnt j - uCnt j) * wlev j)
                = (∑ j ∈ Finset.Icc 0 b, (sCnt j * wlev j - uCnt j * wlev j)) := by
                  apply Finset.sum_congr rfl
                  intro j hj
                  ring
            _ = (∑ j ∈ Finset.Icc 0 b, sCnt j * wlev j) - (∑ j ∈ Finset.Icc 0 b, uCnt j * wlev j) := by
                  rw [Finset.sum_sub_distrib]
        have hneg'' : (∑ j ∈ Finset.Icc 0 b, uCnt j * wlev j) < (9 / 10) * (∑ j ∈ Finset.Icc 0 b, sCnt j * wlev j) := by
          rw [heq] at hneg0
          linarith
        nlinarith
      rw [← h1]
      exact h2
    have hWInt : ∀ j, (W ∩ S') ∩ N.levelSet S' j = W ∩ N.levelSet S' j := by
      intro j
      ext x
      constructor
      · intro hx
        rcases hx with ⟨hxW, hxL⟩
        rcases hxW with ⟨hxW', hxS'⟩
        exact ⟨hxW', hxL⟩
      · intro hx
        rcases hx with ⟨hxW, hxL⟩
        exact ⟨⟨hxW, N.levelSet_subset S' j hxL⟩, hxL⟩
    have hWAU0 : N.weightAbove S' (W ∪ U) b = N.weightAbove S' (W ∩ S') b := by
      unfold Sys.weightAbove
      apply Finset.sum_congr rfl
      intro j hj
      have hjge : b + 1 ≤ j := (Finset.mem_Icc.mp hj).1
      have h1 : (W ∪ U) ∩ N.levelSet S' j = W ∩ N.levelSet S' j := hunion_erase0 (hUhigh0 j hjge)
      have h2 : (W ∩ S') ∩ N.levelSet S' j = W ∩ N.levelSet S' j := hWInt j
      rw [h1, h2]
    have hWA0 : N.weightAbove S' (W ∩ S') b
        = (∑ j ∈ Finset.Icc (b + 1) N.τ, ((W ∩ N.levelSet S' j).ncard : ℝ) * wlev j) := by
      unfold Sys.weightAbove
      apply Finset.sum_congr rfl
      intro j hj
      rw [hWInt j]
    have hpart : N.weight S' (W ∩ S') =
        (∑ j ∈ Finset.Icc 0 b, ((W ∩ N.levelSet S' j).ncard : ℝ) * wlev j)
          + N.weightAbove S' (W ∩ S') b := by
      have hsplit := weight_eq_above_split N (W ∩ S') S' (b := b) hbτ
      calc
        N.weight S' (W ∩ S') = (∑ j ∈ Finset.Icc 0 b, (((W ∩ S') ∩ N.levelSet S' j).ncard : ℝ) * wlev j)
            + N.weightAbove S' (W ∩ S') b := hsplit
        _ = (∑ j ∈ Finset.Icc 0 b, ((W ∩ N.levelSet S' j).ncard : ℝ) * wlev j)
            + N.weightAbove S' (W ∩ S') b := by
              congr 1
              apply Finset.sum_congr rfl
              intro j hj
              rw [hWInt j]
    have htotal : N.totalWeight S' = G0 + N.weightAbove S' S' b := by
      unfold Sys.totalWeight
      have hsplit := weight_eq_above_split N S' S' (b := b) hbτ
      calc
        N.weight S' S' = (∑ j ∈ Finset.Icc 0 b, ((S' ∩ N.levelSet S' j).ncard : ℝ) * wlev j)
            + N.weightAbove S' S' b := hsplit
        _ = G0 + N.weightAbove S' S' b := by
              unfold G0
              congr 1
              apply Finset.sum_congr rfl
              intro j hj
              have hleS : N.levelSet S' j ⊆ S' := N.levelSet_subset S' j
              have hEqS : S' ∩ N.levelSet S' j = N.levelSet S' j := by
                ext x
                constructor
                · intro hx; exact hx.2
                · intro hx; exact ⟨hleS hx, hx⟩
              rw [hEqS]
              rfl
    have hnB_S0 : nB = S0 := by
      unfold nB S0
      calc
        (N.prefixCount S b : ℝ) = (∑ j ∈ Finset.range (b + 1), sCnt j) := by rw [hs_count]
        _ = (∑ j ∈ Finset.Icc 0 b, sCnt j) := sum_range_eq_sum_Icc0 b sCnt
    have hG0_le : (1 / 100 : ℝ) * wlev b * S0 ≤ (9 / 100) * G0 := by
      calc
        (1 / 100 : ℝ) * wlev b * S0 = (∑ j ∈ Finset.Icc 0 b, ((1 / 100 : ℝ) * wlev b) * sCnt j) := by
          unfold S0
          rw [Finset.mul_sum]
        _ ≤ (∑ j ∈ Finset.Icc 0 b, (9 / 100) * (sCnt j * wlev j)) := by
          apply Finset.sum_le_sum
          intro j hj
          have hjb : j ≤ b := (Finset.mem_Icc.mp hj).2
          have hb1 := wlev_bound b j hjb
          have hb2 : (1 / 100 : ℝ) * wlev b ≤ (9 / 100) * wlev j := by
            rw [← wlev_succ_hundred b]
            exact hb1
          have hs : 0 ≤ sCnt j := hs_nonneg j
          calc
            ((1 / 100 : ℝ) * wlev b) * sCnt j ≤ ((9 / 100) * wlev j) * sCnt j := mul_le_mul_of_nonneg_right hb2 hs
            _ = (9 / 100) * (sCnt j * wlev j) := by ring
        _ = (9 / 100) * G0 := by
          unfold G0
          rw [Finset.mul_sum]
    have hD0 : 0 ≤ (9 / 100) * G0 - (1 / 100) * wlev b * (nB - tU) := by
      have hle1 : (1 / 100 : ℝ) * wlev b * (nB - tU) ≤ (1 / 100 : ℝ) * wlev b * S0 := by
        have h1 : nB - tU ≤ S0 := by nlinarith [hnB_S0, htU_nonneg]
        have hle : wlev b * (nB - tU) ≤ wlev b * S0 := mul_le_mul_of_nonneg_left h1 (wlev_nonneg b)
        have hle' : (1 / 100 : ℝ) * (wlev b * (nB - tU)) ≤ (1 / 100 : ℝ) * (wlev b * S0) :=
          mul_le_mul_of_nonneg_left hle (by norm_num)
        simpa [mul_assoc] using hle'
      linarith
    have hlow : (1 / 100 : ℝ) * N.totalWeight S' ≤ N.weight S' (W ∩ S') := by
      have hc0 : (100 : ℝ)⁻¹ * (N.weightAbove S' S' b - wlev b * (nB - tU)) ≤ N.weightAbove S' (W ∪ U) b := by
        simpa [nB, tU] using hfr2
      have hc0' : (100 : ℝ)⁻¹ * (N.weightAbove S' S' b - wlev b * (nB - tU)) ≤ N.weightAbove S' (W ∩ S') b := by
        rw [← hWAU0]
        exact hc0
      have hmid : (1 / 10 : ℝ) * G0 + (100 : ℝ)⁻¹ * (N.weightAbove S' S' b - wlev b * (nB - tU))
          ≤ N.weight S' (W ∩ S') := by
        rw [hpart]
        exact add_le_add hW0_ge hc0'
      have hchain : (1 / 100 : ℝ) * N.totalWeight S' ≤
          (1 / 10 : ℝ) * G0 + (100 : ℝ)⁻¹ * (N.weightAbove S' S' b - wlev b * (nB - tU)) := by
        have hdiff0 : (1 / 10 : ℝ) * G0 + (100 : ℝ)⁻¹ * (N.weightAbove S' S' b - wlev b * (nB - tU))
              - (1 / 100) * N.totalWeight S'
            = (9 / 100) * G0 - (1 / 100) * wlev b * (nB - tU) := by
          rw [htotal]
          have hinv : (100 : ℝ)⁻¹ = (1 / 100 : ℝ) := by norm_num
          rw [hinv]
          ring_nf
        exact (sub_nonneg.mp (by rw [hdiff0]; exact hD0))
      exact le_trans hchain hmid
    -- contradiction with badness and total-weight lower bound
    have hwle : N.weight S' (W ∩ S') ≤ N.procVal W := by
      exact Sel.le_famSup (v := fun T : Set X => N.weight T (W ∩ T)) hS'F
    have hTotS' : ((10 : ℝ) ^ 8)⁻¹ ≤ N.totalWeight S' := hTot S' hS'F
    have hbad' : N.procVal W < ((10 : ℝ) ^ 10)⁻¹ := hbad
    have hten : ((10 : ℝ) ^ 10)⁻¹ ≤ (1 / 100 : ℝ) * N.totalWeight S' := by
      have heq : ((10 : ℝ) ^ 10)⁻¹ = (1 / 100 : ℝ) * ((10 : ℝ) ^ 8)⁻¹ := by
        have hpow : (10 : ℝ) ^ 10 = (10 : ℝ) ^ 8 * 100 := by
          rw [show (10 : ℕ) = 8 + 2 by norm_num]
          rw [pow_add]
          norm_num
        rw [hpow]
        field_simp
      rw [heq]
      exact mul_le_mul_of_nonneg_left hTotS' (by norm_num)
    linarith

end ObsTPrime
end Submission
