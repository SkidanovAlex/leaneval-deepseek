import Mathlib.Probability.Distributions.SetBernoulli
import ChallengeDeps
import Submission.SelCore
import Submission.Deep

/-!
PROVE: `Submission.ObsT.theorem_obsT` (Proposition obs.T of Park--Pham 2024, §2.2).
See Submission/Deep.lean for all definitions.
-/

set_option autoImplicit false
open Classical
open MeasureTheory ProbabilityTheory Measure unitInterval Finset
open scoped NNReal ENNReal BigOperators

namespace Submission

open _root_.SupremumOfSelectorProcesses

namespace ObsT

open Frame
open Sel.Deep
open Sel.Deep.Sys

variable {X : Type*} [Fintype X]

/-! ## weightAbove facts -/

/-- weightAbove depends only on the level-set intersections -/
lemma weightAbove_congr_of_inter (N : Sys X) {S' A B : Set X} {b : ℕ}
    (h : ∀ j, A ∩ N.levelSet S' j = B ∩ N.levelSet S' j) :
    N.weightAbove S' A b = N.weightAbove S' B b := by
  unfold Sys.weightAbove
  apply Finset.sum_congr rfl
  intro j hj
  rw [h j]

/-- weightAbove is monotone in the set argument -/
lemma weightAbove_mono_of_subset (N : Sys X) {S' A B : Set X} {b : ℕ} (h : A ⊆ B) :
    N.weightAbove S' A b ≤ N.weightAbove S' B b := by
  unfold Sys.weightAbove
  apply Finset.sum_le_sum
  intro j hj
  have hle : (A ∩ N.levelSet S' j).ncard ≤ (B ∩ N.levelSet S' j).ncard := by
    exact Set.ncard_le_ncard (Set.inter_subset_inter_left (N.levelSet S' j) h)
  have hleR : ((A ∩ N.levelSet S' j).ncard : ℝ) ≤ ((B ∩ N.levelSet S' j).ncard : ℝ) := by
    exact_mod_cast hle
  exact mul_le_mul_of_nonneg_right hleR (wlev_nonneg j)

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

/-- fragment2 for U plus smallness of the loss gives fragment2 for U∖{x} -/
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

theorem theorem_obsT (N : Sys X) (S : Set X) (W U : Set X) (b : ℕ) (hS : S ∈ N.F)
    (hB : N.LevelBounded) (hmin : N.MinFragmentAt S W U b hS hB)
    {S' : Set X} (hfr : N.IsFragment S W U b S') :
    N.unionBelow S' b \ W = U := by
  exact le_antisymm (unionBelow_diff_subset_U N hfr)
    (U_subset_unionBelow_diff N S W U b hS hB hmin hfr)

end ObsT
end Submission
