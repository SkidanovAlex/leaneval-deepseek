import Mathlib
import Submission.Threshold
import Submission.ThresholdMeas
import Submission.Sec3Core

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

noncomputable section

/-!
# Slab-measure ↔ subset-weight bridge (Tikhomirov 2020, cor: anticoncentration)

The canonical Bernoulli(`p`) product measure `berP p` is atomic on
`supportSet = {0,1}^n`: the configuration `ω` with ones exactly on `B` is the
indicator vector `indVec B` of mass `wB(n,p,B) = p^{|B|}(1-p)^{n-|B|}`.  Hence
the mass of any slab `{|Σᵢ ωᵢ·vᵢ − λ| ≤ R}` equals the sum of those atom
masses over the good subsets `{B : |Σ_{j∈B} vⱼ − λ| ≤ R}`.

This module proves that identity (and its consequences for the Lévy
concentration function `cfP`), which is the first link of
cor: anticoncentration (Section "Proof of Theorem A").
-/

open scoped BigOperators
open MeasureTheory ProbabilityTheory Measure
open Submission.Threshold
open Submission.ThresholdMeas
open Submission.Sec3

namespace Submission.SlabBridge

/-- indicator vectors of distinct subsets are distinct (the map `B ↦ e_B` is
injective). -/
lemma indVec_injective {n : ℕ} : Function.Injective (@indVec n) := by
  intro B₁ B₂ h
  have hf : ∀ i : Fin n, indVec B₁ i = indVec B₂ i := congrFun h
  apply Finset.ext
  intro i
  by_cases hi₁ : i ∈ B₁ <;> by_cases hi₂ : i ∈ B₂
  · simp [hi₁, hi₂]
  · have hv := hf i
    dsimp [indVec] at hv
    simp [hi₁, hi₂] at hv
  · have hv := hf i
    dsimp [indVec] at hv
    simp [hi₁, hi₂] at hv
  · simp [hi₁, hi₂]

/-- the collection of good-atom singletons is pairwise disjoint. -/
lemma pairwiseDisjoint_indVec {n : ℕ} (Good : Finset (Finset (Fin n))) :
    (↑Good : Set (Finset (Fin n))).PairwiseDisjoint
      (fun B : Finset (Fin n) => ({indVec B} : Set (Fin n → ℝ))) := by
  intro B hB B' hB' hne
  change Disjoint ({indVec B} : Set (Fin n → ℝ)) ({indVec B'} : Set (Fin n → ℝ))
  rw [Set.disjoint_left]
  intro ω hω1 hω2
  have hEqB : ω = indVec B := Set.mem_singleton_iff.mp hω1
  have hEqB' : ω = indVec B' := Set.mem_singleton_iff.mp hω2
  have hBB' : B = B' := by
    apply indVec_injective
    rw [← hEqB, hEqB']
  exact hne hBB'

/-- the good-subset Finset (subset sums within `R` of the real center `lam`). -/
def goodSubsets {n : ℕ} (x : Fin n → ℤ) (lam : ℝ) (R : ℝ) : Finset (Finset (Fin n)) :=
  ((Finset.univ : Finset (Fin n)).powerset).filter
    (fun B : Finset (Fin n) => |(Sec3.subSum x B : ℝ) - lam| ≤ R)

/-- slab weight of a center: total Bernoulli mass of the subsets whose sum is
within `R` of `lam`. -/
def slabWeight {n : ℕ} (p : unitInterval) (x : Fin n → ℤ) (lam : ℝ) (R : ℝ) : ℝ :=
  ∑ B ∈ goodSubsets (x := x) lam R, Sec3.wB n p B


/-- `Σᵢ e_B(i)·vᵢ = Σ_{i∈B} vᵢ`. -/
lemma indVec_weighted_sum_eq {n : ℕ} (v : Fin n → ℝ) (B : Finset (Fin n)) :
    (∑ i : Fin n, indVec B i * v i) = ∑ i ∈ B, v i := by
  calc
    (∑ i : Fin n, indVec B i * v i) = ∑ i : Fin n, (if i ∈ B then v i else 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      dsimp [indVec]
      by_cases hB : i ∈ B <;> simp [hB]
    _ = ∑ i ∈ B, v i := by
      rw [← Finset.sum_filter]
      simp

/-- the real cast of an integer subset-sum equals the real subset-sum. -/
lemma cast_subSum {n : ℕ} (x : Fin n → ℤ) (B : Finset (Fin n)) :
    ((Sec3.subSum x B : ℤ) : ℝ) = ∑ i ∈ B, (x i : ℝ) := by
  dsimp [Sec3.subSum]
  rw [Int.cast_sum]

/-- the indicator vector of any subset lies on the support. -/
lemma indVec_mem_support {n : ℕ} (B : Finset (Fin n)) : indVec B ∈ supportSet := by
  intro i
  dsimp [indVec]
  by_cases hi : i ∈ B <;> simp [hi]


/-- the slab intersected with the support is the disjoint union of the good
atoms. -/
lemma slab_inter_support_eq_union {n : ℕ} (x : Fin n → ℤ) (lam R : ℝ) :
    slabEvent (fun i : Fin n => (x i : ℝ)) lam R ∩ supportSet
      = ⋃ B ∈ goodSubsets (x := x) lam R, ({indVec B} : Set (Fin n → ℝ)) := by
  classical
  ext ω
  constructor
  · intro hω
    rcases hω with ⟨hE, hsup⟩
    let B : Finset (Fin n) := (Finset.univ : Finset (Fin n)).filter (fun i => ω i = 1)
    have hωB : ω = indVec B := indVec_support_eq hsup
    have hSig : (∑ i : Fin n, ω i * (x i : ℝ)) = ((Sec3.subSum x B : ℤ) : ℝ) := by
      have h1 := sum_weight_eq_indVec hsup (fun i : Fin n => (x i : ℝ))
      have h2 : (∑ i ∈ (Finset.univ : Finset (Fin n)).filter (fun i => ω i = 1), (x i : ℝ)) =
          ∑ i ∈ B, (x i : ℝ) := by
        simp [B]
      have h3 : (∑ i ∈ B, (x i : ℝ)) = ((Sec3.subSum x B : ℤ) : ℝ) :=
        (cast_subSum x B).symm
      calc
        (∑ i : Fin n, ω i * (x i : ℝ)) = ∑ i ∈ (Finset.univ : Finset (Fin n)).filter (fun i => ω i = 1), (x i : ℝ) := h1
        _ = ∑ i ∈ B, (x i : ℝ) := h2
        _ = ((Sec3.subSum x B : ℤ) : ℝ) := h3
    have hBpow : B ∈ (Finset.univ : Finset (Fin n)).powerset := by simp [B]
    have hBabs : |((Sec3.subSum x B : ℤ) : ℝ) - lam| ≤ R := by
      dsimp [slabEvent] at hE
      rwa [hSig] at hE
    have hBmem : B ∈ goodSubsets (x := x) lam R := by
      rw [goodSubsets, Finset.mem_filter]
      exact ⟨hBpow, hBabs⟩
    exact Set.mem_biUnion hBmem (Set.mem_singleton_iff.mpr hωB)
  · intro hω
    have hm : ∃ B : Finset (Fin n), B ∈ goodSubsets (x := x) lam R ∧
        ω ∈ ({indVec B} : Set (Fin n → ℝ)) := by
      simpa using hω
    rcases hm with ⟨B, hBmem, hωB⟩
    have hEq : ω = indVec B := Set.mem_singleton_iff.mp hωB
    constructor
    · have hgood : |(Sec3.subSum x B : ℝ) - lam| ≤ R := (Finset.mem_filter.mp hBmem).2
      have hSig : (∑ i : Fin n, (indVec B i) * (x i : ℝ)) = ((Sec3.subSum x B : ℤ) : ℝ) := by
        calc
          (∑ i : Fin n, indVec B i * (x i : ℝ)) = ∑ i ∈ B, (x i : ℝ) := indVec_weighted_sum_eq (fun i : Fin n => (x i : ℝ)) B
          _ = ((Sec3.subSum x B : ℤ) : ℝ) := (cast_subSum x B).symm
      rw [hEq]
      dsimp [slabEvent]
      rwa [hSig]
    · rw [hEq]
      exact indVec_mem_support B


/-- the slab weight is at most the total weight `1`. -/
lemma slabWeight_le_one {n : ℕ} (p : unitInterval) (x : Fin n → ℤ) (lam R : ℝ) :
    slabWeight p x lam R ≤ 1 := by
  classical
  unfold slabWeight
  have hsub : goodSubsets (x := x) lam R ⊆ (Finset.univ : Finset (Fin n)).powerset := by
    intro B hB
    exact (Finset.mem_filter.mp hB).1
  have hpos : ∀ B : Finset (Fin n), B ∈ (Finset.univ : Finset (Fin n)).powerset →
      B ∉ goodSubsets (x := x) lam R → 0 ≤ wB n p B := by
    intro B hB hnot
    exact wB_nonneg n p B
  calc
    (∑ B ∈ goodSubsets (x := x) lam R, wB n p B)
        ≤ (∑ B ∈ (Finset.univ : Finset (Fin n)).powerset, wB n p B) := by
            exact Finset.sum_le_sum_of_subset_of_nonneg hsub hpos
    _ = 1 := sum_wB_eq_one n p

/-- the slab weight is non-negative. -/
lemma slabWeight_nonneg {n : ℕ} (p : unitInterval) (x : Fin n → ℤ) (lam R : ℝ) :
    0 ≤ slabWeight p x lam R := by
  classical
  unfold slabWeight
  exact Finset.sum_nonneg (fun B hB => wB_nonneg n p B)

/-- REAL slab mass equals the good-subset weight sum. -/
lemma slab_real_eq_weight {n : ℕ} (p : unitInterval) (x : Fin n → ℤ) (lam R : ℝ) :
    (berP (n := n) p).real (slabEvent (fun i : Fin n => (x i : ℝ)) lam R) =
      slabWeight p x lam R := by
  classical
  have hEmeas : MeasurableSet (slabEvent (fun i : Fin n => (x i : ℝ)) lam R) :=
    measurable_slabEvent (fun i : Fin n => (x i : ℝ)) lam R
  have hEq := measure_slab_eq_inter_support p hEmeas
  have hEq2 : slabEvent (fun i : Fin n => (x i : ℝ)) lam R ∩ supportSet =
      ⋃ B ∈ goodSubsets (x := x) lam R, ({indVec B} : Set (Fin n → ℝ)) :=
    slab_inter_support_eq_union x lam R
  rw [Measure.real_def, hEq, hEq2]
  -- goal: (berP p) (⋃ B ∈ good, {indVec B}) .toReal = slabWeight p x lam R
  change (berP (n := n) p).real (⋃ B ∈ goodSubsets (x := x) lam R, ({indVec B} : Set (Fin n → ℝ))) =
      slabWeight p x lam R
  rw [MeasureTheory.measureReal_biUnion_finset (s := goodSubsets (x := x) lam R)
    (f := fun B : Finset (Fin n) => ({indVec B} : Set (Fin n → ℝ)))
    (pairwiseDisjoint_indVec (goodSubsets (x := x) lam R))
    (hm := by intro B hB; exact measurableSet_singleton (indVec B))]
  unfold slabWeight
  apply Finset.sum_congr rfl
  intro B hB
  exact berP_real_indVec p B

/-- ENNReal slab mass equals `ofReal` of the good-subset weight sum. -/
lemma slab_enn_eq_weight {n : ℕ} (p : unitInterval) (x : Fin n → ℤ) (lam R : ℝ) :
    berP (n := n) p (slabEvent (fun i : Fin n => (x i : ℝ)) lam R) =
      ENNReal.ofReal (slabWeight p x lam R) := by
  have htop : berP (n := n) p (slabEvent (fun i : Fin n => (x i : ℝ)) lam R) ≠ ⊤ :=
    measure_ne_top (berP (n := n) p) (slabEvent (fun i : Fin n => (x i : ℝ)) lam R)
  rw [← ENNReal.ofReal_toReal htop]
  exact congrArg ENNReal.ofReal (slab_real_eq_weight p x lam R)

/-- the real-center weight supremum is bounded above by 1. -/
lemma weightSup_bddAbove {n : ℕ} (p : unitInterval) (x : Fin n → ℤ) (R : ℝ) :
    BddAbove (Set.range (fun lam : ℝ => slabWeight p x lam R)) := by
  refine ⟨1, ?_⟩
  intro y hy
  rcases hy with ⟨lam, rfl⟩
  exact slabWeight_le_one p x lam R

/-- for each real center, the slab mass is at most `ofReal` of the weight
supremum. -/
lemma slab_enn_le_weightSup {n : ℕ} (p : unitInterval) (x : Fin n → ℤ) (lam R : ℝ) :
    berP (n := n) p (slabEvent (fun i : Fin n => (x i : ℝ)) lam R) ≤
      ENNReal.ofReal (sSup (Set.range (fun lam' : ℝ => slabWeight p x lam' R))) := by
  rw [slab_enn_eq_weight]
  exact ENNReal.ofReal_le_ofReal
    (le_csSup (weightSup_bddAbove p x R) ⟨lam, rfl⟩)

/-- **Lévy concentration ≤ `ofReal` of the real-center weight supremum**: the
first link of cor: anticoncentration. -/
lemma cfP_le_ofReal_weightSup {n : ℕ} (p : unitInterval) (x : Fin n → ℤ) (R : ℝ) :
    cfP (n := n) p (fun i : Fin n => (x i : ℝ)) R ≤
      ENNReal.ofReal (sSup (Set.range (fun lam : ℝ => slabWeight p x lam R))) := by
  classical
  unfold cfP
  unfold Submission.Helpers.levyConcentration
  rw [sSup_le_iff]
  rintro b ⟨l, rfl⟩
  change berP (n := n) p {ω : Fin n → ℝ | |∑ i : Fin n, ω i * (x i : ℝ) - l| ≤ R} ≤
    ENNReal.ofReal (sSup (Set.range (fun lam : ℝ => slabWeight p x lam R)))
  exact slab_enn_le_weightSup p x l R

end Submission.SlabBridge

end
