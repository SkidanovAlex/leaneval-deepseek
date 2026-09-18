import Submission.DS.Infinite
import Submission.DS.Summability
import Submission.DS.Measure
open scoped Nat ENNReal NNReal
open Set Filter MeasureTheory
open DuffinSchaefferConjecture

/-!
# Structure of the set 𝒦

We identify `𝒦 ψ` with `[0,1] ∩ limsup_q (per-denominator solution sets)`.
-/

namespace Submission.DS

/-- Infinite subsets of `ℕ+` are unbounded. -/
lemma infinite_iff_forall_ge (s : Set ℕ+) : s.Infinite ↔ ∀ N : ℕ, ∃ q ∈ s, N ≤ (q : ℕ) := by
  classical
  constructor
  · intro h N
    by_contra hc
    have hsub : (fun q : ℕ+ => (q : ℕ)) '' s ⊆ {m : ℕ | m < N} := by
      intro m hm
      rcases hm with ⟨q, hq, rfl⟩
      have hqN : (q : ℕ) < N := by
        by_contra hnlt
        have hle : N ≤ (q : ℕ) := le_of_not_gt hnlt
        exact hc ⟨q, hq, hle⟩
      exact hqN
    have hsN : ((fun q : ℕ+ => (q : ℕ)) '' s).Finite := (finite_lt_nat N).subset hsub
    have hs : s.Finite := by
      exact (Set.finite_image_iff (Set.injOn_of_injective PNat.coe_injective (s := s))).1 hsN
    exact h hs
  · intro h hs
    have hsN : ((fun q : ℕ+ => (q : ℕ)) '' s).Finite := by
      exact (Set.finite_image_iff (Set.injOn_of_injective PNat.coe_injective (s := s))).2 hs
    rcases hsN.bddAbove with ⟨b, hb⟩
    rcases h (b + 1) with ⟨q, hq, hbq⟩
    have hmem : (q : ℕ) ∈ ((fun q : ℕ+ => (q : ℕ)) '' s) := ⟨q, hq, rfl⟩
    have hbq' : (q : ℕ) ≤ b := hb hmem
    omega

/-- `x` lies in the set of points belonging to infinitely many `s q` iff infinitely many
denominators satisfy it. -/
lemma infinite_denoms_iff (s : ℕ+ → Set ℝ) (x : ℝ) :
    ({q : ℕ+ | x ∈ s q}.Infinite) ↔ x ∈ {y : ℝ | {q : ℕ+ | y ∈ s q}.Infinite} := by
  rfl

/-- The set of points lying in infinitely many of the `s q`. -/
def limsupDenoms (s : ℕ+ → Set ℝ) : Set ℝ := {x | {q : ℕ+ | x ∈ s q}.Infinite}

/-- A point is in `limsupDenoms s` iff it belongs to `s q` for arbitrarily large `q`. -/
lemma mem_limsupDenoms_iff_forall_ge (s : ℕ+ → Set ℝ) (x : ℝ) :
    x ∈ limsupDenoms s ↔ ∀ N : ℕ, ∃ q : ℕ+, N ≤ (q : ℕ) ∧ x ∈ s q := by
  unfold limsupDenoms
  change {q : ℕ+ | x ∈ s q}.Infinite ↔ ∀ N : ℕ, ∃ q : ℕ+, N ≤ (q : ℕ) ∧ x ∈ s q
  rw [infinite_iff_forall_ge]
  constructor
  · intro h N
    rcases h N with ⟨q, hqmem, hqN⟩
    exact ⟨q, hqN, hqmem⟩
  · intro h N
    rcases h N with ⟨q, hqN, hx⟩
    exact ⟨q, hx, hqN⟩

/-- `limsupDenoms s = ⋂ N, ⋃ q with N ≤ q, s q`. -/
lemma limsupDenoms_eq_iInter (s : ℕ+ → Set ℝ) :
    limsupDenoms s = ⋂ N : ℕ, ⋃ q : ℕ+, (if (N : ℕ) ≤ (q : ℕ) then s q else ∅) := by
  ext x
  rw [mem_limsupDenoms_iff_forall_ge]
  constructor
  · intro h
    rw [mem_iInter]
    intro N
    rcases h N with ⟨q, hqN, hx⟩
    rw [mem_iUnion]
    exact ⟨q, by simp [hqN, hx]⟩
  · intro h
    intro N
    have hN : x ∈ ⋃ q : ℕ+, (if (N : ℕ) ≤ (q : ℕ) then s q else ∅) := (mem_iInter.mp h) N
    rcases mem_iUnion.mp hN with ⟨q, hq⟩
    by_cases hc : (N : ℕ) ≤ (q : ℕ)
    · exact ⟨q, hc, by simpa [hc] using hq⟩
    · simp [hc] at hq

/-- Per-denominator solution numerators (the fibres). -/
def Kfib (ψ : ℕ+ → ℝ≥0) (x : ℝ) (q : ℕ+) : Set ℕ :=
  {a | a ≤ (q : ℕ) ∧ inequality_1_7 ψ x a q}

/-- Per-denominator solution set for `𝒦 ψ`: `x` is a solution for denominator `q`. -/
def Bq (ψ : ℕ+ → ℝ≥0) (q : ℕ+) : Set ℝ := {x | (Kfib ψ x q).Nonempty}

lemma Kfib_finite (ψ : ℕ+ → ℝ≥0) (x : ℝ) (q : ℕ+) : (Kfib ψ x q).Finite := by
  have hsub : Kfib ψ x q ⊆ Set.Icc 0 (q : ℕ) := by
    intro a ha
    simp [Kfib] at ha
    exact ⟨Nat.zero_le a, ha.1⟩
  exact (Set.finite_Icc 0 (q : ℕ)).subset hsub

lemma pairSet_Kfib (ψ : ℕ+ → ℝ≥0) (x : ℝ) :
    pairSet (Kfib ψ x) = {(a, q) : ℕ × ℕ+ | a ≤ (q : ℕ) ∧ inequality_1_7 ψ x a q} := by
  ext p
  simp [pairSet, Kfib]

/-- `x ∈ 𝒦 ψ` iff `x ∈ [0,1]` and infinitely many denominators have a solution. -/
lemma mem_K_iff (ψ : ℕ+ → ℝ≥0) (x : ℝ) :
    x ∈ 𝒦 ψ ↔ x ∈ Set.Icc 0 1 ∧ x ∈ limsupDenoms (Bq ψ) := by
  unfold 𝒦 limsupDenoms
  simp only [Set.mem_setOf_eq]
  rw [← pairSet_Kfib]
  rw [infinite_pairs_iff_infinite_denoms (Kfib ψ x) (Kfib_finite ψ x)]
  simp [denomSet, Bq]

/-- `𝒦 ψ` equals `[0,1]` intersected with the limsup of the per-denominator sets. -/
lemma K_eq_Icc_inter_limsup (ψ : ℕ+ → ℝ≥0) : 𝒦 ψ = Set.Icc 0 1 ∩ limsupDenoms (Bq ψ) := by
  ext x
  exact mem_K_iff ψ x

/-- The solution interval for a fixed numerator is a closed interval. -/
lemma solInterval_eq_Icc (ψ : ℕ+ → ℝ≥0) (a : ℕ) (q : ℕ+) :
    {x : ℝ | inequality_1_7 ψ x a q} =
      Set.Icc (((a : ℝ) / (q : ℝ)) - ((ψ q / q : ℝ≥0) : ℝ))
        (((a : ℝ) / (q : ℝ)) + ((ψ q / q : ℝ≥0) : ℝ)) := by
  let c : ℝ := (a : ℝ) / (q : ℝ)
  let r : ℝ := (ψ q / q : ℝ≥0)
  have hset : {x : ℝ | inequality_1_7 ψ x a q} = {x : ℝ | |x - c| ≤ r} := by
    ext y
    rfl
  rw [hset]
  simp [c, r]
  ext y
  change |y - c| ≤ r ↔ (c - r ≤ y ∧ y ≤ c + r)
  rw [abs_le]
  constructor <;> intro h <;> constructor <;> linarith

/-- Solution intervals are measurable. -/
lemma measurableSet_solInterval (ψ : ℕ+ → ℝ≥0) (a : ℕ) (q : ℕ+) :
    MeasurableSet {x : ℝ | inequality_1_7 ψ x a q} := by
  rw [solInterval_eq_Icc ψ a q]
  exact isClosed_Icc.measurableSet

/-- The per-denominator solution sets are measurable (indeed closed). -/
lemma measurableSet_Bq (ψ : ℕ+ → ℝ≥0) (q : ℕ+) : MeasurableSet (Bq ψ q) := by
  have hEq : Bq ψ q = ⋃ a : ℕ, (if a ≤ (q : ℕ) then ({x : ℝ | inequality_1_7 ψ x a q} : Set ℝ) else ∅) := by
    ext x
    simp [Bq, Kfib, Set.Nonempty]
  rw [hEq]
  refine MeasurableSet.iUnion (fun a : ℕ => ?_)
  by_cases h : a ≤ (q : ℕ)
  · rw [if_pos h]
    exact measurableSet_solInterval ψ a q
  · rw [if_neg h]
    exact MeasurableSet.empty

/-- `limsupDenoms` of a measurable family is measurable. -/
lemma measurableSet_limsupDenoms {s : ℕ+ → Set ℝ} (hs : ∀ q, MeasurableSet (s q)) :
    MeasurableSet (limsupDenoms s) := by
  rw [limsupDenoms_eq_iInter]
  refine MeasurableSet.iInter (fun N : ℕ => ?_)
  refine MeasurableSet.iUnion (fun q : ℕ+ => ?_)
  by_cases h : (N : ℕ) ≤ (q : ℕ)
  · simp [h]
    exact hs q
  · simp [h]

/-- `𝒦 ψ` is measurable. -/
lemma measurableSet_K (ψ : ℕ+ → ℝ≥0) : MeasurableSet (𝒦 ψ) := by
  rw [K_eq_Icc_inter_limsup]
  exact (isClosed_Icc.measurableSet.inter (measurableSet_limsupDenoms (measurableSet_Bq ψ)))

end Submission.DS
