import Mathlib.Probability.Distributions.SetBernoulli
import ChallengeDeps
import Submission.Prob

/-!
Monotonicity of `μ_p` in `p` for increasing families, via slice recursion.
-/

open ProbabilityTheory MeasureTheory unitInterval Set
open scoped ENNReal NNReal BigOperators unitInterval
open FractionalExpectationThresholds

attribute [local instance] Classical.propDecidable

namespace Submission
namespace FET

universe u

variable {X : Type u} [Fintype X]

/-- members of `𝓕` not containing `x`. -/
def slice0 (𝓕 : Set (Set X)) (x : X) : Set (Set X) := {T | T ∈ 𝓕 ∧ x ∉ T}

/-- `T` (not containing `x`) such that `T ∪ {x} ∈ 𝓕`. -/
def slice1 (𝓕 : Set (Set X)) (x : X) : Set (Set X) := {T | x ∉ T ∧ insert x T ∈ 𝓕}

lemma mem_slice0 {𝓕 : Set (Set X)} {x : X} {S : Set X} : S ∈ slice0 𝓕 x ↔ S ∈ 𝓕 ∧ x ∉ S := by
  change (S ∈ 𝓕 ∧ x ∉ S) ↔ (S ∈ 𝓕 ∧ x ∉ S)
  rfl

lemma mem_slice1 {𝓕 : Set (Set X)} {x : X} {S : Set X} : S ∈ slice1 𝓕 x ↔ x ∉ S ∧ insert x S ∈ 𝓕 := by
  change (x ∉ S ∧ insert x S ∈ 𝓕) ↔ (x ∉ S ∧ insert x S ∈ 𝓕)
  rfl

lemma slice0_subset_slice1_of_upper {𝓕 : Set (Set X)} (h𝓕 : IsUpperSet 𝓕) (x : X) :
    slice0 𝓕 x ⊆ slice1 𝓕 x := by
  intro T hT
  rcases hT with ⟨hT𝓕, hxT⟩
  refine ⟨hxT, ?_⟩
  have hsub : T ⊆ insert x T := by intro y hy; simp [hy]
  exact h𝓕 hsub hT𝓕

lemma insert_inj_of_not_mem {x : X} {T S : Set X} (hxT : x ∉ T) (hxS : x ∉ S)
    (h : insert x T = insert x S) : T = S := by
  ext y
  constructor
  · intro hyT
    have hy : y ∈ insert x S := by rw [← h]; simp [hyT]
    simp at hy
    rcases hy with hyx | hyS
    · exfalso; exact hxT (by simpa [hyx] using hyT)
    · exact hyS
  · intro hyS
    have hy : y ∈ insert x T := by rw [h]; simp [hyS]
    simp at hy
    rcases hy with hyx | hyT
    · exfalso; exact hxS (by simpa [hyx] using hyS)
    · exact hyT

lemma insert_sdiff_self {x : X} {S : Set X} (hxS : x ∈ S) : insert x (S \ {x}) = S := by
  ext y
  by_cases hyx : y = x
  · simp [hyx, hxS]
  · simp [hyx]

lemma sdiff_insert_self {x : X} {T : Set X} (hxT : x ∉ T) : insert x T \ {x} = T := by
  ext y
  by_cases hyx : y = x
  · simp [hyx, hxT]
  · simp [hyx]

/-- `PmassU U p (insert x T) = p * PmassU (U \ {x}) p T`. -/
lemma PmassU_insert {U : Set X} (p : I) {x : X} (hxU : x ∈ U) {T : Set X} (hxT : x ∉ T)
    (hTU : T ⊆ U \ {x}) :
    PmassU U p (insert x T) = (p : ℝ) * PmassU (U \ {x}) p T := by
  classical
  have hsub : insert x T ⊆ U := by
    intro y hy
    simp at hy
    rcases hy with rfl | hy
    · exact hxU
    · exact (hTU hy).1
  have hcard : (U \ {x}).ncard = U.ncard - 1 := by
    have hsd := Set.ncard_sdiff' (s := ({x} : Set X)) (t := U)
      (by intro y hy; simp at hy; simpa [hy] using hxU) (Set.toFinite U)
    simpa using hsd
  have hUpos : 1 ≤ U.ncard := by
    have hp := (Set.ncard_pos (s := U)).2 ⟨x, hxU⟩
    omega
  have hle : T.ncard + 1 ≤ U.ncard := by
    have h1 : T.ncard ≤ (U \ {x}).ncard := Set.ncard_le_ncard hTU (Set.toFinite (U \ {x}))
    omega
  calc
    PmassU U p (insert x T)
        = (p : ℝ) ^ (insert x T).ncard * (1 - (p : ℝ)) ^ (U.ncard - (insert x T).ncard) := by
            rw [PmassU_of_subset hsub]
    _ = (p : ℝ) ^ (T.ncard + 1) * (1 - (p : ℝ)) ^ (U.ncard - (T.ncard + 1)) := by
            rw [Set.ncard_insert_of_notMem hxT]
    _ = (p : ℝ) ^ (T.ncard + 1) * (1 - (p : ℝ)) ^ (U.ncard - T.ncard - 1) := by
            have hA : U.ncard - (T.ncard + 1) = U.ncard - T.ncard - 1 :=
              (Nat.sub_sub U.ncard T.ncard 1).symm
            rw [hA]
    _ = (p : ℝ) * ((p : ℝ) ^ T.ncard * (1 - (p : ℝ)) ^ (U.ncard - T.ncard - 1)) := by
            rw [pow_succ']
            ring
    _ = (p : ℝ) * ((p : ℝ) ^ T.ncard * (1 - (p : ℝ)) ^ ((U \ {x}).ncard - T.ncard)) := by
            have hEq : U.ncard - T.ncard - 1 = (U \ {x}).ncard - T.ncard := by
              rw [hcard]
              omega
            rw [hEq]
    _ = (p : ℝ) * PmassU (U \ {x}) p T := by
            rw [PmassU_of_subset hTU]

/-- For `x ∉ S`: `PmassU U p S = (1-p) * PmassU (U \ {x}) p S`. -/
lemma PmassU_slice0 {U : Set X} (p : I) {x : X} (hxU : x ∈ U) {S : Set X} (hxS : x ∉ S) :
    PmassU U p S = (1 - (p : ℝ)) * PmassU (U \ {x}) p S := by
  classical
  by_cases hSU : S ⊆ U
  · have hS' : S ⊆ U \ {x} := by
      intro y hy
      constructor
      · exact hSU hy
      · intro hyx
        exact hxS (hyx.symm ▸ hy)
    have hcard : (U \ {x}).ncard = U.ncard - 1 := by
      have hsd := Set.ncard_sdiff' (s := ({x} : Set X)) (t := U)
        (by intro y hy; simp at hy; simpa [hy] using hxU) (Set.toFinite U)
      simpa using hsd
    have hUpos : 1 ≤ U.ncard := by
      have hp := (Set.ncard_pos (s := U)).2 ⟨x, hxU⟩
      omega
    calc
      PmassU U p S = (p : ℝ) ^ S.ncard * (1 - (p : ℝ)) ^ (U.ncard - S.ncard) := by
        rw [PmassU_of_subset hSU]
      _ = (p : ℝ) ^ S.ncard * (1 - (p : ℝ)) ^ (((U \ {x}).ncard - S.ncard) + 1) := by
        apply congrArg (fun k : ℕ => (p : ℝ) ^ S.ncard * (1 - (p : ℝ)) ^ k)
        rw [hcard]
        have hSle1 : S.ncard + 1 ≤ U.ncard := by
          have h1 : S.ncard ≤ (U \ {x}).ncard := Set.ncard_le_ncard hS' (Set.toFinite (U \ {x}))
          rw [hcard] at h1
          omega
        omega
      _ = (1 - (p : ℝ)) * ((p : ℝ) ^ S.ncard * (1 - (p : ℝ)) ^ ((U \ {x}).ncard - S.ncard)) := by
        rw [pow_succ]
        ring
      _ = (1 - (p : ℝ)) * PmassU (U \ {x}) p S := by
        rw [PmassU_of_subset hS']
  · have h0 : PmassU U p S = 0 := by
      unfold PmassU
      simp [hSU]
    have h0' : PmassU (U \ {x}) p S = 0 := by
      unfold PmassU
      simp [show ¬ S ⊆ U \ {x} from fun h => hSU (fun y hy => (h hy).1)]
    rw [h0, h0']
    ring

/-- For `x ∉ T`: `PmassU U p (insert x T) = p * PmassU (U \ {x}) p T`.  (no subset hypothesis) -/
lemma PmassU_insert' {U : Set X} (p : I) {x : X} (hxU : x ∈ U) {T : Set X} (hxT : x ∉ T) :
    PmassU U p (insert x T) = (p : ℝ) * PmassU (U \ {x}) p T := by
  classical
  by_cases hTU : T ⊆ U \ {x}
  · exact PmassU_insert p hxU hxT hTU
  · have hnot : ¬ insert x T ⊆ U := by
      intro h
      apply hTU
      intro y hy
      constructor
      · exact h (by simp [hy])
      · intro hyx
        exact hxT (hyx.symm ▸ hy)
    have h0 : PmassU U p (insert x T) = 0 := by
      unfold PmassU
      simp [hnot]
    have h0' : PmassU (U \ {x}) p T = 0 := by
      unfold PmassU
      simp [hTU]
    rw [h0, h0']
    ring


/-- Slice recursion for `muU` at an element `x ∈ U`. -/
lemma muU_slice (U : Set X) (p : I) {x : X} (hxU : x ∈ U) (𝓕 : Set (Set X)) :
    muU U p 𝓕 = (1 - (p : ℝ)) * muU (U \ {x}) p (slice0 𝓕 x) +
      (p : ℝ) * muU (U \ {x}) p (slice1 𝓕 x) := by
  classical
  let wf : Finset (Set X) := (Finset.univ : Finset (Set X)).filter (fun S : Set X => S ∈ 𝓕)
  have hA : muU U p 𝓕 = ∑ S ∈ wf, PmassU U p S := by
    unfold muU
    simp only [wf, Finset.sum_filter]
  have hB0 : (1 - (p : ℝ)) * muU (U \ {x}) p (slice0 𝓕 x) =
      ∑ S ∈ wf.filter (fun S : Set X => x ∉ S), (1 - (p : ℝ)) * PmassU (U \ {x}) p S := by
    unfold muU
    rw [← Finset.sum_filter]
    rw [Finset.mul_sum]
    rw [show (Finset.univ : Finset (Set X)).filter (fun T : Set X => T ∈ slice0 𝓕 x) =
        wf.filter (fun S : Set X => x ∉ S) by
      ext S
      simp [wf, mem_slice0, Finset.mem_filter]]
  have hB0' : (∑ S ∈ wf.filter (fun S : Set X => x ∉ S), PmassU U p S) =
      (1 - (p : ℝ)) * muU (U \ {x}) p (slice0 𝓕 x) := by
    rw [hB0]
    apply Finset.sum_congr rfl
    intro S hS
    have hxS : x ∉ S := (Finset.mem_filter.mp hS).2
    exact PmassU_slice0 (U := U) p hxU hxS
  have hB1 : (p : ℝ) * muU (U \ {x}) p (slice1 𝓕 x) =
      ∑ S ∈ wf.filter (fun S : Set X => x ∈ S), PmassU U p S := by
    unfold muU
    rw [← Finset.sum_filter]
    rw [Finset.mul_sum]
    let E : Finset (Set X) := (Finset.univ : Finset (Set X)).filter (fun T : Set X => T ∈ slice1 𝓕 x)
    let D : Finset (Set X) := wf.filter (fun S : Set X => x ∈ S)
    change (∑ T ∈ E, (p : ℝ) * PmassU (U \ {x}) p T) = ∑ S ∈ D, PmassU U p S
    apply Finset.sum_bij (fun (T : Set X) (_ : T ∈ E) => insert x T)
    · intro T hT
      have hTs : T ∈ slice1 𝓕 x := (Finset.mem_filter.mp hT).2
      have hIns : insert x T ∈ 𝓕 := (mem_slice1.mp hTs).2
      simp [D, wf, hIns]
    · intro T₁ hT₁ T₂ hT₂ hEq
      have hx1 : x ∉ T₁ := (mem_slice1.mp ((Finset.mem_filter.mp hT₁).2)).1
      have hx2 : x ∉ T₂ := (mem_slice1.mp ((Finset.mem_filter.mp hT₂).2)).1
      exact insert_inj_of_not_mem hx1 hx2 hEq
    · intro S hS
      have hSx : x ∈ S := (Finset.mem_filter.mp hS).2
      have hS𝓕 : S ∈ 𝓕 := by
        have hSwf : S ∈ wf := (Finset.mem_filter.mp hS).1
        exact (Finset.mem_filter.mp hSwf).2
      have hins : insert x (S \ {x}) = S := insert_sdiff_self hSx
      refine ⟨S \ {x}, ?_, ?_⟩
      · simp [E, mem_slice1, hins, hS𝓕]
      · exact hins
    · intro T hT
      have hTs : T ∈ slice1 𝓕 x := (Finset.mem_filter.mp hT).2
      have hxT : x ∉ T := (mem_slice1.mp hTs).1
      exact (PmassU_insert' (U := U) p hxU hxT).symm

  calc
    muU U p 𝓕 = ∑ S ∈ wf, PmassU U p S := hA
    _ = (∑ S ∈ wf.filter (fun S : Set X => x ∉ S), PmassU U p S) +
        (∑ S ∈ wf.filter (fun S : Set X => x ∈ S), PmassU U p S) := by
      rw [show (wf.filter (fun S : Set X => x ∈ S)) =
          (wf.filter (fun S : Set X => ¬ x ∉ S)) by
        ext S
        by_cases hS : x ∈ S <;> simp [hS]]
      rw [Finset.sum_filter_add_sum_filter_not wf (fun S : Set X => x ∉ S)]
    _ = (1 - (p : ℝ)) * muU (U \ {x}) p (slice0 𝓕 x) +
        (p : ℝ) * muU (U \ {x}) p (slice1 𝓕 x) := by
      rw [hB1]
      rw [hB0']
end FET
end Submission
