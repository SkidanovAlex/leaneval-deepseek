import Mathlib
import Submission.Threshold
import Submission.Sec3Core

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

noncomputable section

/-!
# Canonical-space atom facts for Section 3

On the canonical Bernoulli(`p`) space `berP` over `(Fin ℓ → ℝ)` (see
`Submission.Threshold`), the measure is concentrated on the `2^ℓ` points
`vOf B := 1_B` (`B ⊆ {0..ℓ−1}`), each of real mass `wB ℓ p B =
p^(|B|)·(1−p)^(ℓ−|B|)`.

This module proves: (1) the real mass of the singleton `{vOf B}` equals
`wB ℓ p B` (`real_singleton_mass`); (2) for any measurable `E`, the weighted
sum of the atom masses inside `E` is at most the real measure of `E`
(`measure_ge_subsetSum`).  These bridge the combinatorial averages of
`Submission.Sec3Core.avgF` to the Lévy-concentration bounds supplied by the
LKR inequality on the canonical space.
-/

open scoped BigOperators
open MeasureTheory ProbabilityTheory Measure

namespace Submission.CanonAtom

open Submission.Threshold
open Submission.Sec3

open Classical
attribute [local instance] Classical.propDecidable

/-- Characteristic function of `B` as an element of the canonical space. -/
def vOf {ℓ : ℕ} (B : Finset (Fin ℓ)) : Fin ℓ → ℝ := fun j => if j ∈ B then 1 else 0

lemma vOf_injective {ℓ : ℕ} : Function.Injective (@vOf ℓ) := by
  intro B C hBC
  ext j
  have h := congrFun hBC j
  by_cases hj : j ∈ B <;> simp [vOf, hj] at h ⊢ <;> by_contra hc <;> simp [vOf, hc] at h

/-- Real mass of the Bernoulli atom `{c}` for `c ∈ {0,1}`. -/
lemma real_bernoulli_atom_mass (p : unitInterval) {c : ℝ} (hc : c = 0 ∨ c = 1) :
    (bernoulliMeasure 1 0 p).real ({c} : Set ℝ) = (if c = 1 then (p : ℝ) else 1 - (p : ℝ)) := by
  classical
  rcases hc with hc0 | hc1
  · rw [hc0]
    have hs : MeasurableSet ({0} : Set ℝ) := measurableSet_singleton (0 : ℝ)
    have h1out : (1 : ℝ) ∉ ({0} : Set ℝ) := by simp
    have h0in : (0 : ℝ) ∈ ({0} : Set ℝ) := by simp
    rw [bernoulliMeasure_real_apply_of_notMem_of_mem p hs h1out h0in]
    simp
  · rw [hc1]
    have hs : MeasurableSet ({1} : Set ℝ) := measurableSet_singleton (1 : ℝ)
    have h1in : (1 : ℝ) ∈ ({1} : Set ℝ) := by simp
    have h0out : (0 : ℝ) ∉ ({1} : Set ℝ) := by simp
    rw [bernoulliMeasure_real_apply_of_mem_of_notMem p hs h1in h0out]
    simp

/-- Real mass of the point `vOf B` equals the weight `wB ℓ p B`. -/
lemma real_singleton_mass {ℓ : ℕ} (p : unitInterval) (B : Finset (Fin ℓ)) :
    (berP (n := ℓ) p).real {x : Fin ℓ → ℝ | x = vOf B} = wB ℓ p B := by
  classical
  -- (berP p){vB} = ∏_j (bernoulliMeasure 1 0 p){vB j}   (pi_singleton)
  have hsing : (berP (n := ℓ) p) {x : Fin ℓ → ℝ | x = vOf B} =
      ∏ j : Fin ℓ, (bernoulliMeasure 1 0 p) {vOf B j} := by
    unfold berP
    simpa using (Measure.pi_singleton (fun _ : Fin ℓ => bernoulliMeasure 1 0 p) (vOf B))
  rw [Measure.real_def]
  rw [hsing]
  rw [ENNReal.toReal_prod]
  have hfactor : ∀ j : Fin ℓ, ((bernoulliMeasure 1 0 p) {vOf B j}).toReal =
      (if j ∈ B then (p : ℝ) else 1 - (p : ℝ)) := by
    intro j
    by_cases hj : j ∈ B
    · have hc : vOf B j = 1 := by simp [vOf, hj]
      rw [hc]
      simpa [hj] using (real_bernoulli_atom_mass p (Or.inr rfl))
    · have hc : vOf B j = 0 := by simp [vOf, hj]
      rw [hc]
      simpa [hj] using (real_bernoulli_atom_mass p (Or.inl rfl))
  rw [show (∏ j : Fin ℓ, ((bernoulliMeasure 1 0 p) {vOf B j}).toReal) =
      (∏ j : Fin ℓ, (if j ∈ B then (p : ℝ) else 1 - (p : ℝ))) by
        apply Finset.prod_congr rfl
        intro j hj
        exact hfactor j]
  -- product over univ splits into B and Bᶜ
  have hsplit := Finset.prod_mul_prod_compl (s := B)
    (fun j : Fin ℓ => if j ∈ B then (p : ℝ) else 1 - (p : ℝ))
  have hBin : (∏ j ∈ B, (if j ∈ B then (p : ℝ) else 1 - (p : ℝ))) = (p : ℝ) ^ B.card := by
    have hc : ∀ j ∈ B, (if j ∈ B then (p : ℝ) else 1 - (p : ℝ)) = (p : ℝ) := by
      intro j hj
      simp [hj]
    calc
      (∏ j ∈ B, (if j ∈ B then (p : ℝ) else 1 - (p : ℝ))) = ∏ j ∈ B, (p : ℝ) :=
          Finset.prod_congr rfl hc
      _ = (p : ℝ) ^ B.card := by simp
  have hBout : (∏ j ∈ Bᶜ, (if j ∈ B then (p : ℝ) else 1 - (p : ℝ))) =
      (1 - (p : ℝ)) ^ (ℓ - B.card) := by
    have hc : ∀ j ∈ Bᶜ, (if j ∈ B then (p : ℝ) else 1 - (p : ℝ)) = (1 - (p : ℝ)) := by
      intro j hj
      have hjn : j ∉ B := Finset.mem_compl.mp hj
      simp [hjn]
    calc
      (∏ j ∈ Bᶜ, (if j ∈ B then (p : ℝ) else 1 - (p : ℝ))) = ∏ j ∈ Bᶜ, (1 - (p : ℝ)) :=
          Finset.prod_congr rfl hc
      _ = (1 - (p : ℝ)) ^ Bᶜ.card := by simp
      _ = (1 - (p : ℝ)) ^ (ℓ - B.card) := by
            congr 1
            rw [Finset.card_compl, Fintype.card_fin]
  rw [← hsplit]
  rw [hBin, hBout]
  unfold wB
  rfl

/-- For any measurable `E`, the weighted sum of the atom masses inside `E` is
at most the real measure of `E`. -/
lemma measure_ge_subsetSum {ℓ : ℕ} (p : unitInterval) (E : Set (Fin ℓ → ℝ))
    (hE : MeasurableSet E) :
    (∑ B ∈ (Finset.univ : Finset (Fin ℓ)).powerset,
      wB ℓ p B * if vOf B ∈ E then 1 else 0) ≤ (berP (n := ℓ) p).real E := by
  classical
  let G : Finset (Finset (Fin ℓ)) :=
    (Finset.univ : Finset (Fin ℓ)).powerset.filter (fun B => vOf B ∈ E)
  -- E ⊇ ⋃_{B ∈ G} {vB}
  have hun : (⋃ B ∈ G, ({vOf B} : Set (Fin ℓ → ℝ))) ⊆ E := by
    intro x hx
    simp at hx
    rcases hx with ⟨B, hB, hx1⟩
    have hBm : B ∈ G := hB
    rw [hx1]
    exact (Finset.mem_filter.mp hBm).2
  have hmeas_sing : ∀ B ∈ G, MeasurableSet ({vOf B} : Set (Fin ℓ → ℝ)) := by
    intro B hB
    exact measurableSet_singleton (vOf B)
  have hdisj : Set.PairwiseDisjoint (↑G : Set (Finset (Fin ℓ)))
      (fun B : Finset (Fin ℓ) => ({vOf B} : Set (Fin ℓ → ℝ))) := by
    intro B hB B' hB' hne
    have hv : vOf B ≠ vOf B' := by
      intro hEq
      exact hne (vOf_injective hEq)
    change Disjoint ({vOf B} : Set (Fin ℓ → ℝ)) ({vOf B'} : Set (Fin ℓ → ℝ))
    exact (Set.disjoint_singleton_left).mpr (by simpa using hv)
  have hbunion : (berP (n := ℓ) p) (⋃ B ∈ G, ({vOf B} : Set (Fin ℓ → ℝ))) =
      ∑ B ∈ G, (berP (n := ℓ) p) ({vOf B} : Set (Fin ℓ → ℝ)) :=
    measure_biUnion_finset hdisj hmeas_sing
  calc
    (∑ B ∈ (Finset.univ : Finset (Fin ℓ)).powerset,
        wB ℓ p B * if vOf B ∈ E then 1 else 0)
        = ∑ B ∈ G, wB ℓ p B := by
            calc
              (∑ B ∈ (Finset.univ : Finset (Fin ℓ)).powerset,
                  wB ℓ p B * if vOf B ∈ E then 1 else 0)
                  = ∑ B ∈ (Finset.univ : Finset (Fin ℓ)).powerset,
                      (if vOf B ∈ E then wB ℓ p B else 0) := by
                      apply Finset.sum_congr rfl
                      intro B hB
                      by_cases h : vOf B ∈ E <;> simp [h]
              _ = ∑ B ∈ G, wB ℓ p B := by
                      dsimp [G]
                      rw [Finset.sum_filter]
    _ = ∑ B ∈ G, (berP (n := ℓ) p).real ({vOf B} : Set (Fin ℓ → ℝ)) := by
            apply Finset.sum_congr rfl
            intro B hB
            change wB ℓ p B = (berP (n := ℓ) p).real {x : Fin ℓ → ℝ | x = vOf B}
            exact (real_singleton_mass p B).symm
    _ = ((berP (n := ℓ) p).real (⋃ B ∈ G, ({vOf B} : Set (Fin ℓ → ℝ)))) := by
            -- real of the disjoint union: sum of reals
            have hfin : ∀ a ∈ G, ((berP (n := ℓ) p) ({vOf a} : Set (Fin ℓ → ℝ))) ≠ ⊤ := by
              intro a ha
              exact measure_ne_top _ _
            change (∑ B ∈ G, ((berP (n := ℓ) p) ({vOf B} : Set (Fin ℓ → ℝ))).toReal) =
              ((berP (n := ℓ) p) (⋃ B ∈ G, ({vOf B} : Set (Fin ℓ → ℝ)))).toReal
            rw [← ENNReal.toReal_sum (s := G) hfin]
            rw [hbunion]
    _ ≤ (berP (n := ℓ) p).real E := by
            exact measureReal_mono hun

end Submission.CanonAtom
