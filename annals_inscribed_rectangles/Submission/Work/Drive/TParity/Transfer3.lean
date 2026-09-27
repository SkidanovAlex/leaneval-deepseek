import Mathlib
import Submission.Work.Drive.TParity.Basic
import Submission.Work.Drive.TripleMeetDefs

/-!
# Translation between the three-cube picture and the nine-box picture

The hypotheses of `Work.Drive.manifold_triple_inter_boundary_parity` are stated for points
`x : Fin 3 → ℝ³` of the product of the three unit cubes; the body of the proof works in the
nine-box `Work.Drive.Amb 8 = ℝ⁹`.  This file records the translation, via
`Work.Drive.TParity.tripleEquiv`.

* `transHyp_of_forall`: the transversality hypothesis of the target statement implies
  `Work.Drive.TParity.transHyp`;
* `faceHyp_of_forall`: likewise for the face hypothesis;
* `S3_ncard_eq` and `tripleBdryMeet_finite_iff`: the counts of the labelled boundary sets in the two
  pictures agree.
-/

namespace Work.Drive.TParity

open scoped Manifold ContDiff Topology
open Manifold Set

noncomputable section

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) Ctop M]

/-- The transversality hypothesis of the target statement, transported to the nine-box. -/
theorem transHyp_of_forall (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M)
    (htrans : ∀ x : Fin 3 → EuclideanSpace ℝ (Fin 3),
      (∀ k, x k ∈ Submission.Drive.unitBox 2) →
      D 0 (x 0) = D 1 (x 1) → D 0 (x 0) = D 2 (x 2) →
      Work.Drive.TripleTransverse
        (mfderiv (𝓡 3) (𝓡 4) (D 0) (x 0)) (mfderiv (𝓡 3) (𝓡 4) (D 1) (x 1))
        (mfderiv (𝓡 3) (𝓡 4) (D 2) (x 2))) :
    transHyp D := by
  intro x hbox hm
  have hybox : ∀ k, (fun k' => Work.Drive.bPart k' x) k ∈ Submission.Drive.unitBox 2 :=
    fun k => (mem_unitBox8_iff x).mp hbox k
  have hy1 : D 0 ((fun k' => Work.Drive.bPart k' x) 0) = D 1 ((fun k' => Work.Drive.bPart k' x) 1) := by
    simpa [bPartC_eq_bPart] using hm.1
  have hy2 : D 0 ((fun k' => Work.Drive.bPart k' x) 0) = D 2 ((fun k' => Work.Drive.bPart k' x) 2) := by
    simpa [bPartC_eq_bPart] using hm.2
  have h := htrans (fun k' => Work.Drive.bPart k' x) hybox hy1 hy2
  have e0 : md3 D 0 x = mfderiv (𝓡 3) (𝓡 4) (D 0) (Work.Drive.bPart 0 x) := by
    unfold md3; congr 2
  have e1 : md3 D 1 x = mfderiv (𝓡 3) (𝓡 4) (D 1) (Work.Drive.bPart 1 x) := by
    unfold md3; congr 2
  have e2 : md3 D 2 x = mfderiv (𝓡 3) (𝓡 4) (D 2) (Work.Drive.bPart 2 x) := by
    unfold md3; congr 2
  rw [e0, e1, e2]
  exact h

/-- The face hypothesis of the target statement, transported to the nine-box. -/
theorem faceHyp_of_forall (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M)
    (hface : ∀ x : Fin 3 → EuclideanSpace ℝ (Fin 3),
      (∀ k, x k ∈ Submission.Drive.unitBox 2) →
      D 0 (x 0) = D 1 (x 1) → D 0 (x 0) = D 2 (x 2) →
      (∃ k, x k ∈ Submission.Drive.unitBoxBdry 2) →
      ∃ (k : Fin 3) (i : Fin 3), (x k i = 0 ∨ x k i = 1) ∧
        (∀ j : Fin 3, j ≠ i → x k j ∈ Set.Ioo (0 : ℝ) 1) ∧
        (∀ k' : Fin 3, k' ≠ k → ∀ j : Fin 3, x k' j ∈ Set.Ioo (0 : ℝ) 1) ∧
        ∃ v : Fin 3 → EuclideanSpace ℝ (Fin 3),
          Work.Drive.TripleCommonDir
            (mfderiv (𝓡 3) (𝓡 4) (D 0) (x 0)) (mfderiv (𝓡 3) (𝓡 4) (D 1) (x 1))
            (mfderiv (𝓡 3) (𝓡 4) (D 2) (x 2)) v ∧ v k i ≠ 0) :
    faceHyp D := by
  intro x hbox hm hbdry
  have hybox : ∀ k, (fun k' => Work.Drive.bPart k' x) k ∈ Submission.Drive.unitBox 2 :=
    fun k => (mem_unitBox8_iff x).mp hbox k
  have hy1 : D 0 ((fun k' => Work.Drive.bPart k' x) 0) = D 1 ((fun k' => Work.Drive.bPart k' x) 1) := by
    simpa [bPartC_eq_bPart] using hm.1
  have hy2 : D 0 ((fun k' => Work.Drive.bPart k' x) 0) = D 2 ((fun k' => Work.Drive.bPart k' x) 2) := by
    simpa [bPartC_eq_bPart] using hm.2
  obtain ⟨-, k, hk⟩ := (mem_unitBoxBdry8_iff x).mp hbdry
  obtain ⟨k0, i0, hi0, hoth, hoth', v, hvcd, hvne⟩ :=
    hface (fun k' => Work.Drive.bPart k' x) hybox hy1 hy2 ⟨k, hk⟩
  refine ⟨k0, i0, ?_, ?_, ?_, v, ?_, hvne⟩
  · simpa [Work.Drive.bPart_apply] using hi0
  · intro j hj
    simpa [Work.Drive.bPart_apply] using hoth j hj
  · intro k' hk' j
    simpa [Work.Drive.bPart_apply] using hoth' k' hk' j
  · have e0 : md3 D 0 x = mfderiv (𝓡 3) (𝓡 4) (D 0) (Work.Drive.bPart 0 x) := by
      unfold md3; congr 2
    have e1 : md3 D 1 x = mfderiv (𝓡 3) (𝓡 4) (D 1) (Work.Drive.bPart 1 x) := by
      unfold md3; congr 2
    have e2 : md3 D 2 x = mfderiv (𝓡 3) (𝓡 4) (D 2) (Work.Drive.bPart 2 x) := by
      unfold md3; congr 2
    rw [e0, e1, e2]
    exact hvcd

/-- The labelled boundary sets agree in the two pictures. -/
theorem S3_ncard_eq (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M) (k : Fin 3) :
    (S3 D k).ncard = (Work.Drive.tripleBdryMeet M D k).ncard := by
  have h : tripleEquiv '' (S3 D k) = Work.Drive.tripleBdryMeet M D k := by
    rw [S3_eq_preimage]
    exact Set.image_preimage_eq _ tripleEquiv.surjective
  rw [← h, Set.ncard_image_of_injective _ tripleEquiv.injective]

/-- The labelled boundary sets are finite in one picture exactly when they are in the other. -/
theorem tripleBdryMeet_finite_iff (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M) (k : Fin 3) :
    (Work.Drive.tripleBdryMeet M D k).Finite ↔ (S3 D k).Finite := by
  have h : tripleEquiv '' (S3 D k) = Work.Drive.tripleBdryMeet M D k := by
    rw [S3_eq_preimage]
    exact Set.image_preimage_eq _ tripleEquiv.surjective
  rw [← h]
  exact ⟨fun hf => Set.Finite.of_finite_image hf tripleEquiv.injective.injOn,
    fun hf => hf.image _⟩

end

end Work.Drive.TParity
