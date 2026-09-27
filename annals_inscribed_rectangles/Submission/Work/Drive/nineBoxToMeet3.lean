import Mathlib
import Submission.Work.Drive.TParity.Basic
import Submission.Work.Drive.meet32_bordism_invariance

/-!
# From the nine-box hypotheses to the engine's three-cube hypotheses

The engine `Work.Drive.manifold_triple_inter_boundary_parity` and the structure `Work.Drive.Meet3Hyp`
(`Submission/Work/Drive/meet32_bordism_invariance.lean`) state their transversality and face
hypotheses in the **three-cube** picture (`x : Fin 3 → ℝ³`), while the *charted* form of the same
hypotheses — what the parametric-Sard route produces, see
`Work.Drive.exists_meet3Data_of_good_family` — is `Work.Drive.TParity.transHyp`/`faceHyp` in the
**nine-box** picture (`y : ℝ⁹`).

The two are *equivalent*: `Work.Drive.TParity.tripleEquiv` (with `mk3` as its inverse) identifies the
points, `Work.Drive.TParity.mem_unitBox8_iff` the box conditions, and `bPartC k (mk3 x) = x k` the
`k`-th block.  This file records the direction *nine-box ⟹ three-cube* (the converse is
`Work.Drive.TParity.transHyp_of_forall` / `faceHyp_of_forall` in `TParity/Transfer3.lean`), together
with the structure assembly. -/

namespace Work.Drive
namespace TParity

open Manifold Set
open scoped Manifold ContDiff Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
  [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]

/-- The transversality hypothesis in the three-cube picture, from the nine-box one. -/
theorem trans_of_transHyp (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M) (h : transHyp D) :
    ∀ x : Fin 3 → EuclideanSpace ℝ (Fin 3),
      (∀ k, x k ∈ Submission.Drive.unitBox 2) →
      D 0 (x 0) = D 1 (x 1) → D 0 (x 0) = D 2 (x 2) →
      TripleTransverse
        (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) (D 0) (x 0))
        (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) (D 1) (x 1))
        (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) (D 2) (x 2)) := by
  intro x hx h01 h02
  have hb : ∀ k : Fin 3, bPart k (mk3 x) = x k := fun k => by
    rw [← bPartC_eq_bPart k (mk3 x), bPartC_mk3]
  have hc : ∀ k : Fin 3, bPartC k (mk3 x) = x k := fun k => bPartC_mk3 k x
  have hbox : mk3 x ∈ Submission.Drive.unitBox 8 := by
    rw [mem_unitBox8_iff]
    intro k
    rw [hb k]
    exact hx k
  have hmeet : meet3 D (mk3 x) := by
    refine ⟨?_, ?_⟩
    · show D 0 (bPartC 0 (mk3 x)) = D 1 (bPartC 1 (mk3 x))
      rw [hc 0, hc 1]; exact h01
    · show D 0 (bPartC 0 (mk3 x)) = D 2 (bPartC 2 (mk3 x))
      rw [hc 0, hc 2]; exact h02
  have key : TripleTransverse (md3 D 0 (mk3 x)) (md3 D 1 (mk3 x)) (md3 D 2 (mk3 x)) :=
    h (mk3 x) hbox hmeet
  rw [show md3 D 0 (mk3 x)
        = mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
            (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) (D 0) (x 0) from by
        rw [md3, hc 0],
      show md3 D 1 (mk3 x)
        = mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
            (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) (D 1) (x 1) from by
        rw [md3, hc 1],
      show md3 D 2 (mk3 x)
        = mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
            (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) (D 2) (x 2) from by
        rw [md3, hc 2]] at key
  exact key

/-- The face hypothesis in the three-cube picture, from the nine-box one. -/
theorem face_of_faceHyp (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M) (h : faceHyp D) :
    ∀ x : Fin 3 → EuclideanSpace ℝ (Fin 3),
      (∀ k, x k ∈ Submission.Drive.unitBox 2) →
      D 0 (x 0) = D 1 (x 1) → D 0 (x 0) = D 2 (x 2) →
      (∃ k, x k ∈ Submission.Drive.unitBoxBdry 2) →
      ∃ (k : Fin 3) (i : Fin 3), (x k i = 0 ∨ x k i = 1) ∧
        (∀ j : Fin 3, j ≠ i → x k j ∈ Set.Ioo (0 : ℝ) 1) ∧
        (∀ k' : Fin 3, k' ≠ k → ∀ j : Fin 3, x k' j ∈ Set.Ioo (0 : ℝ) 1) ∧
        ∃ v : Fin 3 → EuclideanSpace ℝ (Fin 3),
          TripleCommonDir
            (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
              (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) (D 0) (x 0))
            (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
              (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) (D 1) (x 1))
            (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
              (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) (D 2) (x 2)) v ∧
          v k i ≠ 0 := by
  intro x hx h01 h02 hbdry
  have hb : ∀ k : Fin 3, bPart k (mk3 x) = x k := fun k => by
    rw [← bPartC_eq_bPart k (mk3 x), bPartC_mk3]
  have hc : ∀ k : Fin 3, bPartC k (mk3 x) = x k := fun k => bPartC_mk3 k x
  have hbox : mk3 x ∈ Submission.Drive.unitBox 8 := by
    rw [mem_unitBox8_iff]
    intro k
    rw [hb k]
    exact hx k
  have hmeet : meet3 D (mk3 x) := by
    refine ⟨?_, ?_⟩
    · show D 0 (bPartC 0 (mk3 x)) = D 1 (bPartC 1 (mk3 x))
      rw [hc 0, hc 1]; exact h01
    · show D 0 (bPartC 0 (mk3 x)) = D 2 (bPartC 2 (mk3 x))
      rw [hc 0, hc 2]; exact h02
  have hbdry8 : mk3 x ∈ Submission.Drive.unitBoxBdry 8 := by
    rw [mem_unitBoxBdry8_iff]
    refine ⟨hbox, ?_⟩
    obtain ⟨k, hk⟩ := hbdry
    exact ⟨k, by rwa [hb k]⟩
  obtain ⟨k, i, hface, hint, hint', v, hv, hvi⟩ := h (mk3 x) hbox hmeet hbdry8
  have hface' : x k i = 0 ∨ x k i = 1 := by rwa [mk3_bIdx x k i] at hface
  have hint'2 : ∀ j : Fin 3, j ≠ i → x k j ∈ Set.Ioo (0 : ℝ) 1 := fun j hj => by
    have h := hint j hj
    rwa [mk3_bIdx x k j] at h
  have hint'' : ∀ k' : Fin 3, k' ≠ k → ∀ j : Fin 3, x k' j ∈ Set.Ioo (0 : ℝ) 1 :=
    fun k' hk' j => by
      have h := hint' k' hk' j
      rwa [mk3_bIdx x k' j] at h
  have hv' : TripleCommonDir (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) (D 0) (x 0))
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) (D 1) (x 1))
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) (D 2) (x 2)) v := by
    rw [show md3 D 0 (mk3 x)
          = mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
              (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) (D 0) (x 0) from by
          rw [md3, hc 0],
        show md3 D 1 (mk3 x)
          = mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
              (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) (D 1) (x 1) from by
          rw [md3, hc 1],
        show md3 D 2 (mk3 x)
          = mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
              (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) (D 2) (x 2) from by
          rw [md3, hc 2]] at hv
    exact hv
  exact ⟨k, i, hface', hint'2, hint'', v, hv', hvi⟩

/-! ## From hypotheses on a compact set to the full nine-box hypotheses

The parametric genericity route (`Work.Drive.exists_meet3Data_of_good_family`) produces its two
conclusions on a *compact* set `K` — the set that is chosen to contain the perturbed triple locus (by
`Work.Drive.eventually_meet3_subset_of_isOpen`).  The engine, however, takes them at *every* triple
point of the nine-box.  The two lemmas below are that one-line conversion: if every triple point of
the chains in the box lies in `K`, the hypotheses on `K` are the full ones. -/

/-- `TParity.transHyp` from the transversality statement restricted to a compact set containing the
triple locus. -/
theorem transHyp_of_on_compact (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M) (K : Set (Amb 8))
    (hK : ∀ y ∈ Submission.Drive.unitBox 8, meet3 D y → y ∈ K)
    (h : ∀ y ∈ K, y ∈ Submission.Drive.unitBox 8 → meet3 D y →
      TripleTransverse (md3 D 0 y) (md3 D 1 y) (md3 D 2 y)) :
    transHyp D :=
  fun y hybox hmeet => h y (hK y hybox hmeet) hybox hmeet

/-- `TParity.faceHyp` from the face statement restricted to a compact set containing the triple
locus. -/
theorem faceHyp_of_on_compact (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M) (K : Set (Amb 8))
    (hK : ∀ y ∈ Submission.Drive.unitBox 8, meet3 D y → y ∈ K)
    (h : ∀ y ∈ K, y ∈ Submission.Drive.unitBox 8 → meet3 D y →
      y ∈ Submission.Drive.unitBoxBdry 8 →
      ∃ (k : Fin 3) (i : Fin 3), (y (Work.Drive.bIdx k i) = 0 ∨ y (Work.Drive.bIdx k i) = 1) ∧
        (∀ j : Fin 3, j ≠ i → y (Work.Drive.bIdx k j) ∈ Set.Ioo (0 : ℝ) 1) ∧
        (∀ k' : Fin 3, k' ≠ k → ∀ j : Fin 3, y (Work.Drive.bIdx k' j) ∈ Set.Ioo (0 : ℝ) 1) ∧
        ∃ v : Fin 3 → EuclideanSpace ℝ (Fin 3),
          TripleCommonDir (md3 D 0 y) (md3 D 1 y) (md3 D 2 y) v ∧ (v k) i ≠ 0) :
    faceHyp D :=
  fun y hybox hmeet hbdry => h y (hK y hybox hmeet) hybox hmeet hbdry

end

end TParity

/-- **The engine's three-cube hypotheses from the nine-box ones.**

Together with the smoothness of the three chains and their seam invariance, the nine-box hypotheses
`TParity.transHyp` and `TParity.faceHyp` — what the parametric-Sard route produces — assemble into
`Meet3Hyp`, i.e. the input of `Work.Drive.manifold_triple_inter_boundary_parity`. -/
theorem Meet3Hyp.of_nineBox {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M)
    (hsmooth : ∀ k, ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) (D k))
    (htrans : TParity.transHyp D) (hface : TParity.faceHyp D)
    (hseam : ∀ (k : Fin 3) (x : EuclideanSpace ℝ (Fin 3)), onSeam x → D k x = D k (seamInv x)) :
    Meet3Hyp M D :=
  ⟨hsmooth, TParity.trans_of_transHyp D htrans, TParity.face_of_faceHyp D hface, hseam⟩

end Work.Drive
