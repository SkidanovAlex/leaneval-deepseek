import Mathlib
import Submission.Work.WilE2.PosComps.Bound
import Submission.Work.WilE2.FaceDefs
import Submission.Work.WilE2.faceLift_mem_slice

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
open Classical Topology Filter

namespace Work.WilE2

open WilkiesDesign WilkiesDesign.E

/-! ## §8.  The face transfer -/

theorem continuous_faceProj {n : ℕ} (j : Fin (n + 1)) :
    Continuous fun x : Fin (n + 1) → ℝ => faceProj j x := by
  refine continuous_pi fun i => ?_
  exact continuous_apply (j.succAbove i)

/-- The image of the lower dimensional positive set under the face lift lies in the positive set of
the original function. -/
theorem image_faceLift_subset_posSet {n r : ℕ} (c : EAChain (n + 1) r) (Q : EAPoly (n + 1) r)
    (j : Fin (n + 1)) {σ : ℝ} (hσ : |σ| ≤ 1) :
    faceLift j σ '' posSet (chainFace c j σ) (faceSub j σ Q) ⊆ posSet c Q := by
  rintro x ⟨y, hy, rfl⟩
  refine ⟨faceLift_mem_cube j hσ hy.1, ?_⟩
  show 0 < eaEval c Q (faceLift j σ y)
  rw [← faceSub_eval]
  exact hy.2

/-- Lifting a point of the component of `y` keeps it in the component of the lift of `y`. -/
theorem faceLift_mem_component {n r : ℕ} (c : EAChain (n + 1) r) (Q : EAPoly (n + 1) r)
    (j : Fin (n + 1)) {σ : ℝ} (hσ : |σ| ≤ 1)
    {y : Fin n → ℝ} (hy : y ∈ posSet (chainFace c j σ) (faceSub j σ Q))
    {y' : Fin n → ℝ}
    (hy' : y' ∈ connectedComponentIn (posSet (chainFace c j σ) (faceSub j σ Q)) y) :
    faceLift j σ y' ∈ connectedComponentIn (posSet c Q) (faceLift j σ y) := by
  have hpre : IsPreconnected
      (faceLift j σ '' connectedComponentIn (posSet (chainFace c j σ) (faceSub j σ Q)) y) :=
    (isPreconnected_connectedComponentIn (F := posSet (chainFace c j σ) (faceSub j σ Q))
      (x := y)).image _ (continuous_faceLift j σ).continuousOn
  refine hpre.subset_connectedComponentIn ⟨y, mem_connectedComponentIn hy, rfl⟩ ?_
    ⟨y', hy', rfl⟩
  rintro x ⟨z, hz, rfl⟩
  exact image_faceLift_subset_posSet c Q j hσ
    ⟨z, connectedComponentIn_subset _ _ hz, rfl⟩

/-! ## §9.  The induction -/

theorem posComps_aux : ∀ k : ℕ, ∀ (r : ℕ) (c : EAChain k r) (Q : EAPoly k r),
    ∃ s : Finset (Fin k → ℝ), (↑s : Set (Fin k → ℝ)) ⊆ posSet c Q ∧
      ∀ x ∈ posSet c Q, ∃ y ∈ s,
        connectedComponentIn (posSet c Q) x = connectedComponentIn (posSet c Q) y := by
  intro k
  induction k with
  | zero =>
    intro r c Q
    by_cases h : (posSet c Q).Nonempty
    · refine ⟨{h.choose}, ?_, ?_⟩
      · intro y hy
        rw [Finset.coe_singleton, Set.mem_singleton_iff] at hy
        exact hy ▸ h.choose_spec
      · intro x hx
        refine ⟨h.choose, Finset.mem_singleton_self _, ?_⟩
        have hx' : x = h.choose := Subsingleton.elim _ _
        rw [hx']
    · refine ⟨∅, by simp, ?_⟩
      intro x hx
      exact absurd ⟨x, hx⟩ h
  | succ k ih =>
    intro r c Q
    classical
    have hfin : ({C : Set (Fin (k + 1) → ℝ) | IsIsland c Q C}).Finite := islandSet_finite c Q
    set islPt : Set (Fin (k + 1) → ℝ) → Fin (k + 1) → ℝ := fun C =>
      if h : C.Nonempty then h.choose else 0 with hIslPt
    have hislPt_mem : ∀ C, IsIsland c Q C → islPt C ∈ C := by
      intro C hC
      have hne : C.Nonempty := by
        obtain ⟨⟨x, hx, hxC⟩, -⟩ := hC
        exact ⟨x, hxC ▸ mem_connectedComponentIn hx⟩
      rw [hIslPt]
      simp only [dif_pos hne]
      exact hne.choose_spec
    -- the two faces of each coordinate
    let sg : Bool → ℝ := fun b => cond b (1 : ℝ) (-1)
    have hsg_true : sg true = 1 := rfl
    have hsg_false : sg false = -1 := rfl
    have hsg_abs : ∀ b : Bool, |sg b| = 1 := by
      intro b; cases b <;> simp [sg, hsg_true, hsg_false]
    have hface : ∀ (j : Fin (k + 1)) (b : Bool),
        ∃ sf : Finset (Fin k → ℝ), (↑sf : Set (Fin k → ℝ)) ⊆
            posSet (chainFace c j (sg b)) (faceSub j (sg b) Q) ∧
          ∀ x ∈ posSet (chainFace c j (sg b)) (faceSub j (sg b) Q),
            ∃ y ∈ sf,
              connectedComponentIn (posSet (chainFace c j (sg b)) (faceSub j (sg b) Q)) x =
              connectedComponentIn (posSet (chainFace c j (sg b)) (faceSub j (sg b) Q)) y :=
      fun j b => ih r _ _
    choose sf hsf using hface
    refine ⟨(Finset.univ.biUnion fun j : Fin (k + 1) =>
        (Finset.univ : Finset Bool).biUnion fun b =>
          (sf j b).image (faceLift j (sg b))) ∪ (hfin.toFinset.image islPt),
      ?_, ?_⟩
    · intro x hx
      rw [Finset.mem_coe, Finset.mem_union] at hx
      rcases hx with hx | hx
      · rw [Finset.mem_biUnion] at hx
        obtain ⟨j, -, hx⟩ := hx
        rw [Finset.mem_biUnion] at hx
        obtain ⟨b, -, hx⟩ := hx
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
        exact image_faceLift_subset_posSet c Q j (le_of_eq (hsg_abs b))
          ⟨y, (hsf j b).1 hy, rfl⟩
      · obtain ⟨C, hCmem, rfl⟩ := Finset.mem_image.mp hx
        exact island_posSet (hfin.mem_toFinset.mp hCmem)
          (hislPt_mem C (hfin.mem_toFinset.mp hCmem))
    · intro x hx
      by_cases hfr : (connectedComponentIn (posSet c Q) x ∩ frontier (cubeC (k + 1))).Nonempty
      · -- a component meeting the frontier: use a face
        obtain ⟨w, hwC, hwfr⟩ := hfr
        have hwS : w ∈ posSet c Q := connectedComponentIn_subset _ _ hwC
        rcases frontier_cubeC_subset hwfr with ⟨j, hj | hj⟩
        · -- the face `x j = 1`
          have hpos : faceProj j w ∈ posSet (chainFace c j (sg true)) (faceSub j (sg true) Q) := by
            refine ⟨fun i => ?_, ?_⟩
            · rw [faceProj_apply]
              exact hwS.1 (j.succAbove i)
            · show 0 < eaEval (chainFace c j (sg true)) (faceSub j (sg true) Q) (faceProj j w)
              rw [faceSub_eval, show sg true = 1 from hsg_true, faceLift_faceProj j 1 w hj]
              exact hwS.2
          obtain ⟨y', hy', hy''⟩ := (hsf j true).2 (faceProj j w) hpos
          have hy'C : y' ∈ connectedComponentIn
              (posSet (chainFace c j (sg true)) (faceSub j (sg true) Q)) (faceProj j w) :=
            hy''.symm ▸ mem_connectedComponentIn ((hsf j true).1 hy')
          have hmem : faceLift j 1 y' ∈ connectedComponentIn (posSet c Q) w := by
            have h1 := faceLift_mem_component c Q j (le_of_eq (hsg_abs true)) hpos hy'C
            rw [hsg_true, faceLift_faceProj j 1 w hj] at h1
            exact h1
          refine ⟨faceLift j 1 y', ?_, ?_⟩
          · rw [Finset.mem_union]; left
            refine Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, ?_⟩
            refine Finset.mem_biUnion.mpr ⟨true, Finset.mem_univ _, ?_⟩
            exact Finset.mem_image.mpr ⟨y', hy', by rw [hsg_true]⟩
          · have hA : connectedComponentIn (posSet c Q) x = connectedComponentIn (posSet c Q) w :=
              connectedComponentIn_eq hwC
            have hB : connectedComponentIn (posSet c Q) w =
                connectedComponentIn (posSet c Q) (faceLift j 1 y') := connectedComponentIn_eq hmem
            exact hA.trans hB
        · -- the face `x j = -1`
          have hpos : faceProj j w ∈ posSet (chainFace c j (sg false)) (faceSub j (sg false) Q) := by
            refine ⟨fun i => ?_, ?_⟩
            · rw [faceProj_apply]
              exact hwS.1 (j.succAbove i)
            · show 0 < eaEval (chainFace c j (sg false)) (faceSub j (sg false) Q) (faceProj j w)
              rw [faceSub_eval, show sg false = -1 from hsg_false, faceLift_faceProj j (-1) w hj]
              exact hwS.2
          obtain ⟨y', hy', hy''⟩ := (hsf j false).2 (faceProj j w) hpos
          have hy'C : y' ∈ connectedComponentIn
              (posSet (chainFace c j (sg false)) (faceSub j (sg false) Q)) (faceProj j w) :=
            hy''.symm ▸ mem_connectedComponentIn ((hsf j false).1 hy')
          have hmem : faceLift j (-1) y' ∈ connectedComponentIn (posSet c Q) w := by
            have h1 := faceLift_mem_component c Q j (le_of_eq (hsg_abs false)) hpos hy'C
            rw [hsg_false, faceLift_faceProj j (-1) w hj] at h1
            exact h1
          refine ⟨faceLift j (-1) y', ?_, ?_⟩
          · rw [Finset.mem_union]; left
            refine Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, ?_⟩
            refine Finset.mem_biUnion.mpr ⟨false, Finset.mem_univ _, ?_⟩
            exact Finset.mem_image.mpr ⟨y', hy', by rw [hsg_false]⟩
          · have hA : connectedComponentIn (posSet c Q) x = connectedComponentIn (posSet c Q) w :=
              connectedComponentIn_eq hwC
            have hB : connectedComponentIn (posSet c Q) w =
                connectedComponentIn (posSet c Q) (faceLift j (-1) y') := connectedComponentIn_eq hmem
            exact hA.trans hB
      · -- an island: the chosen point of the island
        have hIsl : IsIsland c Q (connectedComponentIn (posSet c Q) x) :=
          ⟨⟨x, hx, rfl⟩, Set.disjoint_iff_inter_eq_empty.mpr
            (Set.not_nonempty_iff_eq_empty.mp hfr)⟩
        refine ⟨islPt (connectedComponentIn (posSet c Q) x), ?_, ?_⟩
        · rw [Finset.mem_union]; right
          exact Finset.mem_image.mpr ⟨_, hfin.mem_toFinset.mpr hIsl, rfl⟩
        · exact connectedComponentIn_eq (hislPt_mem _ hIsl)

theorem posComps_finite {k r : ℕ} (c : WilkiesDesign.E.EAChain k r) (Q : WilkiesDesign.E.EAPoly k r) :
    ∃ s : Finset (Fin k → ℝ),
      (↑s : Set (Fin k → ℝ)) ⊆
        WilkiesDesign.E.cubeC k ∩ {x | 0 < WilkiesDesign.E.eaEval c Q x} ∧
      ∀ x ∈ WilkiesDesign.E.cubeC k ∩ {x | 0 < WilkiesDesign.E.eaEval c Q x}, ∃ y ∈ s,
        connectedComponentIn (WilkiesDesign.E.cubeC k ∩ {x | 0 < WilkiesDesign.E.eaEval c Q x}) x =
        connectedComponentIn (WilkiesDesign.E.cubeC k ∩ {x | 0 < WilkiesDesign.E.eaEval c Q x}) y := by
  obtain ⟨s, hs, hhit⟩ := posComps_aux k r c Q
  exact ⟨s, hs, hhit⟩

end Work.WilE2
