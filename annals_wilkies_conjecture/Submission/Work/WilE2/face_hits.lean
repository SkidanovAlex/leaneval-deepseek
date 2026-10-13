/-
  Work.WilE2 — area E2.  The slice ("face") step for the components bound of an EA variety.

  `face_hits` is the induction step that produces a hitting set of the intersection of the cube
  `cubeC (n+1)`, the variety `Zset c g` and a coordinate hyperplane `{x | x j = σ}`, *with the same
  polynomial bound `Q`* as the `n`-dimensional statement `hIH` it is given.

  The hyperplane `{x j = σ}` is homeomorphic to `ℝⁿ` (`faceLift`/`faceProj`), and slicing transports
  the whole EA problem: the restricted chain `chainFace c j σ` absorbs the contribution `a k j * σ`
  of the frozen coordinate into its constant term (`chainFace_ell`), and the sliced atoms
  `faceSub j σ f` (`faceSub_eval`) have no larger atom degree (`atomDeg_faceSub_le`).  Hence `hIH`
  applies to the slice, and its hitting set is mapped back by `faceLift`, which preserves the
  connected components (`hits_image`, with `continuous_faceLift`).

  If `|σ| > 1` the slice is empty and the empty hitting set works.
-/
import Mathlib
import Submission.Work.WilE2.VcbDefs
import Submission.Work.WilE2.FaceDefs
import Submission.Work.WilE2.faceLift_mem_slice
import Submission.Work.WilE2.faceProj_mem_R
import Submission.Work.WilE2.hits_image

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE2
open WilkiesDesign WilkiesDesign.E

theorem face_hits {n : ℕ} (Q : Polynomial ℕ) {F : ℕ}
    (hIH : ∀ (r : ℕ) (c : WilkiesDesign.E.EAChain n r) (g : Finset (WilkiesDesign.E.EAPoly n r)) (D : ℕ),
      n + r ≤ F → (∑ f ∈ g, WilkiesDesign.E.atomDeg f) ≤ D →
      ∃ s : Finset (Fin n → ℝ), (↑s : Set (Fin n → ℝ)) ⊆ WilkiesDesign.E.cubeC n ∩ Work.WilE2.Zset c g ∧
        s.card ≤ Q.eval D ∧ Work.WilE2.Hits (WilkiesDesign.E.cubeC n ∩ Work.WilE2.Zset c g) s)
    (r : ℕ) (c : WilkiesDesign.E.EAChain (n+1) r) (g : Finset (WilkiesDesign.E.EAPoly (n+1) r))
    (j : Fin (n+1)) (σ : ℝ) (D : ℕ) (hnr : n + r ≤ F) (hD : (∑ f ∈ g, WilkiesDesign.E.atomDeg f) ≤ D) :
    ∃ s : Finset (Fin (n+1) → ℝ),
      (↑s : Set (Fin (n+1) → ℝ)) ⊆ WilkiesDesign.E.cubeC (n+1) ∩ Work.WilE2.Zset c g ∩ {x | x j = σ} ∧
      s.card ≤ Q.eval D ∧
      Work.WilE2.Hits (WilkiesDesign.E.cubeC (n+1) ∩ Work.WilE2.Zset c g ∩ {x | x j = σ}) s := by
  by_cases hσ : |σ| ≤ 1
  · -- The slice is nonempty in principle: transport the problem to `ℝⁿ` and apply `hIH`.
    have hD' : (∑ f ∈ g.image (faceSub j σ), atomDeg f) ≤ D := by
      refine le_trans ?_ hD
      refine le_trans (sum_image_le_nat g (faceSub j σ) atomDeg) ?_
      exact Finset.sum_le_sum fun f _ => atomDeg_faceSub_le j σ f
    obtain ⟨s', hs'S, hs'card, hs'hits⟩ :=
      hIH r (chainFace c j σ) (g.image (faceSub j σ)) D hnr hD'
    refine ⟨s'.image (faceLift j σ), ?_, ?_, ?_⟩
    · -- the lifted points lie in the slice
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      exact faceLift_mem_slice c j σ hσ g y (hs'S hy)
    · -- the lift is injective, so the cardinality does not increase
      exact le_trans Finset.card_image_le hs'card
    · -- the lift carries components of the slice to components of the slice
      exact hits_image (faceLift j σ) (continuous_faceLift j σ) (faceProj j)
        (fun y hy => faceLift_mem_slice c j σ hσ g y hy)
        (fun x hx => faceProj_mem_R c j σ g x hx)
        (fun x hx => faceLift_faceProj j σ x hx.2) s' hs'S hs'hits
  · -- `|σ| > 1`: the slice misses the cube, so it is empty and so is the hitting set.
    have hXempty : cubeC (n+1) ∩ Zset c g ∩ {x : Fin (n+1) → ℝ | x j = σ} = ∅ := by
      ext x
      constructor
      · intro hx
        exact absurd (show |σ| ≤ 1 from by rw [← hx.2]; exact hx.1.1 j) hσ
      · intro hx
        exact absurd hx (Set.notMem_empty x)
    refine ⟨∅, ?_, ?_, ?_⟩
    · rw [hXempty]
      simp
    · simp
    · rw [hXempty]
      intro x hx
      exact absurd hx (by simp)

end Work.WilE2
