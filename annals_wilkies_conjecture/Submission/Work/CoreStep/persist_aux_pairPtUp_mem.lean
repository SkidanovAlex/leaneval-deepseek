import Mathlib
import Submission.Work.WilE7.CoreStep.GermDefs

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.CoreStep

open Work.WilE7.CoreStep

/-- Membership of the pair point of two piece points in the **level-agreeing** pair set: if
`u ∈ T.X.set`, `v ∈ T'.X.set`, the two points have the same base point (`π_n`) and the same last
(vertical) coordinate, then `(u,v)` lies in `absLevelPairSet T T'`.

This is the `levelGlue` analogue of `mem_absPairSet` in `GermDefs`. -/
theorem mem_absLevelPairSet {n m : ℕ} (T T' : WilkiesDesign.E.Stratum 0 (n + (m + 1)))
    (u v : Fin (pDim n m) → ℝ) (hu : u ∈ T.X.set) (hv : v ∈ T'.X.set)
    (hbase : WilkiesDesign.E.projFirst n (m + 1) (absPtInv u) =
      WilkiesDesign.E.projFirst n (m + 1) (absPtInv v))
    (hlev : (WilkiesDesign.E.projSnd n (m + 1) (absPtInv u)) ⟨m, by omega⟩ =
      (WilkiesDesign.E.projSnd n (m + 1) (absPtInv v)) ⟨m, by omega⟩) :
    pairPtUp u v ∈ (absLevelPairSet T T').set := by
  have hup : (fun i : Fin (pPair n m) => pairPtUp u v
      ((Work.WilE7.finEquiv (Nat.zero_add (pPair n m))).symm i)) = pairPt u v := by
    funext i
    show pairPt u v (Fin.cast (Nat.zero_add (pPair n m))
      ((Work.WilE7.finEquiv (Nat.zero_add (pPair n m))).symm i)) = pairPt u v i
    congr 1
  simp only [absLevelPairSet, Work.WilE7.sp_reindex_set, Set.mem_ofPred_eq, hup,
    Work.WilE7.levelGlue_set, projFirst_pairPt, projSnd_pairPt, mem_absReindex,
    absPtUp_absPtInv]
  exact ⟨hu, hv, hbase, hlev⟩

theorem persist_aux_pairPtUp_mem {n m k : ℕ} (T : WilkiesDesign.E.Stratum 0 (n + (m + 1)))
    (C : Set (Fin n → ℝ))
    (s : Fin k → (Fin n → ℝ) → (Fin (m + 1) → ℝ))
    (hsub : ∀ j : Fin k, ∀ x ∈ C,
      Work.WilE7.CoreStep.absPtUp (n := n) (m := m) (Fin.append x (s j x)) ∈ T.X.set)
    (j j' : Fin k) (x₀ : Fin n → ℝ) (hx₀ : x₀ ∈ C)
    (hlev : (s j x₀) (Fin.last m) = (s j' x₀) (Fin.last m)) :
    Work.WilE7.CoreStep.pairPtUp
        (Work.WilE7.CoreStep.absPtUp (n := n) (m := m) (Fin.append x₀ (s j x₀)))
        (Work.WilE7.CoreStep.absPtUp (n := n) (m := m) (Fin.append x₀ (s j' x₀)))
      ∈ (Work.WilE7.CoreStep.absLevelPairSet T T).set := by
  refine mem_absLevelPairSet T T
    (u := Work.WilE7.CoreStep.absPtUp (n := n) (m := m) (Fin.append x₀ (s j x₀)))
    (v := Work.WilE7.CoreStep.absPtUp (n := n) (m := m) (Fin.append x₀ (s j' x₀)))
    ?_ ?_ ?_ ?_
  · exact hsub j x₀ hx₀
  · exact hsub j' x₀ hx₀
  · rw [Work.WilE7.CoreStep.absPtInv_absPtUp, Work.WilE7.CoreStep.absPtInv_absPtUp]
    funext i
    simp [WilkiesDesign.E.projFirst, Fin.append_left]
  · rw [Work.WilE7.CoreStep.absPtInv_absPtUp, Work.WilE7.CoreStep.absPtInv_absPtUp]
    simp only [WilkiesDesign.E.projSnd, Fin.append_right]
    simpa [Fin.last] using hlev

end Work.CoreStep
