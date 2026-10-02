import Mathlib
import Submission.Work.Serre.E0ConeBdd
import Submission.Work.Serre.ConeFaceFamilyMatching
import Submission.Work.Serre.StepFaceFamilyMatching
import Submission.Work.RatHurewicz.ConnectivityBridge

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 4000000

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Simplicial
open scoped Simplicial Topology unitInterval

namespace Work.Serre

noncomputable section

open Work.RatHurewicz.Bridge

variable {X : Type} [TopologicalSpace X]

/-! ## The induction -/

/-- **The geometric half of `serreE0Range`.**  If `πᵢ(X,x₀)` is trivial for every `i ≤ N` then
the singular simplicial set of `X` carries cone data in degrees `≤ N`. -/
theorem exists_coneData {X : Type} [TopologicalSpace X] (x₀ : X) (N : ℕ)
    (h : ∀ i ≤ N, Subsingleton (HomotopyGroup (Fin i) X x₀)) :
    Nonempty (SSetConeData (singSSet X) N) := by
  revert h
  induction N with
  | zero =>
    intro h
    refine ⟨{ H := junkH (singSSet X), face_cast := ?_, face_last := ?_ }⟩
    · intro m hm
      exact absurd hm (by omega)
    · intro m hm s
      obtain rfl : m = 0 := by omega
      exact delta_comp_sigma_apply (K := singSSet X) (n := 0) (i := (0 : Fin 1)) s
  | succ N ih =>
    intro h
    have hpath : PathConnectedSpace X :=
      Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero x₀ (h 0 (by omega))
    rcases N with _ | k
    · haveI := hpath
      have hπ : ∀ y : X, Subsingleton (HomotopyGroup (Fin 1) X y) :=
        subsingleton_homotopyGroup_of_pathConnected hpath 1 (h 1 (by omega))
      have hlast0 : ∀ (i : Fin 2) (s : Simp X 0), i.val = 1 →
          simFace X 0 i (cone0 x₀ s) = s := by
        intro i s hi
        have hi' : i = (1 : Fin 2) := Fin.ext (by simpa using hi)
        rw [hi']
        apply concretize_injective
        rw [(concretize_face_cone0 x₀ s).2]
        exact ContinuousMap.ext fun z => by
          rw [Subsingleton.elim z pt0]
          rfl
      have hconst0 : ∀ (a b : Fin 2) (s t : Simp X 0), a.val = 0 → b.val = 0 →
          simFace X 0 a (cone0 x₀ s) = simFace X 0 b (cone0 x₀ t) := by
        intro a b s t ha hb
        have ha' : a = (0 : Fin 2) := Fin.ext (by simpa using ha)
        have hb' : b = (0 : Fin 2) := Fin.ext (by simpa using hb)
        apply concretize_injective
        rw [ha', hb', (concretize_face_cone0 x₀ s).1, (concretize_face_cone0 x₀ t).1]
      exact e0ConeDataBdd_one hpath hπ (cone0 x₀) hlast0 hconst0
        (fun s i j hij => ConeFaceFamilyMatching (cone0 x₀) hlast0 hconst0 s i j hij)
    · obtain ⟨D⟩ := ih (fun i hi => h i (by omega))
      have hπ : ∀ y : X, Subsingleton (HomotopyGroup (Fin (k+2)) X y) :=
        subsingleton_homotopyGroup_of_pathConnected hpath (k+2) (h (k+2) (by omega))
      exact e0ConeDataStep k hpath hπ D (fun s i j hij => stepFaceFamily_matching k D s i j hij)

/-- The geometric half of `serreE0Range`, in the shape of `Work.Serre.HasSimplexCones`. -/
theorem hasSimplexCones_of_homotopyGroup_subsingleton {X : Type} [TopologicalSpace X]
    (x₀ : X) (N : ℕ)
    (h : ∀ i ≤ N, Subsingleton (HomotopyGroup (Fin i) X x₀)) :
    HasSimplexCones X N :=
  exists_coneData x₀ N h

end

end Work.Serre
