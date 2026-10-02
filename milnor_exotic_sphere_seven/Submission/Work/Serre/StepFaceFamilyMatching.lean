import Mathlib
import Submission.Work.Serre.E0ConeBdd

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Simplicial
open scoped Simplicial Topology unitInterval

namespace Work.Serre

noncomputable section

open Work.RatHurewicz.Bridge

/-- **The matching condition of `exists_simplexFiller` for the degree-`(k+2)` cone faces.** -/
theorem stepFaceFamily_matching {X : Type} [TopologicalSpace X] (k : ℕ)
    (D : SSetConeData (singSSet X) (k+1)) (s : Simp X (k+2)) (i j : Fin (k+4))
    (hij : i < j) :
    (stepFaceFamily k D s j).comp (coface (k+1) ⟨i.val, fin_lt_of_lt i j hij⟩) =
      (stepFaceFamily k D s i).comp (coface (k+1) ⟨j.val - 1, fin_pred_lt j⟩) := by
  obtain ⟨i', rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last i
  · obtain ⟨j', rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last j
    · -- both indices are `castSucc`s
      rw [stepFaceFamily_castSucc, stepFaceFamily_castSucc, ← concretize_face,
        ← concretize_face]
      simp only [Fin.val_castSucc]
      have hlt : i'.val < j'.val := hij
      have hi : i'.val < k + 2 := by have := j'.isLt; omega
      have hj : j'.val - 1 < k + 2 := by have := j'.isLt; omega
      have hfc1 : SimplicialObject.δ (singSSet X) (⟨i'.val, fin_lt_self i'⟩ : Fin (k+3))
          (D.H (k+1) (simFace X (k+1) j' s))
          = D.H k (SimplicialObject.δ (singSSet X) (⟨i'.val, hi⟩ : Fin (k+2))
            (simFace X (k+1) j' s)) := by
        have h := D.face_cast k (by omega) (simFace X (k+1) j' s) (⟨i'.val, hi⟩ : Fin (k+2))
        simpa only [Fin.castSucc, Fin.castAdd, Fin.castLE] using h
      have hfc2 : SimplicialObject.δ (singSSet X) (⟨j'.val - 1, fin3_lt_of_pred j'⟩ : Fin (k+3))
          (D.H (k+1) (simFace X (k+1) i' s))
          = D.H k (SimplicialObject.δ (singSSet X) (⟨j'.val - 1, hj⟩ : Fin (k+2))
            (simFace X (k+1) i' s)) := by
        have h := D.face_cast k (by omega) (simFace X (k+1) i' s) (⟨j'.val - 1, hj⟩ : Fin (k+2))
        simpa only [Fin.castSucc, Fin.castAdd, Fin.castLE] using h
      rw [hfc1, hfc2]
      exact congrArg (fun w => concretize (D.H k w))
        (delta_comp_delta_apply s (⟨i'.val, hi⟩ : Fin (k+2)) j' hlt)
    · -- `i = i'.castSucc`, `j = Fin.last`
      rw [stepFaceFamily_castSucc, stepFaceFamily_last, ← concretize_face, ← concretize_face]
      simp only [Fin.val_castSucc, Fin.val_last]
      have hfl := D.face_last (k+1) (by omega) (simFace X (k+1) i' s)
      simp only [Fin.last] at hfl
      exact congrArg concretize hfl.symm
  · -- `i = Fin.last` is impossible
    have h : (Fin.last (k+3) : Fin (k+4)).val < j.val := hij
    rw [Fin.val_last] at h
    have := j.isLt
    omega

end

end Work.Serre
