import Mathlib
import Submission.Work.RatHurewicz.FillFamilyDefs
import Submission.Work.RatHurewicz.faceComm

/-!
# Consistency of the prescribed boundary data on the top and bottom faces

`Work.RatHurewicz.pieceVal_agree_last`: the value `K ℓ (p ∘ face_i b)` prescribed on a side face
`{z i = cval b}` of `∂I^{ℓ+2}` agrees, at a point `z` lying on the top or bottom face
(`z (last (ℓ+1)) ∈ {0,1}`), with the value prescribed there (`p` resp. `x₀`).  The proof is one
application of the face conditions `hα` of `K ℓ`, together with the "space part" identity
`faceCM j b (initC ℓ (delCM (ℓ+1) j z)) = initC (ℓ+1) z`.
-/

open scoped unitInterval Topology
open Work.Stems.Cubical

namespace Work.RatHurewicz

noncomputable section

theorem succAbove_last_eq (ℓ : ℕ) (j : Fin (ℓ + 1)) :
    (Fin.castSucc j).succAbove (Fin.last ℓ) = Fin.last (ℓ + 1) := by
  apply Fin.ext
  show (((Fin.castSucc j).succAbove (Fin.last ℓ) : Fin (ℓ + 2)) : ℕ) = ℓ + 1
  rw [val_succAbove, Fin.val_castSucc]
  have hj : (j : ℕ) ≤ ℓ := Nat.lt_succ_iff.mp j.isLt
  have hl : ((Fin.last ℓ : Fin (ℓ + 1)) : ℕ) = ℓ := rfl
  rw [hl]
  split_ifs <;> omega

/-- The "space part" of a point on a side face is obtained by inserting the frozen value into the
space part of the deleted point. -/
theorem faceCM_initC_delCM {ℓ : ℕ} (j : Fin (ℓ + 1)) {b : unitInterval} (z : IC (ℓ + 2))
    (hz : z (Fin.castSucc j) = b) :
    faceCM j b (initC ℓ (delCM (ℓ + 1) j z)) = initC (ℓ + 1) z := by
  funext k
  by_cases hk : k = j
  · subst hk
    rw [faceCM_eq_insertNth, Fin.insertNth_apply_same, initC_apply]
    exact hz.symm
  · have hk' : k ≠ j := hk
    have hk'' : k = j.succAbove (predG j k hk') := (succAbove_predG j k hk').symm
    rw [faceCM_eq_insertNth, hk'', Fin.insertNth_apply_succAbove, initC_apply, delCM_apply,
      ← succAbove_castSucc_eq j (predG j k hk'), ← hk'', initC_apply]

theorem pieceVal_agree_last {ℓ : ℕ} {X : Type} [TopologicalSpace X] (x₀ : X)
    (Kp : C(IC ℓ, X) → C(IC (ℓ + 1), X)) (p : C(IC (ℓ + 1), X))
    (hα : ∀ q : C(IC ℓ, X),
      (Kp q).comp (faceCM (Fin.last ℓ) 1) = q ∧
      (Kp q).comp (faceCM (Fin.last ℓ) 0) = cconst ℓ x₀)
    (z : IC (ℓ + 2)) (i : Fin (ℓ + 2)) (b b' : Fin 2)
    (hz : z (Fin.last (ℓ + 1)) = cval b') (hz' : z i = cval b) :
    pieceVal x₀ Kp p i b z = pieceVal x₀ Kp p (Fin.last (ℓ + 1)) b' z := by
  by_cases hi : i = Fin.last (ℓ + 1)
  · subst hi
    have hbb : b = b' := by
      have h : cval b = cval b' := by rw [← hz', hz]
      fin_cases b <;> fin_cases b' <;> simp_all [cval]
    subst hbb
    rfl
  · rw [pieceVal_side x₀ Kp p hi b z, pieceVal_last]
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · rw [delG_eq_delCM j z]
      have hlast : (delCM (ℓ + 1) j z) (Fin.last ℓ) = z (Fin.last (ℓ + 1)) := by
        rw [delCM_apply, succAbove_last_eq]
      by_cases hb : b' = 1
      · rw [if_pos hb]
        have hcoord : (delCM (ℓ + 1) j z) (Fin.last ℓ) = 1 := by
          rw [hlast, hz, hb]; rfl
        rw [show (Fin.castSucc j).castPred hi = j from Fin.castPred_castSucc (i := j) hi]
        rw [← faceCM_last_apply ℓ (delCM (ℓ + 1) j z) hcoord]
        have hq := (hα (p.comp (faceCM j (cval b)))).1
        have h2 := congrFun (congrArg DFunLike.coe hq) (initC ℓ (delCM (ℓ + 1) j z))
        simp only [ContinuousMap.comp_apply] at h2
        rw [h2]
        congr 1
        exact faceCM_initC_delCM j z hz' 
      · rw [if_neg hb]
        have hcoord : (delCM (ℓ + 1) j z) (Fin.last ℓ) = 0 := by
          have hb0 : b' = 0 := by fin_cases b' <;> simp_all
          rw [hlast, hz, hb0]; rfl
        rw [show (Fin.castSucc j).castPred hi = j from Fin.castPred_castSucc (i := j) hi]
        rw [← faceCM_last_apply ℓ (delCM (ℓ + 1) j z) hcoord]
        have hq := (hα (p.comp (faceCM j (cval b)))).2
        have h2 := congrFun (congrArg DFunLike.coe hq) (initC ℓ (delCM (ℓ + 1) j z))
        simp only [ContinuousMap.comp_apply, cconst, ContinuousMap.const_apply] at h2
        rw [h2]
    · exact absurd rfl hi

end

end Work.RatHurewicz
