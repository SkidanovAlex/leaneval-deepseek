import Mathlib
import Submission.Work.RatHurewicz.FillFamilyDefs
import Submission.Work.RatHurewicz.cubeBoundaryGlue
import Submission.Work.RatHurewicz.pieceAgree

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The boundary data of the filling `K (k+2) p`

`Work.RatHurewicz.boundaryMap`: the boundary data of the filling at level `k+2` — the faces
`p`, `x₀` and `K (k+1) (p ∘ face_j b)` — glue to a continuous map on `∂I^{k+3}`.

The only mathematical content is the *consistency* of the prescribed data: the faces must agree on
the codimension two skeleton.  On the top and bottom faces this is
`pieceVal_agree_last` (one application of `hα`).  On a pair of side faces the two prescribed values
expand, by `hβ`, to values of `K k` at a common cube and a common point; that the cubes agree is
`faceCM_comp_eq_gen` and that the points agree is `delCM_comp_eq` (both in `faceComm`).
-/

open scoped unitInterval Topology
open Work.Stems.Cubical

namespace Work.RatHurewicz

noncomputable section

theorem pieceVal_agree_side {k : ℕ} {X : Type} [TopologicalSpace X] (x₀ : X)
    (Kp : C(IC (k + 1), X) → C(IC (k + 2), X)) (Kpp : C(IC k, X) → C(IC (k + 1), X))
    (p : C(IC (k + 2), X))
    (hβ : ∀ (q : C(IC (k + 1), X)) (j : Fin (k + 1)) (b : Fin 2),
      (Kp q).comp (faceCM (Fin.castSucc j) (cval b)) = Kpp (q.comp (faceCM j (cval b))))
    (z : IC (k + 3)) (j j' : Fin (k + 2)) (b b' : Fin 2) (hjj : j ≠ j')
    (hz : z (Fin.castSucc j) = cval b) (hz' : z (Fin.castSucc j') = cval b') :
    pieceVal (ℓ := k + 1) x₀ Kp p (Fin.castSucc j) b z
      = pieceVal (ℓ := k + 1) x₀ Kp p (Fin.castSucc j') b' z := by
  have hjne : (Fin.castSucc j : Fin (k + 3)) ≠ Fin.last (k + 2) := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_castSucc, Fin.val_last] at this
    omega
  have hj'ne : (Fin.castSucc j' : Fin (k + 3)) ≠ Fin.last (k + 2) := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_castSucc, Fin.val_last] at this
    omega
  rw [pieceVal_side x₀ Kp p hjne b z, pieceVal_side x₀ Kp p hj'ne b' z,
    Fin.castPred_castSucc (i := j) hjne, Fin.castPred_castSucc (i := j') hj'ne,
    delG_eq_delCM j z, delG_eq_delCM j' z]
  -- the two "other" coordinates in the deleted worlds
  have hne : (Fin.castSucc j' : Fin (k + 3)) ≠ Fin.castSucc j := fun h =>
    hjj (Fin.castSucc_injective (k + 2) h).symm
  have hne₂ : (Fin.castSucc j : Fin (k + 3)) ≠ Fin.castSucc j' := fun h => hne h.symm
  set κ : Fin (k + 2) := predG (Fin.castSucc j) (Fin.castSucc j') hne with hκdef
  set κ₂ : Fin (k + 2) := predG (Fin.castSucc j') (Fin.castSucc j) hne₂ with hκ₂def
  have hκ : (Fin.castSucc j).succAbove κ = Fin.castSucc j' := succAbove_predG _ _ hne
  have hκ₂ : (Fin.castSucc j').succAbove κ₂ = Fin.castSucc j := succAbove_predG _ _ hne₂
  have hκne : κ ≠ Fin.last (k + 1) := by
    intro h
    have h2 : (Fin.castSucc j' : Fin (k + 3)) = Fin.last (k + 2) := by
      rw [← hκ, h, succAbove_last_eq (k + 1) j]
    have := congrArg Fin.val h2
    simp only [Fin.val_castSucc, Fin.val_last] at this
    omega
  have hκ₂ne : κ₂ ≠ Fin.last (k + 1) := by
    intro h
    have h2 : (Fin.castSucc j : Fin (k + 3)) = Fin.last (k + 2) := by
      rw [← hκ₂, h, succAbove_last_eq (k + 1) j']
    have := congrArg Fin.val h2
    simp only [Fin.val_castSucc, Fin.val_last] at this
    omega
  set κ'' : Fin (k + 1) := κ.castPred hκne with hκ''def
  set κ₂'' : Fin (k + 1) := κ₂.castPred hκ₂ne with hκ₂''def
  have hκ'' : (κ''.castSucc : Fin (k + 2)) = κ := Fin.castSucc_castPred κ hκne
  have hκ₂'' : (κ₂''.castSucc : Fin (k + 2)) = κ₂ := Fin.castSucc_castPred κ₂ hκ₂ne
  -- the expansions
  have hu : (delCM (k + 2) j z) (Fin.castSucc κ'') = cval b' := by
    rw [delCM_apply, hκ'', hκ, hz']
  have hu₂ : (delCM (k + 2) j' z) (Fin.castSucc κ₂'') = cval b := by
    rw [delCM_apply, hκ₂'', hκ₂, hz]
  rw [← faceCM_delCM_of_apply (k + 1) κ'' (delCM (k + 2) j z) hu,
    ← faceCM_delCM_of_apply (k + 1) κ₂'' (delCM (k + 2) j' z) hu₂]
  rw [show (Kp (p.comp (faceCM j (cval b))))
        (faceCM (Fin.castSucc κ'') (cval b')
          (delCM (k + 1) κ'' (delCM (k + 2) j z)))
      = ((Kp (p.comp (faceCM j (cval b)))).comp (faceCM (Fin.castSucc κ'') (cval b')))
          (delCM (k + 1) κ'' (delCM (k + 2) j z)) from rfl]
  rw [show (Kp (p.comp (faceCM j' (cval b'))))
        (faceCM (Fin.castSucc κ₂'') (cval b)
          (delCM (k + 1) κ₂'' (delCM (k + 2) j' z)))
      = ((Kp (p.comp (faceCM j' (cval b')))).comp (faceCM (Fin.castSucc κ₂'') (cval b)))
          (delCM (k + 1) κ₂'' (delCM (k + 2) j' z)) from rfl]
  rw [hβ (p.comp (faceCM j (cval b))) κ'' b', hβ (p.comp (faceCM j' (cval b'))) κ₂'' b]
  -- the two arguments agree
  have hcube : κ'' = predG j j' hjj.symm := by
    have h1 : j.succAbove κ'' = j' := by
      apply Fin.castSucc_injective
      rw [succAbove_castSucc_eq, hκ'', hκ]
    have h3 := succAbove_predG j j' hjj.symm
    exact Fin.succAbove_right_injective (by rw [h1, h3])
  have hcube₂ : κ₂'' = predG j' j hjj := by
    have h1 : j'.succAbove κ₂'' = j := by
      apply Fin.castSucc_injective
      rw [succAbove_castSucc_eq, hκ₂'', hκ₂]
    have h3 := succAbove_predG j' j hjj
    exact Fin.succAbove_right_injective (by rw [h1, h3])
  have hins : (faceCM j (cval b)).comp (faceCM (predG j j' hjj.symm) (cval b'))
      = (faceCM j' (cval b')).comp (faceCM (predG j' j hjj) (cval b)) :=
    faceCM_comp_eq_gen (n := k) j j' hjj (cval b) (cval b')
  have hcubes : (p.comp (faceCM j (cval b))).comp (faceCM κ'' (cval b'))
      = (p.comp (faceCM j' (cval b'))).comp (faceCM κ₂'' (cval b)) := by
    rw [hcube, hcube₂, ContinuousMap.comp_assoc, ContinuousMap.comp_assoc, ← hins]
  have hpt : delCM (k + 1) κ'' (delCM (k + 2) j z)
      = delCM (k + 1) κ₂'' (delCM (k + 2) j' z) := by
    have h := congrFun (congrArg DFunLike.coe (delCM_comp_eq (n := k + 1) j j' hjj hκ hκ₂
      hκ'' hκ₂'')) z
    simpa only [ContinuousMap.comp_apply] using h
  rw [hcubes, hpt]


theorem boundaryMap {k : ℕ} {X : Type} [TopologicalSpace X] (x₀ : X)
    (Kp : C(IC (k + 1), X) → C(IC (k + 2), X)) (Kpp : C(IC k, X) → C(IC (k + 1), X))
    (p : C(IC (k + 2), X))
    (hα : ∀ q : C(IC (k + 1), X),
      (Kp q).comp (faceCM (Fin.last (k + 1)) 1) = q ∧
      (Kp q).comp (faceCM (Fin.last (k + 1)) 0) = cconst (k + 1) x₀)
    (hβ : ∀ (q : C(IC (k + 1), X)) (j : Fin (k + 1)) (b : Fin 2),
      (Kp q).comp (faceCM (Fin.castSucc j) (cval b)) = Kpp (q.comp (faceCM j (cval b)))) :
    ∃ B : C(↥(Cube.boundary (Fin (k + 3))), X),
      B.comp (bface (k + 2) (Fin.last (k + 2)) 1) = p ∧
      B.comp (bface (k + 2) (Fin.last (k + 2)) 0) = cconst (k + 2) x₀ ∧
      (∀ (j : Fin (k + 2)) (b : Fin 2),
        B.comp (bface (k + 2) (Fin.castSucc j) b) =
          Kp (p.comp (faceCM j (cval b)))) := by
  classical
  have hcover : ∀ z : IC (k + 3), z ∈ Cube.boundary (Fin (k + 3)) →
      ∃ q : Fin (k + 3) × Fin 2, z q.1 = cval q.2 := by
    intro z hz
    obtain ⟨i, hi⟩ := hz
    rcases hi with h | h
    · exact ⟨(i, 0), by show z i = cval 0; rw [h]; rfl⟩
    · exact ⟨(i, 1), by show z i = cval 1; rw [h]; rfl⟩
  have hEclosed : ∀ q : Fin (k + 3) × Fin 2, IsClosed {z : IC (k + 3) | z q.1 = cval q.2} :=
    fun q => isClosed_eq (continuous_apply q.1) continuous_const
  have hf : ∀ q : Fin (k + 3) × Fin 2,
      ContinuousOn (pieceVal (ℓ := k + 1) x₀ Kp p q.1 q.2) {z : IC (k + 3) | z q.1 = cval q.2} := by
    rintro ⟨i, b⟩
    by_cases hi : i = Fin.last (k + 2)
    · rw [show pieceVal (ℓ := k + 1) x₀ Kp p i b
          = (if b = 1 then (fun z : IC (k + 3) => p (initC (k + 2) z)) else fun _ => x₀) from by
        funext z; rw [hi, pieceVal_last (ℓ := k + 1)]
        by_cases hb : b = 1
        · rw [if_pos hb, if_pos hb]
        · rw [if_neg hb, if_neg hb]]
      by_cases hb : b = 1
      · rw [if_pos hb]
        exact (p.continuous.comp (initCM (k + 2)).continuous).continuousOn
      · rw [if_neg hb]; exact continuous_const.continuousOn
    · rw [show pieceVal (ℓ := k + 1) x₀ Kp p i b
          = fun z : IC (k + 3) =>
              (Kp (p.comp (faceCM (i.castPred hi) (cval b)))) (delG (k + 2) i z) from by
        funext z; rw [pieceVal_side x₀ Kp p hi]]
      exact ((Kp (p.comp (faceCM (i.castPred hi) (cval b)))).continuous.comp
        (delG (k + 2) i).continuous).continuousOn
  have hagree : ∀ q q' : Fin (k + 3) × Fin 2, ∀ z : IC (k + 3), z q.1 = cval q.2 →
      z q'.1 = cval q'.2 →
      pieceVal (ℓ := k + 1) x₀ Kp p q.1 q.2 z = pieceVal (ℓ := k + 1) x₀ Kp p q'.1 q'.2 z := by
    rintro ⟨i, b⟩ ⟨i', b'⟩ z hz hz'
    by_cases hii : i = i'
    · subst hii
      have hbb : b = b' := by
        have h : cval b = cval b' := by rw [← hz, ← hz']
        fin_cases b <;> fin_cases b' <;> simp_all [cval]
      subst hbb
      rfl
    · by_cases hi : i = Fin.last (k + 2)
      · subst hi
        exact (pieceVal_agree_last (ℓ := k + 1) x₀ Kp p hα z i' b' b hz hz').symm
      · by_cases hi' : i' = Fin.last (k + 2)
        · subst hi'
          exact pieceVal_agree_last (ℓ := k + 1) x₀ Kp p hα z i b b' hz' hz
        · obtain ⟨j, rfl⟩ | h := Fin.eq_castSucc_or_eq_last i
          · obtain ⟨j', rfl⟩ | h' := Fin.eq_castSucc_or_eq_last i'
            · exact pieceVal_agree_side x₀ Kp Kpp p hβ z j j' b b'
                (fun hjj => hii (by rw [hjj])) hz hz'
            · exact absurd h' hi'
          · exact absurd h hi
  obtain ⟨B, hB⟩ := exists_cubeBoundary (k + 2)
    (fun q : Fin (k + 3) × Fin 2 => {z : IC (k + 3) | z q.1 = cval q.2}) hEclosed hcover
    (fun q => pieceVal (ℓ := k + 1) x₀ Kp p q.1 q.2) hf hagree
  have hval : ∀ (q : Fin (k + 3) × Fin 2) (u : IC (k + 2)),
      B (bface (k + 2) q.1 q.2 u)
        = pieceVal (ℓ := k + 1) x₀ Kp p q.1 q.2 (faceCM q.1 (cval q.2) u) := by
    intro q u
    exact hB (bface (k + 2) q.1 q.2 u) q (by
      show ((bface (k + 2) q.1 q.2 u : ↥(Cube.boundary (Fin (k + 3)))) : IC (k + 3)) q.1
        = cval q.2
      rw [bface_apply, faceCM_eq_insertNth, Fin.insertNth_apply_same])
  refine ⟨B, ?_, ?_, ?_⟩
  · ext u
    rw [ContinuousMap.comp_apply, hval (Fin.last (k + 2), 1) u, pieceVal_last]
    rw [if_pos rfl]
    show p (initC (k + 2) (faceCM (Fin.last (k + 2)) (cval 1) u)) = p u
    rw [initC_faceCM_last]
  · ext u
    rw [ContinuousMap.comp_apply, hval (Fin.last (k + 2), 0) u, pieceVal_last]
    rw [if_neg (by decide : ¬ ((0 : Fin 2) = 1))]
    rfl
  · intro j b
    ext u
    rw [ContinuousMap.comp_apply]
    have hi : (Fin.castSucc j : Fin (k + 3)) ≠ Fin.last (k + 2) := by
      intro h
      have := congrArg Fin.val h
      simp only [Fin.val_castSucc, Fin.val_last] at this
      omega
    have hcast : ((Fin.castSucc j : Fin (k + 3))).castPred hi = j :=
      Fin.castPred_castSucc (i := j) hi
    have h1 := hval (Fin.castSucc j, b) u
    simp only [Prod.snd] at h1
    rw [h1, pieceVal_side x₀ Kp p hi b (faceCM (Fin.castSucc j) (cval b) u), hcast,
      faceCM_delG (n := k + 2) (Fin.castSucc j : Fin (k + 3)) (cval b) u]

end

end Work.RatHurewicz
