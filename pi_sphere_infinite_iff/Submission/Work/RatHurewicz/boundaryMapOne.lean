import Mathlib
import Submission.Work.RatHurewicz.FillFamilyDefs
import Submission.Work.RatHurewicz.cubeBoundaryGlue
import Submission.Work.RatHurewicz.pieceAgree

/-!
# The boundary data of the first filling `K 1`

`Work.RatHurewicz.boundaryMapOne`: the four faces of the boundary of `I²` — top `p`, bottom
`x₀` and the two side faces `K 0 (p ∘ face_j b)` — glue to a continuous map on `∂I²`.  They agree
at the four corners by the face conditions `hα` of the level-`0` operator `K0`.
-/

open scoped unitInterval Topology
open Work.Stems.Cubical

namespace Work.RatHurewicz

noncomputable section

theorem boundaryMapOne {X : Type} [TopologicalSpace X] (x₀ : X)
    (K0 : C(IC 0, X) → C(IC 1, X)) (p : C(IC 1, X))
    (hα : ∀ q : C(IC 0, X),
      (K0 q).comp (faceCM (Fin.last 0) 1) = q ∧
      (K0 q).comp (faceCM (Fin.last 0) 0) = cconst 0 x₀) :
    ∃ B : C(↥(Cube.boundary (Fin 2)), X),
      B.comp (bface 1 (Fin.last 1) 1) = p ∧
      B.comp (bface 1 (Fin.last 1) 0) = cconst 1 x₀ ∧
      (∀ (j : Fin 1) (b : Fin 2),
        B.comp (bface 1 (Fin.castSucc j) b) =
          K0 (p.comp (faceCM j (cval b)))) := by
  classical
  have hcover : ∀ z : IC 2, z ∈ Cube.boundary (Fin 2) → ∃ q : Fin 2 × Fin 2, z q.1 = cval q.2 := by
    intro z hz
    obtain ⟨i, hi⟩ := hz
    rcases hi with h | h
    · exact ⟨(i, 0), by show z i = cval 0; rw [h]; rfl⟩
    · exact ⟨(i, 1), by show z i = cval 1; rw [h]; rfl⟩
  have hEclosed : ∀ q : Fin 2 × Fin 2, IsClosed {z : IC 2 | z q.1 = cval q.2} := fun q =>
    isClosed_eq (continuous_apply q.1) continuous_const
  have hf : ∀ q : Fin 2 × Fin 2,
      ContinuousOn (pieceVal (ℓ := 0) x₀ K0 p q.1 q.2) {z : IC 2 | z q.1 = cval q.2} := by
    rintro ⟨i, b⟩
    by_cases hi : i = Fin.last 1
    · rw [show pieceVal (ℓ := 0) x₀ K0 p i b
          = (if b = 1 then (fun z : IC 2 => p (initC 1 z)) else fun _ => x₀) from by
        funext z; rw [hi, pieceVal_last (ℓ := 0)]
        by_cases hb : b = 1
        · rw [if_pos hb, if_pos hb]
        · rw [if_neg hb, if_neg hb]]
      by_cases hb : b = 1
      · rw [if_pos hb]
        exact (p.continuous.comp (initCM 1).continuous).continuousOn
      · rw [if_neg hb]; exact continuous_const.continuousOn
    · rw [show pieceVal (ℓ := 0) x₀ K0 p i b
          = fun z : IC 2 => (K0 (p.comp (faceCM (i.castPred hi) (cval b)))) (delG 1 i z) from by
        funext z; rw [pieceVal_side x₀ K0 p hi]]
      exact ((K0 (p.comp (faceCM (i.castPred hi) (cval b)))).continuous.comp
        (delG 1 i).continuous).continuousOn
  have hagree : ∀ q q' : Fin 2 × Fin 2, ∀ z : IC 2, z q.1 = cval q.2 → z q'.1 = cval q'.2 →
      pieceVal (ℓ := 0) x₀ K0 p q.1 q.2 z = pieceVal (ℓ := 0) x₀ K0 p q'.1 q'.2 z := by
    rintro ⟨i, b⟩ ⟨i', b'⟩ z hz hz'
    by_cases hii : i = i'
    · subst hii
      have hbb : b = b' := by
        have h : cval b = cval b' := by rw [← hz, ← hz']
        fin_cases b <;> fin_cases b' <;> simp_all [cval]
      subst hbb
      rfl
    · have htop : i = Fin.last 1 ∨ i' = Fin.last 1 := by
        fin_cases i <;> fin_cases i' <;> simp_all [Fin.last]
      rcases htop with h | h
      · subst h
        exact (pieceVal_agree_last x₀ K0 p hα z i' b' b hz hz').symm
      · subst h
        exact pieceVal_agree_last x₀ K0 p hα z i b b' hz' hz
  obtain ⟨B, hB⟩ := exists_cubeBoundary 1 (fun q : Fin 2 × Fin 2 => {z : IC 2 | z q.1 = cval q.2})
    hEclosed hcover (fun q => pieceVal (ℓ := 0) x₀ K0 p q.1 q.2) hf hagree
  have hval : ∀ (q : Fin 2 × Fin 2) (u : IC 1),
      B (bface 1 q.1 q.2 u) = pieceVal (ℓ := 0) x₀ K0 p q.1 q.2 (faceCM q.1 (cval q.2) u) := by
    intro q u
    exact hB (bface 1 q.1 q.2 u) q (by
      show ((bface 1 q.1 q.2 u : ↥(Cube.boundary (Fin 2))) : IC 2) q.1 = cval q.2
      rw [bface_apply, faceCM_eq_insertNth, Fin.insertNth_apply_same])
  refine ⟨B, ?_, ?_, ?_⟩
  · ext u
    rw [ContinuousMap.comp_apply, hval (Fin.last 1, 1) u, pieceVal_last]
    rw [if_pos rfl]
    show p (initC 1 (faceCM (Fin.last 1) (cval 1) u)) = p u
    rw [initC_faceCM_last]
  · ext u
    rw [ContinuousMap.comp_apply, hval (Fin.last 1, 0) u, pieceVal_last]
    rw [if_neg (by decide : ¬ ((0 : Fin 2) = 1))]
    rfl
  · intro j b
    ext u
    rw [ContinuousMap.comp_apply]
    have hj : j = ⟨0, by omega⟩ := by fin_cases j; rfl
    subst hj
    have hi : (Fin.castSucc (⟨0, by omega⟩ : Fin 1) : Fin 2) ≠ Fin.last 1 := by decide
    have hcast : ((Fin.castSucc (⟨0, by omega⟩ : Fin 1) : Fin 2)).castPred hi = ⟨0, by omega⟩ :=
      Fin.castPred_castSucc (i := (⟨0, by omega⟩ : Fin 1)) (by decide)
    have h1 := hval (Fin.castSucc (⟨0, by omega⟩ : Fin 1), b) u
    simp only [Prod.fst, Prod.snd] at h1
    rw [h1, pieceVal_side x₀ K0 p hi b
        (faceCM (Fin.castSucc (⟨0, by omega⟩ : Fin 1)) (cval b) u), hcast,
      faceCM_delG (n := 1) (Fin.castSucc (⟨0, by omega⟩ : Fin 1)) (cval b) u]

end

end Work.RatHurewicz
