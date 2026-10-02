import Mathlib
import Submission.Work.RatHurewicz.DCTowerDefs
import Submission.Work.RatHurewicz.towerContraction

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Side faces of the filling of a degenerate cube

For a degeneracy-compatible tower `K : DCTower x₀ N` and a degenerate `(m+1)`-cube
`degenOp j φ`, the `(m+2)`-cube `F := degenOp (Fin.castSucc j) (K.Kf m φ)` is a filling of
`degenOp j φ` whose side faces are exactly the tower fillings of the corresponding faces, as soon
as the tower is available up to level `m` (not `m+1`).
-/

open scoped unitInterval Topology
open Work.Stems.Cubical

namespace Work.RatHurewicz

noncomputable section

variable {X : Type} [TopologicalSpace X]

theorem degenOp_cconst (m : ℕ) (j : Fin (m + 1)) (x : X) :
    degenOp j (cconst m x) = cconst (m + 1) x := by
  ext z
  simp [degenOp, cconst]

/-- A side face of the degenerate extension is the tower filling of the corresponding face of the
degenerate cube (value `0`). -/
theorem dcTower_side_matched_zero {x₀ : X} {N : ℕ} (K : DCTower x₀ N) (m : ℕ) (hm : m ≤ N)
    (j ℓ : Fin (m + 1)) (hjℓ : ℓ ≠ j) (hℓj : j ≠ ℓ) (φ : C(IC m, X)) :
    (degenOp (Fin.castSucc j) (K.Kf m φ)).comp (faceCM (Fin.castSucc ℓ) 0)
      = K.Kf m ((degenOp j φ).comp (faceCM ℓ 0)) := by
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · subst hm0
    exact absurd (Fin.ext (by have := ℓ.isLt; have := j.isLt; omega)) hjℓ
  · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, (Nat.succ_pred_eq_of_pos hmpos).symm⟩
    rw [dcTower_side_face (m := m' + 1) (j := j) (ℓ := ℓ) (ψ := K.Kf (m' + 1) φ)
          (b := 0) hjℓ hℓj]
    rw [show (degenOp j φ).comp (faceCM ℓ 0)
        = degenOp (delIdx ℓ j hℓj) (φ.comp (faceCM (delIdx j ℓ hjℓ) 0)) from by
      rw [degenOp_comp_faceCM (m := m') (i := j) (j := ℓ) (hij := hjℓ) (χ := φ) (b := 0)]]
    rw [(K.hβ m' hm φ (delIdx j ℓ hjℓ)).1]
    rw [← K.hDC m' hm (delIdx ℓ j hℓj) (φ.comp (faceCM (delIdx j ℓ hjℓ) 0))]

/-- A side face of the degenerate extension is the tower filling of the corresponding face of the
degenerate cube (value `1`). -/
theorem dcTower_side_matched_one {x₀ : X} {N : ℕ} (K : DCTower x₀ N) (m : ℕ) (hm : m ≤ N)
    (j ℓ : Fin (m + 1)) (hjℓ : ℓ ≠ j) (hℓj : j ≠ ℓ) (φ : C(IC m, X)) :
    (degenOp (Fin.castSucc j) (K.Kf m φ)).comp (faceCM (Fin.castSucc ℓ) 1)
      = K.Kf m ((degenOp j φ).comp (faceCM ℓ 1)) := by
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · subst hm0
    exact absurd (Fin.ext (by have := ℓ.isLt; have := j.isLt; omega)) hjℓ
  · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, (Nat.succ_pred_eq_of_pos hmpos).symm⟩
    rw [dcTower_side_face (m := m' + 1) (j := j) (ℓ := ℓ) (ψ := K.Kf (m' + 1) φ)
          (b := 1) hjℓ hℓj]
    rw [show (degenOp j φ).comp (faceCM ℓ 1)
        = degenOp (delIdx ℓ j hℓj) (φ.comp (faceCM (delIdx j ℓ hjℓ) 1)) from by
      rw [degenOp_comp_faceCM (m := m') (i := j) (j := ℓ) (hij := hjℓ) (χ := φ) (b := 1)]]
    rw [(K.hβ m' hm φ (delIdx j ℓ hjℓ)).2]
    rw [← K.hDC m' hm (delIdx ℓ j hℓj) (φ.comp (faceCM (delIdx j ℓ hjℓ) 1))]


/-- **The tower contraction identity for a degenerate cube, one level short.** -/
theorem dcTower_cubD_single_short {x₀ : X} {N : ℕ} (K : DCTower x₀ N) (m : ℕ) (hm : m ≤ N)
    (j : Fin (m + 1)) (φ : C(IC m, X)) :
    cubD (m + 1) X (Finsupp.single (degenOp (Fin.castSucc j) (K.Kf m φ)) (1 : ℤ)) =
      (-1 : ℤ) ^ (m + 1) • (Finsupp.single (cconst (m + 1) x₀) (1 : ℤ)
          - Finsupp.single (degenOp j φ) (1 : ℤ))
        + Klin K.toTower m (cubD m X (Finsupp.single (degenOp j φ) (1 : ℤ))) := by
  have htop : faceCube (Fin.last (m + 1)) 1 (degenOp (Fin.castSucc j) (K.Kf m φ)) = degenOp j φ := by
    rw [faceCube, dcTower_last_face (m := m) (j := j) (ψ := K.Kf m φ) (b := 1), (K.hα m hm φ).1]
  have hbot : faceCube (Fin.last (m + 1)) 0 (degenOp (Fin.castSucc j) (K.Kf m φ))
      = cconst (m + 1) x₀ := by
    rw [faceCube, dcTower_last_face (m := m) (j := j) (ψ := K.Kf m φ) (b := 0),
        (K.hα m hm φ).2, degenOp_cconst]
  have hside : ∀ ℓ : Fin (m + 1),
      (Finsupp.single (faceCube (Fin.castSucc ℓ) 0 (degenOp (Fin.castSucc j) (K.Kf m φ))) (1 : ℤ)
        - Finsupp.single (faceCube (Fin.castSucc ℓ) 1 (degenOp (Fin.castSucc j) (K.Kf m φ))) (1 : ℤ))
      = (Klin K.toTower m (Finsupp.single (faceCube ℓ 0 (degenOp j φ)) (1 : ℤ)
          - Finsupp.single (faceCube ℓ 1 (degenOp j φ)) (1 : ℤ))) := by
    intro ℓ
    by_cases hℓ : ℓ = j
    · subst hℓ
      rw [show faceCube (Fin.castSucc ℓ) 0 (degenOp (Fin.castSucc ℓ) (K.Kf m φ)) = K.Kf m φ
            from degenOp_comp_faceCM_self (Fin.castSucc ℓ) (K.Kf m φ) 0,
          show faceCube (Fin.castSucc ℓ) 1 (degenOp (Fin.castSucc ℓ) (K.Kf m φ)) = K.Kf m φ
            from degenOp_comp_faceCM_self (Fin.castSucc ℓ) (K.Kf m φ) 1,
          show faceCube ℓ 0 (degenOp ℓ φ) = φ from degenOp_comp_faceCM_self ℓ φ 0,
          show faceCube ℓ 1 (degenOp ℓ φ) = φ from degenOp_comp_faceCM_self ℓ φ 1]
      simp
    · have hjℓ : j ≠ ℓ := fun h => hℓ h.symm
      rw [show faceCube (Fin.castSucc ℓ) 0 (degenOp (Fin.castSucc j) (K.Kf m φ))
            = K.Kf m (faceCube ℓ 0 (degenOp j φ)) from dcTower_side_matched_zero K m hm j ℓ hℓ hjℓ φ,
          show faceCube (Fin.castSucc ℓ) 1 (degenOp (Fin.castSucc j) (K.Kf m φ))
            = K.Kf m (faceCube ℓ 1 (degenOp j φ)) from dcTower_side_matched_one K m hm j ℓ hℓ hjℓ φ]
      rw [map_sub, Klin_single, Klin_single]
  rw [cubD_single, Fin.sum_univ_castSucc]
  rw [show (Finsupp.single (faceCube (Fin.last (m + 1)) 0 (degenOp (Fin.castSucc j) (K.Kf m φ))) (1 : ℤ)
        - Finsupp.single (faceCube (Fin.last (m + 1)) 1 (degenOp (Fin.castSucc j) (K.Kf m φ))) (1 : ℤ))
      = (Finsupp.single (cconst (m + 1) x₀) (1 : ℤ) - Finsupp.single (degenOp j φ) (1 : ℤ)) from by
    rw [hbot, htop]]
  rw [Finset.sum_congr rfl (fun ℓ _ => by rw [hside ℓ])]
  simp only [Fin.val_castSucc, Fin.val_last]
  rw [cubD_single (s := degenOp j φ), map_sum]
  simp only [map_smul]
  abel

end

end Work.RatHurewicz

