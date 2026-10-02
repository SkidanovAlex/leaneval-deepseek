import Mathlib
import Submission.Work.Stems.Hur2c.PsiLinGen
import Submission.Work.Stems.Hur2c.PsiLinGenCubD
import Submission.Work.RatHurewicz.fillingFamilyConst
import Submission.Work.RatHurewicz.CubicalDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# `ΨLin` kills the constant cube

A sub-case of the crux `Work.RatHurewicz.DegenCycleKilled`: the constant `(m+2)`-cube at any point
`v` is a degenerate cycle (it lies in `Deg`, and all its faces cancel pairwise in `cubD`), so the
crux predicts `ΨLin (single (cconst (m+2) v) 1) = 0`.

The proof is Hutchings `(2.5)` applied to the `(m+3)`-cube
`τ z := γ (z (last (m+2)))` with `γ := K.Kf 0 (const 0 v)` a path from `x₀` to `v` (which the
tower provides at level `0`): the faces of `τ` in the last direction are the constant cubes
`cconst (m+2) (γ b)`, and in every other direction the *same* cube `u ↦ γ (u (last (m+1)))`, so
those cancel in pairs (`(-1)^i · (-1)^{i+1} = -1`).
-/

open scoped unitInterval Topology
open Work.Stems.Cubical

namespace Work.RatHurewicz

noncomputable section

variable {X : Type} [TopologicalSpace X]

/-- The `(m+3)`-cube `z ↦ γ (z (last (m+2)))`, which only uses its last coordinate. -/
def constTube (m : ℕ) (γ : C(IC 1, X)) : C(IC (m + 3), X) where
  toFun z := γ (fun _ => z (Fin.last (m + 2)))
  continuous_toFun := by fun_prop

@[simp] theorem constTube_apply (m : ℕ) (γ : C(IC 1, X)) (z : IC (m + 3)) :
    constTube m γ z = γ (fun _ => z (Fin.last (m + 2))) := rfl

/-- The coordinate `last (m+2)` of `faceCM (castSucc i) b u` is `u (last (m+1))`. -/
theorem faceCM_castSucc_last_apply (m : ℕ) (i : Fin (m + 2)) (b : unitInterval)
    (u : IC (m + 2)) :
    faceCM (Fin.castSucc i) b u (Fin.last (m + 2)) = u (Fin.last (m + 1)) := by
  rw [faceCM_eq_insertNth]
  have h : (Fin.castSucc i).succAbove (Fin.last (m + 1)) = Fin.last (m + 2) := by
    rw [Fin.succAbove, if_neg]
    · exact Fin.ext (by simp)
    · simp only [Fin.lt_def, Fin.val_last, Fin.val_castSucc]
      omega
  rw [← h, Fin.insertNth_apply_succAbove]

theorem constTube_face_last (m : ℕ) (γ : C(IC 1, X)) (b : Fin 2) :
    (constTube m γ).comp (faceCM (Fin.last (m + 2)) (cval b))
      = cconst (m + 2) (γ (fun _ => cval b)) := by
  ext u
  simp only [ContinuousMap.comp_apply, constTube_apply, cconst, ContinuousMap.const_apply]
  apply congrArg γ
  funext k
  rw [faceCM_eq_insertNth, Fin.insertNth_apply_same]

theorem constTube_face_other (m : ℕ) (γ : C(IC 1, X)) (i : Fin (m + 2)) (b : Fin 2) :
    (constTube m γ).comp (faceCM (Fin.castSucc i) (cval b))
      = (⟨fun u => γ (fun _ => u (Fin.last (m + 1))), by fun_prop⟩ : C(IC (m + 2), X)) := by
  ext u
  simp only [ContinuousMap.comp_apply, constTube_apply]
  apply congrArg γ
  funext k
  exact faceCM_castSucc_last_apply m i (cval b) u

/-- **`ΨLin` kills the constant cube.** -/
theorem psiLinGen_single_cconst (N m : ℕ) [Nontrivial (Fin (m + 2))] {x₀ : X}
    (K : Tower x₀ N) (hN : m + 1 ≤ N) (v : X) :
    Work.Stems.Hur2c.psiLinGen N m K hN (Finsupp.single (cconst (m + 2) v) (1 : ℤ)) = 0 := by
  letI : CommGroup (Quotient (GenLoop.Homotopic.setoid (Fin (m + 2)) x₀)) :=
    HomotopyGroup.commGroup
  -- the path from `x₀` to `v`, from the tower at level `0`
  set γ : C(IC 1, X) := K.Kf 0 (cconst 0 v) with hγ
  have h0N : 0 ≤ N := by omega
  have harg (b : unitInterval) :
      faceCM (Fin.last 0) b (fun e : Fin 0 => e.elim0) = (fun _ => b) := by
    funext k
    rw [show k = (Fin.last 0) from Fin.ext (by omega), faceCM_eq_insertNth,
      Fin.insertNth_apply_same]
  have hγ1 : γ (fun _ => (1 : unitInterval)) = v := by
    have h := (K.hα 0 h0N (cconst 0 v)).1
    have h' := congrFun (congrArg DFunLike.coe h) (fun e : Fin 0 => e.elim0)
    simp only [ContinuousMap.comp_apply] at h'
    rw [← hγ, harg 1] at h'
    simpa [cconst, ContinuousMap.const_apply] using h'
  have hγ0 : γ (fun _ => (0 : unitInterval)) = x₀ := by
    have h := (K.hα 0 h0N (cconst 0 v)).2
    have h' := congrFun (congrArg DFunLike.coe h) (fun e : Fin 0 => e.elim0)
    simp only [ContinuousMap.comp_apply] at h'
    rw [← hγ, harg 0] at h'
    simpa [cconst, ContinuousMap.const_apply] using h'
  -- the degenerate cube appearing in the non-last faces
  set ζ : C(IC (m + 2), X) :=
    (⟨fun u => γ (fun _ => u (Fin.last (m + 1))), by fun_prop⟩ : C(IC (m + 2), X)) with hζ
  set τ : C(IC (m + 3), X) := constTube m γ with hτ
  have hY := Work.Stems.HomAdd.PsiKillsBoundary N m K hN τ
  rw [Fin.prod_univ_castSucc] at hY
  -- restate `hY` with `clPsi`, so that the rewriting below matches syntactically
  have hYc : (∏ i : Fin (m + 2), ∏ b : Fin 2,
      (Work.Stems.Hur2c.clPsi N m K hN (τ.comp (faceCM (Fin.castSucc i) (cval b)))) ^
        ((-1 : ℤ) ^ ((Fin.castSucc i : Fin (m + 3)) + (b : ℕ)))) *
      (∏ b : Fin 2,
        (Work.Stems.Hur2c.clPsi N m K hN (τ.comp (faceCM (Fin.last (m + 2)) (cval b)))) ^
        ((-1 : ℤ) ^ ((Fin.last (m + 2) : Fin (m + 3)) + (b : ℕ)))) = 1 := hY
  -- the faces other than the last ones cancel in pairs
  have hone : (∏ i : Fin (m + 2), ∏ b : Fin 2,
      (Work.Stems.Hur2c.clPsi N m K hN (τ.comp (faceCM (Fin.castSucc i) (cval b)))) ^
        ((-1 : ℤ) ^ ((Fin.castSucc i : Fin (m + 3)) + (b : ℕ)))) = 1 := by
    refine Finset.prod_eq_one fun i _ => ?_
    have hcube0 : τ.comp (faceCM (Fin.castSucc i) (cval 0)) = ζ := by
      rw [hτ, hζ]; exact constTube_face_other m γ i 0
    have hcube1 : τ.comp (faceCM (Fin.castSucc i) (cval 1)) = ζ := by
      rw [hτ, hζ]; exact constTube_face_other m γ i 1
    rw [Fin.prod_univ_two, hcube0, hcube1]
    simp only [Fin.val_zero, Fin.val_one, Nat.add_zero, Fin.val_castSucc]
    rcases Nat.even_or_odd (i : ℕ) with ⟨j, hj⟩ | ⟨j, hj⟩
    · have h1 : ((-1 : ℤ) ^ (i : ℕ)) = 1 := Even.neg_one_pow ⟨j, hj⟩
      have h2 : ((-1 : ℤ) ^ ((i : ℕ) + 1)) = -1 := by
        rw [pow_succ, h1]; ring
      rw [h1, h2, zpow_one, zpow_neg_one, mul_inv_cancel]
    · have h1 : ((-1 : ℤ) ^ (i : ℕ)) = -1 := Odd.neg_one_pow ⟨j, hj⟩
      have h2 : ((-1 : ℤ) ^ ((i : ℕ) + 1)) = 1 := by
        rw [pow_succ, h1]; ring
      rw [h1, h2, zpow_neg_one, zpow_one, inv_mul_cancel]
  rw [hone, one_mul] at hYc
  -- the last faces
  have hlast0 : τ.comp (faceCM (Fin.last (m + 2)) (cval 0)) = cconst (m + 2) x₀ := by
    rw [hτ, constTube_face_last, show cval (0 : Fin 2) = (0 : unitInterval) from rfl, hγ0]
  have hlast1 : τ.comp (faceCM (Fin.last (m + 2)) (cval 1)) = cconst (m + 2) v := by
    rw [hτ, constTube_face_last, show cval (1 : Fin 2) = (1 : unitInterval) from rfl, hγ1]
  have hconst : Work.Stems.Hur2c.clPsi N m K hN (cconst (m + 2) x₀) = 1 := by
    rw [Work.Stems.Hur2c.clPsi_def, Psi_const]
    rfl
  rw [Fin.prod_univ_two, hlast0, hlast1, hconst, one_zpow, one_mul] at hYc
  -- `x ^ (±1) = 1` implies `x = 1`
  have hx : Work.Stems.Hur2c.clPsi N m K hN (cconst (m + 2) v) = 1 := by
    have hexp : ((-1 : ℤ) ^ (((Fin.last (m + 2) : Fin (m + 3)) : ℕ) + ((1 : Fin 2) : ℕ)))
        = (-1 : ℤ) ^ (m + 3) := by
      have h1 : (((Fin.last (m + 2) : Fin (m + 3)) : ℕ) + ((1 : Fin 2) : ℕ)) = m + 3 := by
        rw [Fin.val_last, Fin.val_one]
      rw [h1]
    rw [hexp] at hYc
    rcases Nat.even_or_odd (m + 3) with ⟨j, hj⟩ | ⟨j, hj⟩
    · rw [Even.neg_one_pow ⟨j, hj⟩, zpow_one] at hYc
      exact hYc
    · rw [Odd.neg_one_pow ⟨j, hj⟩, zpow_neg_one, inv_eq_one] at hYc
      exact hYc
  rw [Work.Stems.Hur2c.psiLinGen_single, hx]
  rfl

end

end Work.RatHurewicz
