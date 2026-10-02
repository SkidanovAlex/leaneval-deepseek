import Submission.Work.Stems.Hur2c.Faces3
import Submission.Work.Stems.Hur2c.T_const
import Submission.Work.Stems.Hur2b.K1_homotopicRel_edge

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The two coordinate variants of `T` are negatives of each other

`Work.Stems.Hur2c.T_coord : T x₀ 1 δ = - T x₀ 0 δ` — the coordinate transposition of `I²` is
orientation-*reversing* (degree `-1` on `I²/∂I² ≅ S²`), so it negates the class; the wrong sign would
force the false `2 · T = 0`.

The `3`-cube is `τ (u,v,w) := δ (interp w u)` (`interp w u = (1-w)·u + w`, `Hur2b/K1_homotopicRel_edge.lean`).
It does not depend on `v`, so its `v`-faces cancel; its `w`-faces are `degenCube 0 L` (`w = 0`, by
`interp_zero`) and the constant at `δ 1` (`w = 1`, by `interp_one`); its `u`-faces are `degenCube 1 L`
(`u = 0`, by `interp_zero_right`) and the same constant (`u = 1`, by `interp_of_eq_one`).  So `(Y)`
reads `T x₀ 1 L + T x₀ 0 L = 0` (the constants being killed by `PsiLin_single_const_degen`); finally
`L = δ` (`Hur2.iota_eq`).
-/

open scoped unitInterval Topology

namespace Work.Stems.Hur2c

open Work.Stems.Cubical
open Work.Stems.Hur2

noncomputable section

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]

theorem T_coord (x₀ : X) (δ : C(IC 1, X)) :
    T x₀ 1 δ = - T x₀ 0 δ := by
  letI : Group (HomotopyGroup (Fin 2) X x₀) := HomotopyGroup.group (Fin 2)
  let L : C(IC 1, X) := ⟨fun s => δ (fun _ => s 0), δ.continuous.comp (by fun_prop)⟩
  have hL : L = δ := by
    ext t
    show δ (fun _ => t 0) = δ t
    congr 1
    exact Hur2.iota_eq t
  -- the degenerate cubes of `L`, in unfolded form (used as the faces' right-hand sides)
  have hLcube : ∀ k : Fin 2,
      degenCube k L = ⟨fun t : IC 2 => δ (fun _ => t k), by fun_prop⟩ := by
    intro k
    ext t
    rfl
  let cc : C(IC 2, X) := ContinuousMap.const (IC 2) (δ (fun _ => (1 : unitInterval)))
  have hcont : Continuous fun p : IC 3 => Work.Stems.Hur2b.interp (p 2) (p 0) := by
    rw [show (fun p : IC 3 => Work.Stems.Hur2b.interp (p 2) (p 0)) =
        (fun p => Set.projIcc (0 : ℝ) 1 zero_le_one
          ((1 - ((p 2 : unitInterval) : ℝ)) * ((p 0 : unitInterval) : ℝ)
            + ((p 2 : unitInterval) : ℝ))) from rfl]
    exact (continuous_projIcc).comp (by fun_prop)
  let τ : C(IC 3, X) :=
    ⟨fun p => δ (fun _ => Work.Stems.Hur2b.interp (p 2) (p 0)),
      δ.continuous.comp (continuous_pi fun _ => hcont)⟩
  have hY := Work.Stems.Hur2b.PsiLin_cubD_single x₀ τ
  have f0 : faceCube (0 : Fin 3) 0 τ = degenCube 1 L := by
    rw [hLcube 1]
    ext t
    show δ (fun _ => Work.Stems.Hur2b.interp ((faceCM (0 : Fin 3) 0 t) 2)
      ((faceCM (0 : Fin 3) 0 t) 0)) = δ (fun _ => t 1)
    rw [faceCM3_0_2, faceCM3_frozen]
    congr 1
    funext j
    simpa using Work.Stems.Hur2b.interp_zero_right (t 1)
  have f0' : faceCube (0 : Fin 3) 1 τ = cc := by
    ext t
    show δ (fun _ => Work.Stems.Hur2b.interp ((faceCM (0 : Fin 3) 1 t) 2)
      ((faceCM (0 : Fin 3) 1 t) 0)) = δ (fun _ => (1 : unitInterval))
    rw [faceCM3_0_2, faceCM3_frozen]
    congr 1
    funext j
    simpa using Work.Stems.Hur2b.interp_of_eq_one (rfl : (1 : unitInterval) = 1)
  have f1 : faceCube (1 : Fin 3) 0 τ = faceCube (1 : Fin 3) 1 τ := by
    ext t
    show δ (fun _ => Work.Stems.Hur2b.interp ((faceCM (1 : Fin 3) 0 t) 2)
        ((faceCM (1 : Fin 3) 0 t) 0))
      = δ (fun _ => Work.Stems.Hur2b.interp ((faceCM (1 : Fin 3) 1 t) 2)
        ((faceCM (1 : Fin 3) 1 t) 0))
    rw [faceCM3_1_2, faceCM3_1_0, faceCM3_1_2, faceCM3_1_0]
  have f2 : faceCube (2 : Fin 3) 0 τ = degenCube 0 L := by
    rw [hLcube 0]
    ext t
    show δ (fun _ => Work.Stems.Hur2b.interp ((faceCM (2 : Fin 3) 0 t) 2)
      ((faceCM (2 : Fin 3) 0 t) 0)) = δ (fun _ => t 0)
    rw [faceCM_frozen, faceCM3_2_0]
    congr 1
    funext j
    simpa using Work.Stems.Hur2b.interp_zero (t 0)
  have f2' : faceCube (2 : Fin 3) 1 τ = cc := by
    ext t
    show δ (fun _ => Work.Stems.Hur2b.interp ((faceCM (2 : Fin 3) 1 t) 2)
      ((faceCM (2 : Fin 3) 1 t) 0)) = δ (fun _ => (1 : unitInterval))
    rw [faceCM_frozen, faceCM3_2_0]
    congr 1
    funext j
    simpa using Work.Stems.Hur2b.interp_one (t 0)
  have hchain : cubD 2 X (Finsupp.single τ 1)
      = (Finsupp.single (degenCube 1 L) 1 - Finsupp.single cc 1)
        + (Finsupp.single (degenCube 0 L) 1 - Finsupp.single cc 1) := by
    rw [cubD_single, Fin.sum_univ_three, f0, f0', f1, f2, f2']
    norm_num
  rw [hchain, map_add, map_sub, map_sub] at hY
  rw [PsiLin_single_const_degen x₀ (δ (fun _ => (1 : unitInterval)))] at hY
  rw [sub_zero, sub_zero] at hY
  have hgoal : T x₀ 1 L = - T x₀ 0 L := by
    rw [T_def, T_def]
    exact eq_neg_of_add_eq_zero_left hY
  simpa [hL] using hgoal

end

end Work.Stems.Hur2c
