import Submission.Work.Stems.Hur2c.Faces3
import Submission.Work.Stems.Hur2c.T_const

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# `T` of a loop vanishes

`Work.Stems.Hur2c.T_loop : δ 0 = δ 1 → T x₀ i δ = 0`.

The homotopy `H` of the loop `u ↦ δ (fun _ ↦ u)` to the constant (from
`SimplyConnectedSpace.paths_homotopic`; its *first* coordinate is the homotopy parameter and its
*second* the parameter along the path, and every intermediate `H s` is again a loop) gives the
`2`-cube `F (t₀,t₁) := H (t₀,t₁)`.  For the target coordinate `k : Fin 2` the `3`-cube is
`C_k (p) := F (pair2 (p h) (p ℓ))` with the homotopy parameter in the slot `h` and the loop
parameter in the slot `ℓ` chosen so that the loop lands in the *slot `k`* of the surviving face:

* `k = 0`: `(h, ℓ) = (1, 0)`, unused coordinate `2`;
* `k = 1`: `(h, ℓ) = (0, 2)`, unused coordinate `1`.

Its `h`-faces are `degenCube k L` (at `b = 0`) and the constant at `δ 0` (at `b = 1`), its
`ℓ`-faces are the two constants `δ 0`, and its remaining faces are an equal pair; `(Y)` plus the
constant case (`T_const.lean`) gives `T x₀ k L = 0`, and `L = δ`.
-/

open scoped unitInterval Topology

namespace Work.Stems.Hur2c

open Work.Stems.Cubical
open Work.Stems.Hur2

noncomputable section

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]

theorem T_loop (x₀ : X) (i : Fin 2) (δ : C(IC 1, X)) (h : δ 0 = δ 1) :
    T x₀ i δ = 0 := by
  letI : Group (HomotopyGroup (Fin 2) X x₀) := HomotopyGroup.group (Fin 2)
  -- the loop as a `Path`
  let p₁ : Path (δ 0) (δ 0) :=
    { toFun := fun u => δ (fun _ => u)
      continuous_toFun := δ.continuous.comp (continuous_pi fun _ => continuous_id)
      source' := rfl
      target' := h.symm }
  obtain ⟨H⟩ := SimplyConnectedSpace.paths_homotopic p₁ (Path.refl (δ 0))
  -- the `2`-cube of the homotopy
  let F : C(IC 2, X) :=
    ⟨fun t => H.toHomotopy.toContinuousMap (t 0, t 1),
      H.toHomotopy.continuous.comp (by fun_prop)⟩
  -- the `1`-cube of the loop
  let L : C(IC 1, X) :=
    ⟨fun s => δ (fun _ => s 0), δ.continuous.comp (by fun_prop)⟩
  -- `L` is `δ`
  have hL : L = δ := by
    ext t
    show δ (fun _ => t 0) = δ t
    congr 1
    exact Hur2.iota_eq t
  -- the boundary facts of the homotopy
  have hloop : ∀ s : unitInterval, F (pair2 s 0) = δ 0 := by
    intro s
    show H.toHomotopy.toContinuousMap ((pair2 s 0) 0, (pair2 s 0) 1) = δ 0
    rw [pair2_zero, pair2_one]
    simp
  have hloop' : ∀ s : unitInterval, F (pair2 s 1) = δ 0 := by
    intro s
    show H.toHomotopy.toContinuousMap ((pair2 s 1) 0, (pair2 s 1) 1) = δ 0
    rw [pair2_zero, pair2_one]
    simp
  have hstart : ∀ u : unitInterval, F (pair2 0 u) = L (fun _ => u) := by
    intro u
    simpa [F, pair2_zero, pair2_one, L, p₁] using H.toHomotopy.map_zero_left u
  have hend : ∀ u : unitInterval, F (pair2 1 u) = δ 0 := by
    intro u
    simpa [F, pair2_zero, pair2_one] using H.toHomotopy.map_one_left u
  -- the two cubes, one for each target coordinate
  have key0 : T x₀ 0 L = 0 := by
    let C : C(IC 3, X) :=
      ⟨fun p => F (pair2 (p 1) (p 0)),
        F.continuous.comp (continuous_pair2 (by fun_prop) (by fun_prop))⟩
    have hY := Work.Stems.Hur2b.PsiLin_cubD_single x₀ C
    have f0 : faceCube (0 : Fin 3) 0 C = ContinuousMap.const (IC 2) (δ 0) := by
      ext t
      show F (pair2 ((faceCM (0 : Fin 3) 0 t) 1) ((faceCM (0 : Fin 3) 0 t) 0)) = δ 0
      rw [faceCM3_0_1, faceCM3_frozen]
      exact hloop (t 0)
    have f0' : faceCube (0 : Fin 3) 1 C = ContinuousMap.const (IC 2) (δ 0) := by
      ext t
      show F (pair2 ((faceCM (0 : Fin 3) 1 t) 1) ((faceCM (0 : Fin 3) 1 t) 0)) = δ 0
      rw [faceCM3_0_1, faceCM3_frozen]
      exact hloop' (t 0)
    have f1 : faceCube (1 : Fin 3) 0 C = degenCube 0 L := by
      ext t
      show F (pair2 ((faceCM (1 : Fin 3) 0 t) 1) ((faceCM (1 : Fin 3) 0 t) 0))
        = L (fun _ => t 0)
      rw [faceCM3_frozen, faceCM3_1_0]
      exact hstart (t 0)
    have f1' : faceCube (1 : Fin 3) 1 C = ContinuousMap.const (IC 2) (δ 0) := by
      ext t
      show F (pair2 ((faceCM (1 : Fin 3) 1 t) 1) ((faceCM (1 : Fin 3) 1 t) 0)) = δ 0
      rw [faceCM3_frozen, faceCM3_1_0]
      exact hend (t 0)
    have f2 : faceCube (2 : Fin 3) 0 C = faceCube (2 : Fin 3) 1 C := by
      ext t
      show F (pair2 ((faceCM (2 : Fin 3) 0 t) 1) ((faceCM (2 : Fin 3) 0 t) 0))
        = F (pair2 ((faceCM (2 : Fin 3) 1 t) 1) ((faceCM (2 : Fin 3) 1 t) 0))
      rw [faceCM3_2_1, faceCM3_2_0, faceCM3_2_1, faceCM3_2_0]
    have hchain : cubD 2 X (Finsupp.single C 1)
        = -(Finsupp.single (degenCube 0 L) 1
            - Finsupp.single (ContinuousMap.const (IC 2) (δ 0)) 1) := by
      rw [cubD_single, Fin.sum_univ_three, f0, f0', f1, f1', f2]
      norm_num
    rw [hchain, map_neg, map_sub, neg_eq_zero, sub_eq_zero] at hY
    rw [T_def, hY, PsiLin_single_const_degen x₀ (δ 0)]
  have key1 : T x₀ 1 L = 0 := by
    let C : C(IC 3, X) :=
      ⟨fun p => F (pair2 (p 0) (p 2)),
        F.continuous.comp (continuous_pair2 (by fun_prop) (by fun_prop))⟩
    have hY := Work.Stems.Hur2b.PsiLin_cubD_single x₀ C
    have f0 : faceCube (0 : Fin 3) 0 C = degenCube 1 L := by
      ext t
      show F (pair2 ((faceCM (0 : Fin 3) 0 t) 0) ((faceCM (0 : Fin 3) 0 t) 2))
        = L (fun _ => t 1)
      rw [faceCM3_frozen, faceCM3_0_2]
      exact hstart (t 1)
    have f0' : faceCube (0 : Fin 3) 1 C = ContinuousMap.const (IC 2) (δ 0) := by
      ext t
      show F (pair2 ((faceCM (0 : Fin 3) 1 t) 0) ((faceCM (0 : Fin 3) 1 t) 2)) = δ 0
      rw [faceCM3_frozen, faceCM3_0_2]
      exact hend (t 1)
    have f1 : faceCube (1 : Fin 3) 0 C = faceCube (1 : Fin 3) 1 C := by
      ext t
      show F (pair2 ((faceCM (1 : Fin 3) 0 t) 0) ((faceCM (1 : Fin 3) 0 t) 2))
        = F (pair2 ((faceCM (1 : Fin 3) 1 t) 0) ((faceCM (1 : Fin 3) 1 t) 2))
      rw [faceCM3_1_0, faceCM3_1_2, faceCM3_1_0, faceCM3_1_2]
    have f2 : faceCube (2 : Fin 3) 0 C = ContinuousMap.const (IC 2) (δ 0) := by
      ext t
      show F (pair2 ((faceCM (2 : Fin 3) 0 t) 0) ((faceCM (2 : Fin 3) 0 t) 2)) = δ 0
      rw [faceCM3_2_0, faceCM3_frozen]
      exact hloop (t 0)
    have f2' : faceCube (2 : Fin 3) 1 C = ContinuousMap.const (IC 2) (δ 0) := by
      ext t
      show F (pair2 ((faceCM (2 : Fin 3) 1 t) 0) ((faceCM (2 : Fin 3) 1 t) 2)) = δ 0
      rw [faceCM3_2_0, faceCM3_frozen]
      exact hloop' (t 0)
    have hchain : cubD 2 X (Finsupp.single C 1)
        = Finsupp.single (degenCube 1 L) 1
          - Finsupp.single (ContinuousMap.const (IC 2) (δ 0)) 1 := by
      rw [cubD_single, Fin.sum_univ_three, f0, f0', f1, f2, f2']
      norm_num
    rw [hchain, map_sub, sub_eq_zero] at hY
    rw [T_def, hY, PsiLin_single_const_degen x₀ (δ 0)]
  rw [T_def]
  fin_cases i
  · simpa [T_def, hL] using key0
  · simpa [T_def, hL] using key1

end

end Work.Stems.Hur2c
