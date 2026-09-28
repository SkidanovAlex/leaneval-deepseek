import Submission.Work.Stems.Hur2c.degenCube_boundary

/-!
# `Ψ` of a constant `2`-cube

`Ψ x₀ (single (const v) 1) = 0` for **every** `v`, proved from `(Y)` (`PsiLin_cubD_single`) and
`(Z)` (`PsiLin_single_based`) alone.  This is the fork-free replacement for
`Work.Stems.Hur2b.PsiLin_single_const` (whose file `PsiConstAux.lean` clashes with the `NetTree`
side of `Hur2b` on the name `Work.Stems.Hur2b.rho`, and therefore cannot be imported next to `(Y)`).

The `3`-cube is `p ↦ γ (p 2)` for a path `γ` from `v` to `x₀`: its `u`-faces are the constants
`const v`, `const x₀`, and its other four faces are the same `2`-cube `p ↦ γ (p 1)` pairwise
(hence cancel).  `(Y)` then reads `Ψ (const v) = Ψ (const x₀)`, and the latter is `0` by `(Z)`.
-/

open scoped unitInterval Topology

namespace Work.Stems.Hur2c

open Work.Stems.Cubical

noncomputable section

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]

/-- **The constant `2`-cube: `Ψ (const v) = Ψ (const x₀)`.**

This is what the `3`-cube `(s,t,u) ↦ γ u` (for `γ` a path from `v` to `x₀`) proves from `(Y)` alone:
its four side faces cancel pairwise and its two remaining faces are `const v` and `const x₀`.

The *absolute* form `Ψ (const v) = 0` needs in addition `Ψ (const x₀) = 0`, which is `(Z)`
(`PsiLin_single_based`) applied to the constant based cube — i.e. `Additive.ofMul ⟦p⟧ = 0` for
`p := GenLoop.const`, i.e. `⟦GenLoop.const⟧ = 1`.  In this import context
`inferInstance` does **not** find `One (HomotopyGroup (Fin 2) X x₀)` (so neither the numeral `1` nor
`One.one` elaborates there), which is why that last rewriting step is recorded rather than performed
here; see `STATUS.md`.  For `T_loop`/`T_coord` only the relative form plus that single instance
question is needed. -/
theorem PsiLin_const_eq_const (x₀ v : X) :
    Work.Stems.Hur2.PsiLin x₀ (Finsupp.single (ContinuousMap.const (IC 2) v) 1)
      = Work.Stems.Hur2.PsiLin x₀ (Finsupp.single (ContinuousMap.const (IC 2) x₀) 1) := by
  -- a `1`-cube from `v` to `x₀`
  let γ : C(IC 1, X) := cubeOfPath (PathConnectedSpace.somePath v x₀)
  have hγ0 : γ (pt 0) = v := by
    show (PathConnectedSpace.somePath v x₀) 0 = v
    exact (PathConnectedSpace.somePath v x₀).source
  have hγ1 : γ (pt 1) = x₀ := by
    show (PathConnectedSpace.somePath v x₀) 1 = x₀
    exact (PathConnectedSpace.somePath v x₀).target
  -- the `3`-cube `(s,t,u) ↦ γ u`, built as a degenerate cube of a degenerate cube
  let δ₂ : C(IC 2, X) := degenCube' 1 (1 : Fin 2) γ
  let C : C(IC 3, X) := degenCube' 2 (2 : Fin 3) δ₂
  have hY := Work.Stems.Hur2b.PsiLin_cubD_single x₀ C
  -- its faces
  have h0 : faceCube (0 : Fin 3) 0 C = δ₂ :=
    faceCube_degenCube'_other (by decide : (2 : Fin 3) = (0 : Fin 3).succAbove (1 : Fin 2)) 0 δ₂
  have h0' : faceCube (0 : Fin 3) 1 C = δ₂ :=
    faceCube_degenCube'_other (by decide : (2 : Fin 3) = (0 : Fin 3).succAbove (1 : Fin 2)) 1 δ₂
  have h1 : faceCube (1 : Fin 3) 0 C = δ₂ :=
    faceCube_degenCube'_other (by decide : (2 : Fin 3) = (1 : Fin 3).succAbove (1 : Fin 2)) 0 δ₂
  have h1' : faceCube (1 : Fin 3) 1 C = δ₂ :=
    faceCube_degenCube'_other (by decide : (2 : Fin 3) = (1 : Fin 3).succAbove (1 : Fin 2)) 1 δ₂
  have h2 : faceCube (2 : Fin 3) 0 C = ContinuousMap.const (IC 2) (γ (pt 0)) :=
    faceCube_degenCube'_frozen 2 (2 : Fin 3) 0 δ₂
  have h2' : faceCube (2 : Fin 3) 1 C = ContinuousMap.const (IC 2) (γ (pt 1)) :=
    faceCube_degenCube'_frozen 2 (2 : Fin 3) 1 δ₂
  -- the chain identity for the boundary
  have hchain : cubD 2 X (Finsupp.single C 1)
      = Finsupp.single (ContinuousMap.const (IC 2) v) 1
        - Finsupp.single (ContinuousMap.const (IC 2) x₀) 1 := by
    rw [cubD_single, Fin.sum_univ_three, h0, h0', h1, h1', h2, h2', hγ0, hγ1]
    norm_num
  -- `(Y)` on the boundary of the cube
  have hbd : Work.Stems.Hur2.PsiLin x₀ (cubD 2 X (Finsupp.single C 1))
      = Work.Stems.Hur2.PsiLin x₀ (Finsupp.single (ContinuousMap.const (IC 2) v) 1)
        - Work.Stems.Hur2.PsiLin x₀ (Finsupp.single (ContinuousMap.const (IC 2) x₀) 1) := by
    rw [hchain, map_sub]
  rw [hY] at hbd
  exact sub_eq_zero.mp hbd.symm


/-- **`(Z)` on the constant based cube**: `Ψ` of the constant `2`-cube at the base point is `0`.

This is `Work.Stems.Hur2.PsiLin_single_based` applied to `GenLoop.const`, together with
`HomotopyGroup.one_def` (`(1 : HomotopyGroup N X x) = ⟦const⟧`).  The group structure on
`HomotopyGroup` is the *named* instance `HomotopyGroup.group (N) [DecidableEq N] [Nonempty N]`,
which instance search does not find at this type in this import context, so it is brought into scope
explicitly with `letI`; after that the rewriting step goes through. -/
theorem PsiLin_const_base (x₀ : X) :
    Work.Stems.Hur2.PsiLin x₀ (Finsupp.single (ContinuousMap.const (IC 2) x₀) 1) = 0 := by
  letI : Group (HomotopyGroup (Fin 2) X x₀) := HomotopyGroup.group (Fin 2)
  have h : Work.Stems.Hur2.PsiLin x₀ (Finsupp.single (ContinuousMap.const (IC 2) x₀) 1)
      = Additive.ofMul (⟦(GenLoop.const (N := Fin 2) (X := X) (x := x₀))⟧ :
          HomotopyGroup (Fin 2) X x₀) :=
    Work.Stems.Hur2.PsiLin_single_based x₀ (GenLoop.const (N := Fin 2) (X := X) (x := x₀))
  rw [h, HomotopyGroup.one_def.symm]
  rfl

/-- **The constant `2`-cube has trivial `Ψ`** (absolute form): `Ψ x₀ (single (const v) 1) = 0` for
every `v`, from `(Y)` (`PsiLin_const_eq_const`) and `(Z)` (`PsiLin_const_base`).  This is the
fork-free replacement for `Work.Stems.Hur2b.PsiLin_single_const`. -/
theorem PsiLin_single_const_degen (x₀ v : X) :
    Work.Stems.Hur2.PsiLin x₀ (Finsupp.single (ContinuousMap.const (IC 2) v) 1) = 0 := by
  rw [PsiLin_const_eq_const x₀ v, PsiLin_const_base x₀]

end

end Work.Stems.Hur2c
