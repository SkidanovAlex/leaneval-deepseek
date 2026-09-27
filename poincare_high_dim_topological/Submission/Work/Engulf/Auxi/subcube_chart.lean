import Mathlib
import Submission.Work.PL.Defs

/-!
# An affine sub-cube chart (`Work.Engulf.Aux.subcube_chart`)

If the closed cube of radius `ρ` about `c` lies in the open unit cube, then
`y ↦ ψ (c + ρ • y)` is again a cube chart (contract §8, aux Hx2a).

The proof is the affine-scaling argument also used in `Work.Metric.locCube_open_subset`
and `Work.Cells.Connell.exists_cubeChart_subcube`: the map `g := fun y => c + ρ • y` is a
homeomorphism of `PL.E n` (`Homeomorph.smulOfNeZero ρ` followed by `Homeomorph.addLeft c`),
it maps the open unit cube into itself by hypothesis (every point of `openCube 1` lies in
`closedCube 1`), so the restriction `τ` of `g` to `openCube 1` is an open embedding of that
cube into itself; `(openCube 1).domRestrict ψ.toFun` is an open embedding by `ψ.emb`, a
composition of open embeddings is an open embedding, and that composition is exactly
`(openCube 1).domRestrict (fun y => ψ.toFun (c + ρ • y))`.

The two geometric facts about sup-norm cubes used here are proved inline, so the module
depends only on `Mathlib` and the frozen contract file `Submission.Work.PL.Defs` (in
particular it is independent of `Submission.Work.Engulf.Basic`).

## Environment note (`Aux` is an OS-reserved file name)

This file's *directory* is named `Aux`.  Lean 4.34's driver rejects a module whose name has
a component that is a reserved file name on some operating system (`CON`, `PRN`, `AUX`,
`NUL`, ...):

`error: module name 'Submission.Work.Engulf.Auxi.subcube_chart' is not portable: 'Aux' is a
reserved file name on some operating systems`

(`Lean/Elab/Import.lean`, `checkModuleNamePortability`, applied to the name Lake passes via
`--setup`).  The check is unconditional and Lake derives the name from the file path, so
`lake build` can never compile such a file *by itself*.  The module itself is unaffected:
it elaborates and imports normally, and `Submission/Work/Engulf/Aux/fix_reserved_module.sh`
produces the artifacts Lake expects (running Lean on exactly this source with the same
imports, only the internal module name in the setup file being renamed), after which
`lake build Submission.Work.Engulf.Auxi.subcube_chart` succeeds.  See
`Submission/Work/Engulf/Aux/NOTE_reserved_Aux_name.md`.  **Re-run that script after any edit
of this file.**
-/

open Set Metric PL

namespace Work.Engulf.Aux

/-- **`subcube_chart`** (contract §8, aux Hx2a): an affine sub-cube chart.  If the closed cube of radius `ρ` about `c` lies in the open unit cube, then `y ↦ ψ (c + ρ • y)` is again a cube chart.  Used to shrink a `Tame` chart in the `§10` covering trick of `E1` and in the chart cover of `E5`. -/
theorem subcube_chart {n : ℕ} {M : Type*} [TopologicalSpace M] (ψ : PL.CubeChart n M)
    (c : PL.E n) {ρ : ℝ} (hρ : 0 < ρ)
    (hc : ∀ y ∈ PL.closedCube (n := n) 1, c + ρ • y ∈ PL.openCube (n := n) 1) :
    ∃ χ : PL.CubeChart n M, ∀ y, χ.toFun y = ψ.toFun (c + ρ • y) := by
  classical
  -- the open unit cube, and the two elementary facts about sup-norm cubes
  set s : Set (PL.E n) := PL.openCube (n := n) 1 with hs
  have hsopen : IsOpen s := by
    rw [hs]
    have h : PL.openCube (n := n) 1 = ⋂ i : Fin n, {x : PL.E n | |x i| < (1 : ℝ)} := by
      ext x; simp [PL.openCube]
    rw [h]
    exact isOpen_iInter_of_finite fun i =>
      isOpen_lt (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) i).abs continuous_const
  have hsub : s ⊆ PL.closedCube (n := n) 1 := fun _ hx i => le_of_lt (hx i)
  -- the affine map `g`, its open-embedding property, and its restriction `τ` to the cube
  let g : PL.E n → PL.E n := fun z => c + ρ • z
  have hgmem : ∀ z ∈ s, g z ∈ s := fun z hz => hc z (hsub hz)
  have hg : Topology.IsOpenEmbedding g := by
    have h1 : g = ⇑((Homeomorph.smulOfNeZero ρ (ne_of_gt hρ)).trans (Homeomorph.addLeft c)) := by
      funext z; simp [g, Homeomorph.trans_apply]
    rw [h1]; exact Homeomorph.isOpenEmbedding _
  let τ : ↥s → ↥s := fun z => ⟨g z, hgmem z z.2⟩
  have hτ : Topology.IsOpenEmbedding τ := by
    apply (Topology.IsOpenEmbedding.of_comp_iff τ hsopen.isOpenEmbedding_subtypeVal).mp
    have h2 : Topology.IsOpenEmbedding (g ∘ (Subtype.val : ↥s → PL.E n)) :=
      hg.comp hsopen.isOpenEmbedding_subtypeVal
    convert h2 using 1
    ext z; rfl
  -- composing with the open embedding `ψ` on the cube gives the sub-cube embedding
  have hemb : Topology.IsOpenEmbedding (s.domRestrict (fun y => ψ.toFun (c + ρ • y))) := by
    have hcomp : Topology.IsOpenEmbedding ((s.domRestrict ψ.toFun) ∘ τ) := ψ.emb.comp hτ
    convert hcomp using 1
    ext z; rfl
  exact ⟨{ toFun := fun y => ψ.toFun (c + ρ • y)
           cont := continuousOn_iff_continuous_domRestrict.mpr hemb.continuous
           emb := hemb }, fun y => rfl⟩

end Work.Engulf.Aux
