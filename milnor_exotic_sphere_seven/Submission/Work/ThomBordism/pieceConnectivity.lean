import Mathlib
import Submission.Work.ThomBordism.connectivityAssembly
import Submission.Work.ThomBordism.Grassmann.chartPieceCompressFarCrux
import Submission.Work.Stems.subsingleton_homotopyGroup_change_basepoint
import Submission.Work.Stems.subsingleton_of_contractible

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The `(k-1)`-connectivity of the chart piece `far 1 ∪ π⁻¹(W)` of the Thom space (area THOM)

For `k m : ℕ`, a chart `S₀ : ChartIdx k m` and an open `W ⊆ baseSet S₀`, the *piece*

`Z = far 1 ∪ π⁻¹(W) ⊆ Th γ = OnePoint (TotalSpace γ)`

(`far 1 = {fibN > 1} ∪ {∞}`) is `(k-1)`-connected: `π_j(Z, x) = 0` for `j < k` and every base
point `x`.  This is the piece connectivity that the finite-cover Mayer–Vietoris assembly
`Work.ThomBordism.thomSpaceConnected_of_pieces` (this area) and the chart-cell assembly
`Work.ThomBordism.Grassmann.thomSpaceConnectedAssembly` (area GRASSMANN) consume, in the
unrestricted form for *arbitrary* open `W` inside a chart cell.

## The route

1. `Work.ThomBordism.Grassmann.chartPieceCompressFarCrux` (proved, sorry-free) is the
   *compression* form of the vanishing of the relative groups `π_e(Z, far 1)`, `e < k`: every map
   of pairs `(I^j, ∂I^j) → (Z, far 1)`, `j < k`, is homotopic relative to the boundary into
   `far 1`.  It is proved by the cell-by-cell subdivision argument of
   `Work.ThomBordism.Grassmann.TwoSet` applied to the open cover `Z = far 1 ∪ π⁻¹(W)`, in which
   only the `π⁻¹(W)`-typed cells need processing (the shell compression
   `Work.ThomBordism.Grassmann.compress_shellSub`, fed by the trivialisation of the bundle over
   the chart and the connectivity of spheres); the `far 1`-typed cells are already in the target.
2. `Work.ThomBordism.TwoSet.Compress.toSubsingleton` then gives `π_j(Z) = 0` at every base point
   of `far 1`, using that the trace of `far 1` in `Z` is homeomorphic to `far 1`
   (`subSubHomeo`) and that `far 1` is contractible (`Torsion.contractibleFar`).
3. For a base point outside `far 1` we use the base point change along a path
   (`Work.Stems.subsingleton_homotopyGroup_change_basepoint`).  The path is supplied by the
   *zero*-dimensional case of the same compression statement: applied to the constant map at the
   base point it produces a path from that point to a point of `far 1`.

## Main declarations

* `Work.ThomBordism.pieceConnectivity` — the target;
* `Work.ThomBordism.PieceOverChartConnected.ofPieceConnectivity` — the same statement in the
  `Work.ThomBordism.PieceOverChartConnected` of `connectivityAssembly.lean`, which is the input of
  `Work.ThomBordism.thomSpaceConnected_of_pieces`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped Topology unitInterval

namespace Work.ThomBordism

/-- **The points of the zero-cube are never on its (empty) boundary.** -/
theorem not_mem_boundary_zero (y : TwoSet.IC 0) : y ∉ Cube.boundary (Fin 0) := by
  intro hy
  obtain ⟨i, -⟩ := TwoSet.mem_boundary_iff.mp hy
  exact i.elim0

/-- **The chart piece `far 1 ∪ π⁻¹(W)` is `(k-1)`-connected.**

For every `j < k` and every base point `x` of the piece, `π_j` at `x` is a subsingleton. -/
theorem pieceConnectivity (k m : ℕ) (S₀ : Work.ThomBordism.Grassmann.ChartIdx k m)
    (W : Set (Work.ThomBordism.Grassmann.OG k m)) (hW : IsOpen W)
    (hWsub : W ⊆ (Work.ThomBordism.Grassmann.tautologicalBundle k m).baseSet S₀) :
    ∀ j : ℕ, j < k → ∀ x : ↥(Work.ThomBordism.Grassmann.Torsion.far k m 1 ∪
        OnePoint.some '' ((Work.ThomBordism.Grassmann.tautologicalBundle k m).proj ⁻¹' W)),
      Subsingleton (HomotopyGroup (Fin j) ↥(Work.ThomBordism.Grassmann.Torsion.far k m 1 ∪
        OnePoint.some '' ((Work.ThomBordism.Grassmann.tautologicalBundle k m).proj ⁻¹' W)) x) := by
  intro j hj x
  have hkpos : 0 < k := lt_of_le_of_lt (Nat.zero_le j) hj
  -- *Step 1*: the compression of the pair `(Z, farTr)` in dimension `j`, and in dimension `0`.
  have hcomp : TwoSet.Compress ↥(Grassmann.pieceS k m W) (Grassmann.farTr k m W) j :=
    Grassmann.chartPieceCompressFarCrux k m S₀ W hW hWsub j hj
  have hcomp0 : TwoSet.Compress ↥(Grassmann.pieceS k m W) (Grassmann.farTr k m W) 0 :=
    Grassmann.chartPieceCompressFarCrux k m S₀ W hW hWsub 0 hkpos
  -- *Step 2*: `π_j` of the far trace vanishes at every one of its points.
  have hsub : Grassmann.Torsion.far k m 1 ⊆ Grassmann.pieceS k m W := fun _ hy => Or.inl hy
  have htrace : ∀ w : ↥(Grassmann.farTr k m W),
      Subsingleton (HomotopyGroup (Fin j) ↥(Grassmann.farTr k m W) w) := by
    intro w
    haveI : ContractibleSpace ↥(Grassmann.Torsion.far k m 1) :=
      Grassmann.Torsion.contractibleFar k m
    exact Grassmann.subsingleton_homotopyGroup_of_homeomorph (Grassmann.subSubHomeo hsub) rfl j
      (Work.Stems.subsingleton_of_contractible (Grassmann.subSubHomeo hsub w))
  -- *Step 3*: the zero-dimensional compression joins every point of `Z` to the far trace.
  obtain ⟨G, hG0, -, hG1⟩ := hcomp0 (ContinuousMap.const (TwoSet.IC 0) x)
    (fun y hy => absurd hy (not_mem_boundary_zero y))
  let y₀ : TwoSet.IC 0 := fun i => i.elim0
  have hmem : G (y₀, 1) ∈ Grassmann.farTr k m W := hG1 y₀
  have hγ : Path x (G (y₀, 1)) :=
    { toContinuousMap :=
        ⟨fun t => G (y₀, t), G.continuous.comp (continuous_const.prodMk continuous_id)⟩
      source' := by
        show G (y₀, (0 : I)) = x
        rw [hG0 y₀]
        rfl
      target' := rfl }
  -- *Step 4*: `π_j(Z)` vanishes at `G (y₀, 1) ∈ farTr`, hence at `x` by base point change.
  have htarget : Subsingleton (HomotopyGroup (Fin j) ↥(Grassmann.pieceS k m W) (G (y₀, 1))) :=
    TwoSet.Compress.toSubsingleton hcomp hmem (htrace ⟨G (y₀, 1), hmem⟩)
  exact Work.Stems.subsingleton_homotopyGroup_change_basepoint hγ.symm htarget

/-- **The piece connectivity in the vocabulary of `connectivityAssembly.lean`**: the definition
`Work.ThomBordism.PieceOverChartConnected`, which is the hypothesis of
`Work.ThomBordism.thomSpaceConnected_of_pieces` (and hence of the area's endgame
`Work.ThomBordism.thomRational_of_grassmannConnectivity`). -/
theorem PieceOverChartConnected.ofPieceConnectivity : PieceOverChartConnected :=
  fun k m S₀ W hW hWsub j hj x => pieceConnectivity k m S₀ W hW hWsub j hj x

/-- **The `(k-1)`-connectivity of the Thom space of the tautological bundle**, from the piece
connectivity through the finite-cover Mayer–Vietoris assembly of this area
(`thomSpaceConnected_of_pieces`). -/
theorem thomSpaceConnected_of_pieceConnectivity (k m : ℕ) : Grassmann.ThomSpaceConnected k m :=
  thomSpaceConnected_of_pieces PieceOverChartConnected.ofPieceConnectivity k m

end Work.ThomBordism
