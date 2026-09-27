import Mathlib
import Submission.Work.EKLC6Core.CellWDefs
import Submission.Work.EKLC6Core.CellBaseCore
import Submission.Work.EKLC6Core.cell_facts_of_base
import Submission.Work.EKLC6Core.shape_uball_base

/-!
# `Work.EKLC6Core.cellW_atom_shape`

The atom/shape/margin facts for the *usable* cell system `Work.EKLC6Core.CellW`
(`Work.EKLC6Core.CellWDefs`): for `y` a **free** point (`Stab_U y = {1}`) of the `k`-th cell,

* the atom of `MSigW S O = σ(Q k, genCW S O k m)` through `y` is the piece of the `U`-orbit of
  the lift `liftW S k y` cut out by the lifted ball of the cell and intersected with the cell;
* the shape `{u ∈ U | u • y ∈ [y]}` is the trace on `U` of an open set of `SL₃(ℝ)`;
* the shape is contained in a fixed `U`-ball `Uball U ρ`, `ρ > 0`.

## Proof

`CellW` and `CellBase` (`Work.EKLC6Core.PlaqueCellDefs`) have *literally the same fields* in the
same order — `Q, hopen, hdisj, hcover, δ, hδpos, hδsmall, g, hsub, hinj` — so a `CellW` is a raw
cell family and the transport `CellW.toCellBase` below is the identity on the data.  With that
transport the definitions match *definitionally*:

* `genCW S O k m = genC2 U S.Q S.δ S.g O k m`,
* `MSigW S O = MSig2 U S.Q S.δ S.g O`,
* `liftW S k y = lift2 S.toCellBase k y`,

so the three clauses are exactly

* `Work.EKLC6Core.atom_MSig2_self` (in `CellBaseCore`) — atoms of `MSig2` inside a cell are
  `U`-orbit pieces cut by the lifted ball;
* `Work.EKLC6Core.shape_open_of_base` (in `cell_facts_of_base`) — the shape at a free point is
  the trace on `U` of an open set;
* `Work.EKLC6Core.shape_uball_base` (in `shape_uball_base`) — the shape at a free point lies in
  `Uball U 1`,

each applied to `S.toCellBase`.  No measurability of the clipped generators is used for the atom
identity (it is only ever applied to cells and clipped cylinders, both of which are in the
generating family, by the pointwise description
`Work.EKLC6Core.atomMSig_mem_atom_generateFrom` of atoms of a generated `σ`-algebra); the shape
statements use neither `hmeas` nor the covering/disjointness of the cell family beyond `hopen`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal Pointwise

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

variable {μ : MeasureTheory.Measure X3} {U : Subgroup SL3}

/-- **The transport `CellW → CellBase`**: the usable cell system is a raw cell family (the two
structures have the same fields, and none of the `CellW` hypotheses is a datum of `CellBase`). -/
def CellW.toCellBase (S : CellW μ U) : CellBase μ U where
  Q := S.Q
  hopen := S.hopen
  hdisj := S.hdisj
  hcover := S.hcover
  δ := S.δ
  hδpos := S.hδpos
  hδsmall := S.hδsmall
  g := S.g
  hsub := S.hsub
  hinj := S.hinj

/-- The clipped cylinder generator of `CellW` is the clipped generator of the transported raw
cell family. -/
theorem genCW_toCellBase (S : CellW μ U) (O : ℕ → Set SL3) (k m : ℕ) :
    genCW S O k m = genC2 U S.Q S.δ S.g O k m := rfl

/-- The `σ`-algebra of `CellW` is the `σ`-algebra of the transported raw cell family. -/
theorem MSigW_toCellBase (S : CellW μ U) (O : ℕ → Set SL3) :
    MSigW S O = MSig2 U S.Q S.δ S.g O := rfl

/-- The lift of `CellW` is the lift of the transported raw cell family. -/
theorem liftW_toCellBase (S : CellW μ U) (k : ℕ) (y : X3) :
    liftW S k y = lift2 S.toCellBase k y := rfl

/-- **The atom/shape/boundedness facts for the usable cell system.**  At a free point of a cell:
the atom of `MSigW S O` is the `U`-orbit piece of the lift cut by the lifted ball, the shape is
the trace on `U` of an open set of `SL₃(ℝ)`, and the shape lies in a fixed `U`-ball. -/
theorem cellW_atom_shape {μ : MeasureTheory.Measure Work.EKLContract.X3}
    {U : Subgroup Work.EKLContract.SL3} (S : Work.EKLC6Core.CellW μ U)
    (O : ℕ → Set Work.EKLContract.SL3)
    (hOsep : ∀ g g' : Work.EKLContract.SL3,
      (∀ m, (∃ u ∈ U, u * g ∈ O m) ↔ (∃ u ∈ U, u * g' ∈ O m)) → ∃ u ∈ U, g' = u * g)
    (hmeas : ∀ k m, MeasurableSet (Work.EKLC6Core.genCW S O k m)) :
    (∀ (k : ℕ) (y : Work.EKLContract.X3), y ∈ S.Q k →
        (∀ u ∈ U, u • y = y → u = 1) →
        Work.EKLContract.atom (Work.EKLC6Core.MSigW S O) y =
          Work.EKLContract.mkX '' ({g : Work.EKLContract.SL3 |
              ∃ u ∈ U, g = u * Work.EKLC6Core.liftW S k y}
            ∩ Work.EKLC6Core.lifted (S.δ k) (S.g k)) ∩ S.Q k) ∧
    (∀ (k : ℕ) (y : Work.EKLContract.X3), y ∈ S.Q k →
        (∀ u ∈ U, u • y = y → u = 1) →
        ∃ W : Set Work.EKLContract.SL3, IsOpen W ∧
          Work.EKLContract.shape (Work.EKLC6Core.MSigW S O) U y =
            W ∩ (U : Set Work.EKLContract.SL3)) ∧
    (∀ (k : ℕ) (y : Work.EKLContract.X3), y ∈ S.Q k →
        (∀ u ∈ U, u • y = y → u = 1) →
        ∃ ρ : ℝ, 0 < ρ ∧ Work.EKLContract.shape (Work.EKLC6Core.MSigW S O) U y ⊆
          Work.EKLComp.Uball U ρ) := by
  refine ⟨?_, ?_, ?_⟩
  · -- the atom identity: the transported atom theorem of the raw cell family
    intro k y hy _hfree
    exact atom_MSig2_self S.toCellBase O hOsep hmeas hy
  · -- the shape is the trace on `U` of an open set
    intro k y hy hfree
    exact shape_open_of_base S.toCellBase O hOsep hmeas hy hfree
  · -- the shape is contained in a fixed `U`-ball
    intro k y hy hfree
    obtain ⟨ρ, hρpos, hρ⟩ := shape_uball_base S.toCellBase O hOsep
    exact ⟨ρ, hρpos, hρ k y hy hfree⟩

end Work.EKLC6Core
