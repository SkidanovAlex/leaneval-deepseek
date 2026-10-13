/-
  Infrastructure for `Work.WilCrux.graph_representation`: the bookkeeping for peeling one
  level off a cylindrical cell.

  A type word `w = Fin.snoc w' t` is the word of a cell whose top level is a graph (`t = graph`)
  or a band (`t = band`) over the cell of the lower word `w'`.  This file collects the `Nat`
  identities and the index reindexings that relate the band/graph coordinate spaces of `w` to
  those of `w'`, together with the "pair" maps of the band case.
-/
import Mathlib
import Submission.Work.WilCrux.SheetDefs

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilCrux

open WilkiesDesign

/-! ## 0. The `Nat` bookkeeping of `nBand`/`nGraph` under `Fin.snoc` -/

@[simp] theorem nBand_snoc_graph (N : ℕ) (w' : Fin N → CellType) :
    nBand (N + 1) (Fin.snoc w' CellType.graph) = nBand N w' := by
  rw [nBand_succ]; simp

@[simp] theorem nGraph_snoc_graph (N : ℕ) (w' : Fin N → CellType) :
    nGraph (N + 1) (Fin.snoc w' CellType.graph) = nGraph N w' + 1 := by
  rw [nGraph_succ]; simp

@[simp] theorem nBand_snoc_band (N : ℕ) (w' : Fin N → CellType) :
    nBand (N + 1) (Fin.snoc w' CellType.band) = nBand N w' + 1 := by
  rw [nBand_succ]; simp

@[simp] theorem nGraph_snoc_band (N : ℕ) (w' : Fin N → CellType) :
    nGraph (N + 1) (Fin.snoc w' CellType.band) = nGraph N w' := by
  rw [nGraph_succ]; simp

/-! ## 1. The graph case: the band coordinate space is unchanged -/

/-- Read a band coordinate vector of `Fin.snoc w' graph` as one of `w'`. -/
def resG (m N : ℕ) (w' : Fin N → CellType)
    (v : Fin (m + nBand (N + 1) (Fin.snoc w' CellType.graph)) → ℝ) : Fin (m + nBand N w') → ℝ :=
  fun i => v (Fin.cast (congrArg (Nat.add m) (nBand_snoc_graph N w').symm) i)

/-- Read a band coordinate vector of `w'` as one of `Fin.snoc w' graph`. -/
def liftG (m N : ℕ) (w' : Fin N → CellType)
    (v : Fin (m + nBand N w') → ℝ) :
    Fin (m + nBand (N + 1) (Fin.snoc w' CellType.graph)) → ℝ :=
  fun j => v (Fin.cast (congrArg (Nat.add m) (nBand_snoc_graph N w')) j)

/-- Read a graph coordinate vector of `Fin.snoc w' graph` as one of `w'` together with the
top level (last). -/
def liftUg (N : ℕ) (w' : Fin N → CellType) (u : Fin (nGraph N w' + 1) → ℝ) :
    Fin (nGraph (N + 1) (Fin.snoc w' CellType.graph)) → ℝ :=
  fun k => u (Fin.cast (nGraph_snoc_graph N w') k)

/-! ## 2. The band case: one extra band coordinate (the last one) -/

/-- Drop the last (top-level) band coordinate of `Fin.snoc w' band`. -/
def resB (m N : ℕ) (w' : Fin N → CellType)
    (v : Fin (m + nBand (N + 1) (Fin.snoc w' CellType.band)) → ℝ) : Fin (m + nBand N w') → ℝ :=
  fun i => v (Fin.cast (congrArg (Nat.add m) (nBand_snoc_band N w').symm) (Fin.castSucc i))

/-- The last (top-level) band coordinate of `Fin.snoc w' band`. -/
def lastB (m N : ℕ) (w' : Fin N → CellType)
    (v : Fin (m + nBand (N + 1) (Fin.snoc w' CellType.band)) → ℝ) : ℝ :=
  v (Fin.cast (congrArg (Nat.add m) (nBand_snoc_band N w').symm) (Fin.last (m + nBand N w')))

/-- Add a last (top-level) band coordinate to a vector of `w'`. -/
def mkB (m N : ℕ) (w' : Fin N → CellType) (vw : (Fin (m + nBand N w') → ℝ) × ℝ) :
    Fin (m + nBand (N + 1) (Fin.snoc w' CellType.band)) → ℝ :=
  fun j => (Fin.snoc (α := fun _ => ℝ) vw.1 vw.2)
    (Fin.cast (congrArg (Nat.add m) (nBand_snoc_band N w')) j)

/-- Read a graph coordinate vector of `w'` as one of `Fin.snoc w' band`. -/
def liftUb (N : ℕ) (w' : Fin N → CellType) (u : Fin (nGraph N w') → ℝ) :
    Fin (nGraph (N + 1) (Fin.snoc w' CellType.band)) → ℝ :=
  fun k => u (Fin.cast (nGraph_snoc_band N w') k)

end Work.WilCrux
