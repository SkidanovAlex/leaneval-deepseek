/-
  `Work.WilCruxN` — vocabulary for the clean re-proof of node N1 (`IsolatedSheet`).

  A cell `κ ⊆ ℝ^{m+N}` of a sharp cylindrical decomposition which lies over an open base cell
  `C₀ ⊆ ℝ^m` is the graph of a continuous map over its *band coordinates*: the coordinates of
  the ambient space selected by the `N` levels of its type word which are *bands*.  The levels
  which are *graphs* are then functions of the band coordinates.

  This file collects the small coordinate API shared by the pieces of the proof of
  `Work.WilCruxN.IsolatedSheetClean`:

  * `bandProj w` — the projection to the parameters and the band coordinates;
  * `graphProj w` — the projection to the graph coordinates (the graph values, no parameters);
  * `bandImg w κ` — the image of `κ` under `bandProj w` (the "open base" of the sheet);
  * `comp_selBandGraph` — the coordinate selection `selBandGraph` of `SheetDefs`, which is
    exactly `bandProj` followed by one graph coordinate, read as a `Fin.snoc`.

  Everything here is `sorry`-free; this module is imported by the delegations and by
  `Work.WilCruxN.IsolatedSheetClean`.
-/
import Mathlib
import Submission.Work.WilCrux.SheetDefs

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilCruxN

open Work.WilCrux

/-- `Fin.snoc` with the codomain pinned to `ℝ`, avoiding dependent-type inference issues. -/
abbrev snocR {n : ℕ} (p : Fin n → ℝ) (x : ℝ) : Fin (n + 1) → ℝ := Fin.snoc p x

@[simp] theorem snocR_castSucc {n : ℕ} (p : Fin n → ℝ) (x : ℝ) (i : Fin n) :
    snocR p x (Fin.castSucc i) = p i := by simp [snocR]

@[simp] theorem snocR_last {n : ℕ} (p : Fin n → ℝ) (x : ℝ) : snocR p x (Fin.last n) = x := by
  simp [snocR]

theorem snocR_init {n : ℕ} (p : Fin n → ℝ) (x : ℝ) : Fin.init (snocR p x) = p := by
  simp [snocR]

@[simp] theorem snocR_castAdd {n : ℕ} (p : Fin n → ℝ) (x : ℝ) (i : Fin n) :
    snocR p x (Fin.castAdd 1 i) = p i := by
  rw [show Fin.castAdd 1 i = Fin.castSucc i from rfl, snocR_castSucc]

/-! ## 1. The band and graph coordinate projections attached to a type word -/

/-- The projection of a point of `ℝ^{m+N}` to its parameters and its band coordinates, the band
coordinates being read in increasing level order. -/
def bandProj {m N : ℕ} (w : Fin N → CellType) (z : Fin (m + N) → ℝ) :
    Fin (m + nBand N w) → ℝ :=
  fun k => z (selBand m w k)

/-- The graph values of a point of `ℝ^{m+N}`, read in increasing level order. -/
def graphProj {m N : ℕ} (w : Fin N → CellType) (z : Fin (m + N) → ℝ) :
    Fin (nGraph N w) → ℝ :=
  fun l => z (Fin.natAdd m (graphIdx w l))

@[simp] theorem bandProj_castAdd {m N : ℕ} (w : Fin N → CellType) (z : Fin (m + N) → ℝ)
    (i : Fin m) : bandProj w z (Fin.castAdd (nBand N w) i) = z (Fin.castAdd N i) := by
  simp [bandProj]

@[simp] theorem bandProj_natAdd {m N : ℕ} (w : Fin N → CellType) (z : Fin (m + N) → ℝ)
    (k : Fin (nBand N w)) : bandProj w z (Fin.natAdd m k) = z (Fin.natAdd m (bandIdx w k)) := by
  simp [bandProj]

@[simp] theorem graphProj_apply {m N : ℕ} (w : Fin N → CellType) (z : Fin (m + N) → ℝ)
    (l : Fin (nGraph N w)) : graphProj w z l = z (Fin.natAdd m (graphIdx w l)) := rfl

/-- The image of `κ` under the band projection: the set of parameters carrying a point of `κ`,
with the band coordinates of that point.  This is the base of the graph sheet. -/
def bandImg {m N : ℕ} (w : Fin N → CellType) (κ : Set (Fin (m + N) → ℝ)) :
    Set (Fin (m + nBand N w) → ℝ) :=
  {v | ∃ z ∈ κ, v = bandProj w z}

theorem mem_bandImg {m N : ℕ} {w : Fin N → CellType} {κ : Set (Fin (m + N) → ℝ)}
    {v : Fin (m + nBand N w) → ℝ} : v ∈ bandImg w κ ↔ ∃ z ∈ κ, bandProj w z = v := by
  unfold bandImg
  constructor
  · rintro ⟨z, hz, h⟩; exact ⟨z, hz, h.symm⟩
  · rintro ⟨z, hz, h⟩; exact ⟨z, hz, h.symm⟩

theorem bandImg_mono {m N : ℕ} {w : Fin N → CellType} {κ κ' : Set (Fin (m + N) → ℝ)}
    (h : κ ⊆ κ') : bandImg w κ ⊆ bandImg w κ' :=
  fun _ ⟨z, hz, hv⟩ => ⟨z, h hz, hv⟩

theorem bandImg_nonempty {m N : ℕ} {w : Fin N → CellType} {κ : Set (Fin (m + N) → ℝ)}
    (h : κ.Nonempty) : (bandImg w κ).Nonempty := by
  obtain ⟨z, hz⟩ := h
  exact ⟨bandProj w z, z, hz, rfl⟩

/-! ## 2. Reading `selBandGraph` as `bandProj` followed by one graph coordinate -/

/-- The coordinate selection `selBandGraph m w j` (parameters, band coordinates, and the
`j`-th graph coordinate placed last) is `Fin.snoc` of the band projection and that graph
coordinate. -/
theorem comp_selBandGraph {m N : ℕ} (w : Fin N → CellType) (j : Fin (nGraph N w))
    (z : Fin (m + N) → ℝ) :
    z ∘ selBandGraph m w j =
      snocR (z ∘ selBand m w) (z (Fin.natAdd m (graphIdx w j))) := by
  funext i
  refine Fin.addCases
    (motive := fun i => (z ∘ selBandGraph m w j) i =
      snocR (z ∘ selBand m w) (z (Fin.natAdd m (graphIdx w j))) i) ?_ ?_ i
  · intro i'
    simp only [Function.comp_apply, selBandGraph_castAdd, snocR_castAdd]
  · intro i'
    have hlast : Fin.natAdd (m + nBand N w) i' = Fin.last (m + nBand N w) :=
      Fin.ext (by simp [Fin.natAdd, Fin.last])
    rw [hlast, Function.comp_apply, selBandGraph_last, snocR_last]

/-- The same statement with the two projections named. -/
theorem comp_selBandGraph' {m N : ℕ} (w : Fin N → CellType) (j : Fin (nGraph N w))
    (z : Fin (m + N) → ℝ) :
    z ∘ selBandGraph m w j = snocR (bandProj w z) (graphProj w z j) :=
  comp_selBandGraph w j z

end Work.WilCruxN
