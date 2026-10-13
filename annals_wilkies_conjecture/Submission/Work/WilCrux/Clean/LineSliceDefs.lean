/-
  `Work.WilCrux.Clean.LineSliceDefs` — vocabulary for the line-slice lemma
  `Work.WilCrux.Clean.MonotonePiecesOnLine`.

  The target says: for a sharply o-minimal `S`, a format `F`, a degree `D` and a coordinate
  direction `i : Fin n`, there is *one* bound `K` such that for **every** `Ω F D (n+1)`-definable
  `H : ℝⁿ → ℝ` and **every** base point `w₁ : ℝⁿ`, the restriction
  `t ↦ H (w₁ + t • eᵢ)` is differentiable off, and monotone or antitone between, at most `K`
  break points.

  The reduction is to the one-variable statement `Work.WilCrux.UnifMonotonePieces`: the graph of
  the restriction is `Ω`-definable **with format and degree depending only on `n`, `F`, `D`**
  (never on `H` or on `w₁`).  This file fixes the geometry that makes that uniform definability
  work; the two membership/identification lemmas live in `LineSliceEq.lean`
  (`sliceGraph_eq`) and `LineSliceMem.lean` (`sliceLineSet_mem`).

  ## The description

  Working in `ℝ^{n+2}` with coordinates indexed by `Fin (n+2)`:

  * `sxIdx n j` (`j : Fin n`) is the `j`-th "space" coordinate `x j`;
  * `sYIdx n` is the value coordinate `y`;
  * `sTIdx n` is the coordinate `t` of the line parameter.

  `liftFirst 1 (graphOf H)` is `graphOf H` read on the first `n+1` coordinates, so a point `z` of
  `ℝ^{n+2}` is in it iff `(z (sxIdx n ·), z (sYIdx n)) ∈ graphOf H`.  The affine set
  `sliceLineSet n i w₁` imposes `z (sxIdx n j) = w₁ j + z (sTIdx n) · (if j = i then 1 else 0)`,
  i.e. exactly `x = w₁ + t • eᵢ`; this is a *polynomial* condition of degree `1` whose coefficients
  are the (arbitrary) coordinates of `w₁`, so `S.hyp` gives it a format and degree that do not see
  `w₁`.

  The two-coordinate selection `sliceCoord n` keeps `(t, y)`.  Then

  `coordImage (sliceCoord n) (liftFirst 1 (graphOf H) ∩ sliceLineSet n i w₁)`

  is the graph of the restriction — this is `sliceGraph_eq`.  The membership
  `sliceLineSet_mem` and `Work.WilG5.coordImage_mem` then give format and degree depending only on
  `n`, `F`, `D`.
-/
import Mathlib
import Submission.Work.Wilkies.Defs
import Submission.Work.WilG5.Basic
import Submission.Work.WilG5.Reindex3
import Submission.Work.WilG5.Reindex

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilCrux.Clean

open WilkiesDesign

/-! ## 1. The coordinates of the slicing space `ℝ^{n+2}` -/

/-- The index of the `j`-th "space" coordinate inside `Fin (n+2)`. -/
def sxIdx (n : ℕ) (j : Fin n) : Fin (n + 2) := Fin.castAdd 2 j

/-- The index of the line parameter `t` inside `Fin (n+2)`. -/
def sTIdx (n : ℕ) : Fin (n + 2) := Fin.last (n + 1)

/-- The index of the value coordinate `y` inside `Fin (n+2)`. -/
def sYIdx (n : ℕ) : Fin (n + 2) := Fin.castAdd 1 (Fin.last n)

/-- `sxIdx n j` is the `j`-th coordinate of the first `n+1` coordinates of `Fin (n+2)`. -/
theorem sxIdx_castAdd_castSucc (n : ℕ) (j : Fin n) :
    sxIdx n j = Fin.castAdd 1 (Fin.castSucc j) := Fin.ext rfl

/-- `sYIdx n` is the last coordinate of the first `n+1` coordinates of `Fin (n+2)`. -/
theorem sYIdx_castSucc (n : ℕ) : sYIdx n = Fin.castSucc (Fin.last n) := Fin.ext rfl

/-- The affine condition `x = w₁ + t • eᵢ` inside `ℝ^{n+2}`, one linear equation per coordinate. -/
def sliceLineSet (n : ℕ) (i : Fin n) (w₁ : Fin n → ℝ) : Set (Fin (n + 2) → ℝ) :=
  {z | ∀ j : Fin n, z (sxIdx n j) = w₁ j + z (sTIdx n) * (if j = i then (1 : ℝ) else 0)}

/-- The selection of the two coordinates `(t, y)` kept by the slice, in that order. -/
def sliceCoord (n : ℕ) : Fin 2 → Fin (n + 2) := fun l => if l = 0 then sTIdx n else sYIdx n

@[simp] theorem sliceCoord_zero (n : ℕ) : sliceCoord n 0 = sTIdx n := by
  simp [sliceCoord]

@[simp] theorem sliceCoord_one (n : ℕ) : sliceCoord n 1 = sYIdx n := by
  simp [sliceCoord]

/-- Reading `z ∘ sliceCoord` off the two coordinates. -/
theorem comp_sliceCoord_eq {n : ℕ} (z : Fin (n + 2) → ℝ) (u : Fin 2 → ℝ) :
    z ∘ sliceCoord n = u ↔ u 0 = z (sTIdx n) ∧ u 1 = z (sYIdx n) := by
  constructor
  · intro h
    exact ⟨(congrFun h 0).symm, (congrFun h 1).symm⟩
  · rintro ⟨h0, h1⟩
    funext l
    fin_cases l
    · simpa using h0.symm
    · simpa using h1.symm

/-- The line `w₁ + t • eᵢ`, coordinatewise. -/
theorem add_smul_single_apply {n : ℕ} (w₁ : Fin n → ℝ) (i : Fin n) (t : ℝ) :
    (w₁ + t • Pi.single i (1 : ℝ)) = fun j => w₁ j + t * (if j = i then 1 else 0) := by
  funext j
  simp [Pi.single_apply, smul_eq_mul]

end Work.WilCrux.Clean
