/-
Copyright: subproject `OROneRel` -- one-relator combinatorics.

# The reflection `(x, i) ↦ (x, -i)` of the window data of the `ℤ`-cover

The two-letter Freiheitssatz with the weight `-c` is the reflection of the one with the weight `c`:
the level graph of `-c` is the level graph of `c` with every level negated, and the reflection
`(x, i) ↦ (x, -i)` carries

* the walk of `u` at level `0` to the walk of `u` at level `0` (`decor_neg_zero`),
* the window `[lo, hi]` to `[-hi, -lo]` (`mem_winE_neg`),
* loop classes to loop classes (`coverClassAt_neg`), hence `winTree` to `winTree`, and
* the alphabet `winBeta Wt (-c) lo hi` to `winBeta (fun j => Wt (-j)) c (-hi) (-lo)`
  (`sigmaBeta`).

The reflection of the alphabet induces inverse isomorphisms `winReflectHom` / `winUnreflectHom` of
the free groups, which commute with the class maps `winRho` (`winRho_winReflectHom`,
`winRho_winUnreflectHom`) and carry the candidate roots `winRoot` to each other
(`winRoot_neg`, proved from `winRootList_neg` in `Submission/Work/OROneRel/winRootList_neg.lean`).

This file contains the definitions and the elementary (arithmetic and book-keeping) lemmas only; it
is a leaf module, so that the companions of the reduction can import it without importing the target.
-/
import Mathlib
import Submission.Work.OROneRel.winBasisDefs
import Submission.Work.OROneRel.decor_neg
import Submission.Work.OROneRel.MagnusGenDefs

namespace Work.OROneRel

universe u

variable {α : Type u}

/-! ## The reflection of an edge, of a symbol, and of a word -/

/-- The reflection of an edge of the level graph: `(x, i) ↦ (x, -i)`. -/
def reflEdge (e : α × ℤ) : α × ℤ := (e.1, -e.2)

@[simp] theorem reflEdge_invol (e : α × ℤ) : reflEdge (reflEdge e) = e := by
  rcases e with ⟨x, i⟩
  simp [reflEdge]

/-- The reflection of a decorated letter: `((x, i), b) ↦ ((x, -i), b)`. -/
def reflSym (p : (α × ℤ) × Bool) : (α × ℤ) × Bool := ((p.1.1, -p.1.2), p.2)

@[simp] theorem coverEdge_reflSym (p : (α × ℤ) × Bool) :
    coverEdge (reflSym p) = reflEdge (coverEdge p) := rfl

theorem reflSym_eq :
    (fun p : (α × ℤ) × Bool => (((p.1.1, -(p.1.2)) : α × ℤ), p.2)) = reflSym := by
  funext p
  rfl

/-- **The reflection of the decorated walk.**  Decorating a word by the negated weights `-c` at
level `0` is the reflection `((x, i), b) ↦ ((x, -i), b)` of decorating it by `c` at level `0`. -/
theorem decor_neg_zero (c : α → ℤ) (L : List (α × Bool)) :
    decor (fun a => -c a) 0 L = (decor c 0 L).map reflSym := by
  rw [decor_neg_aux c 0 L, reflSym_eq]
  simp only [neg_zero]

/-! ## The reflection of the loop classes and of the window -/

/-- **The loop class reflects.**  The loop class of the edge `e` for the weight `-c` is the loop
class of the reflected edge `reflEdge e` for the weight `c` and the reflected gauge
`j ↦ Wt (-j)`. -/
theorem coverClassAt_neg (Wt : ℤ → FreeGroup α) (c : α → ℤ) (e : α × ℤ) :
    coverClassAt Wt (fun a => -c a) e = coverClassAt (fun j => Wt (-j)) c (reflEdge e) := by
  rcases e with ⟨x, i⟩
  simp only [coverClassAt, gaugeMap_of, reflEdge]
  ring_nf

/-- The same identity read on the reflected edge. -/
theorem coverClassAt_reflEdge_neg (Wt : ℤ → FreeGroup α) (c : α → ℤ) (e : α × ℤ) :
    coverClassAt Wt (fun a => -c a) (reflEdge e) = coverClassAt (fun j => Wt (-j)) c e := by
  have h := coverClassAt_neg Wt c (reflEdge e)
  rw [reflEdge_invol] at h
  exact h

/-- **The window reflects.**  The edge `e` lies in the window `[lo, hi]` of the weight `-c` exactly
when the reflected edge `reflEdge e` lies in the window `[-hi, -lo]` of the weight `c`. -/
theorem mem_winE_neg {c : α → ℤ} {lo hi : ℤ} {e : α × ℤ} :
    e ∈ winE (fun a => -c a) lo hi ↔ reflEdge e ∈ winE c (-hi) (-lo) := by
  rcases e with ⟨x, i⟩
  simp only [reflEdge, mem_winE]
  constructor <;> intro h <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

/-- The same identity read on the reflected edge. -/
theorem mem_winE_reflEdge {c : α → ℤ} {lo hi : ℤ} {e : α × ℤ} :
    reflEdge e ∈ winE (fun a => -c a) lo hi ↔ e ∈ winE c (-hi) (-lo) := by
  rcases e with ⟨x, i⟩
  simp only [reflEdge, mem_winE]
  constructor <;> intro h <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

/-! ## The reflection of the alphabet of the vertex -/

/-- **The reflection of the vertex alphabet**: the non-tree edges of the window `[lo, hi]` of the
weight `-c` are the reflections of the non-tree edges of the window `[-hi, -lo]` of the weight `c`
and of the reflected gauge. -/
noncomputable def sigmaBeta (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ) :
    winBeta Wt (fun a => -c a) lo hi ≃ winBeta (fun j => Wt (-j)) c (-hi) (-lo) where
  toFun e := ⟨reflEdge e.1, (mem_winE_neg (c := c) (lo := lo) (hi := hi)).mp e.2.1,
    fun h => e.2.2 (by rw [coverClassAt_neg Wt c e.1]; exact h)⟩
  invFun f := ⟨reflEdge f.1, (mem_winE_reflEdge (c := c) (lo := lo) (hi := hi)).mpr f.2.1,
    fun h => f.2.2 (by rw [← coverClassAt_reflEdge_neg Wt c f.1]; exact h)⟩
  left_inv e := Subtype.ext (by simp [reflEdge])
  right_inv f := Subtype.ext (by simp [reflEdge])

@[simp] theorem sigmaBeta_val (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ)
    (e : winBeta Wt (fun a => -c a) lo hi) :
    (sigmaBeta Wt c lo hi e).1 = reflEdge e.1 := rfl

@[simp] theorem sigmaBeta_symm_val (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ)
    (f : winBeta (fun j => Wt (-j)) c (-hi) (-lo)) :
    ((sigmaBeta Wt c lo hi).symm f).1 = reflEdge f.1 := rfl

/-! ## The induced isomorphisms of the free groups -/

/-- The reflection homomorphism on the vertex free groups, induced by `sigmaBeta`. -/
noncomputable def winReflectHom (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ) :
    FreeGroup (winBeta Wt (fun a => -c a) lo hi) →*
      FreeGroup (winBeta (fun j => Wt (-j)) c (-hi) (-lo)) :=
  FreeGroup.lift fun e => FreeGroup.of (sigmaBeta Wt c lo hi e)

/-- The inverse of `winReflectHom`, again induced by the reflection `sigmaBeta`. -/
noncomputable def winUnreflectHom (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ) :
    FreeGroup (winBeta (fun j => Wt (-j)) c (-hi) (-lo)) →*
      FreeGroup (winBeta Wt (fun a => -c a) lo hi) :=
  FreeGroup.lift fun f => FreeGroup.of ((sigmaBeta Wt c lo hi).symm f)

theorem winUnreflect_winReflect (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ)
    (x : FreeGroup (winBeta Wt (fun a => -c a) lo hi)) :
    winUnreflectHom Wt c lo hi (winReflectHom Wt c lo hi x) = x := by
  have key : (winUnreflectHom Wt c lo hi).comp (winReflectHom Wt c lo hi) = MonoidHom.id _ := by
    refine FreeGroup.ext_hom _ _ fun e => ?_
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply, winReflectHom, winUnreflectHom,
      FreeGroup.lift_apply_of, Equiv.symm_apply_apply]
  simpa using DFunLike.congr_fun key x

theorem winReflect_winUnreflect (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ)
    (y : FreeGroup (winBeta (fun j => Wt (-j)) c (-hi) (-lo))) :
    winReflectHom Wt c lo hi (winUnreflectHom Wt c lo hi y) = y := by
  have key : (winReflectHom Wt c lo hi).comp (winUnreflectHom Wt c lo hi) = MonoidHom.id _ := by
    refine FreeGroup.ext_hom _ _ fun f => ?_
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply, winReflectHom, winUnreflectHom,
      FreeGroup.lift_apply_of, Equiv.apply_symm_apply]
  simpa using DFunLike.congr_fun key y

theorem winUnreflectHom_eq_map (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ) :
    winUnreflectHom Wt c lo hi = FreeGroup.map (fun f => (sigmaBeta Wt c lo hi).symm f) := by
  refine FreeGroup.ext_hom _ _ fun f => ?_
  simp only [winUnreflectHom, FreeGroup.lift_apply_of, FreeGroup.map.of]

theorem winReflectHom_eq_map (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ) :
    winReflectHom Wt c lo hi = FreeGroup.map (fun e => sigmaBeta Wt c lo hi e) := by
  refine FreeGroup.ext_hom _ _ fun e => ?_
  simp only [winReflectHom, FreeGroup.lift_apply_of, FreeGroup.map.of]

/-- `winUnreflectHom` on a word spelled by a list. -/
theorem winUnreflectHom_mk (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ)
    (L : List (winBeta (fun j => Wt (-j)) c (-hi) (-lo) × Bool)) :
    winUnreflectHom Wt c lo hi (FreeGroup.mk L)
      = FreeGroup.mk (L.map (fun p => ((sigmaBeta Wt c lo hi).symm p.1, p.2))) := by
  rw [winUnreflectHom_eq_map, FreeGroup.map.mk]

/-- The class map of the reflected vertex is the reflection of the class map. -/
theorem winRho_winReflectHom (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ)
    (x : FreeGroup (winBeta Wt (fun a => -c a) lo hi)) :
    winRho (fun j => Wt (-j)) c (-hi) (-lo) (winReflectHom Wt c lo hi x)
      = winRho Wt (fun a => -c a) lo hi x := by
  have key : (winRho (fun j => Wt (-j)) c (-hi) (-lo)).comp (winReflectHom Wt c lo hi)
      = winRho Wt (fun a => -c a) lo hi := by
    refine FreeGroup.ext_hom _ _ fun e => ?_
    simp only [MonoidHom.comp_apply, winReflectHom, FreeGroup.lift_apply_of, winRho_of,
      sigmaBeta_val]
    exact (coverClassAt_neg Wt c e.1).symm
  simpa using DFunLike.congr_fun key x

/-- The class map of the vertex is the reflection of the class map of the reflected vertex. -/
theorem winRho_winUnreflectHom (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ)
    (y : FreeGroup (winBeta (fun j => Wt (-j)) c (-hi) (-lo))) :
    winRho Wt (fun a => -c a) lo hi (winUnreflectHom Wt c lo hi y)
      = winRho (fun j => Wt (-j)) c (-hi) (-lo) y := by
  have key : (winRho Wt (fun a => -c a) lo hi).comp (winUnreflectHom Wt c lo hi)
      = winRho (fun j => Wt (-j)) c (-hi) (-lo) := by
    refine FreeGroup.ext_hom _ _ fun f => ?_
    simp only [MonoidHom.comp_apply, winUnreflectHom, FreeGroup.lift_apply_of, winRho_of,
      sigmaBeta_symm_val]
    exact coverClassAt_reflEdge_neg Wt c f.1
  simpa using DFunLike.congr_fun key y

/-! ## The reflection of the class `cohom` -/

/-- Negating the weights inverts the class: `cohom (-c) w = (cohom c w)⁻¹`. -/
theorem cohom_neg (c : α → ℤ) (w : FreeGroup α) :
    cohom (fun a => -c a) w = (cohom c w)⁻¹ := by
  induction w using FreeGroup.induction_on with
  | one => simp
  | of a => simp
  | inv_of a ih => simp [ih]
  | mul x y hx hy => simp [hx, hy, mul_comm]

end Work.OROneRel
