import Mathlib
import Submission.Work.RatHurewicz.DiskPairDefs
import Submission.Work.RatHurewicz.RelPiPathDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The homotopy fibre of the inclusion of the punctured cell is the punctured cell

Let `A = puncturedCellDisk n = D^{n+2} ∖ {0} ⊆ D^{n+2}` and `i = setIncl A`.  The homotopy fibre
of `i` at `a ∈ A` is the space

  `E_a = {(b, γ) : b ∈ A, γ a path in D^{n+2} from a to b}`.

Since the disc is convex, the projection `E_a → ↥A`, `(b, γ) ↦ b`, is a homotopy equivalence: its
section `b ↦ (b, straight line)` is a homotopy inverse, by the straight-line interpolation
`γ_r(s) = (1-r) · (segment a b)(s) + r · γ(s)` of the straight path and `γ` (all intermediate paths
run from `a` to `b` by convexity).  This is the geometric input that identifies the relative
homotopy groups of `(D^{n+2}, D^{n+2} ∖ {0})` with the homotopy groups of `D^{n+2} ∖ {0}`.
-/

set_option maxHeartbeats 1000000

open scoped Topology unitInterval
open ContinuousMap

namespace Work.RatHurewicz

noncomputable section

/-- The homotopy fibre of the inclusion of the punctured model cell into the model cell. -/
abbrev cellFibre (n : ℕ) (a : ↥(puncturedCellDisk n)) : Type :=
  homotopyFibre (setIncl (puncturedCellDisk n)) a

/-- The inclusion `↥A → D` of the two levels of subtypes, as a continuous map. -/
def puncturedToDisk (n : ℕ) : C(↥(puncturedCellDisk n), cellDisk n) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- The coercion `D → ℝ^{n+2}` as a continuous map. -/
def diskToVec (n : ℕ) : C(cellDisk n, CellVec n) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- The coercion `I → ℝ` as a continuous map. -/
def ItoReal : C(I, ℝ) := ⟨Subtype.val, continuous_subtype_val⟩

/-- The straight path from `a` to `b` inside the disc, as a point of the path space of the disc
based at `a`. -/
def secPath (n : ℕ) (a : ↥(puncturedCellDisk n)) :
    C(↥(puncturedCellDisk n), StemsB.PathSpace (cellDisk n) (setIncl (puncturedCellDisk n) a)) where
  toFun b := ⟨diskSegPathRight n (a : cellDisk n) (b : cellDisk n), by
    show (diskSegPathRight n (a : cellDisk n) (b : cellDisk n) : C(I, cellDisk n)) 0
      = setIncl (puncturedCellDisk n) a
    rw [diskSegPathRight_coe, diskSegPath_zero]
    rfl⟩
  continuous_toFun := Continuous.subtype_mk
    ((diskSegPathRight n (a : cellDisk n)).continuous.comp (puncturedToDisk n).continuous) _

/-- **The section** of the projection `E_a → ↥A`: `b ↦ (b, straight path from a to b)`. -/
def secFibre (n : ℕ) (a : ↥(puncturedCellDisk n)) : C(↥(puncturedCellDisk n), cellFibre n a) where
  toFun b := ⟨(b, secPath n a b), by
    show StemsB.evalOne (cellDisk n) (setIncl (puncturedCellDisk n) a) (secPath n a b)
      = setIncl (puncturedCellDisk n) b
    show ((secPath n a b).1 : C(I, cellDisk n)) 1 = (b : cellDisk n)
    show (diskSegPathRight n (a : cellDisk n) (b : cellDisk n) : C(I, cellDisk n)) 1
      = (b : cellDisk n)
    rw [diskSegPathRight_coe, diskSegPath_one]⟩
  continuous_toFun := Continuous.subtype_mk
    (Continuous.prodMk continuous_id (secPath n a).continuous) _

/-! ## The straight-line deformation of a point of the fibre to the straight path -/

/-- The straight path of the disc, as a continuous family of paths indexed by `(I × E_a) × I`. -/
def straightFamily (n : ℕ) (a : ↥(puncturedCellDisk n)) :
    C((I × cellFibre n a) × I, C(I, cellDisk n)) where
  toFun q := diskSegPathRight n (a : cellDisk n)
    (((q.1.2).1.1 : ↥(puncturedCellDisk n)) : cellDisk n)
  continuous_toFun := by
    have h : Continuous fun q : (I × cellFibre n a) × I =>
        (((q.1.2).1.1 : ↥(puncturedCellDisk n)) : cellDisk n) := by fun_prop
    exact (diskSegPathRight n (a : cellDisk n)).continuous.comp h

/-- The path component of a point of the fibre, as a continuous family of paths. -/
def curveFamily (n : ℕ) (a : ↥(puncturedCellDisk n)) :
    C((I × cellFibre n a) × I, C(I, cellDisk n)) where
  toFun q := fibreCM q.1.2
  continuous_toFun := by
    have h : Continuous fun q : (I × cellFibre n a) × I => (q.1.2 : cellFibre n a) :=
      continuous_snd.comp continuous_fst
    exact (fibreCMFamily a).continuous.comp h

/-- The straight path component, evaluated at a point of `(I × E_a) × I`. -/
def straightAt (n : ℕ) (a : ↥(puncturedCellDisk n)) (q : (I × cellFibre n a) × I) : cellDisk n :=
  straightFamily n a q q.2

/-- The path component of a point of the fibre, evaluated at a point of `(I × E_a) × I`. -/
def curveAt (n : ℕ) (a : ↥(puncturedCellDisk n)) (q : (I × cellFibre n a) × I) : cellDisk n :=
  curveFamily n a q q.2

@[simp] theorem straightAt_coe (n : ℕ) (a : ↥(puncturedCellDisk n))
    (q : (I × cellFibre n a) × I) :
    (straightAt n a q : CellVec n)
      = ((diskSegPathRight n (a : cellDisk n)
          (((q.1.2).1.1 : ↥(puncturedCellDisk n)) : cellDisk n)) q.2 : CellVec n) := rfl

@[simp] theorem curveAt_eq (n : ℕ) (a : ↥(puncturedCellDisk n))
    (q : (I × cellFibre n a) × I) : curveAt n a q = (fibreCM q.1.2) q.2 := rfl

theorem continuous_straightAt (n : ℕ) (a : ↥(puncturedCellDisk n)) :
    Continuous (straightAt n a) := by
  have h : Continuous fun q : (I × cellFibre n a) × I => (straightFamily n a q, q.2) :=
    (straightFamily n a).continuous.prodMk continuous_snd
  exact continuous_eval.comp h

theorem continuous_curveAt (n : ℕ) (a : ↥(puncturedCellDisk n)) :
    Continuous (curveAt n a) := by
  have h : Continuous fun q : (I × cellFibre n a) × I => (curveFamily n a q, q.2) :=
    (curveFamily n a).continuous.prodMk continuous_snd
  exact continuous_eval.comp h

/-- The straight line from `a` to `b`, evaluated at the point `0`, is `a`. -/
theorem straightAt_zero (n : ℕ) (a : ↥(puncturedCellDisk n)) (q : I × cellFibre n a) :
    (straightAt n a (q, 0) : CellVec n) = (a : CellVec n) := by
  rw [straightAt_coe, diskSegPathRight_apply, segComb_zero_I]

/-- The straight line from `a` to `b`, evaluated at the point `1`, is `b`. -/
theorem straightAt_one (n : ℕ) (a : ↥(puncturedCellDisk n)) (q : I × cellFibre n a) :
    (straightAt n a (q, 1) : CellVec n)
      = (((q.2).1.1 : ↥(puncturedCellDisk n)) : CellVec n) := by
  rw [straightAt_coe, diskSegPathRight_apply, segComb_one_I]

/-- The path component of a point of the fibre starts at `i a`. -/
theorem curveAt_zero (n : ℕ) (a : ↥(puncturedCellDisk n)) (q : I × cellFibre n a) :
    (curveAt n a (q, 0) : CellVec n) = (a : CellVec n) := by
  rw [curveAt_eq, fibreCM_zero]
  rfl

/-- The path component of a point of the fibre ends at the base point of that point. -/
theorem curveAt_one (n : ℕ) (a : ↥(puncturedCellDisk n)) (q : I × cellFibre n a) :
    (curveAt n a (q, 1) : CellVec n)
      = (((q.2).1.1 : ↥(puncturedCellDisk n)) : CellVec n) := by
  rw [curveAt_eq, fibreCM_one]
  rfl

/-- The straight-line interpolation, at the level of the ambient vector space. -/
def deformVec (n : ℕ) (a : ↥(puncturedCellDisk n)) : C((I × cellFibre n a) × I, CellVec n) where
  toFun q := segComb n (straightAt n a q) (curveAt n a q) (q.1.1 : ℝ)
  continuous_toFun :=
    continuous_segComb ((diskToVec n).continuous.comp (continuous_straightAt n a))
      ((diskToVec n).continuous.comp (continuous_curveAt n a))
      (ItoReal.continuous.comp (continuous_fst.comp continuous_fst))

/-- The straight-line interpolation, in the disc (convexity). -/
def deformCell (n : ℕ) (a : ↥(puncturedCellDisk n)) : C((I × cellFibre n a) × I, cellDisk n) where
  toFun q := ⟨deformVec n a q, by
    have h : (deformVec n a q : CellVec n)
        = segComb n (straightAt n a q) (curveAt n a q) (q.1.1 : ℝ) := rfl
    rw [h]
    exact segComb_mem_disk (straightAt n a q).2 (curveAt n a q).2 q.1.1.2.1 q.1.1.2.2⟩
  continuous_toFun := Continuous.subtype_mk (deformVec n a).continuous _

@[simp] theorem deformCell_coe (n : ℕ) (a : ↥(puncturedCellDisk n))
    (q : (I × cellFibre n a) × I) :
    (deformCell n a q : CellVec n) = segComb n (straightAt n a q) (curveAt n a q) (q.1.1 : ℝ) :=
  rfl

/-- The interpolated path, as a continuous map `(I × E_a) × I → D^{n+2}`. -/
def deformPath (n : ℕ) (a : ↥(puncturedCellDisk n)) : C(I × cellFibre n a, C(I, cellDisk n)) :=
  (deformCell n a).curry

theorem deformPath_apply (n : ℕ) (a : ↥(puncturedCellDisk n))
    (q : I × cellFibre n a) (s : I) :
    ((deformPath n a q : C(I, cellDisk n)) s : CellVec n)
      = segComb n (straightAt n a (q, s)) (curveAt n a (q, s)) (q.1 : ℝ) :=
  rfl

/-- The value at `0` of the interpolated path is `a`. -/
theorem deformPath_eval_zero (n : ℕ) (a : ↥(puncturedCellDisk n)) (q : I × cellFibre n a) :
    ((deformPath n a q : C(I, cellDisk n)) 0 : CellVec n) = (a : CellVec n) := by
  rw [deformPath_apply, straightAt_zero, curveAt_zero, segComb_self]

/-- The value at `1` of the interpolated path is the base point of the fibre point. -/
theorem deformPath_eval_one (n : ℕ) (a : ↥(puncturedCellDisk n)) (q : I × cellFibre n a) :
    ((deformPath n a q : C(I, cellDisk n)) 1 : CellVec n)
      = (((q.2).1.1 : ↥(puncturedCellDisk n)) : CellVec n) := by
  rw [deformPath_apply, straightAt_one, curveAt_one, segComb_self]

/-- The interpolated path as an element of the path space based at `i a`. -/
def deformPathSpace (n : ℕ) (a : ↥(puncturedCellDisk n)) :
    C(I × cellFibre n a, StemsB.PathSpace (cellDisk n) (setIncl (puncturedCellDisk n) a)) where
  toFun q := ⟨deformPath n a q, by
    apply Subtype.ext
    show (((deformPath n a q : C(I, cellDisk n)) 0 : cellDisk n) : CellVec n) = (a : CellVec n)
    exact deformPath_eval_zero n a q⟩
  continuous_toFun := Continuous.subtype_mk (deformPath n a).continuous _

/-- **The deformation of the fibre**: it moves each `(b, γ)` to `(b, straight path)`. -/
def deformF (n : ℕ) (a : ↥(puncturedCellDisk n)) : C(I × cellFibre n a, cellFibre n a) where
  toFun q := ⟨((q.2).1.1, deformPathSpace n a q), by
    show StemsB.evalOne (cellDisk n) (setIncl (puncturedCellDisk n) a) (deformPathSpace n a q)
      = setIncl (puncturedCellDisk n) ((q.2).1.1)
    show ((deformPathSpace n a q).1 : C(I, cellDisk n)) 1
      = setIncl (puncturedCellDisk n) ((q.2).1.1)
    apply Subtype.ext
    show (((deformPath n a q : C(I, cellDisk n)) 1 : cellDisk n) : CellVec n)
      = (((q.2).1.1 : ↥(puncturedCellDisk n)) : CellVec n)
    exact deformPath_eval_one n a q⟩
  continuous_toFun := Continuous.subtype_mk
    (Continuous.prodMk
      ((homotopyFibreFst (setIncl (puncturedCellDisk n)) a).continuous.comp continuous_snd)
      (deformPathSpace n a).continuous) _

/-! ## The two endpoint computations of the deformation -/

theorem deformPath_zero (n : ℕ) (a : ↥(puncturedCellDisk n)) (p : cellFibre n a) :
    deformPath n a (0, p)
      = (diskSegPathRight n (a : cellDisk n) (p.1.1) : C(I, cellDisk n)) := by
  refine ContinuousMap.ext fun s => Subtype.ext ?_
  show ((deformPath n a (0, p) : C(I, cellDisk n)) s : CellVec n)
    = ((diskSegPathRight n (a : cellDisk n) (p.1.1) : C(I, cellDisk n)) s : CellVec n)
  rw [deformPath_apply]
  show segComb n (straightAt n a (((0 : I), p), s)) (curveAt n a (((0 : I), p), s))
      ((0 : I) : ℝ)
    = ((diskSegPathRight n (a : cellDisk n) (p.1.1) : C(I, cellDisk n)) s : CellVec n)
  rw [segComb_zero_I, straightAt_coe, diskSegPathRight_apply]

theorem deformPath_one (n : ℕ) (a : ↥(puncturedCellDisk n)) (p : cellFibre n a) :
    deformPath n a (1, p) = (p.1.2.1 : C(I, cellDisk n)) := by
  refine ContinuousMap.ext fun s => Subtype.ext ?_
  show ((deformPath n a (1, p) : C(I, cellDisk n)) s : CellVec n)
    = ((p.1.2.1 : C(I, cellDisk n)) s : CellVec n)
  rw [deformPath_apply]
  show segComb n (straightAt n a (((1 : I), p), s)) (curveAt n a (((1 : I), p), s))
      ((1 : I) : ℝ)
    = ((p.1.2.1 : C(I, cellDisk n)) s : CellVec n)
  rw [segComb_one_I, curveAt_eq]
  rfl

theorem deformF_zero (n : ℕ) (a : ↥(puncturedCellDisk n)) (p : cellFibre n a) :
    deformF n a (0, p)
      = secFibre n a (homotopyFibreFst (setIncl (puncturedCellDisk n)) a p) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    exact deformPath_zero n a p

theorem deformF_one (n : ℕ) (a : ↥(puncturedCellDisk n)) (p : cellFibre n a) :
    deformF n a (1, p) = p := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    exact deformPath_one n a p

/-- The straight-line deformation is a homotopy from the composite `section ∘ projection` to the
identity of the homotopy fibre. -/
def fibreHomotopy (n : ℕ) (a : ↥(puncturedCellDisk n)) :
    ((secFibre n a).comp (homotopyFibreFst (setIncl (puncturedCellDisk n)) a)).Homotopy
      (ContinuousMap.id (cellFibre n a)) :=
  ContinuousMap.Homotopy.mk (deformF n a)
    (fun p => deformF_zero n a p)
    (fun p => deformF_one n a p)

/-- **The homotopy fibre of the inclusion of the punctured model cell at `a` is homotopy
equivalent to the punctured model cell.** -/
theorem fibre_puncturedDisk_homotopyEquiv (n : ℕ) (a : ↥(puncturedCellDisk n)) :
    Nonempty (ContinuousMap.HomotopyEquiv (cellFibre n a) ↥(puncturedCellDisk n)) :=
  ⟨{ toFun := homotopyFibreFst (setIncl (puncturedCellDisk n)) a
     invFun := secFibre n a
     left_inv := ⟨fibreHomotopy n a⟩
     right_inv := by
       show ((homotopyFibreFst (setIncl (puncturedCellDisk n)) a).comp (secFibre n a)).Homotopic
         (ContinuousMap.id ↥(puncturedCellDisk n))
       rw [show (homotopyFibreFst (setIncl (puncturedCellDisk n)) a).comp (secFibre n a)
          = ContinuousMap.id ↥(puncturedCellDisk n) from rfl] }⟩

end

end Work.RatHurewicz
