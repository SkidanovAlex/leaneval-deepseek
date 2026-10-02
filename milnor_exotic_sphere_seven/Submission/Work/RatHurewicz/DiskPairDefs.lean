import Mathlib
import Submission.Work.RatHurewicz.AttachCells

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The punctured model cell `D^{n+2} ∖ {0}`

The model cell of this area is `cellDisk n = D^{n+2} ⊆ ℝ^{n+2}`
(`Submission/Work/RatHurewicz/AttachCells.lean`), a closed ball, hence a *convex* subset of a real
normed space.  This module fixes the vocabulary of the pair

  `(cellDisk n, puncturedCellDisk n)`,  `puncturedCellDisk n = {y : cellDisk n | (y : ℝ^{n+2}) ≠ 0}`

together with the elementary convexity facts about the disc that every proof about it needs: the
straight-line combination `segComb`, its membership in the disc (`segComb_mem_disk`), and the
straight-line path `diskSegPath x y` joining two points of the disc, as a function of the second
endpoint (`diskSegPathRight`).

The target of the area is `Work.RatHurewicz.compressRel_cellDisk_compl_centre`: the pair
`(D^{n+2}, D^{n+2} ∖ {0})` is `(n+1)`-connected in compression form.
-/

open scoped Topology unitInterval

namespace Work.RatHurewicz

noncomputable section

/-- The ambient Euclidean space `ℝ^{n+2}` in which the model cell `D^{n+2}` lives. -/
abbrev CellVec (n : ℕ) : Type := EuclideanSpace ℝ (Fin (n + 2))

/-- **The punctured model cell** `D^{n+2} ∖ {0}`: the complement of the centre in the model cell. -/
def puncturedCellDisk (n : ℕ) : Set (cellDisk n) := {y | (y : CellVec n) ≠ 0}

@[simp] theorem mem_puncturedCellDisk {n : ℕ} {y : cellDisk n} :
    y ∈ puncturedCellDisk n ↔ (y : CellVec n) ≠ 0 := Iff.rfl

/-- The model cell `D^{n+2}` is convex (it is a closed ball). -/
theorem convex_diskSet (n : ℕ) : Convex ℝ (Metric.closedBall (0 : CellVec n) 1) :=
  convex_closedBall 0 1

/-- The straight-line combination `(1 - t) • x + t • y` of two points of `ℝ^{n+2}`. -/
def segComb (n : ℕ) (x y : CellVec n) (t : ℝ) : CellVec n := (1 - t) • x + t • y

@[simp] theorem segComb_zero (n : ℕ) (x y : CellVec n) : segComb n x y 0 = x := by
  simp [segComb]

@[simp] theorem segComb_one (n : ℕ) (x y : CellVec n) : segComb n x y 1 = y := by
  simp [segComb]

/-- **Convexity of the disc**: the straight line between two points of the disc stays in the disc. -/
theorem segComb_mem_disk {n : ℕ} {x y : CellVec n}
    (hx : x ∈ Metric.closedBall (0 : CellVec n) 1) (hy : y ∈ Metric.closedBall (0 : CellVec n) 1)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    segComb n x y t ∈ Metric.closedBall (0 : CellVec n) 1 := by
  have h := (convex_iff_add_mem.mp (convex_diskSet n)) hx hy
    (show (0 : ℝ) ≤ 1 - t by linarith) ht0 (show (1 - t) + t = 1 by ring)
  simpa [segComb] using h

@[simp] theorem segComb_zero_I (n : ℕ) (x y : CellVec n) :
    segComb n x y ((0 : I) : ℝ) = x := by
  rw [show ((0 : I) : ℝ) = 0 from rfl, segComb_zero]

@[simp] theorem segComb_one_I (n : ℕ) (x y : CellVec n) :
    segComb n x y ((1 : I) : ℝ) = y := by
  rw [show ((1 : I) : ℝ) = 1 from rfl, segComb_one]

@[simp] theorem segComb_self (n : ℕ) (x : CellVec n) (t : ℝ) : segComb n x x t = x := by
  rw [segComb, ← add_smul, show (1 - t) + t = 1 by ring, one_smul]

/-- `segComb` is continuous in all three variables. -/
theorem continuous_segComb_uncurried (n : ℕ) :
    Continuous fun p : CellVec n × CellVec n × ℝ => segComb n p.1 p.2.1 p.2.2 := by
  unfold segComb
  fun_prop

/-- `segComb` is continuous in all three variables, for continuous parameters. -/
theorem continuous_segComb {n : ℕ} {X : Type*} [TopologicalSpace X]
    {f g : X → CellVec n} {h : X → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hh : Continuous h) :
    Continuous fun x : X => segComb n (f x) (g x) (h x) := by
  unfold segComb
  fun_prop

/-- **The straight-line path of the model disc**: the convex combination of `x` and `y`. -/
def diskSegPath (n : ℕ) (x y : cellDisk n) : Path x y where
  toContinuousMap :=
    { toFun := fun t => ⟨segComb n (x : CellVec n) (y : CellVec n) (t : ℝ),
        segComb_mem_disk x.2 y.2 t.2.1 t.2.2⟩
      continuous_toFun := by
        refine Continuous.subtype_mk ?_ _
        exact continuous_segComb (X := I)
          (f := fun _ => (x : CellVec n)) (g := fun _ => (y : CellVec n))
          (h := fun t : I => (t : ℝ)) continuous_const continuous_const continuous_subtype_val }
  source' := by
    ext
    simp [segComb]
  target' := by
    ext
    simp [segComb]

@[simp] theorem diskSegPath_apply (n : ℕ) (x y : cellDisk n) (t : I) :
    ((diskSegPath n x y : C(I, cellDisk n)) t : CellVec n) = segComb n (x : CellVec n) (y : CellVec n) (t : ℝ) :=
  rfl

@[simp] theorem diskSegPath_zero (n : ℕ) (x y : cellDisk n) :
    (diskSegPath n x y : C(I, cellDisk n)) 0 = x := (diskSegPath n x y).source'

@[simp] theorem diskSegPath_one (n : ℕ) (x y : cellDisk n) :
    (diskSegPath n x y : C(I, cellDisk n)) 1 = y := (diskSegPath n x y).target'

/-- **The straight-line path depends continuously on its second endpoint.**  The map
`y ↦ diskSegPath x y`, as a map into the space of paths of the disc with the compact-open
topology (the space `PathSpace (cellDisk n) x` up to coercion). -/
def diskSegPathRight (n : ℕ) (x : cellDisk n) : C(cellDisk n, C(I, cellDisk n)) :=
  ContinuousMap.curry
    { toFun := fun p : cellDisk n × I =>
        ⟨segComb n (x : CellVec n) (p.1 : CellVec n) (p.2 : ℝ), by
          refine segComb_mem_disk x.2 p.1.2 p.2.2.1 p.2.2.2⟩
      continuous_toFun := by
        refine Continuous.subtype_mk ?_ _
        exact continuous_segComb (X := cellDisk n × I)
          (f := fun _ => (x : CellVec n)) (g := fun p => (p.1 : CellVec n))
          (h := fun p => (p.2 : ℝ)) continuous_const
          (continuous_subtype_val.comp continuous_fst)
          (continuous_subtype_val.comp continuous_snd) }

@[simp] theorem diskSegPathRight_apply (n : ℕ) (x y : cellDisk n) (t : I) :
    ((diskSegPathRight n x y : C(I, cellDisk n)) t : CellVec n)
      = segComb n (x : CellVec n) (y : CellVec n) (t : ℝ) :=
  rfl

theorem diskSegPathRight_coe (n : ℕ) (x : cellDisk n) (y : cellDisk n) :
    (diskSegPathRight n x y : C(I, cellDisk n)) = (diskSegPath n x y : C(I, cellDisk n)) :=
  ContinuousMap.ext fun _ => Subtype.ext rfl

end

end Work.RatHurewicz
