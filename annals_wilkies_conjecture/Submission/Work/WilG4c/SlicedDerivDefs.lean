/-
  WilG4c / `SlicedDerivDefs` — the *fibre* (sliced) derivative vocabulary of BNZ §5.4.

  ## Why this file exists

  `SharpDeriv` controls only the **joint** `C^k`-locus of a family `f`
  (the locus of `famFunHat f` in `ℝ^{p+(n+1)}`), i.e. smoothness in the `p` parameter
  directions *and* the `n+1` cube directions simultaneously.  BNZ §5.4, on the other hand,
  needs the **fibre** locus: for the *slice* `z ↦ f l z` (the parameter `l` fixed) the set of
  cube points at which that slice is `C^k`.  The joint locus is contained in the fibre locus,
  and the inclusion is strict in general (e.g. `f l x = 1_{l≠0} + |x - 1/2|`: at `l = 0` the
  slice is `C¹` off the point `1/2` while the joint locus is empty on the whole line `l = 0`).

  `StepHigherPlan.md` §8 records the resulting gap in the §5.4 design: the near-maximising
  curves produced by `CurveFamAlpha_list_pure` (whose selection set uses the *joint* locus
  `AlLoc`) do not dominate the *fibre*-sup, and the surrogates of the pure-`y` composites along
  them are junk at parameters where the joint locus is thin.  Both defects are repaired by
  replacing the joint derivative graph `AlDgList` by the *slice* derivative graph
  `AlDgListSlice` defined here: it tests the fibre `C^{|L|}` condition and stores the honest
  *fibre* directional derivative.

  The `Ω`-definability of `AlDgListSlice`, with a format that is **uniform in `|L|`** and degree
  `b.eval ![D, |L|]`, is the one genuinely new ingredient §5.4 needs; it is the generalisation
  to `n+1` cube variables of the frozen statement `Work.WilG4a.CD.fibDerivGraph_mem` (whose
  design notes describe the strategy: cell decomposition of the ambient space, the joint
  derivative graph on the cells disjoint from the joint bad locus, and punctured limits
  (`punctured_contDiffAt`, `fibreLimitMem`, `fibreLimitEqMem`) plus a recursion on the number of
  parameters on the thin cells).

  Everything in this file is a definition or a trivial unfolding; it is `sorry`-free.
-/
import Mathlib
import Submission.Work.WilG4c.LipDefs
import Submission.Work.WilG4c.StepHigherDefs

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilkG4c

open WilkiesDesign WilkiesDesign.CG

/-! ## 1. Reading a point of `ℝ^{p+(n+1)}` as `(l, z)` -/

/-- The parameter `l` of a point of `ℝ^{p+(n+1)}` (its first `p` coordinates). -/
def parPt {p n : ℕ} (w : Fin (p + (n + 1)) → ℝ) : Fin p → ℝ :=
  fun i => w (Fin.castAdd (n + 1) i)

/-- The cube point `z` of a point of `ℝ^{p+(n+1)}` (its last `n+1` coordinates). -/
def cubePt {p n : ℕ} (w : Fin (p + (n + 1)) → ℝ) : Fin (n + 1) → ℝ :=
  fun j => w (Fin.natAdd p j)

@[simp] theorem parPt_apply {p n : ℕ} (w : Fin (p + (n + 1)) → ℝ) (i : Fin p) :
    parPt w i = w (Fin.castAdd (n + 1) i) := rfl

@[simp] theorem cubePt_apply {p n : ℕ} (w : Fin (p + (n + 1)) → ℝ) (j : Fin (n + 1)) :
    cubePt w j = w (Fin.natAdd p j) := rfl

theorem famFunHat_eq_parPt_cubePt {p n : ℕ} (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
    (w : Fin (p + (n + 1)) → ℝ) : famFunHat f w = f (parPt w) (cubePt w) := rfl

/-! ## 2. The sliced (fibre) derivative graph -/

/-- **The slice derivative graph.**  `AlDgListSlice p n f L` is the set of points
`z = (l, u, s) ∈ ℝ^{p+(n+1)+1}` such that the *slice* `y ↦ f l y` is `C^{|L|}` at the cube
point `u`, and `s` is its `|L|`-th directional derivative in the directions `L`.

This is `Work.WilkG4c.AlDgList p n f (liftDir L)` with the *joint* locus
`interior {w | ContDiffAt ℝ |L| (famFunHat f) w}` replaced by the *fibre* condition
`ContDiffAt ℝ |L| (fun y => f l y) u`, and with the derivative read on the fibre (the two agree
on the joint locus, but the fibre condition is strictly weaker). -/
def AlDgListSlice (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
    (L : List (Fin (n + 1))) : Set (Fin (p + (n + 1) + 1) → ℝ) :=
  {z | ContDiffAt ℝ L.length (fun y : Fin (n + 1) → ℝ => f (parPt (Fin.init z)) y)
        (cubePt (Fin.init z)) ∧
    z (Fin.last (p + (n + 1))) =
      iteratedFDeriv ℝ L.length (fun y : Fin (n + 1) → ℝ => f (parPt (Fin.init z)) y)
        (cubePt (Fin.init z)) (fun j => Pi.single (L.get j) 1)}

@[simp] theorem mem_AlDgListSlice {p n : ℕ}
    {f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ} {L : List (Fin (n + 1))}
    {z : Fin (p + (n + 1) + 1) → ℝ} :
    z ∈ AlDgListSlice p n f L ↔
      ContDiffAt ℝ L.length (fun y : Fin (n + 1) → ℝ => f (parPt (Fin.init z)) y)
        (cubePt (Fin.init z)) ∧
      z (Fin.last (p + (n + 1))) =
        iteratedFDeriv ℝ L.length (fun y : Fin (n + 1) → ℝ => f (parPt (Fin.init z)) y)
          (cubePt (Fin.init z)) (fun j => Pi.single (L.get j) 1) :=
  Iff.rfl

/-- The *fibre* `C^k` locus of the family `f`, as a subset of `ℝ^{p+(n+1)}`: the points
`(l, u)` at which the slice `y ↦ f l y` is `C^k` at `u`.  It is the projection (dropping the
last, value, coordinate) of the slice derivative graph. -/
def SliceLocus (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (k : ℕ) :
    Set (Fin (p + (n + 1)) → ℝ) :=
  {w | ContDiffAt ℝ k (fun y : Fin (n + 1) → ℝ => f (parPt w) y) (cubePt w)}

/-- The slice `C^k` locus is the projection of the slice derivative graph (in the sense that a
point `w` lies in `SliceLocus p n f k` iff `(w, s) ∈ AlDgListSlice p n f L` for some value `s`,
whenever `L` has length `k`). -/
theorem sliceLocus_iff_exists_mem {p n : ℕ}
    (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (L : List (Fin (n + 1)))
    (w : Fin (p + (n + 1)) → ℝ) :
    w ∈ SliceLocus p n f L.length ↔
      ∃ s : ℝ, Fin.snoc w s ∈ AlDgListSlice p n f L := by
  constructor
  · intro hw
    refine ⟨iteratedFDeriv ℝ L.length (fun y : Fin (n + 1) → ℝ => f (parPt w) y)
      (cubePt w) (fun j => Pi.single (L.get j) 1), ?_, ?_⟩
    · simpa [SliceLocus] using hw
    · simp [AlDgListSlice]
  · rintro ⟨s, hs⟩
    have h := (mem_AlDgListSlice.mp hs).1
    simpa [SliceLocus] using h

end Work.WilkG4c
