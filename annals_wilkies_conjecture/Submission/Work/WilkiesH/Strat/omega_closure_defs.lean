import Mathlib
import Submission.Work.WilkiesH.Strat.Defs
import Submission.Work.WilkiesH.Omega.omega_poly_lt
import Submission.Work.WilG5.Reindex3
import Submission.Work.WilG0.API

/-!
# Closure of an `Ω`-set: shared vocabulary

We express the (topological) closure of a set `W ⊆ ℝⁿ` as the complement of the set of
points admitting a ball disjoint from `W`:

`closure W = (⋃_{t>0} {x | ball(x,t) ∩ W = ∅})ᶜ`,

and the set on the right is a projection of a first-order `Ω`-definable set.  The joint set
lives in `ℝ^(n + (n+1))`: the first `n` coordinates carry the *witness* `y ∈ W`, the next
`n` carry the point `x` and the last one the radius `t`.  All the coordinates are read off by

* `yIdx n i = i`            (first `n` coordinates, the witness),
* `xIdx n i = n + i`        (coordinates `n … 2n-1`, the point),
* `tIdx n   = 2n`           (the last coordinate, the radius),

and the `Ω`-definability of the joint set rests on the strict polynomial inequality
`(x i - y i)² < t²`, available as `Work.WilkiesH.Omega.omega_poly_lt`.
-/

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilkiesH.Strat

open WilkiesDesign WilkiesConjecture

/-! ## The coordinate indices -/

/-- The witness coordinate `y i` of the joint space `ℝ^(n + (n+1))`. -/
def yIdx (n : ℕ) (i : Fin n) : Fin (n + (n + 1)) := Fin.castAdd (n + 1) i

/-- The point coordinate `x i` of the joint space. -/
def xIdx (n : ℕ) (i : Fin n) : Fin (n + (n + 1)) := Fin.natAdd n (Fin.castAdd 1 i)

/-- The radius coordinate `t` of the joint space. -/
def tIdx (n : ℕ) : Fin (n + (n + 1)) := Fin.natAdd n (Fin.last n)

@[simp] lemma yIdx_val (n : ℕ) (i : Fin n) : (yIdx n i).val = i.val := rfl

@[simp] lemma xIdx_val (n : ℕ) (i : Fin n) : (xIdx n i).val = n + i.val := rfl

@[simp] lemma tIdx_val (n : ℕ) : (tIdx n).val = n + n := rfl

/-- The polynomial `(x i - y i)² - t²` on the joint space. -/
def boxPoly (n : ℕ) (i : Fin n) : MvPolynomial (Fin (n + (n + 1))) ℝ :=
  (MvPolynomial.X (xIdx n i) - MvPolynomial.X (yIdx n i)) ^ 2 - MvPolynomial.X (tIdx n) ^ 2

lemma boxPoly_totalDegree_le (n : ℕ) (i : Fin n) : (boxPoly n i).totalDegree ≤ 2 := by
  rw [boxPoly, pow_two, pow_two]
  refine le_trans (Work.WilG5.td_sub_le _ _) (max_le ?_ ?_)
  · refine le_trans (Work.WilG5.td_mul_le _ _) ?_
    have h : (MvPolynomial.X (xIdx n i) - MvPolynomial.X (yIdx n i) :
        MvPolynomial (Fin (n + (n + 1))) ℝ).totalDegree ≤ 1 :=
      le_trans (Work.WilG5.td_sub_le _ _)
        (max_le (Work.WilG5.td_X_le _) (Work.WilG5.td_X_le _))
    omega
  · refine le_trans (Work.WilG5.td_mul_le _ _) ?_
    have h : (MvPolynomial.X (tIdx n) : MvPolynomial (Fin (n + (n + 1))) ℝ).totalDegree ≤ 1 :=
      Work.WilG5.td_X_le _
    omega

@[simp] lemma boxPoly_eval (n : ℕ) (i : Fin n) (z : Fin (n + (n + 1)) → ℝ) :
    (boxPoly n i).eval z = (z (xIdx n i) - z (yIdx n i)) ^ 2 - (z (tIdx n)) ^ 2 := by
  simp [boxPoly]

/-! ## The joint set -/

/-- The `i`-th "box" condition `(x i - y i)² < t²`, as an `Ω`-set on the joint space. -/
def boxSet (n : ℕ) (i : Fin n) : Set (Fin (n + (n + 1)) → ℝ) :=
  {z | (boxPoly n i).eval z < 0}

/-- `{z : 0 < z j}`: the positivity of one coordinate. -/
def posSet (N : ℕ) (j : Fin N) : Set (Fin N → ℝ) := {z | 0 < z j}

/-- The joint set: `y ∈ W`, every box condition holds, and `t > 0`, in `ℝ^(n + (n+1))`. -/
def jointSet {n : ℕ} (W : Set (Fin n → ℝ)) : Set (Fin (n + (n + 1)) → ℝ) :=
  Work.WilG5.coordPre (yIdx n) W ∩ (⋂ i : Fin n, boxSet n i) ∩ posSet (n + (n + 1)) (tIdx n)

/-- The `t`-fattening of `W`: points within (squared) distance `< t²` of a point of `W`. -/
def fatSet {n : ℕ} (W : Set (Fin n → ℝ)) (t : ℝ) : Set (Fin n → ℝ) :=
  {x | ∃ y, y ∈ W ∧ ∀ i, (x i - y i) ^ 2 < t ^ 2}

/-- The points admitting a ball disjoint from `W`; the complement of the closure of `W`. -/
def interiorComp {n : ℕ} (W : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  {x | ∃ t, 0 < t ∧ x ∉ fatSet W t}

/-- The set of limit points of `W`, in the form used by the target statement. -/
def closureSet {n : ℕ} (W : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  {x | ∀ ε > 0, ∃ y, y ∈ W ∧ ∀ i, |y i - x i| < ε}

/-! ## Reading the coordinates of `Fin.snoc` -/

lemma snoc_castAdd_one {n : ℕ} (x : Fin n → ℝ) (t : ℝ) (i : Fin n) :
    (Fin.snoc x t : Fin (n + 1) → ℝ) (Fin.castAdd 1 i) = x i := by
  rw [show Fin.castAdd 1 i = Fin.castSucc i from Fin.ext rfl, Fin.snoc_castSucc]

lemma snoc_last' {n : ℕ} (x : Fin n → ℝ) (t : ℝ) :
    (Fin.snoc x t : Fin (n + 1) → ℝ) (Fin.last n) = t := by simp

end Work.WilkiesH.Strat
