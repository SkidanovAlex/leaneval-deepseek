/-
# The quarter turn, the cross product and the open cone behind the shifted wedges

This is the definition layer of the `c`-shifted wedges `wedgeS c k` of `Work.Cusp.Charts`:
a small amount of two-dimensional linear algebra, on top of which the modules next to it
(`isOpen_wedgeS`) identify the wedges with open cones.

* `rot90 p = (p 1, -p 0)` is the quarter turn of `E2 = ℝ²` that maps the `k`-th edge of the square
  `Sq` to the `(k+1)`-st.  It is the rotation along which the perimeter parameter `u` increases:
  `bndOfU (x + 1/4) = rot90 (bndOfU x)`, and `u (rot90 p) = frac (u p + 1/4)` (see the module
  `Work.Cusp.bndOfU_add_quarter` and `Work.Cusp.isOpen_wedgeS`).

* `cross p q = p 0 * q 1 - p 1 * q 0` is the determinant of the two coordinate columns; it is
  invariant under `rot90` (`cross (rot90 p) (rot90 q) = cross p q`) and bilinear.

* `wedgeCone A B` is the *open cone spanned by `A` and `B`*: inside the two half-planes that `A`
  and `B` cut out, i.e. the set of `p = a • A + b • B` with `a, b > 0` (for linearly independent
  `A`, `B`; if they are parallel it is empty).  Being an intersection of two open half-planes it is
  **open**, which is what makes the shifted wedges open.

The perimeter parameter itself is not continuous on the whole plane (it jumps at the ray through
the corner `(1,1)` of the square), but each wedge is an open arc of directions, and the two
bounding directions of the `k`-th `c`-shifted wedge span the open cone cut out above.
-/
import Mathlib
import Submission.Work.Cusp.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

namespace Work.Cusp

open scoped Real InnerProductSpace

/-- The quarter turn `(x,y) ↦ (y,-x)`: the rotation of `E2` carrying the `k`-th edge of the square
to the `(k+1)`-st, in the direction in which the perimeter parameter `u` grows. -/
def rot90 (p : E2) : E2 := !₂[p 1, -(p 0)]

/-- The inverse quarter turn `(x,y) ↦ (-y,x)`. -/
def rot90Inv (p : E2) : E2 := !₂[-(p 1), p 0]

/-- The determinant `p 0 * q 1 - p 1 * q 0` of a pair of vectors of `E2`. -/
def cross (p q : E2) : ℝ := p 0 * q 1 - p 1 * q 0

/-- **The open cone spanned by `A` and `B`.**  For linearly independent `A`, `B` it is the set of
positive combinations `a • A + b • B` (`a, b > 0`); in the degenerate case `cross A B = 0` it is
empty.  It is an intersection of the two open half-planes `{p | cross A p * cross A B > 0}` and
`{p | cross p B * cross A B > 0}`, hence open. -/
def wedgeCone (A B : E2) : Set E2 :=
  {p : E2 | 0 < cross p B * cross A B ∧ 0 < cross A p * cross A B}

/-! ### Basic identities -/

/-- The inverse of `rot90`. -/
@[simp] theorem rot90_rot90Inv (p : E2) : rot90 (rot90Inv p) = p := by
  ext i; fin_cases i <;> simp [rot90, rot90Inv]

/-- `rot90Inv` is the inverse of `rot90`. -/
@[simp] theorem rot90Inv_rot90 (p : E2) : rot90Inv (rot90 p) = p := by
  ext i; fin_cases i <;> simp [rot90, rot90Inv]

/-- The quarter turn is an isometry of the sup norm `nrm`. -/
theorem nrm_rot90 (p : E2) : nrm (rot90 p) = nrm p := by
  simp only [nrm, rot90, Matrix.cons_val_zero, Matrix.cons_val_one, abs_neg, max_comm]

/-- The quarter turn is additive. -/
theorem rot90_add (p q : E2) : rot90 (p + q) = rot90 p + rot90 q := by
  ext i
  fin_cases i <;> (simp [rot90, PiLp.add_apply]; try ring)

/-- The quarter turn is homogeneous. -/
theorem rot90_smul (c : ℝ) (p : E2) : rot90 (c • p) = c • rot90 p := by
  ext i; fin_cases i <;> simp [rot90, PiLp.smul_apply]

/-- The quarter turn is continuous. -/
theorem continuous_rot90 : Continuous rot90 := by
  show Continuous (fun p : E2 => !₂[p 1, -(p 0)])
  fun_prop

/-- The determinant is invariant under a simultaneous quarter turn. -/
theorem cross_rot (p q : E2) : cross (rot90 p) (rot90 q) = cross p q := by
  simp only [cross, rot90, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- A quarter turn in the second argument of the determinant is an inverse quarter turn in the
first. -/
theorem cross_rot_left (x y : E2) : cross (rot90 x) y = cross x (rot90Inv y) := by
  conv_lhs => rw [show y = rot90 (rot90Inv y) from (rot90_rot90Inv y).symm]
  rw [cross_rot]

/-- A quarter turn in the first argument of the determinant is an inverse quarter turn in the
second. -/
theorem cross_rot_right (x y : E2) : cross x (rot90 y) = cross (rot90Inv x) y := by
  conv_lhs => rw [show x = rot90 (rot90Inv x) from (rot90_rot90Inv x).symm]
  rw [cross_rot]

/-- The determinant is linear in its first argument. -/
theorem cross_smul_left (c : ℝ) (p q : E2) : cross (c • p) q = c * cross p q := by
  simp only [cross, PiLp.smul_apply, smul_eq_mul]; ring

/-- The determinant is linear in its second argument. -/
theorem cross_smul_right (c : ℝ) (p q : E2) : cross p (c • q) = c * cross p q := by
  simp only [cross, PiLp.smul_apply, smul_eq_mul]; ring

/-- The determinant is continuous in its second argument. -/
theorem continuous_cross_left (A : E2) : Continuous (fun p : E2 => cross A p) := by
  simp only [cross]; fun_prop

/-- The determinant is continuous in its first argument. -/
theorem continuous_cross_right (B : E2) : Continuous (fun p : E2 => cross p B) := by
  simp only [cross]; fun_prop

/-! ### The cone -/

/-- **The cone is open**: it is cut out by the two strict inequalities defining the open
half-planes on the two sides of `A` and `B`. -/
theorem isOpen_wedgeCone (A B : E2) : IsOpen (wedgeCone A B) := by
  have h1 : Continuous (fun p : E2 => cross A p * cross A B) :=
    (continuous_cross_left A).mul continuous_const
  have h2 : Continuous (fun p : E2 => cross p B * cross A B) :=
    (continuous_cross_right B).mul continuous_const
  rw [show wedgeCone A B = {p | 0 < cross p B * cross A B} ∩
      {p | 0 < cross A p * cross A B} from rfl]
  exact (isOpen_lt continuous_const h2).inter (isOpen_lt continuous_const h1)

/-- The cone is invariant under positive scaling. -/
theorem wedgeCone_smul {c : ℝ} (hc : 0 < c) (A B : E2) (p : E2) :
    c • p ∈ wedgeCone A B ↔ p ∈ wedgeCone A B := by
  simp only [wedgeCone, Set.mem_ofPred_eq, cross_smul_left, cross_smul_right, mul_assoc,
    mul_pos_iff_of_pos_left hc]

/-- No point of the cone of two vectors of `∂Sq` is the origin. -/
theorem wedgeCone_ne_zero {A B p : E2} (hp : p ∈ wedgeCone A B) : p ≠ 0 := by
  intro h
  rw [h] at hp
  simp only [wedgeCone, Set.mem_ofPred_eq] at hp
  have : cross (0 : E2) B = 0 := by simp [cross]
  rw [this, zero_mul] at hp
  exact absurd hp.1 (lt_irrefl 0)

/-- **The cone of a pair of vectors is the image under the quarter turn of the cone of the rotated
pair**: `rot90` is a linear bijection with `cross (rot90 p) (rot90 q) = cross p q`. -/
theorem mem_wedgeCone_rot (A B p : E2) :
    p ∈ wedgeCone (rot90 A) (rot90 B) ↔ rot90Inv p ∈ wedgeCone A B := by
  simp only [wedgeCone, Set.mem_ofPred_eq]
  rw [cross_rot_right p B, cross_rot_left A p, cross_rot A B]

/-- The cone of a pair is the image under the quarter turn of the cone of the rotated-back pair. -/
theorem wedgeCone_rot (A B : E2) :
    wedgeCone (rot90 A) (rot90 B) = rot90 '' wedgeCone A B := by
  ext p
  rw [mem_wedgeCone_rot]
  constructor
  · intro hp
    exact ⟨rot90Inv p, hp, rot90_rot90Inv p⟩
  · rintro ⟨q, hq, rfl⟩
    simpa using hq

end Work.Cusp
