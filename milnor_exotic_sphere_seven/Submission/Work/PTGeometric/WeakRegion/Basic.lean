import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# PTGEOMETRIC: basic coordinates for the weak region-charting theorem

The weak region-charting theorem (`Work.PTGeometric.RegionManifoldTheoremOfIsCompactWeak`) charts the
region `{Φ ≤ 0}` of a smooth function on a smooth manifold with boundary `A` when `Φ` is only assumed
to have *nonvanishing* derivative at its zeros (rather than to be a submersion in Mathlib's local
normal form sense) and is nonnegative on the boundary near its boundary zeros.

At a *boundary* zero the region is an epigraph `{z 0 ≥ h (tail z)}` of a smooth function `h` of the
tangential coordinates; the chart of the region there is obtained from the chart of `A` by the
"graph straightening" `z ↦ z - h (tail z) • e 0`.  This file collects the elementary coordinate
vocabulary for that construction.

## Main definitions

* `Work.PTGeometric.tailVec`: the tail of a vector of `ℝⁿ` (the vector with the same components
  except that the `0`-th is replaced by `0`).
* `Work.PTGeometric.consVec`: the inverse operation (insert a `0`-th coordinate into a tail).
-/

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter

namespace Work.PTGeometric

noncomputable section

/-- The `0`-th coordinate vector of `ℝⁿ`. -/
def eZero {n : ℕ} [NeZero n] : EuclideanSpace ℝ (Fin n) := PiLp.single 2 (0 : Fin n) (1 : ℝ)

/-- **The tail** of `z : ℝⁿ`: the vector with the same components except that the `0`-th is set
to `0`. -/
def tailVec {n : ℕ} [NeZero n] (z : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  z - z.ofLp 0 • eZero

/-- **Inserting a `0`-th coordinate**: `consVec s u = u + s • e 0`.  It is a one-sided inverse of
`tailVec` (on vectors with vanishing `0`-th coordinate). -/
def consVec {n : ℕ} [NeZero n] (s : ℝ) (u : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  u + s • eZero

theorem eZero_apply {n : ℕ} [NeZero n] : (eZero : EuclideanSpace ℝ (Fin n)).ofLp 0 = 1 := by
  rw [eZero, PiLp.single_apply]; simp

theorem eZero_apply_ne {n : ℕ} [NeZero n] {i : Fin n} (hi : i ≠ 0) :
    (eZero : EuclideanSpace ℝ (Fin n)).ofLp i = 0 := by
  rw [eZero, PiLp.single_apply]; simp [hi]

theorem tailVec_apply_zero {n : ℕ} [NeZero n] (z : EuclideanSpace ℝ (Fin n)) :
    (tailVec z).ofLp 0 = 0 := by
  simp [tailVec, eZero_apply]

theorem tailVec_ofLp_ne_zero {n : ℕ} [NeZero n] {z : EuclideanSpace ℝ (Fin n)} {i : Fin n}
    (hi : i ≠ 0) : (tailVec z).ofLp i = z.ofLp i := by
  simp [tailVec, eZero_apply_ne hi]

theorem consVec_apply_zero {n : ℕ} [NeZero n] (s : ℝ) (u : EuclideanSpace ℝ (Fin n)) :
    (consVec s u).ofLp 0 = s + u.ofLp 0 := by
  simp [consVec, eZero_apply, add_comm]

theorem consVec_ofLp_ne_zero {n : ℕ} [NeZero n] (s : ℝ) (u : EuclideanSpace ℝ (Fin n))
    {i : Fin n} (hi : i ≠ 0) : (consVec s u).ofLp i = u.ofLp i := by
  simp [consVec, eZero_apply_ne hi]

theorem tailVec_consVec {n : ℕ} [NeZero n] (s : ℝ) {u : EuclideanSpace ℝ (Fin n)}
    (hu : u.ofLp 0 = 0) : tailVec (consVec s u) = u := by
  ext i
  rcases eq_or_ne i 0 with rfl | hi
  · rw [tailVec_apply_zero, hu]
  · rw [tailVec_ofLp_ne_zero hi, consVec_ofLp_ne_zero s u hi]

theorem consVec_tailVec {n : ℕ} [NeZero n] (z : EuclideanSpace ℝ (Fin n)) :
    consVec (z.ofLp 0) (tailVec z) = z := by
  ext i
  rcases eq_or_ne i 0 with rfl | hi
  · rw [consVec_apply_zero, tailVec_apply_zero, add_zero]
  · rw [consVec_ofLp_ne_zero _ _ hi, tailVec_ofLp_ne_zero hi]

theorem tailVec_injOn {n : ℕ} [NeZero n] :
    Set.InjOn tailVec {z : EuclideanSpace ℝ (Fin n) | z.ofLp 0 = 0} := by
  intro x hx y hy hxy
  have h1 : x = consVec (x.ofLp 0) (tailVec x) := (consVec_tailVec x).symm
  have h2 : y = consVec (y.ofLp 0) (tailVec y) := (consVec_tailVec y).symm
  rw [h1, h2, hx, hy, hxy]

theorem tailVec_sub_smul_eZero {n : ℕ} [NeZero n] (z : EuclideanSpace ℝ (Fin n)) (a : ℝ) :
    tailVec (z - a • eZero) = tailVec z := by
  have h : (z - a • eZero).ofLp 0 = z.ofLp 0 - a := by
    simp [PiLp.sub_apply, PiLp.smul_apply, eZero_apply]
  show z - a • eZero - ((z - a • eZero).ofLp 0) • eZero = z - z.ofLp 0 • eZero
  rw [h]
  module

theorem continuous_tailVec {n : ℕ} [NeZero n] : Continuous (@tailVec n _) := by
  have h : @tailVec n _ = fun z : EuclideanSpace ℝ (Fin n) => z - (z.ofLp 0) • eZero := rfl
  rw [h]
  fun_prop

theorem contDiff_tailVec {n : ℕ} [NeZero n] : ContDiff ℝ ∞ (@tailVec n _) := by
  have h : @tailVec n _ = fun z : EuclideanSpace ℝ (Fin n) => z - (z.ofLp 0) • eZero := rfl
  rw [h]
  fun_prop

theorem ofLp_sub_smul_eZero {n : ℕ} [NeZero n] (z : EuclideanSpace ℝ (Fin n)) (a : ℝ) :
    (z - a • eZero).ofLp 0 = z.ofLp 0 - a := by
  simp [PiLp.sub_apply, PiLp.smul_apply, eZero_apply]

theorem ofLp_add_smul_eZero {n : ℕ} [NeZero n] (z : EuclideanSpace ℝ (Fin n)) (a : ℝ) :
    (z + a • eZero).ofLp 0 = z.ofLp 0 + a := by
  simp [PiLp.add_apply, PiLp.smul_apply, eZero_apply]

theorem tailVec_add {n : ℕ} [NeZero n] (z w : EuclideanSpace ℝ (Fin n)) :
    tailVec (z + w) = tailVec z + tailVec w := by
  have h : (z + w).ofLp 0 = z.ofLp 0 + w.ofLp 0 := by simp [PiLp.add_apply]
  show z + w - ((z + w).ofLp 0) • eZero = z - z.ofLp 0 • eZero + (w - w.ofLp 0 • eZero)
  rw [h]
  module

end

end Work.PTGeometric
