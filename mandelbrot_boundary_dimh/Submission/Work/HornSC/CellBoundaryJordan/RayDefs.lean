import Mathlib
import Submission.Work.HornSC.CellBoundaryJordan.Defs
import Submission.Work.HornSC.Cells

/-!
# The ray from a point of the plane in direction `1 + εI`

Vocabulary used by the parity argument for crossings of a straight ray with the wall set of a
finite union of lattice cells.
-/

namespace Work.HornSC.CellBoundaryJordan

open Set

/-- The direction `1 + εI` of the ray. -/
noncomputable def rayDir (ε : ℝ) : ℂ := ⟨1, ε⟩

/-- The point of the ray issued from `a` in direction `1 + εI` at time `t`. -/
noncomputable def rayPt (a : ℂ) (ε t : ℝ) : ℂ := a + (t : ℂ) * rayDir ε

@[simp] lemma rayPt_zero (a : ℂ) (ε : ℝ) : rayPt a ε 0 = a := by
  simp [rayPt, rayDir]

lemma rayPt_re (a : ℂ) (ε t : ℝ) : (rayPt a ε t).re = a.re + t := by
  simp [rayPt, rayDir, Complex.add_re, Complex.mul_re]

lemma rayPt_im (a : ℂ) (ε t : ℝ) : (rayPt a ε t).im = a.im + ε * t := by
  simp [rayPt, rayDir, Complex.add_im, Complex.mul_im, mul_comm]

/-- `z` is not a lattice point. -/
def NonLattice (z : ℂ) : Prop := ∀ m n : ℤ, z ≠ (m : ℂ) + (n : ℂ) * Complex.I

lemma lpt_eq_iff' (m n : ℤ) : lpt (m, n) = (m : ℂ) + (n : ℂ) * Complex.I := by
  apply Complex.ext <;> simp [lpt]

lemma NonLattice.of_notMem_lpt {z : ℂ} (h : ∀ v : ℤ × ℤ, z ≠ lpt v) : NonLattice z := by
  intro m n hc
  exact h (m, n) (by rw [hc, lpt_eq_iff'])

lemma NonLattice.notMem_lpt {z : ℂ} (h : NonLattice z) (v : ℤ × ℤ) : z ≠ lpt v := by
  rw [lpt_eq_iff']
  exact h v.1 v.2

end Work.HornSC.CellBoundaryJordan
