/-
Copyright: subproject `Submission/Work/Implosion/` of `mandelbar_not_path_connected`.

# `ecalPt` is invariant under the period lattice

The Écalle point map `ζ(u) = a·(e^{2au}+1)/(e^{2au}−1)` (`Ecalle.lean`) depends on
`u` only through the multiplier `s = ecalE a u = e^{2au}`.  Hence it is invariant
under translation by any period of the Écalle coordinate, i.e. under any element
of the lattice `periodZMod a = (πi/a)ℤ` of punctures of the Écalle cylinder.

Concretely, if `x ∈ (πi/a)ℤ` then `e^{2ax} = 1`, so that
`ecalE a (u+x) = ecalE a u · e^{2ax} = ecalE a u`, and substituting into `ecalPt`
gives `ecalPt a (u+x) = ecalPt a u`.

This is the well-definedness statement that lets a point of the Écalle cylinder
(the quotient of `ℂ` by the period lattice) be lifted to a concrete value of the
Écalle coordinate without ambiguity: moving the lift by a period does not change
the point `ζ` of the local model.
-/
import Mathlib
import Submission.Work.Implosion.Basic
import Submission.Work.Implosion.Ecalle
import Submission.Work.Implosion.Cylinder

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Implosion.Cylinder

open Complex

/-- **`ecalPt` is well defined on the Écalle cylinder.**  Translating the Écalle
coordinate `u` by a period of the Écalle coordinate, i.e. by an element
`x ∈ periodZMod a = (πi/a)ℤ`, does not change the point `ecalPt a u` of the local
model.  Equivalently, `ecalPt a` factors through the quotient of `ℂ` by the period
lattice. -/
theorem ecalPt_eq_of_mem_periodZMod (a u x : ℂ) (ha : a ≠ 0) (hx : x ∈ periodZMod a) :
    ecalPt a (u + x) = ecalPt a u := by
  -- An element of the period lattice is killed by the multiplier coordinate.
  have hx' : Complex.exp (2 * a * x) = 1 := by
    rw [periodZMod, AddSubgroup.mem_zmultiples_iff] at hx
    obtain ⟨n, hn⟩ := hx
    rw [← hn, zsmul_eq_mul,
      show 2 * a * ((n : ℂ) * (Real.pi * I / a)) = (n : ℂ) * (2 * ↑Real.pi * I) by
        field_simp]
    exact Complex.exp_int_mul_two_pi_mul_I n
  -- Hence the multiplier coordinate is unchanged by the translation.
  have hE : ecalE a (u + x) = ecalE a u := by
    rw [ecalE, ecalE, mul_add, Complex.exp_add, hx', mul_one]
  -- And `ecalPt` only depends on the multiplier coordinate.
  simp only [ecalPt, hE]

end Work.Implosion.Cylinder
