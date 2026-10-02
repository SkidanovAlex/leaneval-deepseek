import Mathlib
import Submission.Work.FatouParabolic.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FatouParabolic.Poly

/-- A polynomial of degree `≥ 1` over an algebraically closed field is surjective as a map:
for every `y`, the polynomial `P - C y` is nonconstant and hence has a root `z`, and
`P.eval z = y`.

This is used in the form: the evaluation map of a polynomial of degree `≥ 2` over `ℂ`
(as encoded by `Work.FatouParabolic.IsPolynomialMapOfDegreeAtLeastTwo`) is onto. -/
theorem polynomial_eval_surjective {P : Polynomial ℂ} (hP : 1 ≤ P.natDegree) :
    Function.Surjective fun z : ℂ => P.eval z := by
  intro y
  have hnz : P - Polynomial.C y ≠ 0 := by
    intro hzero
    have h1 : (P - Polynomial.C y).natDegree = P.natDegree := Polynomial.natDegree_sub_C
    rw [hzero] at h1
    simp at h1
    omega
  have hd : (P - Polynomial.C y).degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hnz, Polynomial.natDegree_sub_C]
    simp
    omega
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (P - Polynomial.C y) hd
  exact ⟨z, by simpa only [Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_C,
    sub_eq_zero] using hz⟩

theorem isPolynomialMap_surjective {F : ℂ → ℂ}
    (h : Work.FatouParabolic.IsPolynomialMapOfDegreeAtLeastTwo F) : Function.Surjective F := by
  obtain ⟨P, hP, hFP⟩ := h
  have hsurj : Function.Surjective fun z : ℂ => P.eval z :=
    polynomial_eval_surjective (P := P) (by omega : 1 ≤ P.natDegree)
  intro y
  obtain ⟨z, hz⟩ := hsurj y
  exact ⟨z, by rw [hFP z]; exact hz⟩

end Work.FatouParabolic.Poly
