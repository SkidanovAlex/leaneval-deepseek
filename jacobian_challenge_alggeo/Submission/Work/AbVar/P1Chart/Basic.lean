/-
Area AV: the standard grading on `k[X₀, X₁]` and the affine charts of `P¹`.
-/
import Mathlib
import Submission.Work.AbVar.Basic
import Submission.Work.AbVar.ProjectiveLine

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open HomogeneousLocalization MvPolynomial

noncomputable section

universe u

namespace Work.AbVar.P1Chart

/-- The standard grading of `k[X₀, X₁]` by total degree. -/
noncomputable abbrev gr (k : Type u) [Field k] : ℕ → Submodule k (MvPolynomial (Fin 2) k) :=
  MvPolynomial.homogeneousSubmodule (Fin 2) k

/-- The standard grading of `k[X₀, X₁]` is a `GradedAlgebra` (hence a `GradedRing`). -/
noncomputable instance instGradedAlgebraGr (k : Type u) [Field k] : GradedAlgebra (gr k) :=
  MvPolynomial.gradedAlgebra

/-- The degree-zero part of the localization of `k[X₀, X₁]` at `Xᵢ`; the chart `D₊(Xᵢ)` of
`Proj` is `Spec (AX k i)`.  Note that we write `HomogeneousLocalization (gr k) (.powers (X i))`
rather than `Away (gr k) (X i)` because the latter does not elaborate. -/
abbrev AX (k : Type u) [Field k] (i : Fin 2) : Type u :=
  HomogeneousLocalization (gr k) (Submonoid.powers (MvPolynomial.X i : MvPolynomial (Fin 2) k))

/-- `Xᵢ` is homogeneous of degree one. -/
theorem X_mem (k : Type u) [Field k] (i : Fin 2) :
    (MvPolynomial.X i : MvPolynomial (Fin 2) k) ∈ gr k 1 :=
  (mem_homogeneousSubmodule 1 _).mpr (MvPolynomial.isHomogeneous_X (R := k) i)

/-- The "other" index of `Fin 2`. -/
def other (i : Fin 2) : Fin 2 := if i = 0 then 1 else 0

lemma other_ne (i : Fin 2) : other i ≠ i := by
  fin_cases i <;> decide

lemma eq_other (i l : Fin 2) (h : l ≠ i) : l = other i := by
  fin_cases i <;> fin_cases l <;> simp_all [other]

/-- `X_{j}/X_{i}` in the chart ring, where `j ≠ i`; the chart is a polynomial ring on it. -/
noncomputable def t (k : Type u) [Field k] (i : Fin 2) : AX k i :=
  Away.mk (gr k) (X_mem k i) 1 (MvPolynomial.X (other i)) (by simpa using X_mem k (other i))

end Work.AbVar.P1Chart
