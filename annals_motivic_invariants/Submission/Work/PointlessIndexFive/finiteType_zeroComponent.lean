import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Work.PointlessIndexFive

/-- The standard grading of a multivariate polynomial ring in finitely many variables makes it a
finitely generated algebra over its degree-`0` part: this is the hypothesis
`Algebra.FiniteType (𝒜 0) A` that Mathlib's `IsProper (Proj.toSpecZero 𝒜)`,
`LocallyOfFiniteType (Proj.toSpecZero 𝒜)` and `QuasiCompact (Proj.toSpecZero 𝒜)` require. -/
theorem finiteType_zeroComponent (𝕜 : Type) [Field 𝕜] (σ : Type) [Fintype σ] :
    Algebra.FiniteType ↥(MvPolynomial.homogeneousSubmodule σ 𝕜 0) (MvPolynomial σ 𝕜) := by
  -- `MvPolynomial σ 𝕜` is finitely generated as a `𝕜`-algebra (by the variables `X i`), and the
  -- degree-zero part `𝒜 0 = MvPolynomial.homogeneousSubmodule σ 𝕜 0` is a `𝕜`-subalgebra of it
  -- (the constants).  Hence finite generation survives the change of base ring
  -- (`Algebra.FiniteType.of_restrictScalars_finiteType`).
  --
  -- The three `letI`s pin the scalar actions to the algebra-level ones: they are definitionally,
  -- but not syntactically, the instances that typeclass search would otherwise pick for the
  -- subtype `↥(homogeneousSubmodule σ 𝕜 0)` (which also carries the ambient module structure),
  -- and the scalar-tower field is only reached through the algebra-level actions.
  letI : SMul 𝕜 ↥(MvPolynomial.homogeneousSubmodule σ 𝕜 0) := Algebra.toSMul
  letI : SMul ↥(MvPolynomial.homogeneousSubmodule σ 𝕜 0) (MvPolynomial σ 𝕜) := Algebra.toSMul
  letI : SMul 𝕜 (MvPolynomial σ 𝕜) := Algebra.toSMul
  haveI : IsScalarTower 𝕜 ↥(MvPolynomial.homogeneousSubmodule σ 𝕜 0) (MvPolynomial σ 𝕜) :=
    ⟨fun x y z => by
      simp only [Algebra.smul_def, map_mul, SetLike.GradeZero.algebraMap_apply,
        SetLike.GradeZero.coe_algebraMap]
      ring⟩
  exact Algebra.FiniteType.of_restrictScalars_finiteType 𝕜 _ _

end Work.PointlessIndexFive
