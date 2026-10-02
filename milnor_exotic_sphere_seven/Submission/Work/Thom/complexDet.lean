import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The real determinant of a complex-linear endomorphism

If `V` is a complex vector space, viewed as a real vector space by restriction of scalars, then the
real determinant of a `ℂ`-linear endomorphism is `|det_ℂ|² > 0`.  This is the algebraic input of the
**complex orientation**: the transition function of a complex vector bundle (a `ℂ`-linear gauge)
has positive real determinant, hence preserves the orientation of the fibre, which is what makes the
realification of a complex bundle canonically oriented
(`Work.Thom.isOrientedOver_of_det_pos`, `Submission/Work/Thom/isOrientedOver_of_det_pos.lean`).
-/

namespace Work.Thom

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [Module ℝ V] [IsScalarTower ℝ ℂ V]
  [Module.Free ℂ V] [Module.Finite ℂ V]

/-- **The real determinant of a `ℂ`-linear endomorphism is the squared modulus of its complex
determinant.**  This is Mathlib's `LinearMap.det_restrictScalars` together with
`Algebra.norm_complex_apply`. -/
theorem det_restrictScalars_eq_normSq (f : V →ₗ[ℂ] V) :
    LinearMap.det (f.restrictScalars ℝ) = Complex.normSq (LinearMap.det f) := by
  rw [LinearMap.det_restrictScalars, Algebra.norm_complex_apply]

/-- **A bijective `ℂ`-linear endomorphism has positive real determinant.** -/
theorem det_restrictScalars_pos {f : V →ₗ[ℂ] V} (hf : Function.Bijective f) :
    0 < LinearMap.det (f.restrictScalars ℝ) := by
  rw [det_restrictScalars_eq_normSq]
  refine Complex.normSq_pos.2 fun h => ?_
  have hker : f.ker = ⊥ := LinearMap.ker_eq_bot.2 hf.1
  exact (LinearMap.det_eq_zero_iff_ker_ne_bot.1 h) (by rw [hker])

end

end Work.Thom
