import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.FTS.BSIdent.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `C¹`-regularity of the no-swirl field `axiField a b`

The axisymmetric no-swirl field with reduced radial profile `a` and axial profile `b` is

  `axiField a b x = a (r², x₃) • (x₀, x₁, 0) + b (r², x₃) • e₃`,   `r² = x₀² + x₁²`, `x₃ = x 2`.

Since `x ↦ (r², x₃)` is a polynomial (hence smooth) map and `x ↦ (x₀, x₁, 0)`, `x ↦ e₃` are
linear, the field inherits the regularity of the profiles: if `a` and `b` are jointly `C¹`, so is
`axiField a b`.  Here we prove this in the form needed by the Biot--Savart identification
(`ContDiff ℝ 1`), by reducing to the three coordinates and using the product rule.

The two profile hypotheses are exactly `ContDiff ℝ 1 (Function.uncurry a)` and
`ContDiff ℝ 1 (Function.uncurry b)`, i.e. joint `C¹`-regularity of `(w, z) ↦ a w z`.

The coordinates of the field are

* `(axiField a b x) 0 = a (r², x₃) * x₀`,
* `(axiField a b x) 1 = a (r², x₃) * x₁`,
* `(axiField a b x) 2 = b (r², x₃)`,

which is what the proof checks via `contDiff_piLp`.
-/

namespace Work.FTS.BSIdent.Axi

/-- **`axiField a b` is `C¹` as soon as its two profiles are jointly `C¹`.**  The field
`x ↦ a(r², x₃) • (x₀, x₁, 0) + b(r², x₃) • e₃` is the composition of the smooth coordinate map
`x ↦ (r², x₃)` with the two profiles, multiplied by the linear maps `x ↦ (x₀, x₁, 0)` and
`x ↦ e₃`. -/
theorem contDiff_axiField (a b : ℝ → ℝ → ℝ)
    (ha : ContDiff ℝ 1 (Function.uncurry a)) (hb : ContDiff ℝ 1 (Function.uncurry b)) :
    ContDiff ℝ 1 (Work.Cyl.axiField a b) := by
  -- the smooth coordinate map `x ↦ (r², x₃)`
  have hpair : ContDiff ℝ 1 (fun x : Work.Cyl.R3 => (Work.Cyl.radSq x, Work.Cyl.axial x)) := by
    rw [contDiff_prod_iff]
    constructor
    · show ContDiff ℝ 1 (fun x : Work.Cyl.R3 => Work.Cyl.radSq x)
      unfold Work.Cyl.radSq
      fun_prop
    · show ContDiff ℝ 1 (fun x : Work.Cyl.R3 => Work.Cyl.axial x)
      unfold Work.Cyl.axial
      fun_prop
  -- the two coefficient functions `x ↦ a (r², x₃)`, `x ↦ b (r², x₃)`
  have hA : ContDiff ℝ 1 (fun x : Work.Cyl.R3 => a (Work.Cyl.radSq x) (Work.Cyl.axial x)) :=
    ha.comp hpair
  have hB : ContDiff ℝ 1 (fun x : Work.Cyl.R3 => b (Work.Cyl.radSq x) (Work.Cyl.axial x)) :=
    hb.comp hpair
  -- it suffices to check the three coordinates of the field
  rw [contDiff_piLp]
  intro i
  fin_cases i
  · convert hA.mul (show ContDiff ℝ 1 (fun x : Work.Cyl.R3 => x.ofLp 0) from by fun_prop) using 1
    ext x
    simp [Work.Cyl.axiField]
  · convert hA.mul (show ContDiff ℝ 1 (fun x : Work.Cyl.R3 => x.ofLp 1) from by fun_prop) using 1
    ext x
    simp [Work.Cyl.axiField]
  · convert hB using 1
    ext x
    simp [Work.Cyl.axiField]

end Work.FTS.BSIdent.Axi
