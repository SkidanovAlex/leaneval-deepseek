import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.CoreResiduals.SelfSimReduction
import Submission.Work.CoreResiduals.timeDeriv_ssVort_lam

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `meridianEq_of_dynEqConst` — the chain-rule reduction of the meridian equation

Given profiles `F, Φ` satisfying the constant-rate profile equation `DynEqConst p (2κ) 1 F Φ`
on the open quadrant, and a modulation `λ` with `λ(t) > 0` and `λ'(t) = -κ` (`κ = -λ'`),
the self-similar pair

  `W(r,z,t) = λ(t)⁻¹ F(ρ^p/λ(t), θ)`,  `ψ(r,z,t) = ρ² λ(t)⁻¹ Φ(ρ^p/λ(t), θ)`

solves the meridian scalar equation off the axis.

The engine is the exact pointwise identity (proved below by the chain rule and algebra)

  `meridianResid W ψ r z t = (2 λ(t)²)⁻¹ · ( 2κ·(F + D_z F) + UVR p F Φ )`

evaluated at `(Z, Θ) = (ρ^p/λ(t), arctan(z/r))`; the bracket vanishes by `DynEqConst`.
-/

noncomputable section
open scoped Topology

namespace Work.CoreResiduals


/-- **The expansion of `UVR` in polar coordinates.**  Substituting `sin Θ = z/ρ`, `cos Θ = r/ρ`
and `tan Θ = z/r` turns the operator `UVR p F Φ` at `(Z,Θ)` into the purely rational expression
appearing on the right-hand side (this is the form the meridian-residual algebra produces). -/
lemma UVR_polar_expand (p r z ρ : ℝ) (F Φ : ℝ → ℝ → ℝ) (Z Θ : ℝ)
    (hr : r ≠ 0) (hρ : ρ ≠ 0) (hsin : Real.sin Θ = z / ρ) (hcos : Real.cos Θ = r / ρ)
    (htan : Real.tan Θ = z / r) :
    Work.Construction.UVR p F Φ Z Θ =
      2 * (-3 * Φ Z Θ - p * Z * Work.Cyl.pdR Φ Z Θ) * Work.Cyl.pdZ F Z Θ
      + 2 * p * (Work.Cyl.pdZ Φ Z Θ - (z / r) * Φ Z Θ) * (Z * Work.Cyl.pdR F Z Θ)
      - 2 * ((2 * z * Φ Z Θ + p * z * Z * Work.Cyl.pdR Φ Z Θ + r * Work.Cyl.pdZ Φ Z Θ) / r)
          * F Z Θ := by
  rw [Work.Construction.UVR, Work.Construction.Uop, Work.Construction.Vop, Work.Construction.Rop]
  simp only [Work.Spaces.Dz, Work.Spaces.pz, Work.Spaces.pth, Work.Cyl.pdR, Work.Cyl.pdZ,
    hsin, hcos, htan]
  field_simp



end Work.CoreResiduals
