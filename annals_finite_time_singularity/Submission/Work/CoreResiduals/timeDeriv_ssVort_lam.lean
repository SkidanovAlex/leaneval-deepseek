import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.CoreResiduals.SelfSimReduction
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.bt_integral_weight_id
-- ===== merged: Submission.Work.CoreResiduals.pdR_ssPsi_lam =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The radial partial derivative of the self-similar stream function `ssPsi`

`ssPsi p lam Φ r z t = ρ²·λ(t)⁻¹·Φ(ρ^p/λ(t), θ)` with `ρ = √(r²+z²)`, `θ = arctan(z/r)`.  This
module computes `∂_r` of it at `t` fixed:

`∂_r [ssPsi] = λ⁻¹ · (2r Φ + ρ²·(∂_R Φ · (p·(ρ^p/λ)·(r/ρ²)) − ∂_θ Φ · (z/ρ²)))`,

evaluated at `(R,θ) = (ρ^p/λ, θ)`.  The `ρ²` prefactor contributes `2ρ·∂_rρ = 2r`, while
`∂_r (ρ^p/λ) = p·(ρ^p/λ)·(r/ρ²)` and `∂_r θ = −z/ρ²`.
-/

namespace Work.CoreResiduals

/-- `∂_r ρ(r,z) = r/ρ` (the radial derivative of the polar radius). -/
private lemma hdRhoP (r z : ℝ) (hr : 0 < r) :
    HasDerivAt (fun r' : ℝ => Work.Cyl.rhoP r' z) (r / Work.Cyl.rhoP r z) r := by
  have hsq : HasDerivAt (fun r' : ℝ => r' ^ 2 + z ^ 2) (2 * r) r := by
    have h : HasDerivAt (fun r' : ℝ => r' ^ 2) (2 * r) r := by
      simpa using (hasDerivAt_pow 2 r)
    simpa using h.const_add (z ^ 2)
  have hne : r ^ 2 + z ^ 2 ≠ 0 := by positivity
  have h := hsq.sqrt hne
  have hfun : (fun r' : ℝ => Work.Cyl.rhoP r' z) = fun r' => Real.sqrt (r' ^ 2 + z ^ 2) := by
    funext r'; rw [Work.Cyl.rhoP]
  rw [hfun]
  convert h using 1
  rw [Work.Cyl.rhoP]
  field_simp

/-- `∂_r (ρ^p) = p·ρ^p·(r/ρ²)`. -/
private lemma hdRhoPpow (r z p : ℝ) (hr : 0 < r) :
    HasDerivAt (fun r' : ℝ => Work.Cyl.rhoP r' z ^ p)
      (p * Work.Cyl.rhoP r z ^ p * (r / Work.Cyl.rhoP r z ^ 2)) r := by
  have hne : Work.Cyl.rhoP r z ≠ 0 := Work.Cyl.rhoP_ne_zero hr z
  have hρ : HasDerivAt (fun r' : ℝ => Work.Cyl.rhoP r' z) (r / Work.Cyl.rhoP r z) r :=
    hdRhoP r z hr
  have h := (Real.hasDerivAt_rpow_const (x := Work.Cyl.rhoP r z) (p := p) (Or.inl hne)).comp r hρ
  have hfun : ((fun x : ℝ => x ^ p) ∘ fun r' => Work.Cyl.rhoP r' z) =
      fun r' => Work.Cyl.rhoP r' z ^ p := by funext x; rfl
  rw [hfun] at h
  convert h using 1
  rw [Real.rpow_sub_one hne]
  field_simp

/-- `∂_r θ(r,z) = −z/ρ²` (the radial derivative of the polar angle). -/
private lemma hdThetaP (r z : ℝ) (hr : 0 < r) :
    HasDerivAt (fun r' : ℝ => Work.Cyl.thetaP r' z) (-z / Work.Cyl.rhoP r z ^ 2) r := by
  have hdiv : HasDerivAt (fun r' : ℝ => z / r') (-z / r ^ 2) r := by
    have h := (hasDerivAt_const (x := r) z).div (hasDerivAt_id r) (ne_of_gt hr)
    have hfun : ((fun x : ℝ => z) / id : ℝ → ℝ) = fun r' => z / r' := by
      funext x; simp [Pi.div_apply]
    rw [hfun] at h
    convert h using 1
    simp
  have h := hdiv.arctan
  have hfun : (fun r' : ℝ => Work.Cyl.thetaP r' z) = fun r' => Real.arctan (z / r') := by
    funext r'; rw [Work.Cyl.thetaP]
  rw [hfun]
  convert h using 1
  rw [Work.Cyl.rhoP]
  field_simp
  rw [Real.sq_sqrt (by positivity)]

theorem pdR_ssPsi_lam {p : ℝ} {lam : ℝ → ℝ} {Φ : ℝ → ℝ → ℝ} {r z t : ℝ}
    (hr : 0 < r) (hlam : lam t ≠ 0)
    (hΦ : Work.Cyl.DiffAt2 Φ (Work.Cyl.rhoP r z ^ p / lam t) (Work.Cyl.thetaP r z)) :
    Work.Cyl.pdR (fun r' z' => Work.CoreResiduals.ssPsi p lam Φ r' z' t) r z =
      (lam t)⁻¹ *
        (2 * r * Φ (Work.Cyl.rhoP r z ^ p / lam t) (Work.Cyl.thetaP r z)
          + (Work.Cyl.rhoP r z) ^ 2 *
              (Work.Cyl.pdR Φ (Work.Cyl.rhoP r z ^ p / lam t) (Work.Cyl.thetaP r z)
                  * (p * (Work.Cyl.rhoP r z ^ p / lam t) * (r / Work.Cyl.rhoP r z ^ 2))
                - Work.Cyl.pdZ Φ (Work.Cyl.rhoP r z ^ p / lam t) (Work.Cyl.thetaP r z)
                    * (z / Work.Cyl.rhoP r z ^ 2))) := by
  have hρ : Work.Cyl.rhoP r z ≠ 0 := Work.Cyl.rhoP_ne_zero hr z
  -- `∂_r (ρ^p/λ)`, the derivative of the first argument of `Φ`
  have hR : HasDerivAt (fun r' : ℝ => Work.Cyl.rhoP r' z ^ p / lam t)
      (p * Work.Cyl.rhoP r z ^ p * (r / Work.Cyl.rhoP r z ^ 2) / lam t) r :=
    (hdRhoPpow r z p hr).div_const (lam t)
  -- `∂_r θ`, the derivative of the second argument of `Φ`
  have hZ : HasDerivAt (fun r' : ℝ => Work.Cyl.thetaP r' z) (-z / Work.Cyl.rhoP r z ^ 2) r :=
    hdThetaP r z hr
  -- chain rule for `r' ↦ Φ (ρ(r',z)^p/λ) (θ(r',z))`
  have hG := Work.Cyl.hasDerivAt_comp_two Φ (fun r' : ℝ => Work.Cyl.rhoP r' z ^ p / lam t)
      (fun r' : ℝ => Work.Cyl.thetaP r' z)
      (p * Work.Cyl.rhoP r z ^ p * (r / Work.Cyl.rhoP r z ^ 2) / lam t)
      (-z / Work.Cyl.rhoP r z ^ 2) r hΦ hR hZ
  have hG' := hG.const_mul (lam t)⁻¹
  -- the `ρ²` prefactor: `∂_r (ρ²) = 2r`
  have hP2 : HasDerivAt (fun r' : ℝ => Work.Cyl.rhoP r' z ^ 2) (2 * r) r := by
    have h := (hdRhoP r z hr).pow 2
    have hval : ((2:ℕ) : ℝ) * Work.Cyl.rhoP r z ^ ((2:ℕ) - 1) * (r / Work.Cyl.rhoP r z) = 2 * r := by
      show (2:ℝ) * Work.Cyl.rhoP r z ^ 1 * (r / Work.Cyl.rhoP r z) = 2 * r
      rw [pow_one]
      field_simp
    rw [hval] at h
    convert h using 1
  have hfull := hP2.mul hG'
  rw [show Work.Cyl.pdR (fun r' z' => Work.CoreResiduals.ssPsi p lam Φ r' z' t) r z
      = deriv (fun r' : ℝ => Work.CoreResiduals.ssPsi p lam Φ r' z t) r from rfl]
  rw [show (fun r' : ℝ => Work.CoreResiduals.ssPsi p lam Φ r' z t)
      = ((fun r' : ℝ => Work.Cyl.rhoP r' z ^ 2) *
          (fun y : ℝ => (lam t)⁻¹ * Φ (Work.Cyl.rhoP y z ^ p / lam t) (Work.Cyl.thetaP y z))) from by
        funext r'; rfl]
  rw [hfull.deriv]
  field_simp
  ring

end Work.CoreResiduals
end
-- ===== merged: Submission.Work.CoreResiduals.pdR_ssVort_lam =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals

open Work.Cyl


end Work.CoreResiduals
end
-- ===== merged: Submission.Work.CoreResiduals.pdZ_ssPsi_lam =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Work.CoreResiduals


end Work.CoreResiduals
end
-- ===== merged: Submission.Work.CoreResiduals.pdZ_ssVort_lam =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Work.CoreResiduals


end Work.CoreResiduals
end
-- ===== merged: Submission.Work.CoreResiduals.timeDeriv_ssVort_lam =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals


end Work.CoreResiduals
end
