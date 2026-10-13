import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Cyl.Coords
import Submission.Work.Cyl.Frame
import Submission.Work.Cyl.FieldDeriv

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open scoped Matrix

namespace Work.Cyl

/-! ## Derivatives of the polar coordinate functions in the radial variable

`∂_r ρ = r/ρ` and `∂_r θ = -z/ρ²`, and the chain rule for `ρ^α`.  These are the radial
counterparts of `hasDerivAt_rhoP_snd` / `hasDerivAt_thetaP_snd`. -/

private lemma hasDerivAt_rhoP_fst (r z : ℝ) (hr : 0 < r) :
    HasDerivAt (fun r' : ℝ => rhoP r' z) (r / rhoP r z) r := by
  have hsq : HasDerivAt (fun r' : ℝ => r' ^ 2 + z ^ 2) (2 * r) r := by
    have h : HasDerivAt (fun r' : ℝ => r' ^ 2) (2 * r) r := by
      simpa using (hasDerivAt_pow 2 r)
    simpa using h.const_add (z ^ 2)
  have hne : r ^ 2 + z ^ 2 ≠ 0 := by positivity
  have h := hsq.sqrt hne
  have hfun : (fun r' : ℝ => rhoP r' z) = fun r' => Real.sqrt (r' ^ 2 + z ^ 2) := by
    funext r'; rw [rhoP]
  rw [hfun]
  convert h using 1
  rw [rhoP]
  field_simp

private lemma hasDerivAt_thetaP_fst (r z : ℝ) (hr : 0 < r) :
    HasDerivAt (fun r' : ℝ => thetaP r' z) (-z / rhoP r z ^ 2) r := by
  have hdiv : HasDerivAt (fun r' : ℝ => z / r') (-z / r ^ 2) r := by
    have h := (hasDerivAt_const (x := r) z).div (hasDerivAt_id r) (ne_of_gt hr)
    have hfun : ((fun x : ℝ => z) / id : ℝ → ℝ) = fun r' => z / r' := by
      funext x; simp [Pi.div_apply]
    rw [hfun] at h
    convert h using 1
    simp
  have h := hdiv.arctan
  have hfun : (fun r' : ℝ => thetaP r' z) = fun r' => Real.arctan (z / r') := by
    funext r'; rw [thetaP]
  rw [hfun]
  convert h using 1
  rw [rhoP]
  field_simp
  rw [Real.sq_sqrt (by positivity)]

private lemma hasDerivAt_rhoP_fst_rpow (r z α : ℝ) (hr : 0 < r) :
    HasDerivAt (fun r' : ℝ => rhoP r' z ^ α) (α * rhoP r z ^ α * (r / rhoP r z ^ 2)) r := by
  have hne : rhoP r z ≠ 0 := rhoP_ne_zero hr z
  have hρ : HasDerivAt (fun r' : ℝ => rhoP r' z) (r / rhoP r z) r :=
    hasDerivAt_rhoP_fst r z hr
  have h := (Real.hasDerivAt_rpow_const (x := rhoP r z) (p := α) (Or.inl hne)).comp r hρ
  have hfun : ((fun x : ℝ => x ^ α) ∘ fun r' => rhoP r' z) = fun r' => rhoP r' z ^ α := by
    funext x; rfl
  rw [hfun] at h
  convert h using 1
  rw [Real.rpow_sub_one hne]
  field_simp

theorem pdR_comp_polar (F : ℝ → ℝ → ℝ) (α r z : ℝ) (hr : 0 < r)
    (hF : Work.Cyl.DiffAt2 F (Work.Cyl.rhoP r z ^ α) (Work.Cyl.thetaP r z)) :
    Work.Cyl.pdR (fun r' z' => F (Work.Cyl.rhoP r' z' ^ α) (Work.Cyl.thetaP r' z')) r z =
      Real.cos (Work.Cyl.thetaP r z) / Work.Cyl.rhoP r z *
          (α * Work.Cyl.rhoP r z ^ α * Work.Cyl.pdR F (Work.Cyl.rhoP r z ^ α) (Work.Cyl.thetaP r z))
        - Real.sin (Work.Cyl.thetaP r z) / Work.Cyl.rhoP r z *
          Work.Cyl.pdZ F (Work.Cyl.rhoP r z ^ α) (Work.Cyl.thetaP r z) := by
  have h := hasDerivAt_comp_two F (fun r' => rhoP r' z ^ α) (fun r' => thetaP r' z)
      (α * rhoP r z ^ α * (r / rhoP r z ^ 2)) (-z / rhoP r z ^ 2) r hF
      (hasDerivAt_rhoP_fst_rpow r z α hr) (hasDerivAt_thetaP_fst r z hr)
  rw [pdR, h.deriv, cos_thetaP hr z, sin_thetaP hr z]
  field_simp
  ring

end Work.Cyl
