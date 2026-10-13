import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Cyl.Coords
import Submission.Work.Cyl.Frame
import Submission.Work.Cyl.Basic
import Submission.Work.Cyl.FieldDeriv

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Cyl

/-- The vorticity component `ω^θ` of the stream-function field `psiField ψ` is `-Lψ`, where `L` is
the axisymmetric elliptic operator `cylOp` of (3dBSL). -/
theorem vortTheta_psiField (ψ : ℝ → ℝ → ℝ) (r z : ℝ)
    (hψ : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => ψ p.1 p.2) (r, z)) (hr : r ≠ 0) :
    Work.Cyl.vortTheta (Work.Cyl.pdZ ψ) (fun r z => -(ψ r z / r) - Work.Cyl.pdR ψ r z) r z =
      -Work.Cyl.cylOp ψ r z := by
  -- `ψ(·, z)` is `C²` at `r`, hence so is its first derivative `pdR ψ · z`.
  have hslice : ContDiffAt ℝ 2 (fun r' : ℝ => ψ r' z) r := by
    have hg : ContDiffAt ℝ 2 (fun r' : ℝ => (r', z)) r := by fun_prop
    have h := hψ.comp r hg
    simpa [Function.comp_def] using h
  have hdψ : DifferentiableAt ℝ (fun r' : ℝ => ψ r' z) r := hslice.differentiableAt (by norm_num)
  have hdq : DifferentiableAt ℝ (fun r' : ℝ => ψ r' z / r') r := hdψ.div differentiableAt_id hr
  have hdiv : deriv (fun r' : ℝ => ψ r' z / r') r
      = (deriv (fun r' : ℝ => ψ r' z) r * r - ψ r z) / r ^ 2 := by
    rw [show (fun r' : ℝ => ψ r' z / r') = ((fun r' : ℝ => ψ r' z) / (id : ℝ → ℝ))
        from by funext r'; rfl]
    rw [deriv_div hdψ differentiableAt_id hr]
    simp
  have hdB : DifferentiableAt ℝ (fun r' : ℝ => deriv (fun r' : ℝ => ψ r' z) r') r := by
    have h1 : ContDiffAt ℝ 1 (deriv (fun r' : ℝ => ψ r' z)) r :=
      hslice.derivWithin (m := 1) (by norm_num)
    exact h1.differentiableAt (by norm_num)
  have hB : deriv (fun r' : ℝ => -(ψ r' z / r') - deriv (fun r' : ℝ => ψ r' z) r') r
      = -((deriv (fun r' : ℝ => ψ r' z) r * r - ψ r z) / r ^ 2)
        - deriv (fun r' : ℝ => deriv (fun r' : ℝ => ψ r' z) r') r := by
    rw [show (fun r' : ℝ => -(ψ r' z / r') - deriv (fun r' : ℝ => ψ r' z) r')
        = ((- fun r' : ℝ => ψ r' z / r') - fun r' : ℝ => deriv (fun r' : ℝ => ψ r' z) r')
        from by funext r'; rfl]
    rw [deriv_sub hdq.neg hdB]
    rw [deriv.neg]
    rw [hdiv]
  simp only [Work.Cyl.vortTheta, Work.Cyl.cylOp, Work.Cyl.pdZ, Work.Cyl.pdR, Work.Cyl.pdRR,
    Work.Cyl.pdZZ]
  rw [hB]
  field_simp
  ring

end Work.Cyl
