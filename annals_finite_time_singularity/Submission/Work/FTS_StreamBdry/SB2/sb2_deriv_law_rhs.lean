import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_StreamBdry.SB2

theorem sb2_deriv_law_rhs {αG : ℝ} {P F : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hd2 : DifferentiableAt ℝ (fun z' => Work.Spaces.DzIter 2 P z' θ) z)
    (hd1 : DifferentiableAt ℝ (fun z' => Work.Spaces.DzIter 1 P z' θ) z)
    (hd0 : DifferentiableAt ℝ (fun z' => P z' θ) z)
    (hdF : DifferentiableAt ℝ (fun z' => F z' θ) z) :
    z * deriv (fun z' => -(αG ^ 2 * Work.Spaces.DzIter 2 P z' θ
            + 5 * αG * Work.Spaces.DzIter 1 P z' θ + 6 * P z' θ) - F z' θ) z
      = -(αG ^ 2 * Work.Spaces.DzIter 3 P z θ + 5 * αG * Work.Spaces.DzIter 2 P z θ
            + 6 * Work.Spaces.DzIter 1 P z θ) - Work.Spaces.Dz F z θ := by
  -- `D_z^{k+1} X z θ = z * deriv (fun z' => D_z^k X z' θ) z`, definitionally;
  -- the claim is that `z` times the derivative of the linear combination
  -- `-(αG² · D_z²P + 5αG · D_zP + 6P) - F` is the corresponding combination of
  -- `D_z`-derivatives, i.e. pure additivity/linearity of `deriv` plus one
  -- multiplication by `z`.
  have hA : HasDerivAt (fun z' => αG ^ 2 * Work.Spaces.DzIter 2 P z' θ
        + 5 * αG * Work.Spaces.DzIter 1 P z' θ + 6 * P z' θ)
      (αG ^ 2 * deriv (fun z' => Work.Spaces.DzIter 2 P z' θ) z
        + 5 * αG * deriv (fun z' => Work.Spaces.DzIter 1 P z' θ) z
        + 6 * deriv (fun z' => P z' θ) z) z :=
    ((HasDerivAt.const_mul (αG ^ 2) hd2.hasDerivAt).add
      (HasDerivAt.const_mul (5 * αG) hd1.hasDerivAt)).add
        (HasDerivAt.const_mul 6 hd0.hasDerivAt)
  have hD : deriv (fun z' => -(αG ^ 2 * Work.Spaces.DzIter 2 P z' θ
        + 5 * αG * Work.Spaces.DzIter 1 P z' θ + 6 * P z' θ) - F z' θ) z
      = -(αG ^ 2 * deriv (fun z' => Work.Spaces.DzIter 2 P z' θ) z
        + 5 * αG * deriv (fun z' => Work.Spaces.DzIter 1 P z' θ) z
        + 6 * deriv (fun z' => P z' θ) z) - deriv (fun z' => F z' θ) z :=
    (hA.neg.sub hdF.hasDerivAt).deriv
  have h3 : Work.Spaces.DzIter 3 P z θ
      = z * deriv (fun z' => Work.Spaces.DzIter 2 P z' θ) z := rfl
  have h2 : Work.Spaces.DzIter 2 P z θ
      = z * deriv (fun z' => Work.Spaces.DzIter 1 P z' θ) z := rfl
  have h1 : Work.Spaces.DzIter 1 P z θ = z * deriv (fun z' => P z' θ) z := rfl
  have hF' : Work.Spaces.Dz F z θ = z * deriv (fun z' => F z' θ) z := rfl
  rw [hD, h3, h2, h1, hF']
  ring

end Work.FTS_StreamBdry.SB2
