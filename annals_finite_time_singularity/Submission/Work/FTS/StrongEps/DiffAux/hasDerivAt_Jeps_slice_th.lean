import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.uncurry_partial_c1
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.Kernel
import Submission.Work.FTS.StrongEps.Dth_Jeps

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.DiffAux

theorem hasDerivAt_Jeps_slice_th (ρ : ℝ × ℝ → ℝ) (hρ : Work.FTS.StrongEps.IsMollKernel ρ)
    {ε : ℝ} (hε : 0 < ε) {g : ℝ → ℝ → ℝ}
    (hg : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g) Work.FTS.StrongEps.Quad)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    HasDerivAt (fun θ' => Work.FTS.StrongEps.Jeps ρ ε g z θ')
      (∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
          * (Work.Spaces.pth g (Work.FTS.StrongEps.zShift z p.1)
              (Work.FTS.StrongEps.thShift θ p.2) * deriv (fun θ' => Work.FTS.StrongEps.thShift θ' p.2) θ)) θ := by
  -- the two smoothness hypotheses of the dominated-convergence lemma
  have hf : ContDiffOn ℝ 1 (Function.uncurry g) Work.FTS.StrongEps.Quad := hg 1
  have hdf : ContinuousOn (Function.uncurry (Work.Spaces.pth g)) Work.FTS.StrongEps.Quad :=
    ((Work.Spaces.uncurry_partial_c1 Work.FTS.StrongEps.isOpen_Quad (hg 2)).2).continuousOn
  -- near `θ` the slice of `Jeps` is the `p`-integral defining it
  have hev : (fun θ' => Work.FTS.StrongEps.Jeps ρ ε g z θ')
      =ᶠ[𝓝 θ] fun θ' => ∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
          * g (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ' p.2) := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
    exact Work.FTS.StrongEps.Jeps_eq_integral ρ ε g hz hθ'
  -- the kernel is supported in the ball, so `closedBall`-restricted integrals are unrestricted
  have hF : (fun θ' => ∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
        * g (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ' p.2)
        ∂(volume.restrict (Metric.closedBall (0 : ℝ × ℝ) ε)))
      = fun θ' => ∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
        * g (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ' p.2) := by
    funext θ'
    exact setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume)
      (s := Metric.closedBall (0 : ℝ × ℝ) ε)
      (f := fun p : ℝ × ℝ => Work.FTS.StrongEps.Jker ρ ε p
        * g (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ' p.2))
      (fun p hp => by rw [Work.FTS.StrongEps.Jker_eq_zero_of_not_mem hρ hε hp, zero_mul])
  have hG : (∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
        * (Work.Spaces.pth g (Work.FTS.StrongEps.zShift z p.1)
            (Work.FTS.StrongEps.thShift θ p.2)
          * deriv (fun θ' => Work.FTS.StrongEps.thShift θ' p.2) θ))
      = ∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
        * (Work.Spaces.pth g (Work.FTS.StrongEps.zShift z p.1)
            (Work.FTS.StrongEps.thShift θ p.2)
          * deriv (fun θ' => Work.FTS.StrongEps.thShift θ' p.2) θ)
        ∂(volume.restrict (Metric.closedBall (0 : ℝ × ℝ) ε)) :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume)
      (s := Metric.closedBall (0 : ℝ × ℝ) ε)
      (f := fun p : ℝ × ℝ => Work.FTS.StrongEps.Jker ρ ε p
        * (Work.Spaces.pth g (Work.FTS.StrongEps.zShift z p.1)
            (Work.FTS.StrongEps.thShift θ p.2)
          * deriv (fun θ' => Work.FTS.StrongEps.thShift θ' p.2) θ))
      (fun p hp => by rw [Work.FTS.StrongEps.Jker_eq_zero_of_not_mem hρ hε hp, zero_mul])).symm
  have hd := Work.FTS.StrongEps.hasDerivAt_integral_Jeps_th (ρ := ρ) (ε := ε) (f := g)
    hρ hε hf hdf hz hθ
  rw [hF, ← hG] at hd
  exact hd.congr_of_eventuallyEq hev

end Work.FTS.StrongEps.DiffAux
