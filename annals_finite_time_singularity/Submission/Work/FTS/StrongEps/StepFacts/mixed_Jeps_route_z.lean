import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.Kernel
import Submission.Work.FTS.StrongEps.mixed_Jeps
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.FTS.StrongEps.KernAux.integral_mul_partFst_eq_neg
import Submission.Work.FTS.StrongEps.KernAux.deriv_shift_fst
import Submission.Work.FTS.StrongEps.KernAux.contDiff_shift
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.StepFacts

open scoped Real Topology
open MeasureTheory Set Filter

/-- Smoothness helper: if `f` is `C^n` on the open quadrant for every `n`, so is every
mixed derivative `D_z^a D_θ^b f`. -/
theorem mixed_Jeps_route_z_smooth (f : ℝ → ℝ → ℝ)
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Work.FTS.StrongEps.Quad) (a b : ℕ) :
    ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (Work.Spaces.mixed a b f))
      Work.FTS.StrongEps.Quad :=
  contDiffOn_infty.mp (Work.FTS.LocData.contDiffOn_mixed Work.FTS.StrongEps.isOpen_Quad
    (contDiffOn_infty.mpr hf) a b)

/-- The index bookkeeping: `D_z (D_z^{j-1} D_θ^i f) = D_z^j D_θ^i f` for `1 ≤ j`. -/
theorem mixed_Jeps_route_z_Dz_pred (f : ℝ → ℝ → ℝ) {j : ℕ} (hj : 1 ≤ j) (i : ℕ) :
    Work.Spaces.Dz (Work.Spaces.mixed (j - 1) i f) = Work.Spaces.mixed j i f := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, (Nat.sub_add_cancel hj).symm⟩
  rw [Nat.add_sub_cancel]
  simp only [Work.Spaces.mixed, Work.Spaces.DzIter_succ]

-- context: namespace Work.FTS.StrongEps.StepFacts; imports Mathlib, Submission.Work.FTS.StrongEps.Basic, .Kernel, .mixed_Jeps, Submission.Work.Spaces.Defs
-- `Jeps ρ ε f` is the log-coordinate mollifier; `Jker ρ ε p = ε⁻¹^2 * ρ (ε⁻¹ • p)`; `zShift z p = z*exp(-p)`,
-- `thShift θ p = arctan (tan θ * exp(-p))`; `Quad = (0,∞) × (0,π/2)`; `mixed j i = D_z^j D_θ^i`.
theorem mixed_Jeps_route_z (ρ : ℝ × ℝ → ℝ) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {ε : ℝ} (hε : 0 < ε) {f : ℝ → ℝ → ℝ}
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Work.FTS.StrongEps.Quad)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) (j i : ℕ) (hj : 1 ≤ j) :
    Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ ε f) z θ
      = ∫ p : ℝ × ℝ,
          deriv (fun s : ℝ => Work.FTS.StrongEps.Jker ρ ε (s, p.2)) p.1
          * Work.Spaces.mixed (j - 1) i f (Work.FTS.StrongEps.zShift z p.1)
              (Work.FTS.StrongEps.thShift θ p.2) := by
  -- the profile carrying the remaining `D_z^{j-1}` is smooth on the open quadrant
  have hsm : ∀ n : ℕ, ContDiffOn ℝ n
      (Function.uncurry (Work.Spaces.mixed (j - 1) i f)) Work.FTS.StrongEps.Quad :=
    mixed_Jeps_route_z_smooth f hf (j - 1) i
  have hDz : Work.Spaces.Dz (Work.Spaces.mixed (j - 1) i f) = Work.Spaces.mixed j i f :=
    mixed_Jeps_route_z_Dz_pred f hj i
  -- Step 1: `mixed_Jeps` and the integral (log-coordinate convolution) form of `Jeps`
  have hbase : Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ ε f) z θ
      = ∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
          * Work.Spaces.mixed j i f (Work.FTS.StrongEps.zShift z p.1)
              (Work.FTS.StrongEps.thShift θ p.2) := by
    rw [Work.FTS.StrongEps.mixed_Jeps ρ hρ.moll hε hf hz hθ j i,
      Work.FTS.StrongEps.Jeps_eq_integral ρ ε (Work.Spaces.mixed j i f) hz hθ]
  rw [hbase]
  -- Step 2: integration by parts in `p₁`, moving the derivative onto the kernel
  have hv : ContDiff ℝ 1 (fun p : ℝ × ℝ =>
      Work.Spaces.mixed (j - 1) i f (Work.FTS.StrongEps.zShift z p.1)
        (Work.FTS.StrongEps.thShift θ p.2)) :=
    Work.FTS.StrongEps.KernAux.contDiff_shift _ hz hθ hsm 1
  have hu : ContDiff ℝ 1 (Work.FTS.StrongEps.Jker ρ ε) :=
    Work.FTS.StrongEps.Jker_smooth hρ ε (n := 1)
  have hus : HasCompactSupport (Work.FTS.StrongEps.Jker ρ ε) :=
    Work.FTS.StrongEps.Jker_hasCompactSupport hρ.moll hε
  have hIBP : (∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
        * deriv (fun s : ℝ => Work.Spaces.mixed (j - 1) i f
            (Work.FTS.StrongEps.zShift z s) (Work.FTS.StrongEps.thShift θ p.2)) p.1)
      = - ∫ p : ℝ × ℝ, deriv (fun s : ℝ => Work.FTS.StrongEps.Jker ρ ε (s, p.2)) p.1
          * Work.Spaces.mixed (j - 1) i f (Work.FTS.StrongEps.zShift z p.1)
              (Work.FTS.StrongEps.thShift θ p.2) :=
    Work.FTS.StrongEps.KernAux.integral_mul_partFst_eq_neg hu hus hv
  -- the chain rule: differentiating the shifted profile in the shift parameter is `-D_z`
  have hvs : ∀ p : ℝ × ℝ,
      deriv (fun s : ℝ => Work.Spaces.mixed (j - 1) i f
          (Work.FTS.StrongEps.zShift z s) (Work.FTS.StrongEps.thShift θ p.2)) p.1
        = - Work.Spaces.mixed j i f (Work.FTS.StrongEps.zShift z p.1)
              (Work.FTS.StrongEps.thShift θ p.2) := by
    intro p
    rw [Work.FTS.StrongEps.KernAux.deriv_shift_fst (Work.Spaces.mixed (j - 1) i f)
      hz hθ (hsm 1) p, hDz]
  calc ∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
        * Work.Spaces.mixed j i f (Work.FTS.StrongEps.zShift z p.1)
            (Work.FTS.StrongEps.thShift θ p.2)
      = ∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
          * (- deriv (fun s : ℝ => Work.Spaces.mixed (j - 1) i f
              (Work.FTS.StrongEps.zShift z s) (Work.FTS.StrongEps.thShift θ p.2)) p.1) := by
        refine integral_congr_ae (Eventually.of_forall fun p => ?_)
        simp only [hvs p]
        ring
    _ = - ∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
          * deriv (fun s : ℝ => Work.Spaces.mixed (j - 1) i f
              (Work.FTS.StrongEps.zShift z s) (Work.FTS.StrongEps.thShift θ p.2)) p.1 := by
        rw [← integral_neg]
        exact integral_congr_ae (Eventually.of_forall fun p => by ring)
    _ = - (- ∫ p : ℝ × ℝ, deriv (fun s : ℝ => Work.FTS.StrongEps.Jker ρ ε (s, p.2)) p.1
          * Work.Spaces.mixed (j - 1) i f (Work.FTS.StrongEps.zShift z p.1)
              (Work.FTS.StrongEps.thShift θ p.2)) := by rw [hIBP]
    _ = ∫ p : ℝ × ℝ, deriv (fun s : ℝ => Work.FTS.StrongEps.Jker ρ ε (s, p.2)) p.1
          * Work.Spaces.mixed (j - 1) i f (Work.FTS.StrongEps.zShift z p.1)
              (Work.FTS.StrongEps.thShift θ p.2) := by rw [neg_neg]

end Work.FTS.StrongEps.StepFacts
