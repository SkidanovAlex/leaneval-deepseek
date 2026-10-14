import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Submission.Work.FTS.StrongEps.EpsLimitDefs
import Submission.Work.FTS.StrongEps.PZeroAux.bumpHkNormBound
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongEps.SmoothOpen_Jeps
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.AuxProof
import Submission.Work.FTS.StrongPersist.SupOpenH2
import Submission.Work.FTS_LocDatum3a.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-- **The `ℋ⁶`-size of the projected family**: the projection `P₀` and the mollifier `J_ε` are
jointly bounded on `ℋ⁶`, uniformly in `ε ∈ (0,1]`. -/
theorem HkNorm_JfamP_le {ρ : ℝ × ℝ → ℝ} (hρ : IsSmoothKernel ρ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {α ε : ℝ}, α ∈ Set.Ioc 0 1 → ε ∈ Set.Ioc 0 1 →
      ∀ {g : Fam} {s : ℝ},
        (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (slice g s)) Quad) →
        Work.Spaces.HkMem α 6 (slice g s) →
        Work.Spaces.HkMem α 6 (slice (JfamP ρ ε g) s) ∧
          Work.FTS.StrongGlobal.Xn6 α (slice (JfamP ρ ε g) s)
            ≤ A * Work.FTS.StrongGlobal.Xn6 α (slice g s) := by
  obtain ⟨C, hCpos, hC⟩ := HkSq_Jeps_le ρ hρ.moll
  obtain ⟨A', hA'pos, hA'⟩ := Work.FTS.StrongEps.PZeroAux.hkNorm_Pz_le
  refine ⟨A' * Real.exp (C / 2), by positivity, ?_⟩
  intro α ε hα hε g s hsm hmem
  have hε0 : 0 < ε := hε.1
  have hsmJ : Work.FTS.EllipticEst.SmoothOpen (Jeps ρ ε (slice g s)) :=
    smoothOpen_Jeps ρ hρ hε0 hsm
  have hmemJ : Work.Spaces.HkMem α 6 (Jeps ρ ε (slice g s)) :=
    HkMem_Jeps hρ.moll hα hε0 hsm hmem
  -- the two conclusions of `slice (JfamP ρ ε g) s = Pz (Jeps ρ ε (slice g s))`
  have hmemP : Work.Spaces.HkMem α 6 (slice (JfamP ρ ε g) s) :=
    Work.FTS.StrongEps.PZeroAux.PzJepsHkMem 6 hρ hα hε0 hsm hmem
  refine ⟨hmemP, ?_⟩
  -- the `ℋ⁶`-norm bound, in the shape `Xn6 = HkNorm α 6`
  have hJ : Work.Spaces.HkNorm α 6 (Jeps ρ ε (slice g s))
      ≤ Real.exp (C / 2) * Work.Spaces.HkNorm α 6 (slice g s) := by
    have hsq := hC α hα 6 ε hε0 hε.2 (slice g s) hsm hmem hmemJ
    rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm]
    calc Real.sqrt (Work.Spaces.HkSq α 6 (Jeps ρ ε (slice g s)))
        ≤ Real.sqrt (Real.exp (C * ε) * Work.Spaces.HkSq α 6 (slice g s)) :=
          Real.sqrt_le_sqrt hsq
      _ = Real.sqrt (Real.exp (C * ε)) * Real.sqrt (Work.Spaces.HkSq α 6 (slice g s)) :=
          Real.sqrt_mul (Real.exp_pos _).le _
      _ = Real.exp (C * ε / 2) * Work.Spaces.HkNorm α 6 (slice g s) := by
          rw [Real.exp_half, Work.Spaces.HkNorm]
      _ ≤ Real.exp (C / 2) * Work.Spaces.HkNorm α 6 (slice g s) := by
          refine mul_le_mul_of_nonneg_right ?_ (Work.Spaces.HkNorm_nonneg _ _ _)
          exact Real.exp_le_exp.mpr (by nlinarith [hε.2, hCpos])
  have hP : Work.Spaces.HkNorm α 6 (Work.FTS.StrongEps.Pz (Jeps ρ ε (slice g s)))
      ≤ A' * Work.Spaces.HkNorm α 6 (Jeps ρ ε (slice g s)) :=
    hA' α hα 6 le_rfl (Jeps ρ ε (slice g s)) hsmJ hmemJ
  have hmain : Work.Spaces.HkNorm α 6 (Work.FTS.StrongEps.Pz (Jeps ρ ε (slice g s)))
      ≤ A' * Real.exp (C / 2) * Work.Spaces.HkNorm α 6 (slice g s) := by
    calc Work.Spaces.HkNorm α 6 (Work.FTS.StrongEps.Pz (Jeps ρ ε (slice g s)))
        ≤ A' * Work.Spaces.HkNorm α 6 (Jeps ρ ε (slice g s)) := hP
      _ ≤ A' * (Real.exp (C / 2) * Work.Spaces.HkNorm α 6 (slice g s)) :=
          mul_le_mul_of_nonneg_left hJ hA'pos.le
      _ = A' * Real.exp (C / 2) * Work.Spaces.HkNorm α 6 (slice g s) := by ring
  -- unfold the two `Xn6` occurrences
  simpa only [Work.FTS.StrongGlobal.Xn6, slice_JfamP] using hmain

end Work.FTS.StrongEps
