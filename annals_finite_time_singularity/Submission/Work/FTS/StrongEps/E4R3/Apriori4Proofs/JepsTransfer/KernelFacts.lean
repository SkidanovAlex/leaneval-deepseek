import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Defs
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Recur
import Submission.Work.FTS.StrongEps.HkSqAux.Chain

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `JepsTransfer/KernelFacts.lean` — the elementary facts about the kernel `Jker` and the
log pull-back that the transfer estimate consumes

* `jker_even` — an even kernel (`hρs`) gives an even `Jker ρ ε`;
* `jker_momint` — `p ↦ Jker ρ ε p * (|p.1| + |p.2|)` is integrable (continuity + the support
  in the ball of radius `ε`);
* `logPull_continuous` — the log pull-back of a profile smooth on the open quadrant is
  continuous on the plane;
* `jker_conv_integrable` — consequently `p ↦ Jker ρ ε p * logPull g (y - p)` is integrable;
* `logPull_Jeps_eq` — the key identity
  `logPull (J_ε g) y = ∫ p, Jker ρ ε p * logPull g (y - p)`, expressing the mollifier as the
  even convolution on the plane.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- An even admissible kernel gives an even `Jker ρ ε`. -/
theorem jker_even {ρ : ℝ × ℝ → ℝ} (hρs : ∀ p : ℝ × ℝ, ρ (-p) = ρ p) (ε : ℝ) (p : ℝ × ℝ) :
    Work.FTS.StrongEps.Jker ρ ε (-p) = Work.FTS.StrongEps.Jker ρ ε p := by
  simp only [Work.FTS.StrongEps.Jker, smul_neg, neg_inj, hρs]

/-- The first moment of the kernel is integrable. -/
theorem jker_momint {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsMollKernel ρ) {ε : ℝ}
    (hε : 0 < ε) :
    Integrable (fun p : ℝ × ℝ =>
      Work.FTS.StrongEps.Jker ρ ε p * (|p.1| + |p.2|)) :=
  ((Work.FTS.StrongEps.Jker_continuous hρ ε).mul
      ((continuous_abs.comp continuous_fst).add (continuous_abs.comp continuous_snd)))
    |>.integrable_of_hasCompactSupport
      ((Work.FTS.StrongEps.Jker_hasCompactSupport hρ hε).mul_right)

/-- The log pull-back of a profile smooth on the open quadrant is continuous. -/
theorem logPull_continuous {g : Fn}
    (hg : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g) Work.FTS.EllipticEst.Q0) :
    Continuous (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g) :=
  Work.FTS.StrongEps.continuous_logPull_of_forall_contDiffOn hg

/-- The kernel against a translate of a continuous profile is integrable. -/
theorem jker_conv_integrable {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsMollKernel ρ)
    {ε : ℝ} (hε : 0 < ε) {G : ℝ × ℝ → ℝ} (hG : Continuous G) (y : ℝ × ℝ) :
    Integrable (fun p : ℝ × ℝ => Work.FTS.StrongEps.Jker ρ ε p * G (y - p)) :=
  ((Work.FTS.StrongEps.Jker_continuous hρ ε).mul
      (hG.comp (continuous_const.sub continuous_id)))
    |>.integrable_of_hasCompactSupport
      ((Work.FTS.StrongEps.Jker_hasCompactSupport hρ hε).mul_right)

/-- **The mollifier as an even convolution on the log plane.** -/
theorem logPull_Jeps_eq (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (g : Fn) (y : ℝ × ℝ) :
    Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull (Work.FTS.StrongEps.Jeps ρ ε g) y
      = ∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
          * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g (y - p) := by
  rw [show Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull
        (Work.FTS.StrongEps.Jeps ρ ε g) y
      = Work.FTS.StrongEps.Jeps ρ ε g (Real.exp y.1) (Real.arctan (Real.exp y.2)) from rfl,
    Work.FTS.StrongEps.Jeps_eq_integral ρ ε g (Real.exp_pos y.1)
      ⟨Real.arctan_pos.mpr (Real.exp_pos y.2), Real.arctan_lt_pi_div_two _⟩]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  simp only [Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull,
    Work.FTS.StrongEps.zShift, Work.FTS.StrongEps.thShift, Prod.fst_sub, Prod.snd_sub,
    Real.exp_sub, Real.exp_sub, Real.tan_arctan, Real.exp_neg, div_eq_mul_inv]

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer
