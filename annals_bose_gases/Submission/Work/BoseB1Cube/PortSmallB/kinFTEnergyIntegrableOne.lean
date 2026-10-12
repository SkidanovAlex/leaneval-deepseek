import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.gradient_plancherel_of_contDiff_one
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Integrability of the weighted kinetic Fourier transform at `C¹`

`Work.BoseB1Cube.PortSmallB.kinFTEnergyIntegrableOne`: for a `C¹` compactly supported real
function `u`, the second-moment integrand

`p ↦ ‖p‖² ‖kinFT (u : ℂ) p‖²`

is (Bochner) integrable on `ℝ³`.  This is the integrability half of
`Work.BoseB1Cube.PortSmallB.kinFTEnergyLintegralOne` (which additionally evaluates the
`ℝ≥0∞`-integral); it does not need the gradient-Plancherel *identity*.

## Route

Write `F := (u : ℂ)`, a `C¹` compactly supported complex function, and use the pointwise chain
rule for the `p`-convention Fourier transform in a coordinate direction `e_k = kcStdBasis k`,

`kinFT (∂_{e_k} F) p = i ⟪p, e_k⟫ · kinFT F p`
(`Work.BoseFixB1S.kinFT_fderiv_apply`, i.e. Mathlib's `Real.fourier_fderiv` read off in the
direction `e_k`).  Squaring the moduli,

`‖p‖² ‖kinFT F p‖² = Σ_k ‖kinFT (∂_{e_k} F) p‖²`
(`Submission.BoseGases.sum_inner_kcStdBasis_sq` gives `Σ_k ⟪p,e_k⟫² = ‖p‖²`).

Each directional derivative `∂_{e_k} F` is continuous with compact support, hence in `L¹ ∩ L²`, so
`kinFT (∂_{e_k} F) ∈ L²` (`Work.BoseKinLoc.Momentum.memLp_kinFT`), i.e.
`p ↦ ‖kinFT (∂_{e_k} F) p‖²` is integrable.  A finite sum of integrable functions is integrable,
and the two pointwise identities above identify that sum with the target integrand.
-/

noncomputable section

open MeasureTheory
open scoped Topology Real

namespace Work.BoseB1Cube.PortSmallB

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

theorem kinFTEnergyIntegrableOne {u : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hu : ContDiff ℝ 1 u) (hcs : HasCompactSupport u) :
    MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
      ‖p‖ ^ 2 * ‖Submission.BoseGases.kinFT (fun z : EuclideanSpace ℝ (Fin 3) => (u z : ℂ)) p‖ ^ 2) := by
  -- complexify `u`
  let F : E3 → ℂ := fun z => (u z : ℂ)
  have hF_cd : ContDiff ℝ 1 F := Complex.ofRealCLM.contDiff.comp hu
  have hF_cont : Continuous F := hF_cd.continuous
  have hF_cs : HasCompactSupport F := hcs.comp_left (by simp : ((0 : ℝ) : ℂ) = 0)
  have hF_int : Integrable F := hF_cont.integrable_of_hasCompactSupport hF_cs
  have hF_diff : Differentiable ℝ F := hF_cd.differentiable (by norm_num)
  have hFderiv_int : Integrable (fderiv ℝ F) :=
    (hF_cd.continuous_fderiv (by norm_num)).integrable_of_hasCompactSupport (hF_cs.fderiv ℝ)
  -- the three directional derivatives `∂_{e_k} F` are continuous with compact support
  have hDk_cont : ∀ k : Fin 3,
      Continuous (fun x : E3 => fderiv ℝ F x (Submission.BoseGases.kcStdBasis k)) :=
    fun k => (hF_cd.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hDk_cs : ∀ k : Fin 3,
      HasCompactSupport (fun x : E3 => fderiv ℝ F x (Submission.BoseGases.kcStdBasis k)) :=
    fun k => hF_cs.fderiv_apply ℝ (Submission.BoseGases.kcStdBasis k)
  have hDk_int : ∀ k : Fin 3,
      Integrable (fun x : E3 => fderiv ℝ F x (Submission.BoseGases.kcStdBasis k)) :=
    fun k => (hDk_cont k).integrable_of_hasCompactSupport (hDk_cs k)
  have hDk_mlp : ∀ k : Fin 3,
      MemLp (fun x : E3 => fderiv ℝ F x (Submission.BoseGases.kcStdBasis k)) 2 :=
    fun k => (hDk_cont k).memLp_of_hasCompactSupport (hDk_cs k)
  -- hence the squared moduli of their Fourier transforms are integrable
  have hDk_sq_int : ∀ k : Fin 3, Integrable (fun p : E3 =>
      ‖Submission.BoseGases.kinFT
        (fun x : E3 => fderiv ℝ F x (Submission.BoseGases.kcStdBasis k)) p‖ ^ 2) :=
    fun k => (memLp_two_iff_integrable_sq_norm
      (Work.BoseKinLoc.Momentum.continuous_kinFT_of_integrable (hDk_int k)).aestronglyMeasurable).mp
      (Work.BoseKinLoc.Momentum.memLp_kinFT (hDk_int k) (hDk_mlp k))
  -- the Fourier chain rule, squared
  have hNorm : ∀ a : ℝ, ‖((a : ℝ) : ℂ)‖ ^ 2 = a ^ 2 := fun a => by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]
    ring
  have hpt : ∀ (k : Fin 3) (p : E3),
      ‖Submission.BoseGases.kinFT
          (fun x : E3 => fderiv ℝ F x (Submission.BoseGases.kcStdBasis k)) p‖ ^ 2
        = (inner ℝ p (Submission.BoseGases.kcStdBasis k)) ^ 2
            * ‖Submission.BoseGases.kinFT F p‖ ^ 2 := by
    intro k p
    rw [Work.BoseFixB1S.kinFT_fderiv_apply hF_int hF_diff hFderiv_int k p, norm_mul, norm_mul,
      Complex.norm_I, one_mul, mul_pow, hNorm (inner ℝ p (Submission.BoseGases.kcStdBasis k))]
  -- the directional sum is integrable
  have hsumInt : Integrable (fun p : E3 => ∑ k : Fin 3,
      (inner ℝ p (Submission.BoseGases.kcStdBasis k)) ^ 2
        * ‖Submission.BoseGases.kinFT F p‖ ^ 2) :=
    integrable_finsetSum Finset.univ (fun k _ => (hDk_sq_int k).congr
      (Filter.Eventually.of_forall (fun p => hpt k p)))
  -- and the sum is the target integrand
  change Integrable (fun p : E3 => ‖p‖ ^ 2 * ‖Submission.BoseGases.kinFT F p‖ ^ 2)
  refine hsumInt.congr (Filter.Eventually.of_forall (fun p => ?_))
  show (∑ k : Fin 3, (inner ℝ p (Submission.BoseGases.kcStdBasis k)) ^ 2
      * ‖Submission.BoseGases.kinFT F p‖ ^ 2)
    = ‖p‖ ^ 2 * ‖Submission.BoseGases.kinFT F p‖ ^ 2
  rw [← Finset.sum_mul, Submission.BoseGases.sum_inner_kcStdBasis_sq]

end Work.BoseB1Cube.PortSmallB
