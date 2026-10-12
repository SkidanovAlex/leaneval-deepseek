import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.L1Tails.DefsC
import Submission.Work.BoseBoxFock.L1Tails.latticeDirichlet
import Submission.Work.BoseBoxFock.L1Tails.secondMomentPlancherelOne
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.L1Tails.latFrameSlice

open MeasureTheory Filter

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- Truncated lattice-Dirichlet (frame) inequality for a `C¹` function supported in the box
`boxL ℓ`: for every finite set `T` of lattice modes,
`Σ_{n∈T} ‖κ_n‖²‖ĝ(κ_n)‖² ≤ ℓ³ ∫_w Σ_j ‖∂_{w_j} g w‖²`.  Route: `latticeDirichlet` gives the
`HasSum` of the full lattice sum with value `ℓ³·(2π)⁻³∫_p ‖p‖²‖kinFT g p‖²`; the partial sum over
the finite `T` is at most the total (`Summable.sum_le_tsum`, all terms nonnegative);
`secondMomentPlancherelOne` rewrites `(2π)⁻³∫_p ‖p‖²‖kinFT g p‖²` as `Σ_j ∫_z ‖∂_{e_j} g z‖²`
(using `Submission.BoseGases.kcStdBasis j = EuclideanSpace.single j 1` and
`HasCompactSupport g` from `hts`), and `MeasureTheory.integral_finsetSum` moves the `Σ_j` inside. -/
theorem latFrame_g_le {ℓ : ℝ} (hℓ : 0 < ℓ)
    {g : EuclideanSpace ℝ (Fin 3) → ℂ} (hg : ContDiff ℝ 1 g)
    (hts : tsupport g ⊆ Work.BoseK15.corpusBox.boxL ℓ) (T : Finset (Fin 3 → ℤ)) :
    ∑ n ∈ T, ‖Work.BoseBoxFock.kappaL ℓ n‖ ^ 2
        * ‖Submission.BoseGases.kinFT g (Work.BoseBoxFock.kappaL ℓ n)‖ ^ 2
      ≤ ℓ ^ 3 * ∫ w : EuclideanSpace ℝ (Fin 3), ∑ j : Fin 3,
          ‖fderiv ℝ g w (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 := by
  -- `g` is compactly supported, its support lying in the compact box `boxL ℓ`
  have hcs : HasCompactSupport g :=
    (Work.BoseK15.corpusBox.boxL_compact ℓ).of_isClosed_subset (isClosed_tsupport g) hts
  -- the full lattice sum converges to `ℓ³(2π)⁻³∫_p ‖p‖²‖ĝ(p)‖²`
  have hsum := Work.BoseBoxFock.L1Tails.latticeDirichlet hℓ hg hts
  -- the partial sum over `T` is dominated by the total sum (all terms are nonnegative)
  have h1 : ∑ n ∈ T, ‖Work.BoseBoxFock.kappaL ℓ n‖ ^ 2
        * ‖Submission.BoseGases.kinFT g (Work.BoseBoxFock.kappaL ℓ n)‖ ^ 2
      ≤ ℓ ^ 3 * (((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3,
          ‖p‖ ^ 2 * ‖Submission.BoseGases.kinFT g p‖ ^ 2) := by
    refine le_of_le_of_eq (hsum.summable.sum_le_tsum T (fun n _ => by positivity)) ?_
    rw [hsum.tsum_eq]
  -- it remains to identify the continuum second moment with the Dirichlet energy
  refine le_of_le_of_eq h1 ?_
  have hcont : ∀ j : Fin 3, Continuous
      (fun z : E3 => fderiv ℝ g z (Submission.BoseGases.kcStdBasis j)) :=
    fun j => (hg.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hcsj : ∀ j : Fin 3, HasCompactSupport
      (fun z : E3 => fderiv ℝ g z (Submission.BoseGases.kcStdBasis j)) :=
    fun j => hcs.fderiv_apply ℝ (Submission.BoseGases.kcStdBasis j)
  have hint : ∀ j : Fin 3, Integrable
      (fun z : E3 => ‖fderiv ℝ g z (Submission.BoseGases.kcStdBasis j)‖ ^ 2) :=
    fun j => (MeasureTheory.memLp_two_iff_integrable_sq_norm
      (hcont j).aestronglyMeasurable).mp ((hcont j).memLp_of_hasCompactSupport (hcsj j))
  have hstep : (∑ j : Fin 3, ∫ z : E3,
        ‖fderiv ℝ g z (Submission.BoseGases.kcStdBasis j)‖ ^ 2)
      = ∫ w : E3, ∑ j : Fin 3,
          ‖fderiv ℝ g w (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 := by
    rw [← MeasureTheory.integral_finsetSum (Finset.univ : Finset (Fin 3))
      (fun j _ => hint j)]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp [Submission.BoseGases.kcStdBasis]
  rw [Work.BoseBoxFock.L1Tails.secondMomentPlancherelOne hg hcs, hstep]

end Work.BoseBoxFock.L1Tails.latFrameSlice
