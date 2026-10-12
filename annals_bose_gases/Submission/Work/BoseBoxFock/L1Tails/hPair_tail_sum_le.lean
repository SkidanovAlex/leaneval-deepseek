import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.L1Tails.conjSlice.conjSlice_contDiff_tsupport
import Submission.Work.BoseBoxFock.L1Tails.conjSlice.sum_norm_fderiv_conjSlice
import Submission.Work.BoseBoxFock.L1Tails.hPairFubini.hPair_eq_integral_conjKinFT
import Submission.Work.BoseBoxFock.L1Tails.hPairSqLe.norm_hPair_sq_le
import Submission.Work.BoseBoxFock.L1Tails.kinFTSlice.memLp_kinFT_conjSlice
import Submission.Work.BoseBoxFock.L1Tails.latDefs
import Submission.Work.BoseBoxFock.L1Tails.latFrameSlice.latFrame_g_le
import Submission.Work.BoseBoxFock.L1Tails.sliceDeriv.integrable_sliceDeriv_joint
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory
open scoped BigOperators Real

namespace Work.BoseBoxFock.L1Tails

set_option autoImplicit false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

open sliceDeriv conjSlice kinFTSlice hPairFubini hPairSqLe latFrameSlice

/-- Sharp finite-set bound for the `‖κ_n‖^2`-weighted lattice pairing of a smooth box-supported
kernel.  Route: write
`Ȟ_n = ∫_y e^{-i⟪κ_n,y⟫} (∫_w e^{i⟪κ_n,w⟫} H w y dw) dy` (Fubini), whose inner integral is
`conj (kinFT (fun w => conj (H w y)) (κ_n))`; the `y`-integrand vanishes for `y ∉ boxL ℓ`
(`volume (boxL ℓ) = ℓ^3`), so Cauchy–Schwarz in `y` gives
`‖Ȟ_n‖^2 ≤ ℓ^3 ∫_y ‖kinFT (fun w => conj (H w y)) (κ_n)‖^2 dy`, and summing over the finite `T`
(Tonelli) the inner lattice sum at fixed `y` is controlled by
`Work.BoseBoxFock.L1Tails.latticeDirichlet` (the weighted frame identity, whose value
`ℓ^3 (2π)^{-3} ∫_p ‖p‖^2 ‖kinFT g p‖^2` equals `ℓ^3 Σ_j ∫_x ‖∂_j g x‖^2` by
`Work.BoseKinLoc.Momentum.kinFT_l1l2_plancherel`), while `fderiv` commutes with conjugation. -/
theorem hPair_tail_sum_le {ℓ : ℝ} (hℓ : 0 < ℓ)
    {H : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hH : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry H))
    (hHs : ∀ w y, H w y ≠ 0 →
      w ∈ Work.BoseK15.corpusBox.boxL ℓ ∧ y ∈ Work.BoseK15.corpusBox.boxL ℓ)
    (T : Finset (Fin 3 → ℤ)) :
    ∑ n ∈ T, ‖Work.BoseBoxFock.kappaL ℓ n‖ ^ 2 * ‖Work.BoseBoxFock.L1Tails.hPair ℓ H n‖ ^ 2
      ≤ ℓ ^ 6 * ∫ w, ∫ y, ∑ j : Fin 3,
          ‖fderiv ℝ (fun w' => H w' y) w (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 := by

  classical
  -- per-mode Cauchy–Schwarz
  have hstep1 : ∀ n : Fin 3 → ℤ, ‖hPair ℓ H n‖ ^ 2
      ≤ ℓ ^ 3 * ∫ y : E3, ‖Submission.BoseGases.kinFT (fun w => (starRingEnd ℂ) (H w y))
          (kappaL ℓ n)‖ ^ 2 :=
    fun n => norm_hPair_sq_le hℓ hH hHs n (memLp_kinFT_conjSlice hℓ hH hHs n)
      (hPair_eq_integral_conjKinFT hℓ hH hHs n)
  -- per-`y` frame inequality
  have hstep2 : ∀ y : E3,
      ∑ n ∈ T, ‖kappaL ℓ n‖ ^ 2 * ‖Submission.BoseGases.kinFT (fun w => (starRingEnd ℂ) (H w y))
          (kappaL ℓ n)‖ ^ 2
        ≤ ℓ ^ 3 * ∫ w : E3, ∑ j : Fin 3,
            ‖fderiv ℝ (fun w' => H w' y) w (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 := by
    intro y
    have hcd := conjSlice_contDiff_tsupport hH hHs y
    have hframe := latFrame_g_le hℓ hcd.1 hcd.2 T
    have hbridge : (∫ w : E3, ∑ j : Fin 3,
          ‖fderiv ℝ (fun w' => (starRingEnd ℂ) (H w' y)) w (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)
        = ∫ w : E3, ∑ j : Fin 3,
          ‖fderiv ℝ (fun w' => H w' y) w (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 :=
      integral_congr_ae (Filter.Eventually.of_forall (fun w => sum_norm_fderiv_conjSlice hH y w))
    exact hframe.trans (mul_le_mul_of_nonneg_left (le_of_eq hbridge) (by positivity))
  -- integrability of the two sides
  have hmem : ∀ n : Fin 3 → ℤ, MemLp (fun y : E3 => Submission.BoseGases.kinFT
      (fun w => (starRingEnd ℂ) (H w y)) (kappaL ℓ n)) 2 (volume : Measure E3) :=
    fun n => memLp_kinFT_conjSlice hℓ hH hHs n
  have hint : ∀ n : Fin 3 → ℤ, Integrable (fun y : E3 => ‖Submission.BoseGases.kinFT
      (fun w => (starRingEnd ℂ) (H w y)) (kappaL ℓ n)‖ ^ 2) volume :=
    fun n => (memLp_two_iff_integrable_sq_norm (hmem n).aestronglyMeasurable).mp (hmem n)
  have hgint : ∀ n : Fin 3 → ℤ, Integrable (fun y : E3 => ‖kappaL ℓ n‖ ^ 2
      * ‖Submission.BoseGases.kinFT (fun w => (starRingEnd ℂ) (H w y)) (kappaL ℓ n)‖ ^ 2)
      volume := fun n => (hint n).const_mul _
  -- the slice-derivative energy: joint integrability, and the Fubini swap
  have hjoint : Integrable (fun p : E3 × E3 => ∑ j : Fin 3,
      ‖fderiv ℝ (fun w' => H w' p.2) p.1 (EuclideanSpace.single j (1 : ℝ))‖ ^ 2) volume :=
    integrable_sliceDeriv_joint hH hHs
  have hCint : Integrable (fun y : E3 => ∫ w : E3, ∑ j : Fin 3,
      ‖fderiv ℝ (fun w' => H w' y) w (EuclideanSpace.single j (1 : ℝ))‖ ^ 2) volume :=
    hjoint.integral_prod_right
  have hCint3 : Integrable (fun y : E3 => ℓ ^ 3 * ∫ w : E3, ∑ j : Fin 3,
      ‖fderiv ℝ (fun w' => H w' y) w (EuclideanSpace.single j (1 : ℝ))‖ ^ 2) volume :=
    hCint.const_mul _
  have hswap : (∫ w : E3, ∫ y : E3, ∑ j : Fin 3,
        ‖fderiv ℝ (fun w' => H w' y) w (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)
      = ∫ y : E3, ∫ w : E3, ∑ j : Fin 3,
        ‖fderiv ℝ (fun w' => H w' y) w (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 :=
    integral_integral_swap hjoint
  calc ∑ n ∈ T, ‖kappaL ℓ n‖ ^ 2 * ‖hPair ℓ H n‖ ^ 2
      ≤ ℓ ^ 3 * ∑ n ∈ T, (‖kappaL ℓ n‖ ^ 2 * ∫ y : E3,
          ‖Submission.BoseGases.kinFT (fun w => (starRingEnd ℂ) (H w y)) (kappaL ℓ n)‖ ^ 2) := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum (fun n _ => ?_)
        calc ‖kappaL ℓ n‖ ^ 2 * ‖hPair ℓ H n‖ ^ 2
            ≤ ‖kappaL ℓ n‖ ^ 2 * (ℓ ^ 3 * ∫ y : E3,
                ‖Submission.BoseGases.kinFT (fun w => (starRingEnd ℂ) (H w y))
                  (kappaL ℓ n)‖ ^ 2) :=
              mul_le_mul_of_nonneg_left (hstep1 n) (by positivity)
          _ = ℓ ^ 3 * (‖kappaL ℓ n‖ ^ 2 * ∫ y : E3,
                ‖Submission.BoseGases.kinFT (fun w => (starRingEnd ℂ) (H w y))
                  (kappaL ℓ n)‖ ^ 2) := by ring
    _ = ℓ ^ 3 * ∫ y : E3, ∑ n ∈ T, (‖kappaL ℓ n‖ ^ 2
          * ‖Submission.BoseGases.kinFT (fun w => (starRingEnd ℂ) (H w y)) (kappaL ℓ n)‖ ^ 2) := by
        congr 1
        refine (Finset.sum_congr rfl (fun n _ => (integral_const_mul _ _).symm)).trans ?_
        exact (integral_finsetSum T (fun n _ => hgint n)).symm
    _ ≤ ℓ ^ 3 * ∫ y : E3, ℓ ^ 3 * ∫ w : E3, ∑ j : Fin 3,
          ‖fderiv ℝ (fun w' => H w' y) w (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 :=
        mul_le_mul_of_nonneg_left
          (integral_mono (integrable_finsetSum T (fun n _ => hgint n)) hCint3
            (fun y => hstep2 y)) (by positivity)
    _ = ℓ ^ 3 * (ℓ ^ 3 * ∫ y : E3, ∫ w : E3, ∑ j : Fin 3,
          ‖fderiv ℝ (fun w' => H w' y) w (EuclideanSpace.single j (1 : ℝ))‖ ^ 2) := by
        rw [integral_const_mul]
    _ = ℓ ^ 6 * ∫ w : E3, ∫ y : E3, ∑ j : Fin 3,
          ‖fderiv ℝ (fun w' => H w' y) w (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 := by
        rw [← hswap]; ring

end Work.BoseBoxFock.L1Tails
