import Mathlib.Order.CompletePartialOrder
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.moment_two_kinFT
import Submission.Work.BoseBoxFock.qCoeff_eq_ft
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The second lattice moment of a cube-supported complex state

`Work.BoseBoxFock.moment2LatticeC` is the second lattice-moment identity

`Σ_n ℓ⁻³‖k_n‖²‖kinFT g k_n‖² = (2π)⁻³ ∫_p ‖p‖²‖kinFT g p‖²`,  `k_n = kmomInt ℓ n = ℓ⁻¹•(2πn)`,

for a smooth compactly supported state `g : ℝ³ → ℂ` whose support lies in the *full cube*
`Λ(ℓ) = boxL ℓ = ℓ • [-1/2,1/2]³` of side `ℓ` (rather than in the inscribed ball, which is the
hypothesis of the already-recorded `Work.BoseBoxFock.moment2LatticeComplex` /
`Work.BoseBoxFock.moment_two_kinFT`).

This is the same computation as `moment_two_kinFT`; the only difference is that the support
hypothesis already hands us (i) `HasCompactSupport g` directly and (ii) the box-containment
`tsupport g ⊆ boxL ℓ` used by the frame identity.  Both remaining inputs already accept cube
support:

* `Work.BoseBoxFock.frame_lattice_ball` (the `j = 0` frame/Poisson-summation identity
  `Σ_n ℓ⁻³‖kinFT w k_n‖² = (2π)⁻³∫_p ‖kinFT w p‖²`) is stated for `tsupport w ⊆ boxL ℓ` — the
  lattice translates of the half-open cube tile, and the closed cube meets them only in
  measure-zero faces, so no aliasing occurs;
* `Work.BoseBoxFock.mom2Summable` is the summability of the lattice samples, also for cube
  support.

The weight `‖k_n‖²` is traded for a sum over the three directional derivatives by the
complex-valued chain rule `Work.BoseBoxFock.kinFT_fderiv_applyC`
(`kinFT (∂_i g) p = i⟪p,e_i⟫ · kinFT g p`), which turns the pointwise identity into

`‖p‖²‖kinFT g p‖² = Σ_i ‖kinFT (∂_i g) p‖²`

(`Work.BoseBoxFock.normSq_kinFT_eq_sum_normSq_fderiv`, with `Σ_i ⟪p,e_i⟫² = ‖p‖²`).  Since
`tsupport (∂_i g) ⊆ tsupport g ⊆ boxL ℓ`, the frame identity applies to each `∂_i g`; summing
over `i` (and exchanging the finite sum with the `tsum` via summability, and with the integral
via the integrability of `p ↦ ‖kinFT (∂_i g) p‖²`) gives the claim.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock

theorem moment2LatticeC {ℓ : ℝ} (hℓ : 0 < ℓ) {g : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hg : ContDiff ℝ (⊤ : ENat) g) (hgc : HasCompactSupport g)
    (hsupp : tsupport g ⊆ Work.BoseK15.corpusBox.boxL ℓ) :
    (∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * ‖Work.BoseBoxFock.kmomInt ℓ n‖ ^ 2
        * ‖Submission.BoseGases.kinFT g (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2)
      = ((2 * Real.pi) ^ 3)⁻¹ *
          ∫ p : EuclideanSpace ℝ (Fin 3), ‖p‖ ^ 2 * ‖Submission.BoseGases.kinFT g p‖ ^ 2 := by
  -- the directional derivatives `∂_i g` are smooth, compactly supported and box-supported
  have hcd : ∀ i : Fin 3, ContDiff ℝ (⊤ : ENat)
      (fun z : EuclideanSpace ℝ (Fin 3) =>
        fderiv ℝ g z (Submission.BoseGases.kcStdBasis i)) := by
    intro i
    have hf' : ContDiff ℝ (⊤ : ENat) (fderiv ℝ g) :=
      ContDiff.fderiv_right (f := g) (m := (⊤ : ENat)) (n := (⊤ : ENat)) hg (by simp)
    exact hf'.clm_apply contDiff_const
  have hcs : ∀ i : Fin 3, HasCompactSupport
      (fun z : EuclideanSpace ℝ (Fin 3) =>
        fderiv ℝ g z (Submission.BoseGases.kcStdBasis i)) :=
    fun i => hgc.fderiv_apply ℝ (Submission.BoseGases.kcStdBasis i)
  have hsupp' : ∀ i : Fin 3, tsupport
      (fun z : EuclideanSpace ℝ (Fin 3) =>
        fderiv ℝ g z (Submission.BoseGases.kcStdBasis i))
      ⊆ Work.BoseK15.corpusBox.boxL ℓ :=
    fun i => (tsupport_fderiv_apply_subset ℝ (Submission.BoseGases.kcStdBasis i)).trans hsupp
  -- the pointwise second-moment identity
  have hpoint : ∀ p : EuclideanSpace ℝ (Fin 3),
      ‖p‖ ^ 2 * ‖Submission.BoseGases.kinFT g p‖ ^ 2
      = ∑ i : Fin 3, ‖Submission.BoseGases.kinFT
          (fun z => fderiv ℝ g z (Submission.BoseGases.kcStdBasis i)) p‖ ^ 2 :=
    fun p => normSq_kinFT_eq_sum_normSq_fderiv hg hgc p
  -- summability of each differentiated lattice series
  have hsumm : ∀ i : Fin 3, Summable (fun n : Fin 3 → ℤ => (ℓ ^ 3)⁻¹
      * ‖Submission.BoseGases.kinFT
          (fun z => fderiv ℝ g z (Submission.BoseGases.kcStdBasis i))
          (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2) :=
    fun i => mom2Summable hℓ (hcd i) (hcs i) (hsupp' i)
  -- the frame identity for each differentiated state
  have hframe : ∀ i : Fin 3, (∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹
      * ‖Submission.BoseGases.kinFT
          (fun z => fderiv ℝ g z (Submission.BoseGases.kcStdBasis i))
          (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2)
      = ((2 * Real.pi) ^ 3)⁻¹ * ∫ p, ‖Submission.BoseGases.kinFT
          (fun z => fderiv ℝ g z (Submission.BoseGases.kcStdBasis i)) p‖ ^ 2 :=
    fun i => frame_lattice_ball hℓ (hcd i) (hcs i) (hsupp' i)
  -- integrability of the transformed differentiated states
  have hInt : ∀ i : Fin 3, Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
      ‖Submission.BoseGases.kinFT
        (fun z => fderiv ℝ g z (Submission.BoseGases.kcStdBasis i)) p‖ ^ 2) := by
    intro i
    have h1 : Integrable
        (fun z : EuclideanSpace ℝ (Fin 3) =>
          fderiv ℝ g z (Submission.BoseGases.kcStdBasis i)) :=
      (hcd i).continuous.integrable_of_hasCompactSupport (hcs i)
    have h2 : MemLp (fun z : EuclideanSpace ℝ (Fin 3) =>
        fderiv ℝ g z (Submission.BoseGases.kcStdBasis i)) 2 volume :=
      (hcd i).continuous.memLp_of_hasCompactSupport (hcs i)
    exact (memLp_two_iff_integrable_sq_norm
      (Work.BoseKinLoc.Momentum.continuous_kinFT_of_integrable h1).aestronglyMeasurable).mp
      (Work.BoseKinLoc.Momentum.memLp_kinFT h1 h2)
  calc
    (∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * ‖Work.BoseBoxFock.kmomInt ℓ n‖ ^ 2
        * ‖Submission.BoseGases.kinFT g (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2)
        = ∑' n : Fin 3 → ℤ, ∑ i : Fin 3, (ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT
            (fun z => fderiv ℝ g z (Submission.BoseGases.kcStdBasis i))
            (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2 := by
          refine tsum_congr (fun n => ?_)
          rw [mul_assoc, hpoint (Work.BoseBoxFock.kmomInt ℓ n), Finset.mul_sum]
      _ = ∑ i : Fin 3, ∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT
            (fun z => fderiv ℝ g z (Submission.BoseGases.kcStdBasis i))
            (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2 :=
          Summable.tsum_finsetSum (s := Finset.univ)
            (f := fun (i : Fin 3) (n : Fin 3 → ℤ) => (ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT
              (fun z => fderiv ℝ g z (Submission.BoseGases.kcStdBasis i))
              (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2)
            (fun i _ => hsumm i)
      _ = ∑ i : Fin 3, ((2 * Real.pi) ^ 3)⁻¹ * ∫ p, ‖Submission.BoseGases.kinFT
            (fun z => fderiv ℝ g z (Submission.BoseGases.kcStdBasis i)) p‖ ^ 2 :=
          Finset.sum_congr rfl (fun i _ => hframe i)
      _ = ((2 * Real.pi) ^ 3)⁻¹ * ∑ i : Fin 3, ∫ p, ‖Submission.BoseGases.kinFT
            (fun z => fderiv ℝ g z (Submission.BoseGases.kcStdBasis i)) p‖ ^ 2 :=
          (Finset.mul_sum (Finset.univ : Finset (Fin 3))
            (fun i => ∫ p, ‖Submission.BoseGases.kinFT
              (fun z => fderiv ℝ g z (Submission.BoseGases.kcStdBasis i)) p‖ ^ 2)
            (((2 * Real.pi) ^ 3)⁻¹)).symm
      _ = ((2 * Real.pi) ^ 3)⁻¹ * ∫ p, ∑ i : Fin 3, ‖Submission.BoseGases.kinFT
            (fun z => fderiv ℝ g z (Submission.BoseGases.kcStdBasis i)) p‖ ^ 2 := by
          rw [(integral_finsetSum (Finset.univ : Finset (Fin 3))
            (f := fun (i : Fin 3) (p : EuclideanSpace ℝ (Fin 3)) => ‖Submission.BoseGases.kinFT
              (fun z => fderiv ℝ g z (Submission.BoseGases.kcStdBasis i)) p‖ ^ 2)
            (fun i _ => hInt i)).symm]
      _ = ((2 * Real.pi) ^ 3)⁻¹ *
            ∫ p : EuclideanSpace ℝ (Fin 3), ‖p‖ ^ 2 * ‖Submission.BoseGases.kinFT g p‖ ^ 2 := by
          rw [integral_congr_ae (Filter.Eventually.of_forall (fun p => (hpoint p).symm))]

end Work.BoseBoxFock
