import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.SqrtKin.kinFT_weight_integrable
import Submission.Work.BoseBoxFock.moment2LatticeC
import Submission.Work.BoseBoxFock.tauPsiLatticeSummable
import Submission.Work.BoseBoxFock.tauThetaKinFTIntegrable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

open scoped BigOperators Pointwise
open MeasureTheory

/-- **The closed ball `closedBall 0 (ℓ/2)` sits in the box `Λ(ℓ) = boxL ℓ = ℓ•[−1/2,1/2]³`.**
A coordinate of a point of the closed ball is bounded by its Euclidean norm (`|x i| ≤ ‖x‖` for
the sup-norm-coordinate, here the `WithLp` coordinate), hence by `ℓ/2`; after dividing by `ℓ` it
lies in `[−1/2,1/2]`.

This is the closed-ball companion of `Work.BoseBoxFock.ball_subset_corpusBox_boxL` (the open
version, `<` in place of `≤`); the box support is what makes the Poisson/frame identities
(`frame_lattice_ball`, `moment2LatticeC`, `summable_lattice_kinFT_weight`) applicable, since the
`ℓℤ³`-translates of the cube `boxL ℓ` meet only in measure-zero faces. -/
private lemma closedBall_subset_boxL_deficit {ℓ : ℝ} (hℓ : 0 < ℓ) :
    Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) (ℓ / 2)
      ⊆ Work.BoseK15.corpusBox.boxL ℓ := by
  intro x hx
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hx
  show x ∈ (ℓ : ℝ) • (Work.BoseB4.unitCell : Set (EuclideanSpace ℝ (Fin 3)))
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ (ne_of_gt hℓ)]
  intro i
  rw [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
  have h1 : ‖x.ofLp i‖ ≤ ‖x‖ := by
    rw [EuclideanSpace.norm_eq]
    exact Real.le_sqrt_of_sq_le
      (Finset.single_le_sum (fun j _ => sq_nonneg ‖x.ofLp j‖) (Finset.mem_univ i))
  have h2 : |x.ofLp i| ≤ ‖x‖ := by rwa [Real.norm_eq_abs] at h1
  rw [abs_mul, abs_inv, abs_of_pos hℓ]
  calc ℓ⁻¹ * |x.ofLp i| ≤ ℓ⁻¹ * ‖x‖ :=
        mul_le_mul_of_nonneg_left h2 (le_of_lt (inv_pos.mpr hℓ))
    _ ≤ ℓ⁻¹ * (ℓ/2) := mul_le_mul_of_nonneg_left hx (le_of_lt (inv_pos.mpr hℓ))
    _ = (1:ℝ)/2 := by field_simp

theorem deficit_inputs {ℓ c : ℝ} (hℓ : 0 < ℓ) (hc : 0 < c)
    {g : EuclideanSpace ℝ (Fin 3) → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g)
    (hgc : HasCompactSupport g)
    (hgsupp : tsupport g ⊆ Metric.closedBall 0 (ℓ / 2)) :
    ((∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹
          * ‖Submission.BoseGases.kinFT g (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2)
        = ((2 * Real.pi) ^ 3)⁻¹
            * ∫ p : EuclideanSpace ℝ (Fin 3), ‖Submission.BoseGases.kinFT g p‖ ^ 2)
    ∧ ((∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * ‖Work.BoseBoxFock.kmomInt ℓ n‖ ^ 2
          * ‖Submission.BoseGases.kinFT g (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2)
        = ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3),
            ‖p‖ ^ 2 * ‖Submission.BoseGases.kinFT g p‖ ^ 2)
    ∧ Summable (fun n : Fin 3 → ℤ =>
        (ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT g (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2)
    ∧ Summable (fun n : Fin 3 → ℤ => (ℓ ^ 3)⁻¹ * ‖Work.BoseBoxFock.kmomInt ℓ n‖
        * ‖Submission.BoseGases.kinFT g (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2)
    ∧ Summable (fun n : Fin 3 → ℤ => (ℓ ^ 3)⁻¹ * ‖Work.BoseBoxFock.kmomInt ℓ n‖ ^ 2
        * ‖Submission.BoseGases.kinFT g (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2)
    ∧ Summable (fun n : Fin 3 → ℤ => (ℓ ^ 3)⁻¹
        * Work.BoseBoxFock.tauPsi c ‖Work.BoseBoxFock.kmomInt ℓ n‖
        * ‖Submission.BoseGases.kinFT g (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2)
    ∧ Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
        ‖p‖ * ‖Submission.BoseGases.kinFT g p‖ ^ 2)
    ∧ Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
        Work.BoseBoxFock.tauTheta c ‖p‖ * ‖Submission.BoseGases.kinFT g p‖ ^ 2) := by
  -- the closed-ball support put inside the box `Λ(ℓ)`, which is what the Poisson/frame
  -- identities and the `ℓ⁻³`-weighted lattice summability are stated for
  have hbox : tsupport g ⊆ Work.BoseK15.corpusBox.boxL ℓ :=
    hgsupp.trans (closedBall_subset_boxL_deficit hℓ)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the frame (Poisson summation) identity `S₀ = R₀`
    exact frame_lattice_ball hℓ hg hgc hbox
  · -- the second lattice moment `S₂ = R₂`
    exact moment2LatticeC hℓ hg hgc hbox
  · -- summability of `Σ ℓ⁻³‖kinFT g k_n‖²` (weight `j = 0`)
    simpa using summable_lattice_kinFT_weight (ℓ := ℓ) hℓ hg hgc 0
  · -- summability of `Σ ℓ⁻³‖k_n‖‖kinFT g k_n‖²` (weight `j = 1`)
    simpa using summable_lattice_kinFT_weight (ℓ := ℓ) hℓ hg hgc 1
  · -- summability of `Σ ℓ⁻³‖k_n‖²‖kinFT g k_n‖²` (weight `j = 2`)
    exact summable_lattice_kinFT_weight (ℓ := ℓ) hℓ hg hgc 2
  · -- summability with the convexity defect weight `tauPsi`
    exact tauPsiLatticeSummable hℓ hc hg hgc
  · -- integrability of `p ↦ ‖p‖‖kinFT g p‖²`
    exact SqrtKin.kinFT_weight_integrable hg hgc
  · -- integrability with the cap weight `tauTheta`
    exact tauThetaKinFTIntegrable hc hg hgc

end Work.BoseBoxFock
