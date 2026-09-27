import Mathlib
import Submission.Work.Mostow.BCGDefs
import Submission.Work.Mostow.NatMeasure
import Submission.Work.Mostow.HlinPairing
import Submission.Work.Mostow.HlinStrictMoment

/-!
# The second-moment operator `Hlin n φ` of a boundary homeomorphism `φ`

`Hlin n φ = ∫ ξ, (innerSL ℝ (φ ξ)).smulRight (φ ξ) ∂(sigma n)` is the second-moment operator
of the push-forward of the rotation-invariant probability measure `sigma n` on the sphere by `φ`.
For a homeomorphism `φ` of `Sph n` it is symmetric, positive semi-definite, of trace `1`, and
strictly smaller than the identity — the four facts used in the Besson–Courtois–Gallot
computation of the Jacobian of the natural map.

The bulk of the computation is provided by two helper lemmas:
`HlinPairing` (the pairing identity `⟪Hlin n φ v, w⟫ = ∫ ξ, ⟪φ ξ, v⟫ * ⟪φ ξ, w⟫ ∂sigma n`) and
`HlinStrictMoment` (strict positivity of `∫ ξ, ‖v‖ ^ 2 - ⟪φ ξ, v⟫ ^ 2 ∂sigma n` for `v ≠ 0`,
which uses that `sigma n` has no atoms).
-/

set_option linter.style.haveILetI false

open scoped InnerProductSpace

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

/-- The second-moment integrand of the push-forward of `sigma n` by `φ` is integrable: on the
support of `sigma n` (the sphere) the vector `φ ξ` is a unit vector. -/
lemma integrable_inner_mul_comp {n : ℕ} (φ : E n → E n)
    (hbij : Set.BijOn φ (Sph n) (Sph n)) (hcont : ContinuousOn φ (Sph n))
    (hprob : sigma n Set.univ = 1) (hsupp : sigma n (Sph n)ᶜ = 0) (v w : E n) :
    Integrable (fun ξ => (inner ℝ (φ ξ) v) * (inner ℝ (φ ξ) w)) (sigma n) := by
  haveI : IsFiniteMeasure (sigma n) := ⟨by rw [hprob]; exact ENNReal.one_lt_top⟩
  have hSph : MeasurableSet (Sph n) := Metric.isClosed_sphere.measurableSet
  have hφae : AEMeasurable φ (sigma n) :=
    aemeasurable_of_continuousOn_of_compl_eq_zero (0 : E n) hSph hcont hsupp
  have hφasm : AEStronglyMeasurable φ (sigma n) := hφae.aestronglyMeasurable
  have hcont2 : Continuous (fun x : E n => (inner ℝ x v) * (inner ℝ x w)) :=
    (continuous_id.inner continuous_const).mul (continuous_id.inner continuous_const)
  refine Integrable.of_bound (hcont2.comp_aestronglyMeasurable hφasm) (‖v‖ * ‖w‖) ?_
  have hnorm : ∀ᵐ ξ ∂(sigma n), ‖φ ξ‖ = 1 := by
    have hsph_ae : ∀ᵐ ξ ∂(sigma n), ξ ∈ Sph n := by
      rw [ae_iff]; simpa only [Set.compl_def] using hsupp
    filter_upwards [hsph_ae] with ξ hξ
    have h1 : φ ξ ∈ Sph n := hbij.1 hξ
    simpa [Sph, Metric.mem_sphere, dist_eq_norm] using h1
  filter_upwards [hnorm] with ξ hξ
  rw [norm_mul]
  calc ‖inner ℝ (φ ξ) v‖ * ‖inner ℝ (φ ξ) w‖
      ≤ (‖φ ξ‖ * ‖v‖) * (‖φ ξ‖ * ‖w‖) := by
        gcongr <;> exact norm_inner_le_norm _ _
    _ = ‖v‖ * ‖w‖ := by rw [hξ]; ring

/-- Almost every point of the support of `sigma n` is mapped by `φ` to a unit vector. -/
lemma ae_inner_self_comp_eq_one {n : ℕ} (φ : E n → E n)
    (hbij : Set.BijOn φ (Sph n) (Sph n)) (hsupp : sigma n (Sph n)ᶜ = 0) :
    ∀ᵐ ξ ∂(sigma n), inner ℝ (φ ξ) (φ ξ) = 1 := by
  have hsph_ae : ∀ᵐ ξ ∂(sigma n), ξ ∈ Sph n := by
    rw [ae_iff]; simpa only [Set.compl_def] using hsupp
  filter_upwards [hsph_ae] with ξ hξ
  have h1 : φ ξ ∈ Sph n := hbij.1 hξ
  have h2 : ‖φ ξ‖ = 1 := by
    simpa [Sph, Metric.mem_sphere, dist_eq_norm] using h1
  rw [real_inner_self_eq_norm_sq, h2]
  norm_num

theorem HProps (n : ℕ) (hn : 2 ≤ n) (φ : Submission.Mostow.E n → Submission.Mostow.E n)
    (hbij : Set.BijOn φ (Submission.Mostow.Sph n) (Submission.Mostow.Sph n))
    (hcont : ContinuousOn φ (Submission.Mostow.Sph n))
    (hprob : (Submission.Mostow.sigma n) Set.univ = 1)
    (hsupp : Submission.Mostow.sigma n (Submission.Mostow.Sph n)ᶜ = 0)
    (hatom : ∀ ξ : Submission.Mostow.E n, Submission.Mostow.sigma n {ξ} = 0) :
    (∀ v w : Submission.Mostow.E n,
      inner ℝ ((Work.Mostow.Hlin n φ) v) w = inner ℝ v ((Work.Mostow.Hlin n φ) w)) ∧
    (∀ w : Submission.Mostow.E n, 0 ≤ inner ℝ ((Work.Mostow.Hlin n φ) w) w) ∧
    LinearMap.trace ℝ (Submission.Mostow.E n) (Work.Mostow.Hlin n φ).toLinearMap = 1 ∧
    (∀ v : Submission.Mostow.E n, v ≠ 0 →
      inner ℝ v v - inner ℝ ((Work.Mostow.Hlin n φ) v) v > 0) := by
  haveI : IsFiniteMeasure (sigma n) := ⟨by rw [hprob]; exact ENNReal.one_lt_top⟩
  -- the pairing identity and the strict moment inequality
  have hP : ∀ v w : E n,
      inner ℝ ((Hlin n φ) v) w = ∫ ξ, (inner ℝ (φ ξ) v) * (inner ℝ (φ ξ) w) ∂(sigma n) :=
    fun v w => HlinPairing n φ hbij hcont hsupp v w
  have hS : ∀ v : E n, v ≠ 0 →
      0 < ∫ ξ, (‖v‖ ^ 2 - (inner ℝ (φ ξ) v) ^ 2) ∂(sigma n) :=
    fun v hv => HlinStrictMoment n φ hbij hcont hprob hsupp hatom v hv
  have hInt : ∀ v w : E n,
      Integrable (fun ξ => (inner ℝ (φ ξ) v) * (inner ℝ (φ ξ) w)) (sigma n) :=
    fun v w => integrable_inner_mul_comp φ hbij hcont hprob hsupp v w
  have hae := ae_inner_self_comp_eq_one φ hbij hsupp
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- symmetry of the second-moment operator
    intro v w
    rw [hP v w, real_inner_comm ((Hlin n φ) w) v, hP w v]
    congr 1
    ext ξ
    ring
  · -- positive semi-definiteness
    intro w
    rw [hP w w]
    exact integral_nonneg (fun ξ => mul_self_nonneg _)
  · -- trace one
    let b : OrthonormalBasis (Fin n) ℝ (E n) := EuclideanSpace.basisFun (Fin n) ℝ
    rw [LinearMap.trace_eq_sum_inner (Hlin n φ).toLinearMap b]
    calc ∑ i, inner ℝ (b i) ((Hlin n φ) (b i))
        = ∑ i, ∫ ξ, (inner ℝ (φ ξ) (b i)) * (inner ℝ (φ ξ) (b i)) ∂(sigma n) := by
            refine Finset.sum_congr rfl (fun i _ => ?_)
            rw [real_inner_comm, hP]
      _ = ∫ ξ, ∑ i, (inner ℝ (φ ξ) (b i)) * (inner ℝ (φ ξ) (b i)) ∂(sigma n) :=
            (integral_finsetSum Finset.univ (fun i _ => hInt (b i) (b i))).symm
      _ = ∫ ξ, inner ℝ (φ ξ) (φ ξ) ∂(sigma n) := by
            congr 1
            funext ξ
            rw [← b.sum_inner_mul_inner (φ ξ) (φ ξ)]
            refine Finset.sum_congr rfl (fun i _ => ?_)
            rw [real_inner_comm (b i) (φ ξ)]
      _ = 1 := by
            rw [integral_congr_ae hae, integral_const]
            simp [Measure.real, hprob]
  · -- strict dominance by the identity
    intro v hv
    have h1 : ∫ ξ, (‖v‖ ^ 2 : ℝ) ∂(sigma n) = ‖v‖ ^ 2 := by
      rw [integral_const]
      simp [Measure.real, hprob]
    have h2 : ∫ ξ, (inner ℝ (φ ξ) v) ^ 2 ∂(sigma n)
        = ∫ ξ, (inner ℝ (φ ξ) v) * (inner ℝ (φ ξ) v) ∂(sigma n) := by
      congr 1
      ext ξ
      rw [pow_two]
    have h3i : Integrable (fun ξ => (inner ℝ (φ ξ) v) ^ 2) (sigma n) := by
      refine (hInt v v).congr ?_
      filter_upwards with ξ
      rw [pow_two]
    have h3 : ∫ ξ, (‖v‖ ^ 2 - (inner ℝ (φ ξ) v) ^ 2) ∂(sigma n)
        = ∫ ξ, (‖v‖ ^ 2 : ℝ) ∂(sigma n)
          - ∫ ξ, (inner ℝ (φ ξ) v) ^ 2 ∂(sigma n) :=
      integral_sub (integrable_const _) h3i
    have hs := hS v hv
    rw [h3, h1, h2] at hs
    rw [real_inner_self_eq_norm_sq, hP v v]
    linarith

end

end Work.Mostow
