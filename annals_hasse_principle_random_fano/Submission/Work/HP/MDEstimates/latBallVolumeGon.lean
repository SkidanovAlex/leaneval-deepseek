import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.GonLib
import Submission.Work.HP.volume_closedBall_euclid

/-!
# The volume of the coefficient ball of a lattice map

For an injective `ℝ`-linear map `Φ : (Fin R → ℝ) →ₗ[ℝ] EuclideanSpace ℝ ι`, presented in
coefficient space, the Lebesgue measure of `{x | ‖Φ x‖ ≤ S}` is the Euclidean volume of the
radius-`S` ball in `ℝ^R` divided by the covolume `latCovol Φ = √det(Φᵀ Φ)` of the lattice.

The proof reads `Φ` on the Euclidean space `ℝ^R` as `latMapE Φ` (so that `LinearMap.normDet`
applies), computes the `R`-dimensional Hausdorff measure of the ball cut out on the image
subspace, and rewrites `normDet` as `latCovol`, which is its Gram-determinant form.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory MeasureTheory.Measure Metric Set
open scoped ENNReal

namespace Work.HP.MDEstimates

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The lattice map with the domain `Fin R → ℝ` read as the Euclidean space `ℝ^R`, so that
Mathlib's `LinearMap.normDet` (the volume factor for Hausdorff measure) applies to it. -/
def latMapE {R : ℕ} (Φ : Work.HP.LatMap (ι := ι) R) :
    EuclideanSpace ℝ (Fin R) →ₗ[ℝ] EuclideanSpace ℝ ι :=
  Φ.comp (WithLp.linearEquiv 2 ℝ (Fin R → ℝ)).toLinearMap

@[simp] lemma latMapE_apply {R : ℕ} (Φ : Work.HP.LatMap (ι := ι) R)
    (x : EuclideanSpace ℝ (Fin R)) : latMapE Φ x = Φ x.ofLp := rfl

/-- Injectivity is preserved by the change of presentation of the domain. -/
lemma latMapE_injective {R : ℕ} (Φ : Work.HP.LatMap (ι := ι) R) (hΦ : Function.Injective Φ) :
    Function.Injective (latMapE Φ) := by
  intro x y hxy
  exact WithLp.ofLp_injective (p := 2) (hΦ hxy)

/-- The Lebesgue measure of a coefficient set is unchanged by reading the coefficients as an
element of `EuclideanSpace ℝ (Fin R)` rather than as a function `Fin R → ℝ`. -/
theorem volume_latMapE {R : ℕ} (Φ : Work.HP.LatMap (ι := ι) R) (S : ℝ) :
    MeasureTheory.volume {x : Fin R → ℝ | ‖Φ x‖ ≤ S} =
      MeasureTheory.volume {x : EuclideanSpace ℝ (Fin R) | ‖latMapE Φ x‖ ≤ S} := by
  have hT : MeasurableSet {y : Fin R → ℝ | ‖Φ y‖ ≤ S} :=
    (isClosed_le (continuous_norm.comp Φ.continuous_of_finiteDimensional)
      continuous_const).measurableSet
  have hmp := MeasurePreserving.measure_preimage (PiLp.volume_preserving_ofLp (Fin R))
    hT.nullMeasurableSet
  have hset : {x : EuclideanSpace ℝ (Fin R) | ‖latMapE Φ x‖ ≤ S}
      = WithLp.ofLp ⁻¹' {y : Fin R → ℝ | ‖Φ y‖ ≤ S} := by
    ext x; simp [latMapE_apply]
  rw [hset]
  exact hmp.symm

/-- `latCovol` is the norm determinant (the volume factor) of the map read on `ℝ^R`. -/
theorem latCovol_eq_normDet {R : ℕ} (Φ : Work.HP.LatMap (ι := ι) R) :
    Work.HP.latCovol Φ = (latMapE Φ).normDet := by
  have hgram : Matrix.gram ℝ (fun x => latMapE Φ (EuclideanSpace.basisFun (Fin R) ℝ x))
      = Matrix.of (fun i j : Fin R =>
          inner ℝ (Φ (Pi.basisFun ℝ (Fin R) i)) (Φ (Pi.basisFun ℝ (Fin R) j))) := by
    ext i j
    simp [Matrix.gram, latMapE_apply, EuclideanSpace.single]
  unfold Work.HP.latCovol
  rw [← hgram, ← LinearMap.normDet_sq_eq_det_gram (latMapE Φ) (EuclideanSpace.basisFun (Fin R) ℝ)]
  exact Real.sqrt_sq (latMapE Φ).normDet_nonneg

/-- The volume `ballVol R` of the unit ball in `ℝ^R` in the closed form `√π^R / Γ(R/2+1)`. -/
theorem ballVol_eq_sqrt_pi (R : ℕ) (hR : 1 ≤ R) :
    Work.HP.ballVol R = √Real.pi ^ R / Real.Gamma ((R:ℝ)/2 + 1) := by
  have hne : Nonempty (Fin R) := ⟨⟨0, by omega⟩⟩
  have h1 := EuclideanSpace.volume_closedBall (Fin R) (0 : EuclideanSpace ℝ (Fin R)) 1
  rw [Fintype.card_fin] at h1
  simp only [ENNReal.ofReal_one, one_pow, one_mul] at h1
  rw [Work.HP.ballVol, h1, ENNReal.toReal_ofReal (by positivity)]

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]

/-- The `R`-dimensional Hausdorff measure of the radius-`S` ball cut out on an `R`-dimensional
subspace of a Euclidean space is `ballVol R * S^R`. -/
theorem hausdorffMeasure_submodule_closedBall {R : ℕ} (hR : 1 ≤ R)
    (M : Submodule ℝ W) (hdim : Module.finrank ℝ M = R) (S : ℝ) (hS : 0 ≤ S) :
    μHE[R] ((M : Set W) ∩ Metric.closedBall (0 : W) S) =
      ENNReal.ofReal (Work.HP.ballVol R * S ^ R) := by
  have hnt : Nontrivial M := Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [hdim]; omega)
  have hiso : Isometry ((↑) : M → W) := isometry_subtype_coe
  have hpre := Isometry.euclideanHausdorffMeasure_preimage (d := R) hiso
      ((M : Set W) ∩ Metric.closedBall (0 : W) S)
  have hset1 : ((↑) : M → W) ⁻¹' ((M : Set W) ∩ Metric.closedBall (0 : W) S)
      = Metric.closedBall (0 : M) S := by
    ext x
    simp only [Set.mem_preimage, Set.mem_inter_iff, Subtype.coe_prop, true_and,
      Metric.mem_closedBall, dist_zero_right]
    exact Iff.rfl
  have hset2 : ((M : Set W) ∩ Metric.closedBall (0 : W) S) ∩ Set.range ((↑) : M → W)
      = (M : Set W) ∩ Metric.closedBall (0 : W) S := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_range, SetLike.mem_coe]
    constructor
    · exact fun h => h.1
    · intro h
      exact ⟨h, ⟨⟨x, h.1⟩, rfl⟩⟩
  rw [hset1, hset2] at hpre
  rw [← hpre]
  conv_lhs => rw [← hdim]
  rw [InnerProductSpace.euclideanHausdorffMeasure_eq_volume, InnerProductSpace.volume_closedBall]
  rw [hdim]
  rw [ballVol_eq_sqrt_pi R hR, ← ENNReal.ofReal_pow hS]
  rw [← ENNReal.ofReal_mul (by positivity)]
  ring_nf

/-- The `R`-dimensional Hausdorff measure of `closedBall 0 S ∩ range A` for an injective linear
map `A : ℝ^R → ℝ^ι` is `ballVol R * S^R`. -/
theorem hausdorffMeasure_range_closedBall {R : ℕ} (hR : 1 ≤ R)
    (A : EuclideanSpace ℝ (Fin R) →ₗ[ℝ] EuclideanSpace ℝ ι) (hA : Function.Injective A)
    (S : ℝ) (hS : 0 ≤ S) :
    μHE[R] (LinearMap.range A ∩ Metric.closedBall (0 : EuclideanSpace ℝ ι) S) =
      ENNReal.ofReal (Work.HP.ballVol R * S ^ R) := by
  have hdim : Module.finrank ℝ (LinearMap.range A) = R := by
    rw [LinearMap.finrank_range_of_inj hA, finrank_euclideanSpace, Fintype.card_fin]
  exact hausdorffMeasure_submodule_closedBall hR (LinearMap.range A) hdim S hS

theorem latBallVolumeGon {ι : Type*} [Fintype ι] [DecidableEq ι] {R : ℕ} (hR : 1 ≤ R)
    (Φ : Work.HP.LatMap (ι := ι) R) (hΦ : Function.Injective Φ) (S : ℝ) (hS : 0 ≤ S) :
    MeasureTheory.volume {x : Fin R → ℝ | ‖Φ x‖ ≤ S} =
      ENNReal.ofReal (Work.HP.ballVol R * S ^ R / Work.HP.latCovol Φ) := by
  have hinj : Function.Injective (latMapE Φ) := latMapE_injective Φ hΦ
  have hset : {x : EuclideanSpace ℝ (Fin R) | ‖latMapE Φ x‖ ≤ S}
      = latMapE Φ ⁻¹' Metric.closedBall (0 : EuclideanSpace ℝ ι) S := by
    ext x
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Metric.mem_closedBall, dist_zero_right]
  have hmain : ENNReal.ofReal ((latMapE Φ).normDet) *
      MeasureTheory.volume (latMapE Φ ⁻¹' Metric.closedBall (0 : EuclideanSpace ℝ ι) S)
      = ENNReal.ofReal (Work.HP.ballVol R * S ^ R) := by
    have h := LinearMap.euclideanHausdorffMeasure_image_eq_normDet_mul_volume (latMapE Φ)
      (latMapE Φ ⁻¹' Metric.closedBall (0 : EuclideanSpace ℝ ι) S)
    rw [Set.image_preimage_eq_inter_range, Set.inter_comm, ← LinearMap.coe_range (latMapE Φ),
      finrank_euclideanSpace, Fintype.card_fin] at h
    rw [hausdorffMeasure_range_closedBall hR (latMapE Φ) hinj S hS] at h
    exact h.symm
  have hpos : 0 < (latMapE Φ).normDet := by
    refine lt_of_le_of_ne (latMapE Φ).normDet_nonneg (Ne.symm ?_)
    rw [Ne, LinearMap.normDet_eq_zero_iff_ker_ne_bot, not_not, LinearMap.ker_eq_bot]
    exact hinj
  have hvol : MeasureTheory.volume (latMapE Φ ⁻¹' Metric.closedBall (0 : EuclideanSpace ℝ ι) S)
      = ENNReal.ofReal (Work.HP.ballVol R * S ^ R / (latMapE Φ).normDet) := by
    have hc : ENNReal.ofReal ((latMapE Φ).normDet) *
        (ENNReal.ofReal ((latMapE Φ).normDet))⁻¹ = 1 :=
      ENNReal.mul_inv_cancel (ENNReal.ofReal_ne_zero_iff.mpr hpos) ENNReal.ofReal_ne_top
    calc MeasureTheory.volume (latMapE Φ ⁻¹' Metric.closedBall (0 : EuclideanSpace ℝ ι) S)
        = (ENNReal.ofReal ((latMapE Φ).normDet))⁻¹ *
            (ENNReal.ofReal ((latMapE Φ).normDet) *
              MeasureTheory.volume
                (latMapE Φ ⁻¹' Metric.closedBall (0 : EuclideanSpace ℝ ι) S)) := by
          rw [← mul_assoc, mul_comm (ENNReal.ofReal ((latMapE Φ).normDet))⁻¹
            (ENNReal.ofReal ((latMapE Φ).normDet)), hc, one_mul]
      _ = (ENNReal.ofReal ((latMapE Φ).normDet))⁻¹ *
            ENNReal.ofReal (Work.HP.ballVol R * S ^ R) := by
          rw [hmain]
      _ = ENNReal.ofReal (Work.HP.ballVol R * S ^ R / (latMapE Φ).normDet) := by
          rw [ENNReal.ofReal_div_of_pos hpos, div_eq_mul_inv, mul_comm]
  rw [volume_latMapE Φ S, hset, hvol, latCovol_eq_normDet Φ]

end Work.HP.MDEstimates
