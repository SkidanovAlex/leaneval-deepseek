import Mathlib.Tactic.Have
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import ChallengeDeps
import Submission.Commons.Measure.Orthant.integral_orthant_eq_inv_pow
import Submission.Work.ESYRound5.Energy.pairSplit
import Submission.Work.ESYStage.neuMode_integral_zero
import Submission.Work.KinPSuperadd.fubini_abox_two
import Submission.Work.SmallBoxA0.acube_axis_ftoc
import Submission.Work.SmallBoxBridge.Kernel.volumeCosInnerZeroNull
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.ESYRound9.Condensate

set_option linter.unusedVariables false

open MeasureTheory
open scoped Topology

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

/-- Pointwise strict positivity of the corpus self-convolution `χ⋆χ` on the ball of
radius `1/2` (the closed ball of radius `ℓ/2` scaled by `ℓ⁻¹`).  Proof: for
`‖w‖ ≤ 1/2` the point `y := w/2` satisfies `‖y‖ ≤ 1/4` and `‖w − y‖ = ‖y‖ ≤ 1/4`,
so `χ y = χ (w − y) = 1/√chiNormSq > 0`; continuity turns this into positivity of
the integral. -/
lemma conv3_chi_pos_of_norm_le_half {w : ℝ³} (hw : ‖w‖ ≤ 1 / 2) :
    0 < Submission.BoseGases.conv3 chi chi w := by
  have hcont : Continuous (fun y : ℝ³ => chi y * chi (w - y)) :=
    chi_continuous.mul (chi_continuous.comp (continuous_const.sub continuous_id))
  have hcpt : HasCompactSupport (fun y : ℝ³ => chi y * chi (w - y)) :=
    (HasCompactSupport.mul_right (f := chi) (f' := fun y : ℝ³ => chi (w - y))
        chi_hasCompactSupport : HasCompactSupport (fun y : ℝ³ => chi y * chi (w - y)))
  have hnn : ∀ y : ℝ³, 0 ≤ chi y * chi (w - y) :=
    fun y => mul_nonneg (chi_nonneg y) (chi_nonneg (w - y))
  have hne : (fun y : ℝ³ => chi y * chi (w - y)) ((1 / 2 : ℝ) • w) ≠ 0 := by
    simp only
    have hw' : w - (1 / 2 : ℝ) • w = (1 / 2 : ℝ) • w := by module
    rw [hw', mul_self_ne_zero]
    have hnorm : ‖(1 / 2 : ℝ) • w‖ ≤ 1 / 4 := by
      rw [norm_smul, Real.norm_eq_abs]
      have h : |(1 / 2 : ℝ)| = 1 / 2 := by norm_num
      rw [h]
      linarith [norm_nonneg w]
    have h1 : chiBase ((1 / 2 : ℝ) • w) = 1 := chiBase_eq_one_of_norm_le hnorm
    have hval : chi ((1 / 2 : ℝ) • w) = 1 / Real.sqrt chiNormSq := by
      simp only [chi, h1]
    rw [hval]
    exact div_ne_zero one_ne_zero (ne_of_gt (Real.sqrt_pos.mpr chiNormSq_pos))
  have hpos := Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (μ := volume) hcont hcpt hnn hne
  simpa only [Submission.BoseGases.conv3] using hpos

/-- **A uniform positive lower bound for the χ-renormalisation denominator on the
support-compatible ball.**  If `‖z‖ ≤ ℓ/2` then `(χ⋆χ)(z/ℓ) = convScale ℓ z` is
bounded below by a positive constant.  Proof: `convScale ℓ` is continuous and
positive on the compact set `closedBall 0 (ℓ/2)`; a minimiser `x₀` of it attains a
value `> 0`, and that value bounds `convScale ℓ` from below on the whole ball. -/
lemma convScale_lower_of_le_half {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ∃ m : ℝ, 0 < m ∧ ∀ z : ℝ³, ‖z‖ ≤ ℓ / 2 → m ≤ convScale ℓ z := by
  have hKc : IsCompact (Metric.closedBall (0 : ℝ³) (ℓ / 2)) := isCompact_closedBall 0 (ℓ / 2)
  have hKne : (Metric.closedBall (0 : ℝ³) (ℓ / 2)).Nonempty :=
    ⟨0, Metric.mem_closedBall_self (by linarith)⟩
  obtain ⟨x₀, hx₀K, hx₀min⟩ := hKc.exists_isMinOn hKne (convScale_continuous ℓ).continuousOn
  refine ⟨convScale ℓ x₀, ?_, ?_⟩
  · have hnorm : ‖x₀‖ ≤ ℓ / 2 := by
      have h := hx₀K
      simp only [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h
      exact h
    have hsm : ‖(ℓ⁻¹) • x₀‖ ≤ 1 / 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hℓ]
      calc ℓ⁻¹ * ‖x₀‖ ≤ ℓ⁻¹ * (ℓ / 2) :=
            mul_le_mul_of_nonneg_left hnorm (inv_nonneg.mpr (le_of_lt hℓ))
        _ = 1 / 2 := by field_simp
    have := conv3_chi_pos_of_norm_le_half hsm
    rwa [convScale]
  · intro z hz
    exact hx₀min (show z ∈ Metric.closedBall (0 : ℝ³) (ℓ / 2) from by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hz)

/-- **The χ-renormalisation error of ESY's two-body condensate datum, exactly.**  ESY's
zero-momentum two-body datum is `V̂₀ = ∫_{Λ} V = ∫v` (the box containing the support), while the
corpus's `modeV ℓ v 0 = ∫_{acube ℓ} v/(χ⋆χ)(·/ℓ)` differs from it by the renormalisation factor
`1/(χ⋆χ)(·/ℓ) − 1`.  Together with `Condensate.zeroLat_eq_l3_integral`
(`twoLat ℓ (wPairC ℓ v) 0 0 = ℓ³∫v`) this isolates the two independent normalisation effects of
the (D1b)/(D2) dictionary at the condensate momentum: the box volume `ℓ³` (which the χ-factors
supply) and the χ-renormalisation of the mass. -/
theorem modeV_zero_deviation {R ℓ : ℝ} (hR : 0 < R) {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hv : MeasureTheory.Integrable v)
    (hv_supp : ∀ x : EuclideanSpace ℝ (Fin 3), R ≤ ‖x‖ → v x = 0)
    (hℓ : 0 < ℓ) (hR2 : R ≤ ℓ / 2) :
    (∫ z in Submission.BoseGases.acube ℓ, Submission.BoseGases.wScaled ℓ v z)
        - ∫ u : EuclideanSpace ℝ (Fin 3), v u
      = ∫ z in Submission.BoseGases.acube ℓ,
          v z * (1 / Submission.BoseGases.convScale ℓ z - 1) := by
  obtain ⟨m, hmpos, hmlb⟩ := convScale_lower_of_le_half (ℓ := ℓ) hℓ
  -- `v` is supported in the open ball of radius `R`, hence in `closedBall 0 (ℓ/2) ⊆ acube ℓ`.
  have hv_norm : ∀ z : ℝ³, v z ≠ 0 → ‖z‖ ≤ ℓ / 2 := by
    intro z hz
    have hzR : ‖z‖ < R := lt_of_not_ge (fun h => hz (hv_supp z h))
    exact le_trans (le_of_lt hzR) hR2
  have hmem : ∀ z : ℝ³, v z ≠ 0 → z ∈ Submission.BoseGases.acube ℓ := by
    intro z hz
    rw [Submission.BoseGases.mem_acube_iff]
    intro i
    have hzi : |z i| ≤ ‖z‖ := by simpa using PiLp.norm_apply_le z i
    rw [Set.mem_Icc]
    constructor <;> linarith [neg_abs_le (z i), le_abs_self (z i), hv_norm z hz]
  -- integrability of the renormalised kernel `wScaled ℓ v = v/(χ⋆χ)(·/ℓ)`
  have hAEm : AEMeasurable (fun z : ℝ³ => v z * (convScale ℓ z)⁻¹) (volume : Measure ℝ³) :=
    hv.aemeasurable.mul ((convScale_continuous ℓ).measurable.inv.aemeasurable)
  have hAE' : AEStronglyMeasurable (wScaled ℓ v) (volume : Measure ℝ³) := by
    have h1 : AEStronglyMeasurable (fun z : ℝ³ => v z * (convScale ℓ z)⁻¹)
        (volume : Measure ℝ³) :=
      hAEm.aestronglyMeasurable
    refine h1.congr ?_
    filter_upwards with z
    simp only [wScaled, div_eq_mul_inv]
  have hbound : ∀ z : ℝ³, ‖wScaled ℓ v z‖ ≤ (1 / m) * ‖v z‖ := by
    intro z
    by_cases hz : v z = 0
    · simp [wScaled, hz]
    · have hz2 : m ≤ convScale ℓ z := hmlb z (hv_norm z hz)
      have hpos : 0 < convScale ℓ z := lt_of_lt_of_le hmpos hz2
      rw [Real.norm_eq_abs, wScaled, abs_div, abs_of_pos hpos]
      calc |v z| / convScale ℓ z ≤ |v z| / m :=
            div_le_div_of_nonneg_left (abs_nonneg _) hmpos hz2
        _ = (1 / m) * |v z| := by rw [div_eq_mul_inv, one_div]; ring
  have hwInt : Integrable (wScaled ℓ v) (volume : Measure ℝ³) :=
    (hv.norm.const_mul (1 / m)).mono' hAE' (ae_of_all _ hbound)
  -- `v` integrates the same over the cube as over the whole space
  have hsupp : ∫ z in Submission.BoseGases.acube ℓ, v z = ∫ z : ℝ³, v z := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    by_contra hne
    exact hz (hmem z hne)
  calc
    (∫ z in Submission.BoseGases.acube ℓ, Submission.BoseGases.wScaled ℓ v z)
        - ∫ u : ℝ³, v u
        = (∫ z in Submission.BoseGases.acube ℓ, Submission.BoseGases.wScaled ℓ v z)
            - ∫ z in Submission.BoseGases.acube ℓ, v z := by rw [hsupp]
    _ = ∫ z in Submission.BoseGases.acube ℓ,
          (Submission.BoseGases.wScaled ℓ v z - v z) := by
          rw [← MeasureTheory.integral_sub hwInt.integrableOn hv.integrableOn]
    _ = ∫ z in Submission.BoseGases.acube ℓ,
          v z * (1 / Submission.BoseGases.convScale ℓ z - 1) := by
          apply MeasureTheory.integral_congr_ae
          exact ae_of_all _ (fun z => by
            simp only [Submission.BoseGases.wScaled, div_eq_mul_inv]; ring)

end Work.ESYRound9.Condensate
