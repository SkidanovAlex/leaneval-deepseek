/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# Auxiliaries for the localized `(0,1)`-Poincaré operator

The scaled datum `sclData ρ f` of `Work.NN.Final.FlatData` is compactly supported and smooth
wherever `f` is smooth on the polydisc of multiradii `4ρ`; to feed the local Schauder estimate
`Work.NN.Final.schauderIterateNoClosed` one needs a globally smooth datum on the polydisc of
multiradii `4ρ` agreeing with `f` on the solution polydisc.  This module provides the pulled-back
cutoff `cutoffPull ρ = cutCn ∘ (z ↦ z / (scl ρ))` and its properties.
-/
import Mathlib
import Submission.Work.NN.Final.FlatData

noncomputable section

open scoped NNReal ENNReal ContDiff Topology
open Set Filter MeasureTheory
open Work.CR.Flat Work.CR.Flat.Cauchy

namespace Work.NN.Final

variable {n : ℕ} {α : ℝ} {ρ : Fin n → ℝ}

/-- The cut-off in the original (`z`-variable) coordinates: the pull-back of `cutCn` along the
inverse scaling `z ↦ z / (scl ρ)`. -/
noncomputable def cutoffPull {n : ℕ} (ρ : Fin n → ℝ) : (Fin n → ℂ) → ℂ :=
  fun z => cutCn (invRescaleMap 0 (scl ρ) z)

lemma contDiff_cutoffPull (hρ : ∀ j, 0 < ρ j) :
    ContDiff ℝ ∞ (cutoffPull ρ : (Fin n → ℂ) → ℂ) :=
  contDiff_cutCn.comp ((contDiff_invRescaleMap 0 (scl ρ)).of_le le_top)

/-- The radius up to which the pulled-back cut-off is equal to `1`. -/
lemma cutoffPull_eq_one (hρ : ∀ j, 0 < ρ j) {z : Fin n → ℂ}
    (hz : ∀ i, ‖z i‖ ≤ 3 * ρ i) : cutoffPull ρ z = 1 := by
  refine cutCn_eq_one fun i => ?_
  rw [invRescaleMap_apply]
  simp only [Pi.zero_apply, neg_zero, zero_div, zero_add, norm_mul]
  rw [Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr (scl_pos hρ i).le)]
  rw [show (scl ρ i)⁻¹ * ‖z i‖ = ‖z i‖ / scl ρ i from by rw [div_eq_mul_inv, mul_comm]]
  rw [div_le_iff₀ (scl_pos hρ i), mul_comm]
  have hS : scl ρ i = (7 / 2) * ρ i := rfl
  rw [hS]
  have hk : kappa * cutIn = 117 / 128 := by norm_num [kappa, cutIn]
  rw [hk]
  nlinarith [hρ i, hz i]

lemma cutoffPull_eq_zero_of_norm_ge (hρ : ∀ j, 0 < ρ j) {z : Fin n → ℂ} {i : Fin n}
    (hz : kappa * cutOut * scl ρ i ≤ ‖z i‖) : cutoffPull ρ z = 0 := by
  refine cutCn_eq_zero_of_norm_ge (j := i) ?_
  rw [invRescaleMap_apply]
  simp only [Pi.zero_apply, neg_zero, zero_div, zero_add, norm_mul]
  rw [Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr (scl_pos hρ i).le)]
  rw [show (scl ρ i)⁻¹ * ‖z i‖ = ‖z i‖ / scl ρ i from by rw [div_eq_mul_inv, mul_comm]]
  rw [le_div_iff₀ (scl_pos hρ i)]
  exact hz

lemma cutoffPull_eventuallyEq_zero (hρ : ∀ j, 0 < ρ j) {z : Fin n → ℂ}
    (hz : ∃ i, kappa * cutOut * scl ρ i < ‖z i‖) :
    (cutoffPull ρ : (Fin n → ℂ) → ℂ) =ᶠ[𝓝 z] 0 := by
  obtain ⟨i, hi⟩ := hz
  have hmem : {z' : Fin n → ℂ | kappa * cutOut * scl ρ i < ‖z' i‖} ∈ 𝓝 z :=
    (isOpen_lt continuous_const ((continuous_apply i).norm)).mem_nhds hi
  filter_upwards [hmem] with z' hz'
  exact cutoffPull_eq_zero_of_norm_ge hρ (le_of_lt hz')

/-- A bound for the radius of the support of the pulled-back cut-off. -/
lemma cutoffPull_support_bound (hρ : ∀ j, 0 < ρ j) {z : Fin n → ℂ}
    (hz : cutoffPull ρ z ≠ 0) (i : Fin n) :
    ‖z i‖ ≤ kappa * cutOut * scaleR (scl ρ) := by
  by_contra hcon
  rw [not_le] at hcon
  have hle : scl ρ i ≤ scaleR (scl ρ) := by
    rw [scaleR_eq]
    linarith [Finset.single_le_sum (fun k _ => (scl_pos hρ k).le) (Finset.mem_univ i)]
  exact hz (cutoffPull_eq_zero_of_norm_ge hρ
    (le_trans (mul_le_mul_of_nonneg_left hle
      (mul_nonneg kappa_pos.le cutOut_pos.le)) (le_of_lt hcon)))

lemma hasCompactSupport_cutoffPull (hρ : ∀ j, 0 < ρ j) :
    HasCompactSupport (cutoffPull ρ : (Fin n → ℂ) → ℂ) := by
  refine HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : Fin n → ℂ) (kappa * cutOut * scaleR (scl ρ))) ?_
  intro z hz
  rw [Metric.mem_closedBall, dist_zero_right]
  refine (pi_norm_le_iff_of_nonneg
    (mul_nonneg (mul_nonneg kappa_pos.le cutOut_pos.le) (scaleR_scl_pos hρ).le)).mpr fun i => ?_
  rw [Function.mem_support] at hz
  exact cutoffPull_support_bound hρ hz i

/-- The product of the pulled-back cut-off with a function which is `C^m` on the polydisc of
multiradii `4ρ` is globally `C^m`. -/
lemma contDiff_mul_cutoffPull (hρ : ∀ j, 0 < ρ j) {m : ℕ} {f : (Fin n → ℂ) → ℂ}
    (hf : ContDiffOn ℝ (m : ℕ∞) f (polydisc 0 (fun j => 4 * ρ j))) :
    ContDiff ℝ m (fun z => cutoffPull ρ z * f z) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : ∃ i, kappa * cutOut * scl ρ i < ‖z i‖
  · have hev : (fun z' : Fin n → ℂ => cutoffPull ρ z' * f z') =ᶠ[𝓝 z] 0 := by
      filter_upwards [cutoffPull_eventuallyEq_zero hρ hz] with z' hz'
      simp only [hz', Pi.zero_apply, zero_mul]
    exact (contDiffAt_const : ContDiffAt ℝ m (fun _ : Fin n → ℂ => (0 : ℂ)) z)
      |>.congr_of_eventuallyEq hev
  · push Not at hz
    have hmem : z ∈ polydisc 0 (fun j => 4 * ρ j) := by
      intro i
      show ‖z i - 0‖ < 4 * ρ i
      rw [sub_zero]
      refine lt_of_le_of_lt (hz i) ?_
      have hS : scl ρ i = (7 / 2) * ρ i := rfl
      rw [hS]
      have hk : kappa * cutOut = 63 / 64 := by norm_num [kappa, cutOut]
      rw [hk]
      nlinarith [hρ i]
    have hη : ContDiffAt ℝ m (cutoffPull ρ) z :=
      (contDiff_cutoffPull hρ).contDiffAt.of_le coe_le_infty
    have hf' : ContDiffAt ℝ m f z :=
      (hf.contDiffAt ((isOpen_polydisc 0 (fun j => 4 * ρ j)).mem_nhds hmem))
    exact hη.mul hf'

end Work.NN.Final
