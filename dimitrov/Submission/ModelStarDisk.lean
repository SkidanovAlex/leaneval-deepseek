import Mathlib
import Submission.ModelStarExterior
import Submission.ModelStarStruct
import Submission.Commons.Analysis.Complex.rouche_simple_zero
import Submission.Commons.Analysis.Complex.rouche_simple_zero_of_analyticOnNhd

/-!
# ModelStarDisk -- the unit-disk model of the model map

STATUS: work in progress (research isolate; NOT imported by `Submission.lean`).

For the model map `modelF z₀ r z = z · ∏_k (1 - z₀ k · z⁻¹)^(2 r k)` put
`u := z⁻¹` and

    `diskPhi z₀ r u := ∏_k (1 - z₀ k · u)^(2 r k)`

so that `u · modelF z₀ r u⁻¹ = diskPhi z₀ r u` for `u ≠ 0`.  This module
develops the analytic properties of `diskPhi` on the closed unit disk
(analytic on the open disk, continuous on the closed disk, `≤ 4` on the
circle) and the resulting COUNTING statement

  * `exists_unique_zero` : for `4 < ‖w‖` the function `diskPhi z₀ r - w·id`
    has exactly one zero in the unit disk (Rouché against `w·id`),
  * `exists_unique_preimage` : equivalently `modelF z₀ r` has exactly one
    preimage of `w` in the exterior `{1 < ‖z‖}`,
  * `preimage_iff` : the general pointwise correspondence between exterior
    preimages of `w` and zeros of `diskPhi z₀ r - w·id` in the unit disk.

-/

noncomputable section

open scoped Real BigOperators Topology
open Filter Set Complex

namespace Submission.ModelStarDisk

open Submission.ModelStarMap

/-- The `k`-th factor of the disk model: `(1 - a·u)^t`. -/
def diskFactor (a : ℂ) (t : ℝ) (u : ℂ) : ℂ := (1 - a * u) ^ (t : ℂ)

/-- The disk model of the model map: `∏_k (1 - z₀ k·u)^(2 r k)`. -/
def diskPhi {s : ℕ} (z₀ : Fin s → ℂ) (r : Fin s → ℝ) (u : ℂ) : ℂ :=
  ∏ k : Fin s, diskFactor (z₀ k) (2 * r k) u

variable {s : ℕ} {z₀ : Fin s → ℂ} {r φ : Fin s → ℝ}

/-! ## Elementary identities -/

lemma diskPhi_zero (z₀ : Fin s → ℂ) (r : Fin s → ℝ) : diskPhi z₀ r 0 = 1 := by
  simp [diskPhi, diskFactor, Complex.one_cpow]

lemma diskFactor_eq_modelFactor {a : ℂ} {t : ℝ} {u : ℂ} :
    diskFactor a t u = modelFactor a t u⁻¹ := by
  unfold diskFactor modelFactor
  rw [inv_inv]

lemma diskPhi_eq_modelProduct (z₀ : Fin s → ℂ) (r : Fin s → ℝ) {u : ℂ} (hu : u ≠ 0) :
    diskPhi z₀ r u = modelProduct z₀ r u⁻¹ := by
  unfold diskPhi modelProduct
  exact Finset.prod_congr rfl fun k _ => diskFactor_eq_modelFactor

lemma modelF_inv_eq (z₀ : Fin s → ℂ) (r : Fin s → ℝ) {u : ℂ} (hu : u ≠ 0) :
    modelF z₀ r u⁻¹ = u⁻¹ * diskPhi z₀ r u := by
  unfold modelF
  rw [diskPhi_eq_modelProduct z₀ r hu]

lemma mul_modelF_inv_eq (z₀ : Fin s → ℂ) (r : Fin s → ℝ) {u : ℂ} (hu : u ≠ 0) :
    u * modelF z₀ r u⁻¹ = diskPhi z₀ r u := by
  rw [modelF_inv_eq z₀ r hu, ← mul_assoc, mul_inv_cancel₀ hu, one_mul]

/-- The disk model vanishes exactly at the disk-preimages of `0`. -/
lemma diskPhi_sub_eq (z₀ : Fin s → ℂ) (r : Fin s → ℝ) {u w : ℂ} (hu : u ≠ 0) :
    diskPhi z₀ r u - w * u = u * (modelF z₀ r u⁻¹ - w) := by
  rw [← mul_modelF_inv_eq z₀ r hu]
  ring

/-! ## Bounds on the circle -/

lemma norm_diskFactor_le {a : ℂ} {t : ℝ} (ht : 0 ≤ t) {u : ℂ} (hau : ‖a‖ ≤ 1)
    (hu : ‖u‖ ≤ 1) : ‖diskFactor a t u‖ ≤ 2 ^ t := by
  have haun : ‖a * u‖ ≤ 1 := by
    calc ‖a * u‖ = ‖a‖ * ‖u‖ := norm_mul _ _
      _ ≤ 1 * 1 := mul_le_mul hau hu (norm_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  have hbase : ‖1 - a * u‖ ≤ 2 := by
    calc ‖1 - a * u‖ ≤ ‖(1 : ℂ)‖ + ‖a * u‖ := norm_sub_le _ _
      _ = 1 + ‖a * u‖ := by simp
      _ ≤ 1 + 1 := by linarith
      _ = 2 := by norm_num
  unfold diskFactor
  rw [Complex.norm_cpow_real]
  exact Real.rpow_le_rpow (norm_nonneg _) hbase ht

lemma norm_diskPhi_le_four (z₀ : Fin s → ℂ) (r : Fin s → ℝ) (hunit : ∀ k, ‖z₀ k‖ = 1)
    (hr : ∀ k, 0 ≤ r k) (hsum : (∑ k : Fin s, r k) = 1) {u : ℂ} (hu : ‖u‖ ≤ 1) :
    ‖diskPhi z₀ r u‖ ≤ 4 := by
  rw [show diskPhi z₀ r u = ∏ k : Fin s, diskFactor (z₀ k) (2 * r k) u from rfl,
    norm_prod Finset.univ (fun k : Fin s => diskFactor (z₀ k) (2 * r k) u)]
  calc ∏ k : Fin s, ‖diskFactor (z₀ k) (2 * r k) u‖
      ≤ ∏ k : Fin s, (2 : ℝ) ^ (2 * r k) := by
        refine Finset.prod_le_prod (fun k _ => norm_nonneg _) (fun k _ => ?_)
        exact norm_diskFactor_le (by linarith [hr k]) (le_of_eq (hunit k)) hu
    _ = (2 : ℝ) ^ (∑ k : Fin s, 2 * r k) :=
        (Real.rpow_sum_of_pos (by norm_num) (fun k : Fin s => 2 * r k) Finset.univ).symm
    _ = (2 : ℝ) ^ (2 : ℝ) := by
        rw [← Finset.mul_sum, hsum, mul_one]
    _ = 4 := by rw [Real.rpow_two]; norm_num

/-! ## Continuity on the closed disk -/

lemma continuousAt_diskFactor {a : ℂ} {t : ℝ} (ht : 0 < t) {u : ℂ} (hau : ‖a‖ ≤ 1)
    (hu : ‖u‖ ≤ 1) : ContinuousAt (fun u : ℂ => diskFactor a t u) u := by
  have hre : 0 ≤ (1 - a * u).re := by
    have haun : ‖a * u‖ ≤ 1 := by
      calc ‖a * u‖ = ‖a‖ * ‖u‖ := norm_mul _ _
        _ ≤ 1 * 1 := mul_le_mul hau hu (norm_nonneg _) (by norm_num)
        _ = 1 := by norm_num
    have h2 := Complex.re_le_norm (a * u)
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have hw : 0 < ((t : ℂ)).re := by simpa using ht
  have hcont : ContinuousAt (fun u : ℂ => 1 - a * u) u := by fun_prop
  have h := ContinuousAt.comp (x := u) (f := fun u : ℂ => 1 - a * u)
      (g := fun x : ℂ => x ^ (t : ℂ))
      (Complex.continuousAt_cpow_const_of_re_pos (Or.inl hre) hw) hcont
  simpa [diskFactor, Function.comp_def] using h

lemma continuousAt_diskPhi (z₀ : Fin s → ℂ) (r : Fin s → ℝ) (hunit : ∀ k, ‖z₀ k‖ = 1)
    (hr : ∀ k, 0 < r k) {u : ℂ} (hu : ‖u‖ ≤ 1) : ContinuousAt (diskPhi z₀ r) u := by
  rw [ContinuousAt]
  exact tendsto_finsetProd _ (fun k _ => continuousAt_diskFactor (by linarith [hr k])
    (le_of_eq (hunit k)) hu)

lemma continuousOn_diskPhi_closedBall (z₀ : Fin s → ℂ) (r : Fin s → ℝ)
    (hunit : ∀ k, ‖z₀ k‖ = 1) (hr : ∀ k, 0 < r k) :
    ContinuousOn (diskPhi z₀ r) (Metric.closedBall 0 1) := by
  intro u hu
  rw [Metric.mem_closedBall, dist_zero_right] at hu
  exact (continuousAt_diskPhi z₀ r hunit hr hu).continuousWithinAt

/-! ## Analyticity on the open disk -/

lemma mem_slitPlane_one_sub {a u : ℂ} (hau : ‖a‖ ≤ 1) (hu : ‖u‖ < 1) :
    1 - a * u ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  left
  have haun : ‖a * u‖ < 1 := by
    have h : ‖a * u‖ = ‖a‖ * ‖u‖ := norm_mul _ _
    nlinarith [norm_nonneg a, norm_nonneg u]
  have h2 := Complex.re_le_norm (a * u)
  simp only [Complex.sub_re, Complex.one_re]
  linarith

lemma analyticAt_diskFactor {a : ℂ} {t : ℝ} {u : ℂ} (hau : ‖a‖ ≤ 1) (hu : ‖u‖ < 1) :
    AnalyticAt ℂ (fun u : ℂ => diskFactor a t u) u := by
  have hbase : 1 - a * u ∈ Complex.slitPlane := mem_slitPlane_one_sub hau hu
  have han : AnalyticAt ℂ (fun u : ℂ => 1 - a * u) u := by fun_prop
  have h := AnalyticAt.cpow han (analyticAt_const (v := ((t : ℂ)))) hbase
  simpa [diskFactor] using h

lemma analyticAt_diskPhi (z₀ : Fin s → ℂ) (r : Fin s → ℝ) (hunit : ∀ k, ‖z₀ k‖ = 1)
    {u : ℂ} (hu : ‖u‖ < 1) : AnalyticAt ℂ (diskPhi z₀ r) u := by
  have hfac : ∀ k ∈ (Finset.univ : Finset (Fin s)),
      AnalyticAt ℂ (fun u : ℂ => diskFactor (z₀ k) (2 * r k) u) u :=
    fun k _ => analyticAt_diskFactor (le_of_eq (hunit k)) hu
  have h := Finset.analyticAt_fun_prod (𝕜 := ℂ) (E := ℂ) (A := ℂ)
    (f := fun k : Fin s => fun u : ℂ => diskFactor (z₀ k) (2 * r k) u)
    (Finset.univ : Finset (Fin s)) hfac
  exact h

/-! ## The counting statements -/

/-- The general pointwise correspondence between exterior preimages of `w`
and zeros of `diskPhi - w·id` in the unit disk. -/
lemma preimage_iff (z₀ : Fin s → ℂ) (r : Fin s → ℝ) {w ζ : ℂ} (hζ : ζ ≠ 0) :
    (modelF z₀ r ζ = w ∧ 1 < ‖ζ‖) ↔
      (ζ⁻¹ ∈ Metric.ball (0 : ℂ) 1 ∧ diskPhi z₀ r ζ⁻¹ = w * ζ⁻¹) := by
  have hnorm : ‖ζ⁻¹‖ = ‖ζ‖⁻¹ := norm_inv ζ
  constructor
  · rintro ⟨hF, hlt⟩
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_ball, dist_zero_right, hnorm]
      exact inv_lt_one_of_one_lt₀ hlt
    · have h := mul_modelF_inv_eq z₀ r (inv_ne_zero hζ)
      rw [inv_inv, hF] at h
      rw [← h, mul_comm]
  · rintro ⟨hball, hzero⟩
    rw [Metric.mem_ball, dist_zero_right, hnorm] at hball
    have hpos : 0 < ‖ζ‖ := norm_pos_iff.mpr hζ
    have hlt : 1 < ‖ζ‖ := by
      rw [inv_lt_one_iff₀] at hball
      exact hball.resolve_left (not_le.mpr hpos)
    refine ⟨?_, hlt⟩
    have h := mul_modelF_inv_eq z₀ r (inv_ne_zero hζ)
    rw [inv_inv, hzero, mul_comm w ζ⁻¹] at h
    exact mul_left_cancel₀ (inv_ne_zero hζ) h

/-- `diskPhi z₀ r - w·id` has no zero on the unit circle when `w ∉ M`. -/
lemma diskPhi_sub_ne_zero_sphere (z₀ : Fin s → ℂ) (r : Fin s → ℝ) {w u : ℂ}
    (hu : ‖u‖ = 1) (hw : diskPhi z₀ r u = w * u)
    (hw0 : w ∉ Submission.ModelStarExterior.modelStarImage z₀ r) : False := by
  have hu0 : u ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hu
    exact one_ne_zero hu.symm
  have hpre : modelF z₀ r u⁻¹ = w := by
    have h : u * modelF z₀ r u⁻¹ = u * w := by
      rw [mul_modelF_inv_eq z₀ r hu0, hw, mul_comm]
    exact mul_left_cancel₀ hu0 h
  refine hw0 ⟨u⁻¹, ?_, hpre⟩
  rw [Submission.ModelStarExterior.mem_circle, norm_inv, hu, inv_one]

/-- **Rouché.**  For `4 < ‖w‖`, `diskPhi z₀ r - w·id` has exactly one zero in
the unit disk. -/
theorem exists_unique_zero (z₀ : Fin s → ℂ) (r : Fin s → ℝ) (hunit : ∀ k, ‖z₀ k‖ = 1)
    (hr : ∀ k, 0 < r k) (hsum : (∑ k : Fin s, r k) = 1) {w : ℂ} (hw : 4 < ‖w‖) :
    ∃! u : ℂ, u ∈ Metric.ball (0 : ℂ) 1 ∧ diskPhi z₀ r u = w * u := by
  have hw0 : w ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hw
    norm_num at hw
  have hsp : ∀ z ∈ Metric.sphere (0 : ℂ) (1 : ℝ),
      ‖diskPhi z₀ r z‖ < ‖(fun u : ℂ => (-w) * u) z‖ := by
    intro z hz
    have hz1 : ‖z‖ = 1 := by simpa using hz
    rw [norm_mul, hz1, mul_one, norm_neg]
    exact lt_of_le_of_lt
      (norm_diskPhi_le_four z₀ r hunit (fun k => (hr k).le) hsum (le_of_eq hz1)) hw
  have hder : deriv (fun u : ℂ => (-w) * u) 0 ≠ 0 := by
    have hd : deriv (fun u : ℂ => (-w) * u) 0 = -w := by
      simpa using ((hasDerivAt_id (0 : ℂ)).const_mul (-w)).deriv
    rw [hd]
    simpa using hw0
  obtain ⟨z, hz, hz0, hzuniq⟩ :=
    Commons.Analysis.Complex.rouche_simple_zero_of_analyticOnNhd (R := 1)
      (f := fun u : ℂ => (-w) * u) (g := diskPhi z₀ r) (a := 0) one_pos (by simp)
      (by intro u hu; fun_prop)
      (by intro u hu; fun_prop)
      (fun u hu => analyticAt_diskPhi z₀ r hunit (by
        rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hu
        exact hu))
      (continuousOn_diskPhi_closedBall z₀ r hunit hr)
      hsp (by simp) hder (by intro z hz; simpa [hw0] using hz)
  refine ⟨z, ⟨hz, ?_⟩, ?_⟩
  · have h := hz0
    simp only [Pi.mul_apply, Pi.add_apply, neg_mul] at h
    linear_combination h
  · intro y hy
    refine hzuniq y hy.1 ?_
    simp only [Pi.mul_apply, Pi.add_apply, neg_mul]
    linear_combination hy.2

/-- **Exactly one exterior preimage** of `w` when `4 < ‖w‖`. -/
theorem exists_unique_preimage (z₀ : Fin s → ℂ) (r : Fin s → ℝ) (hunit : ∀ k, ‖z₀ k‖ = 1)
    (hr : ∀ k, 0 < r k) (hsum : (∑ k : Fin s, r k) = 1) {w : ℂ} (hw : 4 < ‖w‖) :
    ∃! ζ : ℂ, 1 < ‖ζ‖ ∧ modelF z₀ r ζ = w := by
  obtain ⟨z, ⟨hzball, hzzero⟩, hzuniq⟩ := exists_unique_zero z₀ r hunit hr hsum hw
  rw [Metric.mem_ball, dist_zero_right] at hzball
  have hz0 : z ≠ 0 := by
    intro h0
    rw [h0, diskPhi_zero, mul_zero] at hzzero
    exact one_ne_zero hzzero
  have hF : modelF z₀ r z⁻¹ = w := by
    have h := mul_modelF_inv_eq z₀ r hz0
    rw [hzzero, mul_comm w z] at h
    exact mul_left_cancel₀ hz0 h
  refine ⟨z⁻¹, ⟨?_, hF⟩, ?_⟩
  · rw [norm_inv]
    exact one_lt_inv_iff₀.mpr ⟨norm_pos_iff.mpr hz0, hzball⟩
  · intro y hy
    have hy0 : y ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hy
      linarith [hy.1]
    have hzy : y⁻¹ ∈ Metric.ball (0 : ℂ) 1 ∧ diskPhi z₀ r y⁻¹ = w * y⁻¹ := by
      constructor
      · rw [Metric.mem_ball, dist_zero_right, norm_inv]
        exact inv_lt_one_of_one_lt₀ hy.1
      · have h := mul_modelF_inv_eq z₀ r (inv_ne_zero hy0)
        rw [inv_inv, hy.2] at h
        rw [← h, mul_comm]
    have : y⁻¹ = z := hzuniq y⁻¹ hzy
    rw [← this, inv_inv]

end Submission.ModelStarDisk
