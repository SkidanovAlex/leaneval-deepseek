import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.UBBInputs9.B.pd_aux.boxMean_sq_le
import Submission.Work.UBBInputs9.B.pd_aux.kinIntD_le
import Submission.Work.UBBInputs9.B.pd_aux.ofReal_min_cube_le_volume_dlBox
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.UBBInputs9.B.pd_aux.boxMean_term_le`

The uniform (in the witness scaling `cc`) bound on the box-mean term

    `∫_{(u,x)} boxMean ℓ d u (kwPhi ℓ cc)² · kinIntD ℓ d u x  ∂(pdMu ℓ) ≤ C`

which is the projection-defect input of `Work.UBBInputs9.B.proj_defect`.

The substance is that the mean of the *narrow* witness state `kwPhi ℓ cc` (supported in the ball
of radius `1/(2cc) < ℓ/4`) over the sliding box `B(u)` is small *in `u`-integral*:

* `boxMean ℓ d u (kwPhi ℓ cc)` is the normalised average of the `ℝ³`-avatar
  `F z = kwPhi ℓ cc (fun _ => z)` over `dlBox ℓ d u`, so by Cauchy–Schwarz
  `boxMean² ≤ (∫_{B(u)} F²)/boxMass u ≤ 1/boxMass u`;
* the box `B(u)` meets the support of `F` only if it meets the inner cube
  `acube (ℓ/2)`, and in that case `boxMass u ≥ (min (ℓ/4) (ℓd/2))³` (the geometric input
  `ofReal_min_cube_le_volume_dlBox`);
* the `u`-region on which `B(u)` meets the inner cube is bounded
  (`exists_R_norm_lt_of_mem_dlBox_notMem_acube_half`), so `boxMean² ≤ γ⁻³ · 1_{‖u‖ ≤ R}`;
* `kinIntD` is bounded by a constant `K` independent of `u, x` (`kinIntD_le`).

Hence the integrand is dominated by the integrable function
`γ^{-3}·K·1_{‖u‖ ≤ R}` on the product measure, whose integral is
`γ^{-3}·K·volume(ball R)·vol(abox 1 ℓ)`.
-/

namespace Work.UBBInputs9.B.pd_aux

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal
open Submission.BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)
local notation "X1" => Submission.BoseGases.X 1

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## Elementary coordinate helpers -/

private lemma coord_sub_smul (z u : ℝ³) (s : ℝ) (i : Fin 3) : (z - s • u) i = z i - s * u i := by
  simp [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]

private lemma abs_coord_le_of_mem_acube {L : ℝ} {z : ℝ³} (hz : z ∈ acube L) (i : Fin 3) :
    |z i| ≤ L / 2 := by
  have h := hz i
  rw [Set.mem_Icc] at h
  exact abs_le.mpr ⟨by linarith [h.1], by linarith [h.2]⟩

private lemma exists_coord_abs_gt_of_notMem_acube {L : ℝ} {z : ℝ³} (hz : z ∉ acube L) :
    ∃ i : Fin 3, L / 2 < |z i| := by
  by_contra h
  push Not at h
  exact hz (fun i => by
    rw [Set.mem_Icc]
    have h1 := abs_le.mp (h i)
    exact ⟨by linarith [h1.1], by linarith [h1.2]⟩)

private lemma norm_le_three_mul_of_abs_coord_le {u : ℝ³} {M : ℝ} (hM : ∀ i : Fin 3, |u i| ≤ M)
    (hM0 : 0 ≤ M) : ‖u‖ ≤ 3 * M := by
  have hsq : ‖u‖ ^ 2 ≤ (3 * M) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc ∑ i, u i ^ 2 ≤ ∑ _i : Fin 3, M ^ 2 := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          nlinarith [abs_le.mp (hM i) |>.1, abs_le.mp (hM i) |>.2, hM0]
      _ = 3 * M ^ 2 := by simp [Finset.sum_const, Finset.card_univ]
      _ ≤ (3 * M) ^ 2 := by nlinarith
  exact le_of_sq_le_sq hsq (by positivity)

/-! ## The `u`-region on which the sliding box can meet the inner cube -/

lemma exists_R_norm_lt_of_mem_dlBox_notMem_acube_half {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) :
    ∃ R : ℝ, ∀ u : ℝ³, R < ‖u‖ → ∀ z : ℝ³, z ∈ dlBox ℓ d u → z ∉ acube (ℓ / 2) := by
  refine ⟨3 * ((ℓ / 4 + ℓ * d / 2) / (ℓ * d)), fun u hu z hz hzmem => ?_⟩
  have hld : 0 < ℓ * d := mul_pos hℓ hd
  have hM : ∀ i : Fin 3, |u i| ≤ (ℓ / 4 + ℓ * d / 2) / (ℓ * d) := by
    intro i
    have hzi : |z i| ≤ ℓ / 4 := by
      have := abs_coord_le_of_mem_acube hzmem i
      linarith
    have hzu : |z i - (ℓ * d) * u i| ≤ ℓ * d / 2 := by
      have h := abs_coord_le_of_mem_acube ((mem_dlBox_iff ℓ d u z).mp hz).2 i
      rwa [coord_sub_smul] at h
    have hkey : ℓ * d * |u i| ≤ ℓ / 4 + ℓ * d / 2 := by
      have h1 : |ℓ * d * u i| = ℓ * d * |u i| := by rw [abs_mul, abs_of_pos hld]
      have h2 : |ℓ * d * u i| ≤ |z i| + |z i - ℓ * d * u i| := by
        have h3 : ℓ * d * u i = z i + -(z i - ℓ * d * u i) := by ring
        calc |ℓ * d * u i| = |z i + -(z i - ℓ * d * u i)| := by conv_lhs => rw [h3]
          _ ≤ |z i| + |-(z i - ℓ * d * u i)| := abs_add_le _ _
          _ = |z i| + |z i - ℓ * d * u i| := by rw [abs_neg]
      linarith [h1, h2]
    exact (le_div_iff₀ hld).mpr (by linarith [hkey])
  have hnorm := norm_le_three_mul_of_abs_coord_le hM (by positivity)
  linarith [hu, hnorm]

/-! ## The `ℝ³`-avatar of the witness state -/

lemma kwPhi_eq_zero_of_notMem_acube_half {ℓ cc : ℝ} (hℓ : 0 < ℓ) (hcc : 2 / ℓ < cc)
    {z : ℝ³} (hz : z ∉ acube (ℓ / 2)) : Work.SmallBoxA0.kwPhi ℓ cc (fun _ : Fin 1 => z) = 0 := by
  obtain ⟨_, _, hvan, _, _, _⟩ := Work.SmallBoxA0.kwPhi_props (s := ℓ) (c := cc) hℓ hcc
  refine hvan (fun _ => z) ?_
  obtain ⟨i, hi⟩ := exists_coord_abs_gt_of_notMem_acube hz
  have hlt : 1 / (2 * cc) < ℓ / 4 := by
    have hc : 0 < cc := lt_trans (div_pos two_pos hℓ) hcc
    have h2 : 2 < ℓ * cc := by
      rw [div_lt_iff₀ hℓ] at hcc
      linarith
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have h4 : ℓ / 4 < ‖z‖ := by
    have := abs_coord_le_norm z i
    linarith [hi, this]
  show 1 / (2 * cc) < ‖(fun _ : Fin 1 => z) 0‖
  simpa using lt_trans hlt h4

/-- The `L²`-normalisation of the `ℝ³`-avatar of the witness state. -/
lemma integral_kwPhi_avatar_sq {ℓ cc : ℝ} (hℓ : 0 < ℓ) (hcc : 2 / ℓ < cc) :
    (∫ z : ℝ³, (Work.SmallBoxA0.kwPhi ℓ cc (fun _ : Fin 1 => z)) ^ 2) = 1 := by
  obtain ⟨_, _, _, _, hL2, _⟩ := Work.SmallBoxA0.kwPhi_props (s := ℓ) (c := cc) hℓ hcc
  have h0 : ∀ z : ℝ³, z ∉ acube ℓ →
      (Work.SmallBoxA0.kwPhi ℓ cc (fun _ : Fin 1 => z)) ^ 2 = 0 := by
    intro z hz
    have hz2 : z ∉ acube (ℓ / 2) := by
      intro h
      exact hz (fun i => by
        have h1 := abs_coord_le_of_mem_acube h i
        rw [Set.mem_Icc]
        have h2 := abs_le.mp h1
        constructor <;> linarith [h2.1, h2.2, hℓ])
    rw [kwPhi_eq_zero_of_notMem_acube_half hℓ hcc hz2, zero_pow (by norm_num)]
  have hext := Work.SmallBoxA0.kwBoxExtend (s := ℓ)
    (F := fun z : ℝ³ => (Work.SmallBoxA0.kwPhi ℓ cc (fun _ : Fin 1 => z)) ^ 2) h0
  rw [← hext]
  have hx : ∀ x : X1, (fun _ : Fin 1 => x 0) = x :=
    fun x => funext fun i => by rw [Fin.eq_zero i]
  rw [show (∫ x in abox 1 ℓ, (Work.SmallBoxA0.kwPhi ℓ cc (fun _ : Fin 1 => x 0)) ^ 2)
      = ∫ x in abox 1 ℓ, (Work.SmallBoxA0.kwPhi ℓ cc x) ^ 2 from
    setIntegral_congr_fun (abox_measurable 1 ℓ) (fun x _ => by rw [hx x])]
  exact hL2

/-! ## `kinIntD` is nonnegative -/

lemma kinIntD_nonneg (ℓ d : ℝ) (u : ℝ³) (x : X1) :
    0 ≤ Work.UBBInputs9.B.kinIntD ℓ d u x := by
  unfold Work.UBBInputs9.B.kinIntD
  exact Finset.sum_nonneg fun k _ => sq_nonneg _

/-! ## The assembly -/

/-- **The integral bound, from the four pointwise inputs.**  If `kinIntD` is bounded by `K ≥ 0`,
the box mean is bounded by `(γ³)⁻¹` and vanishes outside a ball of radius `R`, then the integral
of `boxMean² · kinIntD` over `pdMu ℓ` is at most
`(γ³)⁻¹ · K · volume(closedBall 0 R) · vol(abox 1 ℓ)`. -/
lemma integral_le_of_bounds {ℓ d cc K γ R : ℝ} (hℓ : 0 < ℓ)
    (hK : 0 ≤ K) (hγ : 0 < γ)
    (hkin : ∀ (u : ℝ³) (x : X1), Work.UBBInputs9.B.kinIntD ℓ d u x ≤ K)
    (hbm : ∀ u : ℝ³,
      (Work.UBBInputs9.B.boxMean ℓ d u (Work.SmallBoxA0.kwPhi ℓ cc)) ^ 2 ≤ (γ ^ 3)⁻¹)
    (hsup : ∀ u : ℝ³, R < ‖u‖ →
      Work.UBBInputs9.B.boxMean ℓ d u (Work.SmallBoxA0.kwPhi ℓ cc) = 0) :
    (∫ p : ℝ³ × X1,
        (Work.UBBInputs9.B.boxMean ℓ d p.1 (Work.SmallBoxA0.kwPhi ℓ cc)) ^ 2 *
          Work.UBBInputs9.B.kinIntD ℓ d p.1 p.2
        ∂(Work.UBBInputs9.B.pdMu ℓ))
      ≤ (γ ^ 3)⁻¹ * K * (volume : Measure ℝ³).real (closedBall (0 : ℝ³) R)
          * (((volume : Measure X1).restrict (abox 1 ℓ)).real Set.univ) := by
  rw [Work.UBBInputs9.B.pdMu]
  set μX : Measure X1 := (volume : Measure X1).restrict (abox 1 ℓ) with hμXdef
  haveI hμXfin : IsFiniteMeasure μX := ⟨by
    rw [hμXdef, Measure.restrict_apply_univ, abox_volume 1 ℓ hℓ.le]
    exact ENNReal.ofReal_lt_top⟩
  set c : ℝ := (γ ^ 3)⁻¹ * K with hcdef
  have hc0 : 0 ≤ c := by rw [hcdef]; positivity
  set g : ℝ³ × X1 → ℝ :=
    fun p => (c * (closedBall (0 : ℝ³) R).indicator (1 : ℝ³ → ℝ) p.1) * 1 with hgdef
  -- the pointwise domination
  have hpt : ∀ p : ℝ³ × X1,
      (Work.UBBInputs9.B.boxMean ℓ d p.1 (Work.SmallBoxA0.kwPhi ℓ cc)) ^ 2 *
        Work.UBBInputs9.B.kinIntD ℓ d p.1 p.2 ≤ g p := by
    intro p
    show (Work.UBBInputs9.B.boxMean ℓ d p.1 (Work.SmallBoxA0.kwPhi ℓ cc)) ^ 2 *
        Work.UBBInputs9.B.kinIntD ℓ d p.1 p.2
      ≤ c * (closedBall (0 : ℝ³) R).indicator (1 : ℝ³ → ℝ) p.1 * 1
    by_cases hp : p.1 ∈ closedBall (0 : ℝ³) R
    · rw [Set.indicator_of_mem hp, Pi.one_apply, mul_one, mul_one]
      calc (Work.UBBInputs9.B.boxMean ℓ d p.1 (Work.SmallBoxA0.kwPhi ℓ cc)) ^ 2 *
            Work.UBBInputs9.B.kinIntD ℓ d p.1 p.2
          ≤ (γ ^ 3)⁻¹ * K :=
            mul_le_mul (hbm p.1) (hkin p.1 p.2)
              (kinIntD_nonneg ℓ d p.1 p.2) (by positivity)
        _ = c := rfl
    · have hu : R < ‖p.1‖ := by
        have h1 : ¬ (‖p.1‖ ≤ R) := by
          have h2 := hp
          rw [mem_closedBall, dist_eq_norm, sub_zero] at h2
          exact h2
        exact lt_of_not_ge h1
      rw [Set.indicator_of_notMem hp, mul_zero, zero_mul,
        hsup p.1 hu, zero_pow (by norm_num), zero_mul]
  -- the dominating function is integrable
  have hgint : Integrable g ((volume : Measure ℝ³).prod μX) := by
    rw [hgdef]
    have h1 : Integrable
        (fun u : ℝ³ => (closedBall (0 : ℝ³) R).indicator (1 : ℝ³ → ℝ) u)
        (volume : Measure ℝ³) := by
      rw [integrable_indicator_iff isClosed_closedBall.measurableSet]
      exact integrableOn_const (measure_closedBall_lt_top).ne
    have h2 : Integrable
        (fun u : ℝ³ => c * (closedBall (0 : ℝ³) R).indicator (1 : ℝ³ → ℝ) u)
        (volume : Measure ℝ³) := h1.const_mul c
    have h3 : Integrable (fun _ : X1 => (1 : ℝ)) μX := integrable_const 1
    exact h2.mul_prod h3
  -- the monotone integral bound
  have hmain : (∫ p : ℝ³ × X1,
        (Work.UBBInputs9.B.boxMean ℓ d p.1 (Work.SmallBoxA0.kwPhi ℓ cc)) ^ 2 *
          Work.UBBInputs9.B.kinIntD ℓ d p.1 p.2 ∂((volume : Measure ℝ³).prod μX))
      ≤ ∫ p : ℝ³ × X1, g p ∂((volume : Measure ℝ³).prod μX) :=
    integral_mono_of_nonneg
      (ae_of_all _ fun p => mul_nonneg (sq_nonneg _) (kinIntD_nonneg ℓ d p.1 p.2))
      hgint (ae_of_all _ hpt)
  -- the value of the dominating integral
  have hval : (∫ p : ℝ³ × X1, g p ∂((volume : Measure ℝ³).prod μX))
      = c * (volume : Measure ℝ³).real (closedBall (0 : ℝ³) R) * (μX.real Set.univ) := by
    rw [hgdef]
    rw [MeasureTheory.integral_prod_mul (μ := (volume : Measure ℝ³)) (ν := μX)
      (f := fun u : ℝ³ => c * (closedBall (0 : ℝ³) R).indicator (1 : ℝ³ → ℝ) u)
      (g := fun _ : X1 => (1 : ℝ))]
    have hA : (∫ u : ℝ³, c * (closedBall (0 : ℝ³) R).indicator (1 : ℝ³ → ℝ) u)
        = c * (volume : Measure ℝ³).real (closedBall (0 : ℝ³) R) := by
      rw [MeasureTheory.integral_const_mul,
        MeasureTheory.integral_indicator_one isClosed_closedBall.measurableSet]
    have hB : (∫ _x : X1, (1 : ℝ) ∂μX) = μX.real Set.univ := by
      rw [MeasureTheory.integral_const]
      simp
    rw [hA, hB]
  calc (∫ p : ℝ³ × X1,
        (Work.UBBInputs9.B.boxMean ℓ d p.1 (Work.SmallBoxA0.kwPhi ℓ cc)) ^ 2 *
          Work.UBBInputs9.B.kinIntD ℓ d p.1 p.2 ∂((volume : Measure ℝ³).prod μX))
      ≤ ∫ p : ℝ³ × X1, g p ∂((volume : Measure ℝ³).prod μX) := hmain
    _ = c * (volume : Measure ℝ³).real (closedBall (0 : ℝ³) R) * (μX.real Set.univ) := hval
    _ = (γ ^ 3)⁻¹ * K * (volume : Measure ℝ³).real (closedBall (0 : ℝ³) R)
          * (((volume : Measure X1).restrict (abox 1 ℓ)).real Set.univ) := by
        rw [hcdef, hμXdef]

theorem boxMean_term_le {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ cc : ℝ, 2 / ℓ < cc →
      (∫ p : (EuclideanSpace ℝ (Fin 3)) × Submission.BoseGases.X 1,
          (Work.UBBInputs9.B.boxMean ℓ d p.1 (Work.SmallBoxA0.kwPhi ℓ cc)) ^ 2 *
            Work.UBBInputs9.B.kinIntD ℓ d p.1 p.2
          ∂(Work.UBBInputs9.B.pdMu ℓ)) ≤ C := by
  -- the three uniform inputs: bounded `kinIntD`, bounded `boxMean`, bounded `u`-support
  obtain ⟨K, hK0, hK⟩ := kinIntD_le hℓ hd
  obtain ⟨R, hR⟩ := exists_R_norm_lt_of_mem_dlBox_notMem_acube_half hℓ hd
  have hγpos : 0 < min (ℓ / 4) (ℓ * d / 2) := lt_min (by linarith) (by positivity)
  refine ⟨((min (ℓ / 4) (ℓ * d / 2)) ^ 3)⁻¹ * K *
      (volume : Measure ℝ³).real (closedBall (0 : ℝ³) R) *
      (((volume : Measure X1).restrict (abox 1 ℓ)).real Set.univ), ?_, ?_⟩
  · refine mul_nonneg (mul_nonneg (mul_nonneg ?_ hK0) MeasureTheory.measureReal_nonneg)
      MeasureTheory.measureReal_nonneg
    exact le_of_lt (inv_pos.mpr (pow_pos hγpos 3))
  · intro cc hcc
    refine integral_le_of_bounds hℓ hK0 hγpos hK ?_ ?_
    · exact boxMean_sq_le hℓ hd hcc hγpos (ofReal_min_cube_le_volume_dlBox hℓ hd)
    · intro u hu
      rw [Work.UBBInputs9.B.boxMean]
      rw [MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero ?_, mul_zero]
      intro z hz
      exact kwPhi_eq_zero_of_notMem_acube_half hℓ hcc (hR u hu z hz)

end Work.UBBInputs9.B.pd_aux
