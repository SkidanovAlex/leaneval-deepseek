import Submission.FUP.PSHToFourier2
import Submission.FUP.HormanderPsh

open FractalUncertainty MeasureTheory FourierTransform Metric Filter Set
open scoped ENNReal BigOperators Topology ContDiff

set_option autoImplicit false
variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)
local notation "ℂᵈ" => (Fin d → ℂ)

/-!
# §5 of Cohen's paper, part 7: the instantiation of Hörmander's `∂̄` theorem

`Submission/FUP/HormanderPsh.lean` proves Hörmander's `∂̄`-theorem
(`HormanderStatementExact`) for a real-valued **upper semicontinuous** weight which is locally
integrable and locally bounded below near the support of the data.  This module supplies that
form of the theorem for the §5 weight

  `φ = section5Phi ρ u u₀ = 2u + Λ + ρu₀ + (ρ/2)(⟨Im z⟩ - 1)`,

with curvature `κ = section5Kappa ρ = (ρ/8)⟨Im z⟩^{-3}`, and re-proves the "step (B)" construction
`exists_F_of_hormander_exact` of `Submission/FUP/PSHToFourier2.lean` with the black box
`HormanderStatement` replaced by the proved `HormanderStatementExact`.

The four inputs required by `HormanderStatementExact` are:

* `upperSemicontinuous_section5Phi` — `2u` and `ρu₀` are u.s.c. (`IsPSH.1`), `Λ` is u.s.c.
  (`logWeight` is continuous off the origin and jumps *up* to `0` at the origin), and the last
  term is continuous;
* `locallyIntegrable_section5Phi` — the only non-trivial term is `Λ`, whose local integrability is
  `Commons.Measure.EuclideanSpace.integrableOn_abs_log_sum_sq`;
* `continuous_section5Kappa`;
* `section5Phi_lower_bound` — the local lower bound, whose main ingredient is the annulus bound
  `section5Phi_ge_le` (a general-radius version of `section5Phi_ge`): the data `∂̄(bumpC d)` is
  supported in `{1/2 ≤ ‖z‖}` and vanishes outside `{‖z‖ ≤ 1}`.
-/

namespace Submission.FUP

/-! ## Step 1: helpers -/

lemma upperSemicontinuous_const_mul {f : ℂᵈ → ℝ} (hf : UpperSemicontinuous f) {c : ℝ}
    (hc : 0 ≤ c) : UpperSemicontinuous (fun z => c * f z) := by
  rw [UpperSemicontinuous] at hf ⊢
  intro z y hy
  rcases eq_or_lt_of_le hc with hc0 | hc0
  · subst hc0
    have hy' : (0 : ℝ) < y := by simpa using hy
    exact Filter.Eventually.of_forall (fun w => by simpa using hy')
  · have hlt : f z < y / c := by rw [lt_div_iff₀ hc0]; linarith
    filter_upwards [hf z (y / c) hlt] with w hw
    calc c * f w < c * (y / c) := mul_lt_mul_of_pos_left hw hc0
      _ = y := by field_simp

/-! ## Step 2: `logWeight` is upper semicontinuous -/

lemma upperSemicontinuous_logWeight : UpperSemicontinuous (logWeight (d := d)) := by
  rw [UpperSemicontinuous]
  intro z y hy
  by_cases hz : ∑ j, ‖z j‖ ^ 2 = 0
  · have hfz : logWeight (d := d) z = 0 := by
      simp only [logWeight, hz, Real.log_zero, mul_zero]
    have hy' : (0 : ℝ) < y := by rw [hfz] at hy; exact hy
    have htend : ∀ᶠ w in 𝓝 z, ∑ j, ‖w j‖ ^ 2 < 1 := by
      have hc : ContinuousAt (fun w : ℂᵈ => ∑ j, ‖w j‖ ^ 2) z :=
        (contDiff_sum_sq (d := d)).continuous.continuousAt
      have h1 : (fun w : ℂᵈ => ∑ j, ‖w j‖ ^ 2) z < (1 : ℝ) := by
        show (∑ j, ‖z j‖ ^ 2) < (1 : ℝ)
        rw [hz]; norm_num
      exact hc.preimage_mem_nhds (isOpen_Iio.mem_nhds h1)
    filter_upwards [htend] with w hw
    have hw0 : 0 ≤ ∑ j, ‖w j‖ ^ 2 := sum_sq_nonneg w
    have hlog : Real.log (∑ j, ‖w j‖ ^ 2) ≤ 0 := Real.log_nonpos hw0 hw.le
    show logWeight w < y
    rw [logWeight]
    have hcoef : (0 : ℝ) ≤ 10 * (d : ℝ) := by positivity
    have h2 := mul_nonpos_of_nonneg_of_nonpos hcoef hlog
    linarith
  · have hcont : ContinuousAt (logWeight (d := d)) z := by
      change ContinuousAt (fun w : ℂᵈ => 10 * (d : ℝ) * Real.log (∑ j, ‖w j‖ ^ 2)) z
      have hS : ContinuousAt (fun w : ℂᵈ => ∑ j, ‖w j‖ ^ 2) z :=
        (contDiff_sum_sq (d := d)).continuous.continuousAt
      exact ((Real.continuousAt_log hz).comp (f := fun w : ℂᵈ => ∑ j, ‖w j‖ ^ 2) hS).const_mul (10 * (d : ℝ))
    exact hcont.preimage_mem_nhds (isOpen_Iio.mem_nhds hy)

/-! ## Step 3: `logWeight` is locally integrable -/

lemma locallyIntegrable_logWeight (hd : 1 ≤ d) :
    LocallyIntegrable (logWeight (d := d)) (volume : Measure (ℂᵈ)) := by
  rw [locallyIntegrable_iff]
  intro K hK
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : ℂᵈ)
  have hbase : IntegrableOn (fun z : ℂᵈ => |Real.log (∑ j, ‖z j‖ ^ 2)|)
      (Metric.closedBall (0 : ℂᵈ) R) volume :=
    Commons.Measure.EuclideanSpace.integrableOn_abs_log_sum_sq hd R
  have hlog : IntegrableOn (fun z : ℂᵈ => Real.log (∑ j, ‖z j‖ ^ 2))
      (Metric.closedBall (0 : ℂᵈ) R) volume := by
    have hmeas : AEStronglyMeasurable (fun z : ℂᵈ => Real.log (∑ j, ‖z j‖ ^ 2))
        (volume.restrict (Metric.closedBall (0 : ℂᵈ) R)) :=
      (Real.measurable_log.comp (contDiff_sum_sq (d := d)).continuous.measurable).aestronglyMeasurable
    have hbase' : Integrable (fun z : ℂᵈ => ‖Real.log (∑ j, ‖z j‖ ^ 2)‖)
        (volume.restrict (Metric.closedBall (0 : ℂᵈ) R)) := by
      rw [show (fun z : ℂᵈ => ‖Real.log (∑ j, ‖z j‖ ^ 2)‖)
          = (fun z : ℂᵈ => |Real.log (∑ j, ‖z j‖ ^ 2)|) from
            funext (fun z => Real.norm_eq_abs _)]
      exact hbase
    exact (integrable_norm_iff hmeas).mp hbase'
  have hlog' : IntegrableOn (fun z : ℂᵈ => 10 * (d : ℝ) * Real.log (∑ j, ‖z j‖ ^ 2))
      (Metric.closedBall (0 : ℂᵈ) R) volume := hlog.const_mul (10 * (d : ℝ))
  exact hlog'.mono_set hR

/-! ## Step 4: `section5Kappa` is continuous -/

lemma continuous_section5Kappa (ρ : ℝ) : Continuous (section5Kappa (d := d) ρ) := by
  change Continuous (fun z : ℂᵈ => (ρ / 8) / (imNorm z) ^ 3)
  refine continuous_const.div ((contDiff_imNorm (d := d)).continuous.pow 3) fun z => ?_
  exact pow_ne_zero 3 (ne_of_gt (imNorm_pos z))

/-! ## Step 5: upper semicontinuity of the §5 weight -/

theorem upperSemicontinuous_section5Phi {ρ : ℝ} (hρ : 0 < ρ) {u u0 : ℂᵈ → ℝ}
    (hupsh : IsPSH u) (hu0psh : IsPSH u0) :
    UpperSemicontinuous (section5Phi ρ u u0) := by
  have h1 : UpperSemicontinuous (fun z : ℂᵈ => 2 * u z) :=
    upperSemicontinuous_const_mul hupsh.1 (by norm_num)
  have h2 : UpperSemicontinuous (fun z : ℂᵈ => ρ * u0 z) :=
    upperSemicontinuous_const_mul hu0psh.1 hρ.le
  have h3 : UpperSemicontinuous (fun z : ℂᵈ => (ρ / 2) * (imNorm z - 1)) :=
    (continuous_const.mul ((contDiff_imNorm (d := d)).continuous.sub continuous_const)).upperSemicontinuous
  have h4 := ((h1.add (upperSemicontinuous_logWeight (d := d))).add h2).add h3
  change UpperSemicontinuous (fun z : ℂᵈ =>
    2 * u z + logWeight z + ρ * u0 z + (ρ / 2) * (imNorm z - 1))
  exact h4

/-! ## Step 6: local integrability of the §5 weight -/

theorem locallyIntegrable_section5Phi (hd : 1 ≤ d) {CLip ρ : ℝ} (hCLip : 0 ≤ CLip) (hρ : 0 < ρ)
    {u u0 : ℂᵈ → ℝ} (hupsh : IsPSH u) (hu0psh : IsPSH u0)
    (huzero : ∀ x : ℝᵈ, ‖x‖ ≤ 2 → u (toCpx x) = 0)
    (hulip : ∀ x₁ x₂ : ℝᵈ, |u (toCpx x₁) - u (toCpx x₂)| ≤ CLip * ‖x₁ - x₂‖)
    (hugrowth : ∀ z : ℂᵈ, u (toCpx (reVec z)) ≤ u z ∧
      u z ≤ u (toCpx (reVec z)) + ρ * ‖imVec z‖)
    (hu0zero : ∀ x : ℝᵈ, ‖x‖ ≤ 2 → u0 (toCpx x) = 0)
    (hu0lip : ∀ x₁ x₂ : ℝᵈ, |u0 (toCpx x₁) - u0 (toCpx x₂)| ≤ 1 * ‖x₁ - x₂‖)
    (hu0growth : ∀ z : ℂᵈ, u0 (toCpx (reVec z)) ≤ u0 z ∧
      u0 z ≤ u0 (toCpx (reVec z)) + (1 / 2) * ‖imVec z‖) :
    LocallyIntegrable (section5Phi ρ u u0) (volume : Measure (ℂᵈ)) := by
  have hu : LocallyIntegrable u (volume : Measure (ℂᵈ)) :=
    locallyIntegrable_of_upperSemicontinuous (d := d) hupsh.1
      (boundedOnCompact_of_hyp (d := d) hCLip hρ.le huzero hulip hugrowth)
  have hu0 : LocallyIntegrable u0 (volume : Measure (ℂᵈ)) :=
    locallyIntegrable_of_upperSemicontinuous (d := d) hu0psh.1
      (boundedOnCompact_of_hyp (d := d) (by norm_num : (0:ℝ) ≤ 1) (by norm_num : (0:ℝ) ≤ 1/2)
        hu0zero hu0lip hu0growth)
  have h1 : LocallyIntegrable (fun z : ℂᵈ => 2 * u z) (volume : Measure (ℂᵈ)) := by
    rw [show (fun z : ℂᵈ => 2 * u z) = (2 : ℝ) • u from by
      funext z; simp only [Pi.smul_apply, smul_eq_mul]]
    exact hu.smul (2 : ℝ)
  have h2 : LocallyIntegrable (fun z : ℂᵈ => ρ * u0 z) (volume : Measure (ℂᵈ)) := by
    rw [show (fun z : ℂᵈ => ρ * u0 z) = ρ • u0 from by
      funext z; simp only [Pi.smul_apply, smul_eq_mul]]
    exact hu0.smul ρ
  have h3 : LocallyIntegrable (fun z : ℂᵈ => (ρ / 2) * (imNorm z - 1)) (volume : Measure (ℂᵈ)) :=
    (continuous_const.mul ((contDiff_imNorm (d := d)).continuous.sub continuous_const)).locallyIntegrable
  have h4 := ((h1.add (locallyIntegrable_logWeight (d := d) hd)).add h2).add h3
  change LocallyIntegrable (fun z : ℂᵈ =>
    2 * u z + logWeight z + ρ * u0 z + (ρ / 2) * (imNorm z - 1)) (volume : Measure (ℂᵈ))
  exact h4

/-! ## Step 7: the annulus lower bound for the §5 weight, with a general radius -/

lemma section5Phi_ge_le {CLip ρ c R : ℝ} (hCLip : 0 ≤ CLip) (hρ : 0 < ρ) (hc : 0 < c)
    {u u0 : ℂᵈ → ℝ} (huzero : ∀ x : ℝᵈ, ‖x‖ ≤ 2 → u (toCpx x) = 0)
    (hulip : ∀ x₁ x₂ : ℝᵈ, |u (toCpx x₁) - u (toCpx x₂)| ≤ CLip * ‖x₁ - x₂‖)
    (hugrowth : ∀ z : ℂᵈ, u (toCpx (reVec z)) ≤ u z)
    (hu0zero : ∀ x : ℝᵈ, ‖x‖ ≤ 2 → u0 (toCpx x) = 0)
    (hu0lip : ∀ x₁ x₂ : ℝᵈ, |u0 (toCpx x₁) - u0 (toCpx x₂)| ≤ 1 * ‖x₁ - x₂‖)
    (hu0growth : ∀ z : ℂᵈ, u0 (toCpx (reVec z)) ≤ u0 z) :
    ∀ z : ℂᵈ, c ≤ ‖z‖ → ‖z‖ ≤ R →
      -(2 * CLip + ρ) * Real.sqrt d * R + 20 * (d : ℝ) * Real.log c
        ≤ section5Phi ρ u u0 z := by
  intro z hz1 hz2
  have hre : ‖reVec z‖ ≤ Real.sqrt d * R := by
    calc ‖reVec z‖ ≤ Real.sqrt (d : ℝ) * ‖z‖ := norm_reVec_le z
      _ ≤ Real.sqrt (d : ℝ) * R := mul_le_mul_of_nonneg_left hz2 (Real.sqrt_nonneg _)
  have hu1 : -CLip * (Real.sqrt d * R) ≤ u z := by
    have h1 : |u (toCpx (reVec z))| ≤ CLip * ‖reVec z‖ := by
      have h := hulip (reVec z) 0
      have h0 : u (toCpx (0 : ℝᵈ)) = 0 := huzero 0 (by simp)
      simpa only [h0, sub_zero] using h
    have h2 : -CLip * ‖reVec z‖ ≤ u (toCpx (reVec z)) := by
      linarith [neg_abs_le (u (toCpx (reVec z)))]
    have h3 : CLip * ‖reVec z‖ ≤ CLip * (Real.sqrt d * R) :=
      mul_le_mul_of_nonneg_left hre hCLip
    linarith [hugrowth z]
  have hu2 : -1 * (Real.sqrt d * R) ≤ u0 z := by
    have h1 : |u0 (toCpx (reVec z))| ≤ 1 * ‖reVec z‖ := by
      have h := hu0lip (reVec z) 0
      have h0 : u0 (toCpx (0 : ℝᵈ)) = 0 := hu0zero 0 (by simp)
      simpa only [h0, sub_zero] using h
    have h2 : -1 * ‖reVec z‖ ≤ u0 (toCpx (reVec z)) := by
      linarith [neg_abs_le (u0 (toCpx (reVec z)))]
    linarith [hu0growth z, hre]
  have hlw : 20 * (d : ℝ) * Real.log c ≤ logWeight z := logWeight_ge_of_le_norm z hc hz1
  have ht : 0 ≤ (ρ / 2) * (imNorm z - 1) :=
    mul_nonneg (by positivity) (by linarith [one_le_imNorm z])
  rw [section5Phi]
  nlinarith [hu1, hu2, hlw, ht, hρ.le, Real.sqrt_nonneg (d : ℝ)]

/-! ## Step 8: the support of the data -/

lemma tsupport_formNormSq_dbarFun_bumpC_subset_half :
    tsupport (formNormSq (dbarFun (bumpC (d := d)))) ⊆ {z : ℂᵈ | (1 : ℝ) / 2 ≤ ‖z‖} := by
  refine closure_minimal ?_ (isClosed_Ici.preimage continuous_norm)
  intro z hz
  by_contra h
  exact hz (formNormSq_eq_zero (dbarFun_bumpC_eq_zero_of_lt_half (d := d) (not_le.mp h)))

lemma tsupport_formNormSq_dbarFun_bumpC_subset_one :
    tsupport (formNormSq (dbarFun (bumpC (d := d)))) ⊆ {z : ℂᵈ | ‖z‖ ≤ 1} := by
  refine closure_minimal ?_ (isClosed_Iic.preimage continuous_norm)
  intro z hz
  by_contra h
  exact hz (formNormSq_eq_zero (dbarFun_bumpC_eq_zero_of_one_lt (d := d) (not_le.mp h)))

/-! ## Step 9: the local lower bound -/

theorem section5Phi_lower_bound {CLip ρ : ℝ} (hCLip : 0 ≤ CLip) (hρ : 0 < ρ)
    {u u0 : ℂᵈ → ℝ} (huzero : ∀ x : ℝᵈ, ‖x‖ ≤ 2 → u (toCpx x) = 0)
    (hulip : ∀ x₁ x₂ : ℝᵈ, |u (toCpx x₁) - u (toCpx x₂)| ≤ CLip * ‖x₁ - x₂‖)
    (hugrowth : ∀ z : ℂᵈ, u (toCpx (reVec z)) ≤ u z)
    (hu0zero : ∀ x : ℝᵈ, ‖x‖ ≤ 2 → u0 (toCpx x) = 0)
    (hu0lip : ∀ x₁ x₂ : ℝᵈ, |u0 (toCpx x₁) - u0 (toCpx x₂)| ≤ 1 * ‖x₁ - x₂‖)
    (hu0growth : ∀ z : ℂᵈ, u0 (toCpx (reVec z)) ≤ u0 z) :
    ∃ M : ℝ, ∀ z : ℂᵈ,
      (∃ w ∈ tsupport (formNormSq (dbarFun (bumpC (d := d)))), ‖z - w‖ ≤ 1 / 3) →
      -M ≤ section5Phi ρ u u0 z := by
  refine ⟨(2 * CLip + ρ) * Real.sqrt d * (4 / 3) - 20 * (d : ℝ) * Real.log (1 / 6),
    fun z hz => ?_⟩
  obtain ⟨w, hw, hdist⟩ := hz
  have hw12 : (1 : ℝ) / 2 ≤ ‖w‖ :=
    tsupport_formNormSq_dbarFun_bumpC_subset_half (d := d) hw
  have hw1 : ‖w‖ ≤ 1 :=
    tsupport_formNormSq_dbarFun_bumpC_subset_one (d := d) hw
  have hzw : ‖z - w‖ = ‖w - z‖ := norm_sub_rev z w
  have hz16 : (1 : ℝ) / 6 ≤ ‖z‖ := by
    have h3 : ‖w‖ ≤ ‖w - z‖ + ‖z‖ := by
      have := norm_add_le (w - z) z
      simpa using this
    linarith
  have hz43 : ‖z‖ ≤ 4 / 3 := by
    have h3 : ‖z‖ ≤ ‖z - w‖ + ‖w‖ := by
      have := norm_add_le (z - w) w
      simpa using this
    linarith
  have hge := section5Phi_ge_le (d := d) hCLip hρ (by norm_num : (0 : ℝ) < 1 / 6)
    huzero hulip hugrowth hu0zero hu0lip hu0growth z hz16 hz43
  linarith [hge]

/-! ## Step 10: the whole of §5 from `HormanderStatementExact` -/

lemma hasCompactSupport_bumpC : HasCompactSupport (bumpC (d := d)) :=
  (isCompact_closedBall (0 : ℂᵈ) 1).of_isClosed_subset (isClosed_tsupport _) (tsupport_bumpC_subset (d := d))

/-- **Step (B)**: applying Hörmander's `∂̄` theorem (in the exact-data, u.s.c.-weight form
`HormanderStatementExact`) to `η = ∂̄h` produces `g` and the entire function `F = h - g` of §5. -/
theorem exists_F_of_hormander_exact (hH : HormanderStatementExact (d := d)) (hd : 1 ≤ d)
    {CLip ρ : ℝ} (hCLip : 0 ≤ CLip) (hρ : 0 < ρ)
    {u u0 : ℂᵈ → ℝ} (hupsh : IsPSH u) (hu0psh : IsPSH u0)
    (huzero : ∀ x : ℝᵈ, ‖x‖ ≤ 2 → u (toCpx x) = 0)
    (hulip : ∀ x₁ x₂ : ℝᵈ, |u (toCpx x₁) - u (toCpx x₂)| ≤ CLip * ‖x₁ - x₂‖)
    (hugrowth : ∀ z : ℂᵈ, u (toCpx (reVec z)) ≤ u z ∧
      u z ≤ u (toCpx (reVec z)) + ρ * ‖imVec z‖)
    (hu0zero : ∀ x : ℝᵈ, ‖x‖ ≤ 2 → u0 (toCpx x) = 0)
    (hu0lip : ∀ x₁ x₂ : ℝᵈ, |u0 (toCpx x₁) - u0 (toCpx x₂)| ≤ 1 * ‖x₁ - x₂‖)
    (hu0growth : ∀ z : ℂᵈ, u0 (toCpx (reVec z)) ≤ u0 z ∧
      u0 z ≤ u0 (toCpx (reVec z)) + (1 / 2) * ‖imVec z‖) :
    ∃ (F g : ℂᵈ → ℂ), Differentiable ℂ F ∧
      (∀ z, F z = bumpC z - g z) ∧ ContDiff ℝ ∞ g ∧
      (∀ j : Fin d, (fun z => partialZbar j g z) = fun z => dbarFun (bumpC (d := d)) z j) ∧
      (∫⁻ z, ENNReal.ofReal (‖g z‖ ^ 2 * Real.exp (-(section5Phi ρ u u0 z)))
        ≤ ∫⁻ z, ENNReal.ofReal (formNormSq (dbarFun (bumpC (d := d))) z
            * Real.exp (-(section5Phi ρ u u0 z)) / section5Kappa ρ z)) := by
  have hpos : DbarDbarPos (section5Phi ρ u u0) (section5Kappa ρ) :=
    dbarDbarPos_section5Phi hd hCLip hρ hupsh hu0psh huzero hulip hugrowth hu0zero hu0lip
      hu0growth
  have hκpos : ∀ z : ℂᵈ, 0 < section5Kappa ρ z := fun z => section5Kappa_pos hρ z
  obtain ⟨B, hB⟩ := exists_bound_fderiv_bumpC (d := d)
  have hint := lintegral_hormanderTest_le (d := d) hd hCLip hρ hB huzero hulip
    (fun z => (hugrowth z).1) hu0zero hu0lip (fun z => (hu0growth z).1)
  have hint_lt : ∫⁻ z, ENNReal.ofReal (formNormSq (dbarFun (bumpC (d := d))) z
      * Real.exp (-(section5Phi ρ u u0 z)) / section5Kappa ρ z) < ⊤ :=
    lt_of_le_of_lt hint (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (isCompact_closedBall (0 : ℂᵈ) 1).measure_lt_top)
  have hφusc : UpperSemicontinuous (section5Phi ρ u u0) :=
    upperSemicontinuous_section5Phi hρ hupsh hu0psh
  have hφli : LocallyIntegrable (section5Phi ρ u u0) (volume : Measure (ℂᵈ)) :=
    locallyIntegrable_section5Phi hd hCLip hρ hupsh hu0psh huzero hulip hugrowth hu0zero hu0lip
      hu0growth
  have hlb := section5Phi_lower_bound (d := d) hCLip hρ huzero hulip
    (fun z => (hugrowth z).1) hu0zero hu0lip (fun z => (hu0growth z).1)
  obtain ⟨g, hgsm, hgpart, hgL2⟩ := hH (section5Phi ρ u u0) (section5Kappa ρ) hφusc hφli
    hpos hκpos (continuous_section5Kappa ρ) (bumpC (d := d)) contDiff_bumpC_top
    hasCompactSupport_bumpC hlb hint_lt
  have hbump : Differentiable ℝ (bumpC (d := d)) := contDiff_bumpC.differentiable (by norm_num)
  have hgd : Differentiable ℝ g := hgsm.differentiable (by simp)
  refine ⟨fun z => bumpC z - g z, g, ?_, fun z => rfl, hgsm, hgpart, hgL2⟩
  refine Commons.Analysis.Complex.differentiable_complex_of_dbar_eq_zero (hbump.sub hgd) ?_
  intro j z
  have h1 : partialZbar j (fun z => bumpC z - g z) z = 0 := by
    rw [partialZbar_sub j (hbump z) (hgd z)]
    have hz := congrFun (hgpart j) z
    simp only [dbarFun] at hz
    rw [hz, sub_self]
  have h2 : partialZbar j (fun z => bumpC z - g z) z
      = (fderiv ℝ (fun z => bumpC z - g z) z (Pi.single j 1)
        + Complex.I * fderiv ℝ (fun z => bumpC z - g z) z (Pi.single j Complex.I)) / 2 := rfl
  rw [h2] at h1
  rcases div_eq_zero_iff.mp h1 with h | h
  · exact h
  · norm_num at h

end Submission.FUP
