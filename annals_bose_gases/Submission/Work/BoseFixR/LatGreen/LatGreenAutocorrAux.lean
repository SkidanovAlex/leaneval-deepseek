import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.BoseFixR.LatGreen.LGFormAux
import Submission.Work.BoseFixR.LatGreen.LatGreenSmoothBddBelow
import Submission.Work.BoseFixR.LatGreen.latGreen_le_inv_fourpi_infDist
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.LatGreen.LatGreenAutocorrAux`

Auxiliary lemmas for `Work.BoseFixR.LatGreen.latGreen_autocorr_integral_le`, the smeared
sharp bound

`∫ u, autoCorr V u * latGreen u ≤ (4π)⁻¹ ∫ u, autoCorr V u / d(u, ℤ³)`

for a nonnegative charge `V` supported in the unit ball (`d(u,ℤ³) = Metric.infDist u ℤ³`).

The pointwise input is the sharp nearest-image bound
`latGreen u ≤ 1/(4π d(u,ℤ³))` (`latGreen_le_inv_fourpi_infDist`, which handles the lattice
points by Lean's `1/0 = 0` convention), together with a *two-sided* control of `latGreen`:

* upper bound `latGreen u ≤ 1/(4π d u)` (`latGreen_le_inv_latDist`);
* lower bound `-C ≤ latGreen u` (`neg_latGreenLB_le_latGreen`, extracted from the Madelung
  lower bound `LatGreenSmoothBddBelow`).

To turn the pointwise bound into an integral inequality both sides must be integrable; the
only non-trivial input is the **local integrability of the lattice Coulomb singularity**
`integrableOn_inv_latDist_ball`: in dimension three `1/‖x − p‖` is integrable near `p ∈ ℤ³`,
and on `ball 0 R` only finitely many lattice points matter.

The autocorrelation input: `autoCorr V` is integrable (`autoCorr_bound_noMeas`), bounded by
`∫ V²`, nonnegative for `V ≥ 0`, and supported in the ball of radius `2`.
-/

noncomputable section

open scoped Real BigOperators
open MeasureTheory Set

namespace Work.BoseFixR.LatGreen

local notation "ℝ3" => EuclideanSpace ℝ (Fin 3)

/-! ## The distance to the lattice -/

/-- The distance from `u` to the `ℤ³` lattice. -/
noncomputable def latDist (u : ℝ3) : ℝ :=
  Metric.infDist u (Set.range (latVec : (Fin 3 → ℤ) → ℝ3))

lemma latDist_nonneg (u : ℝ3) : 0 ≤ latDist u := Metric.infDist_nonneg

lemma latDist_latVec (n : Fin 3 → ℤ) : latDist (latVec n) = 0 :=
  Metric.infDist_zero_of_mem ⟨n, rfl⟩

/-! ## Measurability of `latGreen` -/

theorem measurable_latGreen : Measurable (fun u : ℝ3 => latGreen u) := by
  have h1 : StronglyMeasurable (Function.uncurry (fun (t : ℝ) (u : ℝ3) => heatPeriod t u - 1)) :=
    (measurable_heatPeriod_pair.sub measurable_const).stronglyMeasurable
  have h2 : StronglyMeasurable (fun u : ℝ3 =>
      ∫ t, (fun (t : ℝ) (u : ℝ3) => heatPeriod t u - 1) t u
        ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))) :=
    h1.integral_prod_left (μ := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
  exact h2.measurable

/-! ## Two-sided bounds on `latGreen` -/

/-- The sharp pointwise nearest-image bound, valid at every `u` (at a lattice point both sides
vanish, by the `1/0 = 0` convention). -/
theorem latGreen_le_inv_latDist (u : ℝ3) : latGreen u ≤ (4 * Real.pi * latDist u)⁻¹ := by
  by_cases hmem : u ∈ Set.range (latVec : (Fin 3 → ℤ) → ℝ3)
  · obtain ⟨n, rfl⟩ := hmem
    rw [latGreen_latVec_eq_zero n, latDist_latVec n]
    simp
  · have hu : u ≠ 0 := fun h0 => hmem ⟨0, by rw [h0, latVec_zero]⟩
    have h := latGreen_le_inv_fourpi_infDist hu
    rw [latDist]
    simpa [one_div] using h

/-- A nonnegative constant `C` with `-C ≤ latGreen u` for all `u`, extracted from the Madelung
lower bound `LatGreenSmoothBddBelow`. -/
noncomputable def latGreenLB : ℝ := max (Classical.choose LatGreenSmoothBddBelow) 0

lemma latGreenLB_nonneg : 0 ≤ latGreenLB := le_max_right _ _

lemma neg_latGreenLB_le_latGreen (u : ℝ3) : -latGreenLB ≤ latGreen u := by
  by_cases hmem : u ∈ Set.range (latVec : (Fin 3 → ℤ) → ℝ3)
  · obtain ⟨n, rfl⟩ := hmem
    rw [latGreen_latVec_eq_zero n]
    exact neg_nonpos.mpr latGreenLB_nonneg
  · have hu : ∀ n : Fin 3 → ℤ, u ≠ latVec n := fun n hn => hmem ⟨n, hn.symm⟩
    have h1 : -Classical.choose LatGreenSmoothBddBelow ≤ latGreenSmooth u :=
      Classical.choose_spec LatGreenSmoothBddBelow u hu
    have h2 : latGreenSmooth u = latGreen u - 1 / (4 * Real.pi * ‖u‖) := rfl
    have h3 : (0 : ℝ) ≤ 1 / (4 * Real.pi * ‖u‖) := by positivity
    have h4 : -Classical.choose LatGreenSmoothBddBelow ≤ latGreen u := by
      rw [h2] at h1
      linarith
    exact le_trans (neg_le_neg (le_max_left _ _)) h4

/-- The two-sided bound `|latGreen u| ≤ (4π)⁻¹ d(u,ℤ³)⁻¹ + C`. -/
theorem abs_latGreen_le (u : ℝ3) :
    |latGreen u| ≤ (4 * Real.pi)⁻¹ * (latDist u)⁻¹ + latGreenLB := by
  have hup : latGreen u ≤ (4 * Real.pi * latDist u)⁻¹ := latGreen_le_inv_latDist u
  have hlo : -latGreenLB ≤ latGreen u := neg_latGreenLB_le_latGreen u
  have hnn : (0 : ℝ) ≤ (4 * Real.pi)⁻¹ * (latDist u)⁻¹ :=
    mul_nonneg (by positivity) (inv_nonneg.mpr (latDist_nonneg u))
  have h2 : (4 * Real.pi * latDist u)⁻¹ = (4 * Real.pi)⁻¹ * (latDist u)⁻¹ := mul_inv _ _
  have h3 : (0 : ℝ) ≤ latGreenLB := latGreenLB_nonneg
  rw [abs_le]
  constructor <;> linarith

/-! ## The autocorrelation of a charge -/

/-- `autoCorr` of a nonnegative charge is nonnegative. -/
theorem autoCorr_nonneg {V : ℝ3 → ℝ} (hVnn : ∀ x, V x ≥ 0) (u : ℝ3) : 0 ≤ autoCorr V u := by
  rw [autoCorr_apply]
  exact integral_nonneg fun x => mul_nonneg (hVnn x) (hVnn (x + u))

/-- **Autocorrelation bounds for `V ∈ L¹ ∩ L²`**, with no measurability hypothesis on `V`:
`autoCorr V` is integrable and `|autoCorr V u| ≤ ∫ V²` for every `u`. -/
theorem autoCorr_integrable_and_bound' {V : ℝ3 → ℝ}
    (hV1 : MeasureTheory.Integrable V) (hV2 : MeasureTheory.MemLp V 2 MeasureTheory.volume) :
    MeasureTheory.Integrable (autoCorr V) ∧
      ∀ u : ℝ3, |autoCorr V u| ≤ ∫ x : ℝ3, V x ^ 2 := by
  constructor
  · have hVneg : MeasureTheory.Integrable (fun t : ℝ3 => V (-t)) MeasureTheory.volume :=
      hV1.comp_neg
    have hconv : MeasureTheory.Integrable
        (MeasureTheory.convolution (fun t : ℝ3 => V (-t)) V
          (ContinuousLinearMap.mul ℝ ℝ) MeasureTheory.volume) MeasureTheory.volume :=
      hVneg.integrable_convolution (L := ContinuousLinearMap.mul ℝ ℝ) hV1
    refine hconv.congr ?_
    filter_upwards with u
    rw [autoCorr_apply, MeasureTheory.convolution_def]
    calc (∫ t : ℝ3, (ContinuousLinearMap.mul ℝ ℝ (V (-t))) (V (u - t)))
        = ∫ t : ℝ3, V (-t) * V (u - t) :=
          MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => by
            show ((ContinuousLinearMap.mul ℝ ℝ) (V (-t))) (V (u - t)) = V (-t) * V (u - t)
            rw [ContinuousLinearMap.mul_apply'])
      _ = ∫ s : ℝ3, V s * V (u + s) := by
          rw [← MeasureTheory.integral_neg_eq_self (fun s : ℝ3 => V s * V (u + s))
            MeasureTheory.volume]
          rfl
      _ = ∫ x : ℝ3, V x * V (x + u) := by
          refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          show V x * V (u + x) = V x * V (x + u)
          rw [add_comm u x]
  · intro u
    have hpq : (2 : ℝ).HolderConjugate 2 :=
      Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
    have hV2u : MeasureTheory.MemLp (fun x : ℝ3 => V (x + u)) 2 MeasureTheory.volume :=
      hV2.comp_measurePreserving (MeasureTheory.measurePreserving_add_right MeasureTheory.volume u)
    have hHolder : (∫ a : ℝ3, ‖V a‖ * ‖V (a + u)‖) ≤
        (∫ a : ℝ3, ‖V a‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
          * (∫ a : ℝ3, ‖V (a + u)‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
      MeasureTheory.integral_mul_norm_le_Lp_mul_Lq (μ := MeasureTheory.volume)
        (f := V) (g := fun x : ℝ3 => V (x + u)) hpq (by simpa using hV2) (by simpa using hV2u)
    have hA : (∫ a : ℝ3, ‖V a‖ ^ (2 : ℝ)) = ∫ a : ℝ3, V a ^ 2 :=
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun a => by
        show ‖V a‖ ^ (2 : ℝ) = V a ^ 2
        rw [Real.rpow_two, Real.norm_eq_abs, sq_abs])
    have hB : (∫ a : ℝ3, ‖V (a + u)‖ ^ (2 : ℝ)) = ∫ a : ℝ3, V a ^ 2 := by
      rw [MeasureTheory.integral_add_right_eq_self (fun a : ℝ3 => ‖V a‖ ^ (2 : ℝ)) u, hA]
    have hsq : (∫ a : ℝ3, V a ^ 2) ^ (1 / 2 : ℝ) * (∫ a : ℝ3, V a ^ 2) ^ (1 / 2 : ℝ)
        = ∫ a : ℝ3, V a ^ 2 := by
      have hnn : (0 : ℝ) ≤ ∫ a : ℝ3, V a ^ 2 :=
        MeasureTheory.integral_nonneg fun a => sq_nonneg (V a)
      rw [← Real.sqrt_eq_rpow, ← pow_two, Real.sq_sqrt hnn]
    calc |autoCorr V u|
        = |∫ x : ℝ3, V x * V (x + u)| := by rw [autoCorr_apply]
      _ ≤ ∫ x : ℝ3, |V x * V (x + u)| := MeasureTheory.abs_integral_le_integral_abs
      _ = ∫ x : ℝ3, ‖V x‖ * ‖V (x + u)‖ := by
          refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          show |V x * V (x + u)| = ‖V x‖ * ‖V (x + u)‖
          simp [abs_mul]
      _ ≤ (∫ a : ℝ3, ‖V a‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
            * (∫ a : ℝ3, ‖V (a + u)‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := hHolder
      _ = ∫ a : ℝ3, V a ^ 2 := by rw [hA, hB, hsq]

/-- The autocorrelation of a charge supported in the unit ball vanishes for `‖u‖ ≥ 2`. -/
theorem autoCorr_eq_zero_of_two_le_norm {V : ℝ3 → ℝ}
    (hVsupp : tsupport V ⊆ Metric.ball (0 : ℝ3) 1) :
    ∀ u : ℝ3, 2 ≤ ‖u‖ → autoCorr V u = 0 := by
  intro u hu
  have hzero : ∀ x : ℝ3, V x * V (x + u) = 0 := by
    intro x
    by_cases hx : V x = 0
    · rw [hx, zero_mul]
    · have hxt : x ∈ tsupport V := subset_tsupport V (Function.mem_support.mpr hx)
      have hx1 : ‖x‖ < 1 := by
        have := hVsupp hxt
        simpa [Metric.mem_ball, dist_eq_norm] using this
      have hxu : V (x + u) = 0 := by
        by_contra hne
        have hxut : x + u ∈ tsupport V := subset_tsupport V (Function.mem_support.mpr hne)
        have h2 := hVsupp hxut
        rw [Metric.mem_ball, dist_eq_norm, sub_zero] at h2
        have h3 : ‖u‖ ≤ ‖x + u‖ + ‖x‖ := by
          calc ‖u‖ = ‖(x + u) - x‖ := by rw [add_sub_cancel_left]
            _ ≤ ‖x + u‖ + ‖x‖ := norm_sub_le _ _
        linarith
      rw [hxu, mul_zero]
  rw [autoCorr_apply]
  simp only [hzero, integral_zero]

/-! ## Local integrability of the lattice Coulomb singularity -/

/-- `x ↦ 1/‖x‖` is integrable on any ball (polar coordinates in dimension three). -/
lemma integrableOn_inv_norm_ball (c : ℝ3) (R : ℝ) :
    IntegrableOn (fun x : ℝ3 => 1 / ‖x‖) (Metric.ball c R) := by
  have hr : (0 : ℝ) < |R| + ‖c‖ + 1 := by positivity
  have hball0 : IntegrableOn (fun x : ℝ3 => 1 / ‖x‖) (Metric.ball (0 : ℝ3) (|R| + ‖c‖ + 1)) := by
    rw [MeasureTheory.integrableOn_fun_norm_addHaar (μ := (volume : Measure ℝ3))
      (f := fun y : ℝ => 1 / y) (r := |R| + ‖c‖ + 1)]
    have hfr : Module.finrank ℝ ℝ3 = 3 := by simp
    rw [hfr]
    have hgoal : IntegrableOn (fun y : ℝ => y) (Set.Ioo (0 : ℝ) (|R| + ‖c‖ + 1)) := by
      have h := (intervalIntegral.integrableOn_Ioo_rpow_iff (s := (1 : ℝ)) hr).mpr
        (by norm_num : (-1 : ℝ) < 1)
      simpa [Real.rpow_one] using h
    refine hgoal.congr_fun ?_ measurableSet_Ioo
    intro y hy
    have hy0 : y ≠ 0 := ne_of_gt hy.1
    have hpow : y ^ (3 - 1 : ℕ) = y ^ 2 := by norm_num
    show y = y ^ (3 - 1 : ℕ) • (1 / y)
    rw [hpow, smul_eq_mul, pow_two, mul_one_div, mul_div_cancel_right₀ _ hy0]
  refine hball0.mono_set ?_
  intro x hx
  rw [Metric.mem_ball, dist_eq_norm] at hx
  rw [Metric.mem_ball, dist_eq_norm, sub_zero]
  calc ‖x‖ = ‖x - c + c‖ := by rw [sub_add_cancel]
    _ ≤ ‖x - c‖ + ‖c‖ := norm_add_le _ _
    _ < R + ‖c‖ := by linarith
    _ ≤ |R| + ‖c‖ := by linarith [le_abs_self R]
    _ < |R| + ‖c‖ + 1 := by linarith

/-- `u ↦ 1/‖u - a‖` is integrable on the ball `ball 0 R`. -/
lemma integrableOn_inv_norm_sub_ball (a : ℝ3) (R : ℝ) :
    IntegrableOn (fun u : ℝ3 => 1 / ‖u - a‖) (Metric.ball (0 : ℝ3) R) := by
  have hmp : MeasureTheory.MeasurePreserving (fun u : ℝ3 => u - a) MeasureTheory.volume
      MeasureTheory.volume := MeasureTheory.measurePreserving_sub_right MeasureTheory.volume a
  have hemb : MeasurableEmbedding (fun u : ℝ3 => u - a) := by
    have hfun : (fun u : ℝ3 => u - a) = ⇑(MeasurableEquiv.addRight (-a)) := by
      funext u
      simp [sub_eq_add_neg]
    rw [hfun]
    exact MeasurableEquiv.measurableEmbedding (MeasurableEquiv.addRight (-a))
  have hset : (fun u : ℝ3 => u - a) '' Metric.ball (0 : ℝ3) R = Metric.ball (-a) R := by
    ext z
    constructor
    · rintro ⟨u, hu, rfl⟩
      rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hu
      rw [Metric.mem_ball, dist_eq_norm]
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hu
    · intro hz
      refine ⟨z + a, ?_, by abel⟩
      rw [Metric.mem_ball, dist_eq_norm, sub_zero]
      rw [Metric.mem_ball, dist_eq_norm] at hz
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hz
  have key := hmp.integrableOn_image hemb (f := fun z : ℝ3 => 1 / ‖z‖)
    (s := Metric.ball (0 : ℝ3) R)
  rw [hset] at key
  exact key.mp (integrableOn_inv_norm_ball (-a) R)

/-- **Local integrability of `u ↦ 1/d(u,ℤ³)` on `ball 0 R`.** -/
theorem integrableOn_inv_latDist_ball (R : ℝ) :
    IntegrableOn (fun u : ℝ3 => 1 / latDist u) (Metric.ball (0 : ℝ3) R) := by
  by_cases hR : R ≤ 0
  · rw [Metric.ball_eq_empty.mpr hR, IntegrableOn, MeasureTheory.Measure.restrict_empty]
    exact MeasureTheory.integrable_zero_measure
  · push_neg at hR
    set T : ℤ := ⌈R + 1⌉ with hT
    set K : Finset (Fin 3 → ℤ) := Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (-T) T) with hK
    have hRT : R + 1 / 2 < (T : ℝ) := by
      have h1 : R + 1 ≤ ((T : ℤ) : ℝ) := by
        rw [hT]
        exact Int.le_ceil (R + 1)
      linarith
    -- ## The pointwise majorant
    have hpoint : ∀ u ∈ Metric.ball (0 : ℝ3) R,
        ‖1 / latDist u‖ ≤ ∑ m ∈ K, 1 / ‖u - latVec m‖ := by
      intro u hu
      have hnn : (0 : ℝ) ≤ 1 / latDist u := div_nonneg zero_le_one (latDist_nonneg u)
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      obtain ⟨n, hn⟩ := exists_cell_rep u
      have hcell : ∀ i, |(u - latVec n) i| ≤ 1 / 2 := fun i => by
        simpa only [WithLp.ofLp_sub, Pi.sub_apply, latVec_apply] using hn i
      have hd : latDist u = ‖u - latVec n‖ := by
        rw [latDist, ← infDist_sub_latVec u n, infDist_eq_norm_of_cell hcell]
      rw [hd]
      refine Finset.single_le_sum (f := fun m : Fin 3 → ℤ => 1 / ‖u - latVec m‖)
        (fun m _ => by positivity) ?_
      rw [hK, Fintype.mem_piFinset]
      intro i
      rw [Finset.mem_Icc]
      have huR : ‖u‖ < R := by simpa [Metric.mem_ball, dist_eq_norm] using hu
      have hcoord : |u i| ≤ ‖u‖ := by
        have h := PiLp.norm_apply_le (p := (2 : ENNReal)) u i
        simpa [Real.norm_eq_abs] using h
      have hn2 : |u i - ((n i : ℤ) : ℝ)| ≤ 1 / 2 := by simpa [latVec_apply] using hn i
      have htri : |((n i : ℤ) : ℝ)| ≤ |u i| + |u i - ((n i : ℤ) : ℝ)| := by
        have h := abs_sub_le (0 : ℝ) (u i) ((n i : ℤ) : ℝ)
        simpa using h
      have hni : |((n i : ℤ) : ℝ)| < (T : ℝ) := by linarith
      have hlt : ((n i : ℤ) : ℝ) < ((T : ℤ) : ℝ) := (abs_lt.mp hni).2
      have hgt : -(((T : ℤ)) : ℝ) < ((n i : ℤ) : ℝ) := (abs_lt.mp hni).1
      have h1 : n i < T := by exact_mod_cast hlt
      have h2 : -T < n i := by exact_mod_cast hgt
      constructor <;> omega
    -- ## The majorant is integrable
    have hmaj : IntegrableOn (fun u : ℝ3 => ∑ m ∈ K, 1 / ‖u - latVec m‖) (Metric.ball (0 : ℝ3) R) :=
      MeasureTheory.integrable_finsetSum K (fun m _ => integrableOn_inv_norm_sub_ball (latVec m) R)
    -- ## Measurability
    have hmeas : AEStronglyMeasurable (fun u : ℝ3 => 1 / latDist u)
        (MeasureTheory.volume.restrict (Metric.ball (0 : ℝ3) R)) := by
      have h : Measurable (fun u : ℝ3 => 1 / latDist u) := by
        have h2 : Measurable (fun u : ℝ3 => (latDist u)⁻¹) :=
          (measurable_infDist (s := Set.range (latVec : (Fin 3 → ℤ) → ℝ3))).inv
        simpa [latDist, one_div] using h2
      exact h.aestronglyMeasurable
    exact hmaj.mono' hmeas (by
      filter_upwards [self_mem_ae_restrict measurableSet_ball] with u hu
      exact hpoint u hu)

end Work.BoseFixR.LatGreen
