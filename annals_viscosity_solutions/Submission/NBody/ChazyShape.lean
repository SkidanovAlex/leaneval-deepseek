import ChallengeDeps
import Submission.NBody.ChazyTube
import Submission.NBody.Chazy
import Submission.NBody.FirstVariation
import Submission.Commons.Analysis.ODE.tube_invariant_Icc
import Submission.Commons.Analysis.Calculus.norm_sub_le_of_hasDerivAt_of_norm_le_inv_sq
import Mathlib

/-!
# The asymptotic shape of a solution which enters the invariant tube

This is the analytic content of Chazy's continuity of the limit shape, in the form needed for the
cone argument of the paper: a solution `z` of the `N`-body system which enters the invariant tube
around the ray `t ↦ t • a` (at a time `t₁` large enough that the force bound `K / t₁ < ρ / 3`
holds) stays in the tube for all later times up to `S`, and its *shape* `t ↦ t⁻¹ • (z t).1`
becomes eventually close to a configuration `b` with `dist b a ≤ 2ρ/3` — uniformly in `S`.

Since the shape converges only as `t → ∞`, the statement below is the "finite horizon" form: we
exhibit `b` (namely the velocity `(z S).2`, which is within `2ρ/3` of `a`) and show that the shape
at any time `t ≥ t₂` is within `ε` of it, with `t₂` depending only on the tube data.
-/

open ViscositySolutions
open Filter Gradient Real Set Metric
open scoped BigOperators Topology ENNReal
open MeasureTheory

set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {N : ℕ}

namespace Submission.NBody

/-- A closed ball around a collision-free configuration is collision-free. -/
lemma exists_ball_withoutCollisions {a : EN E N} (ha : WithoutCollisions a) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ y : EN E N, dist y a ≤ ρ → WithoutCollisions y := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    ((isOpen_setOf_withoutCollisions (E := E) (N := N)).mem_nhds ha)
  refine ⟨r / 2, by linarith, fun y hy => hball ?_⟩
  rw [Metric.mem_ball]
  linarith

/-- The mass-weighted force is bounded near a collision-free configuration. -/
lemma exists_bound_weightedGrad {m : Fin N → ℝ} {a : EN E N} (ha : WithoutCollisions a) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ K : ℝ, ∀ y : EN E N, dist y a ≤ ρ → ‖weightedGrad m (U m) y‖ ≤ K := by
  have hcont : ContinuousAt (fun y : EN E N => weightedGrad m (U m) y) a :=
    (contDiffAt_weightedGrad_U m a ha).continuousAt
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    (hcont.norm.eventually (eventually_le_nhds (lt_add_one _)))
  refine ⟨r / 2, by linarith, ‖weightedGrad m (U m) a‖ + 1, fun y hy => ?_⟩
  refine hball ?_
  rw [Metric.mem_ball]
  linarith

/-- **The force decays like `t⁻²` along a solution in the tube.** -/
lemma norm_weightedGrad_le_inv_sq_of_tube {m : Fin N → ℝ} {a : EN E N} {ρ K t₁ S : ℝ}
    (ht₁ : 0 < t₁)
    (hnc : ∀ y : EN E N, dist y a ≤ ρ → WithoutCollisions y)
    (hb : ∀ y : EN E N, dist y a ≤ ρ → ‖weightedGrad m (U m) y‖ ≤ K)
    {z : ℝ → EN E N × EN E N}
    (htube : ∀ t ∈ Set.Icc t₁ S, dist (z t).1 (t • a) < t * ρ ∧ dist (z t).2 a < 2 * ρ / 3)
    (hz : ∀ t ∈ Set.Icc t₁ S, HasDerivAt z (stateField m (z t)) t) :
    ∀ t ∈ Set.Icc t₁ S, ‖weightedGrad m (U m) (z t).1‖ ≤ K / t ^ 2 := by
  intro t ht
  have ht0 : 0 < t := lt_of_lt_of_le ht₁ ht.1
  have hw : dist (t⁻¹ • (z t).1) a < ρ := by
    have h1 := (htube t ht).1
    have hsm : t⁻¹ • (t • a) = a := by
      rw [smul_smul, inv_mul_cancel₀ (ne_of_gt ht0), one_smul]
    calc dist (t⁻¹ • (z t).1) a = dist (t⁻¹ • (z t).1) (t⁻¹ • (t • a)) := by rw [hsm]
      _ = ‖(t⁻¹ : ℝ)‖ * dist (z t).1 (t • a) := dist_smul₀ _ _ _
      _ = t⁻¹ * dist (z t).1 (t • a) := by rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht0)]
      _ < t⁻¹ * (t * ρ) := mul_lt_mul_of_pos_left h1 (inv_pos.mpr ht0)
      _ = ρ := by rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt ht0), one_mul]
  have hnc' := hnc _ hw.le
  have hb' := hb _ hw.le
  have hzu : (z t).1 = t • (t⁻¹ • (z t).1) := by
    rw [smul_smul, mul_inv_cancel₀ (ne_of_gt ht0), one_smul]
  rw [hzu, weightedGrad_U_smul m ht0 _ hnc', norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (t ^ 2)⁻¹)]
  calc (t ^ 2)⁻¹ * ‖weightedGrad m (U m) (t⁻¹ • (z t).1)‖ ≤ (t ^ 2)⁻¹ * K :=
        mul_le_mul_of_nonneg_left hb' (by positivity)
    _ = K / t ^ 2 := by rw [div_eq_inv_mul]

/-- **The force bound on the tube**, in the form required by the abstract invariant-tube lemma:
for `y` with `dist y (t • a) ≤ t ρ` one has `‖∇ₘ U(y)‖ ≤ K / t ^ 2`. -/
lemma tube_force_bound {m : Fin N → ℝ} {a : EN E N} {ρ K t₁ S : ℝ}
    (ht₁ : 0 < t₁) (hnc : ∀ y : EN E N, dist y a ≤ ρ → WithoutCollisions y)
    (hb : ∀ y : EN E N, dist y a ≤ ρ → ‖weightedGrad m (U m) y‖ ≤ K) :
    ∀ t ∈ Set.Icc t₁ S, ∀ y : EN E N, dist y (t • a) ≤ t * ρ →
      ‖weightedGrad m (U m) y‖ ≤ K / t ^ 2 := by
  intro t ht y hy
  have ht0 : 0 < t := lt_of_lt_of_le ht₁ ht.1
  have hnorm : dist (t⁻¹ • y) a ≤ ρ := by
    have hsm : t⁻¹ • (t • a) = a := by
      rw [smul_smul, inv_mul_cancel₀ (ne_of_gt ht0), one_smul]
    calc dist (t⁻¹ • y) a = dist (t⁻¹ • y) (t⁻¹ • (t • a)) := by rw [hsm]
      _ = ‖(t⁻¹ : ℝ)‖ * dist y (t • a) := dist_smul₀ _ _ _
      _ = t⁻¹ * dist y (t • a) := by rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht0)]
      _ ≤ t⁻¹ * (t * ρ) := mul_le_mul_of_nonneg_left hy (inv_pos.mpr ht0).le
      _ = ρ := by rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt ht0), one_mul]
  have hnc' := hnc _ hnorm
  have hb' := hb _ hnorm
  have hyu : y = t • (t⁻¹ • y) := by
    rw [smul_smul, mul_inv_cancel₀ (ne_of_gt ht0), one_smul]
  rw [hyu, weightedGrad_U_smul m ht0 _ hnc', norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (t ^ 2)⁻¹)]
  calc (t ^ 2)⁻¹ * ‖weightedGrad m (U m) (t⁻¹ • y)‖ ≤ (t ^ 2)⁻¹ * K :=
        mul_le_mul_of_nonneg_left hb' (by positivity)
    _ = K / t ^ 2 := by rw [div_eq_inv_mul]

/-- **The invariant tube for the `N`-body system** (finite horizon, no hypothesis on the tube). -/
lemma tube_of_hasDerivAt {m : Fin N → ℝ} {a : EN E N} {ρ K t₁ S : ℝ}
    (hρ : 0 < ρ) (ht₁ : 0 < t₁) (htK : K / t₁ < ρ / 3)
    (hnc : ∀ y : EN E N, dist y a ≤ ρ → WithoutCollisions y)
    (hb : ∀ y : EN E N, dist y a ≤ ρ → ‖weightedGrad m (U m) y‖ ≤ K)
    {z : ℝ → EN E N × EN E N}
    (hz : ∀ t ∈ Set.Icc t₁ S, HasDerivAt z (stateField m (z t)) t)
    (hpos : dist (z t₁).1 (t₁ • a) < t₁ * ρ / 3) (hvel : dist (z t₁).2 a < ρ / 3) :
    ∀ t ∈ Set.Icc t₁ S, dist (z t).1 (t • a) < t * ρ ∧ dist (z t).2 a < 2 * ρ / 3 :=
  Commons.Analysis.ODE.tube_invariant_Icc (g := fun x : EN E N => weightedGrad m (U m) x)
    hρ ht₁ htK (tube_force_bound (t₁ := t₁) (S := S) ht₁ hnc hb)
    (by simpa [stateField] using hz) hpos hvel

/-- **Chazy's continuity of the limit shape, tube form.**  A solution which enters the invariant
tube at a time `t₁` stays in it up to any later time `S`, and its shape `t⁻¹ • (z t).1` becomes
eventually close (within `ε`) to the velocity `(z S).2`, which itself lies within `2ρ/3` of `a`. -/
theorem exists_shape_close_of_tube {m : Fin N → ℝ} {a : EN E N} {ρ K t₁ : ℝ}
    (ht₁ : 0 < t₁)
    (hnc : ∀ y : EN E N, dist y a ≤ ρ → WithoutCollisions y)
    (hb : ∀ y : EN E N, dist y a ≤ ρ → ‖weightedGrad m (U m) y‖ ≤ K)
    {S : ℝ} (ht₁S : t₁ ≤ S) {z : ℝ → EN E N × EN E N}
    (htube : ∀ t ∈ Set.Icc t₁ S, dist (z t).1 (t • a) < t * ρ ∧ dist (z t).2 a < 2 * ρ / 3)
    (hz : ∀ t ∈ Set.Icc t₁ S, HasDerivAt z (stateField m (z t)) t)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ b : EN E N, dist b a ≤ 2 * ρ / 3 ∧ ∃ t₂ : ℝ, t₁ ≤ t₂ ∧
      ∀ t ∈ Set.Icc t₂ S, dist (t⁻¹ • (z t).1) b < ε := by
  have hforce := norm_weightedGrad_le_inv_sq_of_tube ht₁ hnc hb htube hz
  -- derivatives of the two components
  have hfst : ∀ t ∈ Set.Icc t₁ S, HasDerivAt (fun s : ℝ => (z s).1) ((z t).2) t := by
    intro t ht
    have h := (ContinuousLinearMap.fst ℝ (EN E N) (EN E N)).hasFDerivAt.comp_hasDerivAt t
      (hz t ht)
    simpa [stateField, Function.comp_def] using h
  have hsnd : ∀ t ∈ Set.Icc t₁ S, HasDerivAt (fun s : ℝ => (z s).2)
      (weightedGrad m (U m) (z t).1) t := by
    intro t ht
    have h := (ContinuousLinearMap.snd ℝ (EN E N) (EN E N)).hasFDerivAt.comp_hasDerivAt t
      (hz t ht)
    simpa [stateField, Function.comp_def] using h
  -- collision-freeness and continuity of the force along the tube
  have hncTube : ∀ t ∈ Set.Icc t₁ S, WithoutCollisions (z t).1 := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le ht₁ ht.1
    have h1 := (htube t ht).1
    have hsm : t⁻¹ • (t • a) = a := by
      rw [smul_smul, inv_mul_cancel₀ (ne_of_gt ht0), one_smul]
    have h2 : dist (t⁻¹ • (z t).1) (t⁻¹ • (t • a)) = ‖(t⁻¹ : ℝ)‖ * dist (z t).1 (t • a) :=
      dist_smul₀ _ _ _
    have hw : dist (t⁻¹ • (z t).1) a < ρ := by
      calc dist (t⁻¹ • (z t).1) a = dist (t⁻¹ • (z t).1) (t⁻¹ • (t • a)) := by rw [hsm]
        _ = t⁻¹ * dist (z t).1 (t • a) := by
              rw [h2, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht0)]
        _ < t⁻¹ * (t * ρ) := mul_lt_mul_of_pos_left h1 (inv_pos.mpr ht0)
        _ = ρ := by rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt ht0), one_mul]
    have hzu : (z t).1 = t • (t⁻¹ • (z t).1) := by
      rw [smul_smul, mul_inv_cancel₀ (ne_of_gt ht0), one_smul]
    rw [hzu]
    exact withoutCollisions_smul (hnc _ hw.le) (ne_of_gt ht0)
  have hcont : ContinuousOn (fun t : ℝ => weightedGrad m (U m) (z t).1) (Set.Icc t₁ S) := by
    have hzcont : ContinuousOn z (Set.Icc t₁ S) :=
      fun t ht => (hz t ht).continuousAt.continuousWithinAt
    exact continuousOn_weightedGrad_comp (m := m)
      (continuousOn_fderiv_U_comp (m := m) (continuous_fst.comp_continuousOn hzcont) hncTube)
  -- the velocity estimate
  have hvel_est : ∀ t ∈ Set.Icc t₁ S, ‖(z S).2 - (z t).2‖ ≤ K / t := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le ht₁ ht.1
    have h := Commons.Analysis.Calculus.norm_sub_le_of_hasDerivAt_of_norm_le_inv_sq ht0 ht.2
      (fun u hu => hsnd u ⟨le_trans ht.1 hu.1, hu.2⟩)
      (hcont.mono (Set.Icc_subset_Icc_left ht.1))
      (fun u hu => hforce u ⟨le_trans ht.1 hu.1, hu.2⟩)
    simpa only [norm_sub_rev] using h
  -- the position estimate: `(z t).1 - t • b` is bounded by `log`
  have hpos_est : ∀ t ∈ Set.Icc t₁ S,
      ‖(z t).1 - t • (z S).2‖ ≤ ‖(z t₁).1 - t₁ • (z S).2‖ + K * Real.log (t / t₁) := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le ht₁ ht.1
    have hInt : IntervalIntegrable (fun u : ℝ => (z u).2) volume t₁ t := by
      refine ContinuousOn.intervalIntegrable ?_
      intro u hu
      rw [Set.uIcc_of_le ht.1] at hu
      exact (hsnd u ⟨hu.1, le_trans hu.2 ht.2⟩).continuousAt.continuousWithinAt
    have hIntc : IntervalIntegrable (fun _ : ℝ => (z S).2) volume t₁ t := intervalIntegrable_const
    have hFTC : (∫ u in t₁..t, (z u).2) = (z t).1 - (z t₁).1 := by
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun u : ℝ => (z u).1) ?_ hInt
      intro u hu
      rw [Set.uIcc_of_le ht.1] at hu
      exact hfst u ⟨hu.1, le_trans hu.2 ht.2⟩
    have hsplit : (z t).1 - t • (z S).2
        = ((z t₁).1 - t₁ • (z S).2) + ∫ u in t₁..t, ((z u).2 - (z S).2) := by
      rw [intervalIntegral.integral_sub hInt hIntc, intervalIntegral.integral_const, hFTC]
      module
    have hbound : ‖∫ u in t₁..t, ((z u).2 - (z S).2)‖ ≤ ∫ u in t₁..t, (K / u) := by
      refine intervalIntegral.norm_integral_le_of_norm_le ht.1 (Filter.Eventually.of_forall ?_) ?_
      · intro u hu
        rw [norm_sub_rev]
        exact hvel_est u ⟨hu.1.le, le_trans hu.2 ht.2⟩
      · refine ContinuousOn.intervalIntegrable ?_
        refine ContinuousOn.div continuousOn_const continuousOn_id ?_
        intro u hu
        rw [Set.uIcc_of_le ht.1] at hu
        exact ne_of_gt (lt_of_lt_of_le ht₁ hu.1)
    have hint : (∫ u in t₁..t, (K / u)) = K * Real.log (t / t₁) := by
      have h1 : ∀ u : ℝ, K / u = K * u⁻¹ := fun u => by rw [div_eq_mul_inv]
      simp_rw [h1]
      rw [intervalIntegral.integral_const_mul,
        integral_inv (by
          rw [Set.uIcc_of_le ht.1]
          exact fun h => (not_le.mpr ht₁) h.1)]
    calc ‖(z t).1 - t • (z S).2‖
        = ‖((z t₁).1 - t₁ • (z S).2) + ∫ u in t₁..t, ((z u).2 - (z S).2)‖ := by rw [hsplit]
      _ ≤ ‖(z t₁).1 - t₁ • (z S).2‖ + ‖∫ u in t₁..t, ((z u).2 - (z S).2)‖ := norm_add_le _ _
      _ ≤ ‖(z t₁).1 - t₁ • (z S).2‖ + ∫ u in t₁..t, (K / u) := by
          exact add_le_add le_rfl hbound
      _ = ‖(z t₁).1 - t₁ • (z S).2‖ + K * Real.log (t / t₁) := by rw [hint]
  -- the limiting behaviour of the bound
  have hlim : Tendsto (fun t : ℝ =>
      (‖(z t₁).1 - t₁ • (z S).2‖ + K * Real.log (t / t₁)) / t) atTop (𝓝 0) := by
    have hlog : Tendsto (fun t : ℝ => Real.log t / t) atTop (𝓝 0) :=
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
    have hlog₁ : Tendsto (fun t : ℝ => Real.log t₁ / t) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have hconst : Tendsto (fun t : ℝ => ‖(z t₁).1 - t₁ • (z S).2‖ / t) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have heq : (fun t : ℝ => (‖(z t₁).1 - t₁ • (z S).2‖ + K * Real.log (t / t₁)) / t)
        =ᶠ[atTop] fun t : ℝ =>
          ‖(z t₁).1 - t₁ • (z S).2‖ / t + K * (Real.log t / t) - K * (Real.log t₁ / t) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      rw [Real.log_div (ne_of_gt ht) (ne_of_gt ht₁)]
      ring
    rw [Filter.tendsto_congr' heq]
    have h2 := (hconst.add (hlog.const_mul K)).sub (hlog₁.const_mul K)
    simpa using h2
  have hev : ∀ᶠ t : ℝ in atTop,
      (‖(z t₁).1 - t₁ • (z S).2‖ + K * Real.log (t / t₁)) / t < ε :=
    (hlim.eventually (isOpen_Ioo.mem_nhds ⟨neg_lt_zero.mpr hε, hε⟩)).mono fun t ht => ht.2
  obtain ⟨t₂, ht₂⟩ := eventually_atTop.mp hev
  refine ⟨(z S).2, (htube S ⟨ht₁S, le_rfl⟩).2.le, max t₁ t₂, le_max_left _ _, ?_⟩
  intro t ht
  have ht₁t : t₁ ≤ t := le_trans (le_max_left _ _) ht.1
  have htSt : t ≤ S := ht.2
  have ht0 : 0 < t := lt_of_lt_of_le ht₁ ht₁t
  have hbnd := ht₂ t (le_trans (le_max_right _ _) ht.1)
  rw [dist_eq_norm]
  have hsm : t⁻¹ • (z t).1 - (z S).2 = t⁻¹ • ((z t).1 - t • (z S).2) := by
    rw [smul_sub, smul_smul, inv_mul_cancel₀ (ne_of_gt ht0), one_smul]
  rw [hsm, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht0)]
  calc t⁻¹ * ‖(z t).1 - t • (z S).2‖
      ≤ t⁻¹ * (‖(z t₁).1 - t₁ • (z S).2‖ + K * Real.log (t / t₁)) :=
        mul_le_mul_of_nonneg_left (hpos_est t ⟨ht₁t, htSt⟩) (inv_pos.mpr ht0).le
    _ = (‖(z t₁).1 - t₁ • (z S).2‖ + K * Real.log (t / t₁)) / t := by
          ring
    _ < ε := hbnd

/-- **Chazy's continuity of the limit shape** (finite horizon, for the `N`-body system).

A solution `z` of the `N`-body system which enters the invariant tube around the ray `t ↦ t • a`
at a time `t₁` (with `K / t₁ < ρ / 3`) stays in the tube up to any later time `S` and its shape
`t ↦ t⁻¹ • (z t).1` is eventually (for `t ≥ t₂`) within `ε` of a configuration `b` with
`dist b a ≤ 2ρ/3`.  This is the form of Chazy's lemma used by the cone argument. -/
theorem chazy_continuity_tube {m : Fin N → ℝ} {a : EN E N} {ρ K t₁ : ℝ}
    (hρ : 0 < ρ) (ht₁ : 0 < t₁) (htK : K / t₁ < ρ / 3)
    (hnc : ∀ y : EN E N, dist y a ≤ ρ → WithoutCollisions y)
    (hb : ∀ y : EN E N, dist y a ≤ ρ → ‖weightedGrad m (U m) y‖ ≤ K)
    {S : ℝ} (ht₁S : t₁ ≤ S) {z : ℝ → EN E N × EN E N}
    (hz : ∀ t ∈ Set.Icc t₁ S, HasDerivAt z (stateField m (z t)) t)
    (hpos : dist (z t₁).1 (t₁ • a) < t₁ * ρ / 3) (hvel : dist (z t₁).2 a < ρ / 3)
    {ε : ℝ} (hε : 0 < ε) :
    (∀ t ∈ Set.Icc t₁ S, dist (z t).1 (t • a) < t * ρ ∧ dist (z t).2 a < 2 * ρ / 3) ∧
      ∃ b : EN E N, dist b a ≤ 2 * ρ / 3 ∧ ∃ t₂ : ℝ, t₁ ≤ t₂ ∧
        ∀ t ∈ Set.Icc t₂ S, dist (t⁻¹ • (z t).1) b < ε :=
  ⟨tube_of_hasDerivAt hρ ht₁ htK hnc hb hz hpos hvel,
    exists_shape_close_of_tube ht₁ hnc hb ht₁S
      (tube_of_hasDerivAt hρ ht₁ htK hnc hb hz hpos hvel) hz hε⟩

end Submission.NBody
