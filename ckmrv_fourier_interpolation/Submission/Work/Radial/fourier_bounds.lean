import Mathlib

namespace Work.Radial

open Filter MeasureTheory
open scoped ContDiff FourierTransform Topology SchwartzMap

/-- The Fourier transform of a smooth compactly supported function on `ℝ` is smooth and
rapidly decreasing, together with the associated integrability and tail-vanishing statements.

The proof bundles `h` as a Schwartz function `H = hc.toSchwartzMap hh` (using that a smooth
function with compact support is Schwartz) and reads off all four claims from the Fourier
transform `G = 𝓕 H` on the Schwartz space, using that the Schwartz Fourier transform agrees
with the ordinary Fourier transform of the underlying function. -/
theorem fourier_bounds {h : ℝ → ℂ} (hh : ContDiff ℝ ∞ h)
    (hsupp : ∃ R : ℝ, ∀ t : ℝ, R ≤ |t| → h t = 0) :
    ContDiff ℝ ∞ (𝓕 h) ∧
    (∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, (1 + |u|) ^ N * ‖(𝓕 h) u‖ ≤ C) ∧
    (∀ l : ℕ, Integrable (fun u : ℝ => (2 * Real.pi * |u|) ^ l * ‖(𝓕 h) u‖)) ∧
    (∀ l : ℕ, Tendsto (fun T : ℝ => ∫ u in {u : ℝ | T < |u|},
        (2 * Real.pi * |u|) ^ l * ‖(𝓕 h) u‖) atTop (𝓝 0)) := by
  -- `h` has compact support.
  have hc : HasCompactSupport h := by
    obtain ⟨R, hR⟩ := hsupp
    rw [← exists_compact_iff_hasCompactSupport]
    refine ⟨Metric.closedBall 0 R, isCompact_closedBall 0 R, ?_⟩
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right, not_le, Real.norm_eq_abs] at hx
    exact hR x (le_of_lt hx)
  -- View `h` as a Schwartz function.
  let H : 𝓢(ℝ, ℂ) := hc.toSchwartzMap hh
  have hH : (H : ℝ → ℂ) = h :=
    funext fun x => HasCompactSupport.toSchwartzMap_toFun hc hh x
  -- Its Schwartz Fourier transform agrees with the ordinary Fourier transform of `h`.
  let G : 𝓢(ℝ, ℂ) := 𝓕 H
  have hG : (G : ℝ → ℂ) = 𝓕 h := by
    show ((𝓕 H : 𝓢(ℝ, ℂ)) : ℝ → ℂ) = 𝓕 h
    rw [SchwartzMap.fourier_coe, hH]
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Smoothness.
    rw [← hG]
    exact G.smooth ⊤
  · -- Rapid decrease.
    intro N
    refine ⟨2 ^ N * ((Finset.Iic (N, 0)).sup
        (fun m => SchwartzMap.seminorm ℝ m.1 m.2)) G, by positivity, ?_⟩
    intro u
    have hb := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (N, 0))
      (k := N) (n := 0) le_rfl le_rfl G u
    simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at hb
    rw [← congr_fun hG u]
    exact hb
  · -- Integrability of `(2π|u|)^l ‖𝓕 h u‖`.
    intro l
    have hInt_pow : Integrable (fun x : ℝ => (2 * Real.pi) ^ l * (‖x‖ ^ l * ‖G x‖)) :=
      (SchwartzMap.integrable_pow_mul (volume : Measure ℝ) G l).const_mul _
    have hfun : (fun u : ℝ => (2 * Real.pi * |u|) ^ l * ‖(𝓕 h) u‖) =
        (fun x : ℝ => (2 * Real.pi) ^ l * (‖x‖ ^ l * ‖G x‖)) := by
      funext u
      rw [← congr_fun hG u, Real.norm_eq_abs, mul_pow]
      ring
    rw [hfun]
    exact hInt_pow
  · -- Vanishing of the tail integrals.
    intro l
    have hf0 : Integrable (fun u : ℝ => (2 * Real.pi * |u|) ^ l * ‖(𝓕 h) u‖) := by
      have hInt_pow : Integrable (fun x : ℝ => (2 * Real.pi) ^ l * (‖x‖ ^ l * ‖G x‖)) :=
        (SchwartzMap.integrable_pow_mul (volume : Measure ℝ) G l).const_mul _
      have hfun : (fun u : ℝ => (2 * Real.pi * |u|) ^ l * ‖(𝓕 h) u‖) =
          (fun x : ℝ => (2 * Real.pi) ^ l * (‖x‖ ^ l * ‖G x‖)) := by
        funext u
        rw [← congr_fun hG u, Real.norm_eq_abs, mul_pow]
        ring
      rw [hfun]
      exact hInt_pow
    have hf0nn : ∀ u : ℝ, 0 ≤ (2 * Real.pi * |u|) ^ l * ‖(𝓕 h) u‖ := by
      intro u; positivity
    have hmeas : ∀ T : ℝ, MeasurableSet {u : ℝ | T < |u|} := by
      intro T; measurability
    have hmain := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (μ := (volume : Measure ℝ)) (l := atTop)
      (F := fun T u =>
        {u : ℝ | T < |u|}.indicator (fun u => (2 * Real.pi * |u|) ^ l * ‖(𝓕 h) u‖) u)
      (f := fun _ => (0 : ℝ))
      (bound := fun u => (2 * Real.pi * |u|) ^ l * ‖(𝓕 h) u‖)
      (Eventually.of_forall fun T => hf0.aestronglyMeasurable.indicator (hmeas T))
      (Eventually.of_forall fun T => ae_of_all _ fun u =>
          (norm_indicator_le_norm_self _ u).trans_eq (Real.norm_of_nonneg (hf0nn u)))
      hf0
      (ae_of_all _ fun u => by
        have hc0 : (fun T : ℝ => {u : ℝ | T < |u|}.indicator
              (fun u => (2 * Real.pi * |u|) ^ l * ‖(𝓕 h) u‖) u) =ᶠ[atTop] (fun _ => (0 : ℝ)) := by
          filter_upwards [eventually_gt_atTop |u|] with T hT
          rw [Set.indicator_of_notMem (s := {x : ℝ | T < |x|}) (a := u)
            (not_lt.mpr (le_of_lt hT))]
        exact Filter.Tendsto.congr' hc0.symm tendsto_const_nhds)
    have heq : (fun T : ℝ => ∫ u, {u : ℝ | T < |u|}.indicator
          (fun u => (2 * Real.pi * |u|) ^ l * ‖(𝓕 h) u‖) u) =
        fun T => ∫ u in {u : ℝ | T < |u|}, (2 * Real.pi * |u|) ^ l * ‖(𝓕 h) u‖ := by
      funext T
      rw [MeasureTheory.integral_indicator (hmeas T)]
    rw [heq, integral_zero] at hmain
    exact hmain

end Work.Radial
