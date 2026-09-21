import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.Kernel.Diag
import Submission.Work.OddVolterra.Kernel.G2Deriv
import Submission.Work.OddVolterra.Existence.Theta_integrand_intervalIntegrable

namespace Work.OddVolterra.Existence

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

set_option maxHeartbeats 1000000

/-- **Continuity in `σ` of the `G₂`-derivative integral.**  The τ-integrand is
`(√(τ(1-τ)))⁻¹ (1-τ) ∂_a K(s+τ(σ-s),σ,Z σ)`, dominated by `Cm (√(τ(1-τ)))⁻¹`,
with a.e. (indeed every) τ-continuity in `σ` coming from the joint continuity of
the first-argument derivative field of `Kvec` on the region where the Abel
denominators are positive. -/
theorem continuousOn_integral_deriv_G2_apply (n : ℕ) (hn : 1 ≤ n) {h : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) {Z : ℝ → Work.OddVolterra.St}
    (hZ : ContDiffOn ℝ (⊤ : ℕ∞) Z (Set.Ioi (0:ℝ)))
    {s : ℝ} (hs : s ∈ Set.Ioo (0:ℝ) 1) (i : Fin 2)
    {δ Cm : ℝ} (hδ : 0 < δ) (hCm : 0 < Cm)
    (hpos : ∀ σ ∈ Set.Icc s 1, ∀ a ∈ Set.Icc (s - δ) σ,
      0 < Work.OddVolterra.krad h σ (-(Z σ 0)) a ∧
        0 < Work.OddVolterra.krad h σ (Z σ 1) a)
    (hbdK : ∀ σ ∈ Set.Icc s 1, ∀ a ∈ Set.Ico (s - δ) σ,
      ‖Work.OddVolterra.Kvec n h a σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3)‖ ≤ Cm)
    (hbdD : ∀ σ ∈ Set.Icc s 1, ∀ a ∈ Set.Ico (s - δ) σ,
      ‖deriv (fun u : ℝ => Work.OddVolterra.Kvec n h u σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3)) a‖ ≤ Cm) :
    ContinuousOn (fun σ : ℝ =>
        ∫ τ in (0:ℝ)..1, (Real.sqrt (τ * (1 - τ)))⁻¹ *
          ((1 - τ) * ((deriv (fun u : ℝ => Work.OddVolterra.Kvec n h u σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3)) (s + τ * (σ - s))) i)))
      (Set.Ioo s 1) := by
  have hs0 : 0 < s := hs.1
  let Φ : ℝ → ℝ → ℝ := fun σ τ => (Real.sqrt (τ * (1 - τ)))⁻¹ *
      ((1 - τ) * ((deriv (fun u : ℝ => Work.OddVolterra.Kvec n h u σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3)) (s + τ * (σ - s))) i))
  have hΦapply : ∀ (σ τ : ℝ), Φ σ τ = (Real.sqrt (τ * (1 - τ)))⁻¹ *
      ((1 - τ) * ((deriv (fun u : ℝ => Work.OddVolterra.Kvec n h u σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3)) (s + τ * (σ - s))) i)) :=
    fun σ τ => rfl
  change ContinuousOn (fun σ : ℝ => ∫ τ in (0:ℝ)..1, Φ σ τ) (Set.Ioo s 1)
  -- joint continuity of the first-argument derivative field of `Kvec`
  have hderivOn : ContinuousOn (fun p : (ℝ × ℝ) × Work.OddVolterra.St =>
      (deriv (fun u : ℝ => Work.OddVolterra.Kvec n h u p.1.2 (p.2 0) (p.2 1) (p.2 2) (p.2 3)) p.1.1) i)
      (kvecRegion h) :=
    (continuous_apply i).comp_continuousOn (continuousOn_deriv_Kvec n hn hh)
  -- continuity of `Z` inside the slope window
  have hZIoo : ContinuousOn Z (Set.Ioo s 1) :=
    hZ.continuousOn.mono (fun x hx => lt_trans hs0 hx.1)
  intro σ0 hσ0
  have hσ0Icc : σ0 ∈ Set.Icc s 1 := ⟨le_of_lt hσ0.1, le_of_lt hσ0.2⟩
  refine intervalIntegral.continuousWithinAt_of_dominated_interval
    (μ := volume) (a := (0:ℝ)) (b := 1)
    (s := Set.Ioo s 1) (x₀ := σ0) (F := Φ)
    (bound := fun τ => (Real.sqrt (τ * (1 - τ)))⁻¹ * Cm) ?_ ?_ ?_ ?_
  · -- measurability in σ
    refine Filter.Eventually.of_forall (fun x => ?_)
    refine Measurable.aestronglyMeasurable ?_
    rw [show Φ x = fun τ : ℝ => (Real.sqrt (τ * (1 - τ)))⁻¹ *
        ((1 - τ) * ((deriv (fun u : ℝ => Work.OddVolterra.Kvec n h u x (Z x 0) (Z x 1) (Z x 2) (Z x 3)) (s + τ * (x - s))) i)) from funext (fun τ => hΦapply x τ)]
    refine Measurable.mul ?_ (Measurable.mul ?_ ?_)
    · exact (Real.continuous_sqrt.measurable.comp
        (measurable_id.mul (measurable_const.sub measurable_id))).inv
    · exact measurable_const.sub measurable_id
    · exact (measurable_pi_apply i).comp ((measurable_deriv (𝕜 := ℝ)
        (fun u : ℝ => Work.OddVolterra.Kvec n h u x (Z x 0) (Z x 1) (Z x 2) (Z x 3))).comp
          (by fun_prop : Measurable fun τ : ℝ => s + τ * (x - s)))
  · -- domination
    rw [eventually_nhdsWithin_iff]
    refine Filter.Eventually.of_forall (fun x hx => ?_)
    refine Filter.Eventually.of_forall (fun t ht => ?_)
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
    rcases eq_or_lt_of_le ht.2 with h1 | h1
    · subst h1
      rw [hΦapply x 1]
      norm_num
    · have hxIcc : x ∈ Set.Icc s 1 := ⟨le_of_lt hx.1, le_of_lt hx.2⟩
      have hxpos : 0 < x - s := by linarith [hx.1]
      have ha_ge : s - δ ≤ s + t * (x - s) := by
        have : 0 ≤ t * (x - s) := mul_nonneg ht.1.le hxpos.le
        linarith
      have ha_lt : s + t * (x - s) < x := by
        have hlt : t * (x - s) < 1 * (x - s) := mul_lt_mul_of_pos_right h1 hxpos
        linarith
      have hD := hbdD x hxIcc (s + t * (x - s)) ⟨ha_ge, ha_lt⟩
      have hDi : |deriv (fun u : ℝ => Work.OddVolterra.Kvec n h u x (Z x 0) (Z x 1) (Z x 2) (Z x 3)) (s + t * (x - s)) i| ≤ Cm := by
        rw [← Real.norm_eq_abs]
        exact le_trans (norm_le_pi_norm _ i) hD
      have hgle : 0 ≤ (Real.sqrt (t * (1 - t)))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
      have ht1 : 0 ≤ 1 - t := by linarith [h1.le]
      rw [hΦapply x t, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hgle, abs_of_nonneg ht1]
      calc (Real.sqrt (t * (1 - t)))⁻¹ * ((1 - t) *
              |deriv (fun u : ℝ => Work.OddVolterra.Kvec n h u x (Z x 0) (Z x 1) (Z x 2) (Z x 3)) (s + t * (x - s)) i|)
          ≤ (Real.sqrt (t * (1 - t)))⁻¹ * (1 * Cm) := by
            refine mul_le_mul_of_nonneg_left ?_ hgle
            calc (1 - t) * |deriv (fun u : ℝ => Work.OddVolterra.Kvec n h u x (Z x 0) (Z x 1) (Z x 2) (Z x 3)) (s + t * (x - s)) i|
                ≤ 1 * |deriv (fun u : ℝ => Work.OddVolterra.Kvec n h u x (Z x 0) (Z x 1) (Z x 2) (Z x 3)) (s + t * (x - s)) i| :=
                  mul_le_mul_of_nonneg_right (by linarith [ht.1] : 1 - t ≤ 1) (abs_nonneg _)
              _ ≤ 1 * Cm := mul_le_mul_of_nonneg_left hDi (by norm_num)
        _ = (Real.sqrt (t * (1 - t)))⁻¹ * Cm := by ring
  · -- integrability of the dominating function
    exact Commons.Geometry.Ulam.intervalIntegrable_abel_weight.mul_const Cm
  · -- a.e. (in fact every) τ-slice is continuous in σ
    refine Filter.Eventually.of_forall (fun t ht => ?_)
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
    rcases eq_or_lt_of_le ht.2 with h1 | h1
    · subst h1
      have hzero : (fun x : ℝ => Φ x 1) = fun _ => (0:ℝ) := by
        funext x
        rw [hΦapply x 1]
        norm_num
      rw [hzero]
      exact continuousWithinAt_const
    · -- `0 < t < 1`
      have htIoo : t ∈ Set.Ioo (0:ℝ) 1 := ⟨ht.1, h1⟩
      -- the moving point map
      have hψ : ContinuousOn (fun σ : ℝ => ((s + t * (σ - s), σ), Z σ)) (Set.Ioo s 1) := by
        intro σ hσ
        exact ContinuousWithinAt.prodMk
          ((by fun_prop : Continuous fun σ : ℝ => (s + t * (σ - s), σ)).continuousWithinAt)
          (hZIoo.continuousWithinAt hσ)
      -- it maps into the good region
      have hmaps : Set.MapsTo (fun σ : ℝ => ((s + t * (σ - s), σ), Z σ)) (Set.Ioo s 1)
          (kvecRegion h) := by
        intro σ hσ
        have hσIcc : σ ∈ Set.Icc s 1 := ⟨le_of_lt hσ.1, le_of_lt hσ.2⟩
        have hxpos : 0 < σ - s := by linarith [hσ.1]
        have ha_lt : s + t * (σ - s) < σ := by
          have hlt : t * (σ - s) < 1 * (σ - s) := mul_lt_mul_of_pos_right h1 hxpos
          linarith
        have ha_ge : s - δ ≤ s + t * (σ - s) := by
          have : 0 ≤ t * (σ - s) := mul_nonneg ht.1.le hxpos.le
          linarith
        have hk := hpos σ hσIcc (s + t * (σ - s)) ⟨ha_ge, ha_lt.le⟩
        exact ⟨ha_lt, hk.1, hk.2⟩
      have hcov : ContinuousWithinAt (fun σ : ℝ =>
          (deriv (fun u : ℝ => Work.OddVolterra.Kvec n h u σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3)) (s + t * (σ - s))) i)
          (Set.Ioo s 1) σ0 := by
        have h := hderivOn.comp hψ hmaps
        have := h.continuousWithinAt hσ0
        simpa [Function.comp_def] using this
      change ContinuousWithinAt (fun σ : ℝ => (Real.sqrt (t * (1 - t)))⁻¹ *
        ((1 - t) * ((deriv (fun u : ℝ => Work.OddVolterra.Kvec n h u σ (Z σ 0) (Z σ 1) (Z σ 2) (Z σ 3)) (s + t * (σ - s))) i)))
        (Set.Ioo s 1) σ0
      exact (hcov.const_mul (1 - t)).const_mul _

end Work.OddVolterra.Existence
