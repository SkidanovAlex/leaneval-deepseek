/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# Symmetry of the Bochner–Martinelli pairing

The lemma `czPair` is the purely measure-theoretic ingredient behind the `L²`-self-adjointness of
the Bochner–Martinelli potential: for continuous compactly supported `a b : ℂⁿ → ℂ`,

  `∫ z, b z * (∫ ζ, bmKernel j (ζ - z) * a ζ) = ∫ ζ, a ζ * (∫ z, bmKernel j (ζ - z) * b z)`.

Both sides are the same double integral `∫∫ b z · bmKernel j (ζ - z) · a ζ` (the complex numbers
are commutative), so the mathematical content is Fubini's theorem; it requires the absolute
convergence of the double integral.  The integrand is supported in `tsupport b × tsupport a` and
the kernel is dominated by `‖x‖ ^ (1 - 2 * n)`, which is integrable on balls of `ℂⁿ` (a real vector
space of dimension `2n`); the necessary estimates are established below, the key one being the
uniform bound `integral_norm_bmKernel_sub_le` on the inner integral.
-/
import Mathlib
import Submission.Work.NN.Core.czB_C0_defs

noncomputable section

open MeasureTheory Set Filter
open scoped NNReal ENNReal

namespace Work.NN.Core

/-! ### Elementary facts about compactly supported continuous functions on `ℂⁿ` -/

/-- A continuous compactly supported complex function on `ℂⁿ` is bounded by a nonnegative
constant. -/
private lemma exists_norm_le_of_continuous_hasCompactSupport {n : ℕ} {g : (Fin n → ℂ) → ℂ}
    (hg : Continuous g) (hgc : HasCompactSupport g) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖g x‖ ≤ B := by
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp (hgc.isCompact_range hg).isBounded
  exact ⟨max C 0, le_max_right _ _, fun x => (hC (g x) (mem_range_self x)).trans (le_max_left _ _)⟩

/-- A compactly supported complex function on `ℂⁿ` vanishes outside a ball. -/
private lemma exists_radius_of_hasCompactSupport {n : ℕ} {g : (Fin n → ℂ) → ℂ}
    (hgc : HasCompactSupport g) : ∃ R : ℝ, 0 ≤ R ∧ ∀ x, R ≤ ‖x‖ → g x = 0 := by
  obtain ⟨K, hK, hKzero⟩ := exists_compact_iff_hasCompactSupport.mpr hgc
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hK.isBounded
  refine ⟨max C 0 + 1, by positivity, fun x hx => ?_⟩
  by_cases hxK : x ∈ K
  · exfalso
    have h1 := hC x hxK
    have h3 : C ≤ max C 0 := le_max_left _ _
    linarith
  · exact hKzero x hxK

/-! ### The `(1 - 2n)`-power is integrable on balls -/

/-- `w ↦ ‖w‖ ^ (1 - 2n)` is integrable on balls of `ℂⁿ`, since the exponent `2n - 1` is smaller
than the real dimension `2n` of `ℂⁿ`.  This is the bound for the Bochner–Martinelli kernel
`‖bmKernel j w‖ ≤ ‖w‖ ^ (1 - 2n)`. -/
private lemma integrableOn_norm_rpow_ball_cn {n : ℕ} (hn : 0 < n) (R : ℝ) :
    IntegrableOn (fun w : Fin n → ℂ => ‖w‖ ^ (1 - 2 * (n : ℝ))) (Metric.ball 0 R) := by
  have hfr : Module.finrank ℝ (Fin n → ℂ) = 2 * n := by
    rw [Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex, mul_comm]
  refine MeasureTheory.integrableOn_ball_of_norm_le_rpow (C := 1) (α := 2 * (n : ℝ) - 1)
    ?_ ?_ ?_ ?_
  · rw [hfr]; omega
  · rw [hfr]; push_cast; linarith
  · filter_upwards with x
    have hexp : -(2 * (n : ℝ) - 1) = 1 - 2 * (n : ℝ) := by ring
    rw [hexp, one_mul, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg x) _)]
  · exact (by measurability : Measurable (fun w : Fin n → ℂ => ‖w‖ ^ (1 - 2 * (n : ℝ)))).aestronglyMeasurable

/-! ### The uniform bound on the inner integral -/

/-- **Uniform bound for the inner integral.**  If `a` is bounded by `A` and vanishes outside the
ball of radius `Ra`, then for `‖x‖ ≤ Rb` the integral of `‖bmKernel j (· - x)‖ * ‖a ·‖` is bounded
by `A` times the integral of `‖w‖ ^ (1 - 2n)` over the ball of radius `Ra + Rb`: the translation
`w = y - x` turns the kernel into `bmKernel j w`, and `a (w + x)` can only be nonzero when
`‖w‖ ≤ Ra + Rb`. -/
private lemma integral_norm_bmKernel_sub_le {n : ℕ} (hn : 0 < n) (j : Fin n) {a : (Fin n → ℂ) → ℂ}
    (ha : Continuous a) {A Ra Rb : ℝ} (hA : ∀ y, ‖a y‖ ≤ A)
    (hna : ∀ y, Ra ≤ ‖y‖ → a y = 0) {x : Fin n → ℂ} (hx : ‖x‖ ≤ Rb) :
    (∫ y, ‖Work.CR.Flat.Cauchy.bmKernel j (y - x)‖ * ‖a y‖)
      ≤ A * ∫ w, (Metric.ball (0 : Fin n → ℂ) (Ra + Rb)).indicator
          (fun w => ‖w‖ ^ (1 - 2 * (n : ℝ))) w := by
  have hs : (∫ y : Fin n → ℂ, ‖Work.CR.Flat.Cauchy.bmKernel j (y - x)‖ * ‖a y‖)
      = ∫ w : Fin n → ℂ, ‖Work.CR.Flat.Cauchy.bmKernel j w‖ * ‖a (w + x)‖ := by
    refine Eq.trans
      (b := ∫ y, (fun w : Fin n → ℂ => ‖Work.CR.Flat.Cauchy.bmKernel j w‖ * ‖a (w + x)‖) (y - x)) ?_ ?_
    · exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => by simp)
    · exact MeasureTheory.integral_sub_right_eq_self (μ := (volume : Measure (Fin n → ℂ)))
        (fun w : Fin n → ℂ => ‖Work.CR.Flat.Cauchy.bmKernel j w‖ * ‖a (w + x)‖) x
  rw [hs]
  have hpt : ∀ w : Fin n → ℂ, ‖Work.CR.Flat.Cauchy.bmKernel j w‖ * ‖a (w + x)‖
      ≤ A * (Metric.ball (0 : Fin n → ℂ) (Ra + Rb)).indicator
          (fun w => ‖w‖ ^ (1 - 2 * (n : ℝ))) w := by
    intro w
    by_cases hw : w ∈ Metric.ball (0 : Fin n → ℂ) (Ra + Rb)
    · rw [Set.indicator_of_mem hw]
      have h1 : ‖Work.CR.Flat.Cauchy.bmKernel j w‖ ≤ ‖w‖ ^ (1 - 2 * (n : ℝ)) :=
        Work.CR.Flat.Cauchy.norm_bmKernel_le j w
      have h2 : ‖a (w + x)‖ ≤ A := hA (w + x)
      have h3 : 0 ≤ ‖w‖ ^ (1 - 2 * (n : ℝ)) := Real.rpow_nonneg (norm_nonneg w) _
      calc ‖Work.CR.Flat.Cauchy.bmKernel j w‖ * ‖a (w + x)‖
          ≤ ‖w‖ ^ (1 - 2 * (n : ℝ)) * A := mul_le_mul h1 h2 (norm_nonneg _) h3
        _ = A * ‖w‖ ^ (1 - 2 * (n : ℝ)) := by ring
    · rw [Set.indicator_of_notMem hw]
      have hw' : Ra + Rb ≤ ‖w‖ := le_of_not_gt (fun h => hw (Metric.mem_ball.mpr (by simpa using h)))
      have h4 : Ra ≤ ‖w + x‖ := by
        have h5 := norm_sub_le (w + x) x
        rw [add_sub_cancel_right] at h5
        linarith
      rw [hna (w + x) h4, norm_zero, mul_zero, mul_zero]
  have hgint : Integrable (fun w : Fin n → ℂ => A * (Metric.ball (0 : Fin n → ℂ) (Ra + Rb)).indicator
      (fun w => ‖w‖ ^ (1 - 2 * (n : ℝ))) w) volume :=
    MeasureTheory.Integrable.const_mul
      ((MeasureTheory.integrable_indicator_iff measurableSet_ball).mpr
        (integrableOn_norm_rpow_ball_cn hn (Ra + Rb))) A
  have hfint : Integrable (fun w : Fin n → ℂ => ‖Work.CR.Flat.Cauchy.bmKernel j w‖ * ‖a (w + x)‖) volume :=
    MeasureTheory.Integrable.mono' hgint
      ((Work.CR.Flat.Cauchy.measurable_bmKernel j).norm.aestronglyMeasurable.mul
        ((ha.comp (continuous_add_const x)).norm.aestronglyMeasurable))
      (Filter.Eventually.of_forall fun w => by
        rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
        exact hpt w)
  exact (MeasureTheory.integral_mono hfint hgint hpt).trans_eq
    (MeasureTheory.integral_const_mul A (fun w => (Metric.ball (0 : Fin n → ℂ) (Ra + Rb)).indicator
      (fun w => ‖w‖ ^ (1 - 2 * (n : ℝ))) w))

/-! ### Integrability of the inner and outer integrals -/

/-- For fixed `x` the map `y ↦ bmKernel j (y - x) * a y` is integrable: it is a translate of
`w ↦ bmKernel j w * a (w + x)`, and `‖bmKernel j‖` is locally integrable while `a (· + x)` is
continuous with compact support. -/
private lemma integrable_inner_czPair {n : ℕ} (hn : 0 < n) {j : Fin n} {a : (Fin n → ℂ) → ℂ}
    (ha : Continuous a) (hac : HasCompactSupport a) (x : Fin n → ℂ) :
    Integrable (fun y : Fin n → ℂ => Work.CR.Flat.Cauchy.bmKernel j (y - x) * a y) volume := by
  have h1 : Integrable (fun w : Fin n → ℂ => Work.CR.Flat.Cauchy.bmKernel j w * a (w + x)) volume :=
    Work.CR.Flat.Cauchy.integrable_bmKernel_mul hn j (ha.comp (continuous_add_const x))
      (hac.comp_homeomorph (Homeomorph.addRight x))
  exact (h1.comp_sub_right x).congr (Filter.Eventually.of_forall fun y => by simp)

/-- The integrand `(z, ζ) ↦ b z * (bmKernel j (ζ - z) * a ζ)` is a.e. strongly measurable for the
product measure. -/
private lemma aeStronglyMeasurable_czPair_integrand {n : ℕ} {j : Fin n} {a b : (Fin n → ℂ) → ℂ}
    (ha : Continuous a) (hb : Continuous b) :
    AEStronglyMeasurable (fun p : (Fin n → ℂ) × (Fin n → ℂ) =>
      b p.1 * (Work.CR.Flat.Cauchy.bmKernel j (p.2 - p.1) * a p.2)) (volume.prod volume) := by
  have h1 : AEStronglyMeasurable (fun p : (Fin n → ℂ) × (Fin n → ℂ) => b p.1) (volume.prod volume) :=
    hb.aestronglyMeasurable.comp_fst
  have h2 : AEStronglyMeasurable (fun p : (Fin n → ℂ) × (Fin n → ℂ) =>
      Work.CR.Flat.Cauchy.bmKernel j (p.2 - p.1)) (volume.prod volume) :=
    ((Work.CR.Flat.Cauchy.measurable_bmKernel j).comp (measurable_snd.sub measurable_fst)).aestronglyMeasurable
  have h3 : AEStronglyMeasurable (fun p : (Fin n → ℂ) × (Fin n → ℂ) => a p.2) (volume.prod volume) :=
    ha.aestronglyMeasurable.comp_snd
  exact h1.mul (h2.mul h3)

/-- The outer integrand `x ↦ ∫ y, ‖b x * (bmKernel j (y - x) * a y)‖` is integrable: it is
supported in the compact support of `b` and bounded there by the uniform estimate
`integral_norm_bmKernel_sub_le`. -/
private lemma integrable_norm_inner_czPair {n : ℕ} (hn : 0 < n) {j : Fin n} {a b : (Fin n → ℂ) → ℂ}
    (ha : Continuous a) (hac : HasCompactSupport a) (hb : Continuous b) (hbc : HasCompactSupport b) :
    Integrable (fun x : Fin n → ℂ => ∫ y, ‖b x * (Work.CR.Flat.Cauchy.bmKernel j (y - x) * a y)‖) volume := by
  obtain ⟨A, hA0, hA⟩ := exists_norm_le_of_continuous_hasCompactSupport ha hac
  obtain ⟨Ra, hRa0, hna⟩ := exists_radius_of_hasCompactSupport hac
  obtain ⟨B, hB0, hB⟩ := exists_norm_le_of_continuous_hasCompactSupport hb hbc
  obtain ⟨Rb, hRb0, hnb⟩ := exists_radius_of_hasCompactSupport hbc
  set J : ℝ := ∫ w, (Metric.ball (0 : Fin n → ℂ) (Ra + Rb)).indicator
      (fun w => ‖w‖ ^ (1 - 2 * (n : ℝ))) w with hJdef
  have hJnn : 0 ≤ J := by
    rw [hJdef]
    exact MeasureTheory.integral_nonneg
      (Set.indicator_nonneg fun w _ => Real.rpow_nonneg (norm_nonneg w) _)
  have hmain : ∀ x : Fin n → ℂ, ‖x‖ ≤ Rb →
      (∫ y, ‖b x * (Work.CR.Flat.Cauchy.bmKernel j (y - x) * a y)‖) ≤ B * (A * J) := by
    intro x hx
    have hbound := integral_norm_bmKernel_sub_le hn j ha hA hna hx
    rw [hJdef]
    calc ∫ y, ‖b x * (Work.CR.Flat.Cauchy.bmKernel j (y - x) * a y)‖
        = ∫ y, ‖b x‖ * (‖Work.CR.Flat.Cauchy.bmKernel j (y - x)‖ * ‖a y‖) := by
          refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
          simp only [norm_mul]
      _ = ‖b x‖ * ∫ y, ‖Work.CR.Flat.Cauchy.bmKernel j (y - x)‖ * ‖a y‖ :=
          MeasureTheory.integral_const_mul _ _
      _ ≤ ‖b x‖ * (A * ∫ w, (Metric.ball (0 : Fin n → ℂ) (Ra + Rb)).indicator
            (fun w => ‖w‖ ^ (1 - 2 * (n : ℝ))) w) :=
          mul_le_mul_of_nonneg_left hbound (norm_nonneg _)
      _ ≤ B * (A * ∫ w, (Metric.ball (0 : Fin n → ℂ) (Ra + Rb)).indicator
            (fun w => ‖w‖ ^ (1 - 2 * (n : ℝ))) w) :=
          mul_le_mul_of_nonneg_right (hB x) (mul_nonneg hA0 (by rw [← hJdef]; exact hJnn))
  have hgint : Integrable (fun x : Fin n → ℂ =>
      (Metric.closedBall (0 : Fin n → ℂ) Rb).indicator (fun _ => B * (A * J)) x) volume := by
    refine (MeasureTheory.integrable_indicator_iff measurableSet_closedBall).mpr ?_
    refine MeasureTheory.integrableOn_const ?_
    exact ne_of_lt (isCompact_closedBall (0 : Fin n → ℂ) Rb).measure_lt_top
  refine MeasureTheory.Integrable.mono' hgint ?_ ?_
  · simpa only [Function.uncurry] using
      ((aeStronglyMeasurable_czPair_integrand ha hb).norm).integral_prod_right'
  · filter_upwards with x
    by_cases hx : ‖x‖ ≤ Rb
    · have hx' : x ∈ Metric.closedBall (0 : Fin n → ℂ) Rb := by
        rw [Metric.mem_closedBall, dist_zero_right]; exact hx
      rw [Set.indicator_of_mem hx',
        Real.norm_of_nonneg (MeasureTheory.integral_nonneg fun y => norm_nonneg _)]
      exact hmain x hx
    · have hx' : x ∉ Metric.closedBall (0 : Fin n → ℂ) Rb := by
        rw [Metric.mem_closedBall, dist_zero_right]; exact hx
      rw [Set.indicator_of_notMem hx']
      have hb0 : b x = 0 := hnb x (le_of_not_gt (fun h => hx h.le))
      have hz : (fun y : Fin n → ℂ => ‖b x * (Work.CR.Flat.Cauchy.bmKernel j (y - x) * a y)‖)
          = fun _ => (0 : ℝ) := by
        funext y; rw [hb0, zero_mul, norm_zero]
      rw [hz, MeasureTheory.integral_zero, norm_zero]

/-! ### The pairing identity -/

lemma czPair {n : ℕ} (hn : 0 < n) (j : Fin n)
    {a b : (Fin n → ℂ) → ℂ} (ha : Continuous a) (hac : HasCompactSupport a)
    (hb : Continuous b) (hbc : HasCompactSupport b) :
    ∫ z, b z * (∫ ζ, Work.CR.Flat.Cauchy.bmKernel j (ζ - z) * a ζ)
      = ∫ ζ, a ζ * (∫ z, Work.CR.Flat.Cauchy.bmKernel j (ζ - z) * b z) := by
  have hfasm := aeStronglyMeasurable_czPair_integrand (j := j) ha hb
  have hint : Integrable (fun p : (Fin n → ℂ) × (Fin n → ℂ) =>
      b p.1 * (Work.CR.Flat.Cauchy.bmKernel j (p.2 - p.1) * a p.2)) (volume.prod volume) := by
    rw [MeasureTheory.integrable_prod_iff hfasm]
    constructor
    · filter_upwards with x
      exact (integrable_inner_czPair hn ha hac x).const_mul (b x)
    · exact integrable_norm_inner_czPair hn ha hac hb hbc
  have hswap := MeasureTheory.integral_integral_swap
    (f := fun (z : Fin n → ℂ) (ζ : Fin n → ℂ) =>
      b z * (Work.CR.Flat.Cauchy.bmKernel j (ζ - z) * a ζ)) hint
  have hL : (∫ z, b z * (∫ ζ, Work.CR.Flat.Cauchy.bmKernel j (ζ - z) * a ζ))
      = ∫ z, ∫ ζ, b z * (Work.CR.Flat.Cauchy.bmKernel j (ζ - z) * a ζ) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    exact (MeasureTheory.integral_const_mul (b z)
      (fun ζ : Fin n → ℂ => Work.CR.Flat.Cauchy.bmKernel j (ζ - z) * a ζ)).symm
  have hR : (∫ ζ, ∫ z, b z * (Work.CR.Flat.Cauchy.bmKernel j (ζ - z) * a ζ))
      = ∫ ζ, a ζ * (∫ z, Work.CR.Flat.Cauchy.bmKernel j (ζ - z) * b z) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_)
    show (∫ z, b z * (Work.CR.Flat.Cauchy.bmKernel j (ζ - z) * a ζ))
      = a ζ * ∫ z, Work.CR.Flat.Cauchy.bmKernel j (ζ - z) * b z
    rw [← MeasureTheory.integral_const_mul (a ζ)
      (fun z : Fin n → ℂ => Work.CR.Flat.Cauchy.bmKernel j (ζ - z) * b z)]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    ring
  exact hL.trans (hswap.trans hR)

end Work.NN.Core
