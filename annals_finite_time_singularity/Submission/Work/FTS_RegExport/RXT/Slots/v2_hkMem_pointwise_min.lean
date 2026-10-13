import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS_RegExport.RXA1w.Helpers
import Submission.Work.FTS_RegExport.RXT.Slots.v2_agmonZ_noDecay
import Submission.Work.FTS_RegExport.RXT.Slots.v2_theta_sup_uniform

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The trace-free weighted `ℋ⁴ → L^∞` trade-off

For `0 < α ≤ 1` there is `C = C(α)` such that every `C⁴` function `f` on the open quadrant
`Q0 = (0,∞) × (0,π/2)` which is honestly in `ℋ⁴` satisfies, for every `a + b ≤ 2`,

  `|D_z^b D_θ^a f (z,θ)| ≤ C · min z 1 · |f|_{ℋ⁴}`     (`z > 0`, `0 < θ < π/2`).

Unlike `Work.FTS_RegExport.RXA1w.abs_mixed_le_HkNorm_C4_w_proved` this needs **no**
`BdryTraces` hypothesis: the boundary terms of the angular Hardy and of the radial Agmon
inequality are replaced by

* the weighted angular sup bound `v2_theta_sup_uniform` (a companion angle minimising the
  `θ`-slice on `[π/8,3π/8]` plus Cauchy–Schwarz), and
* the trace-free radial Agmon inequality `v2_agmonZ_noDecay` (whose decay at `∞` is automatic
  from the integrability, via `liminf`).

The constant depends on `α` only; the consumer allows that.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- `z^{3/2}/(1+z)² ≤ min z 1` for `z > 0`. -/
theorem v2_zpow_div_le_min {z : ℝ} (hz : 0 < z) :
    z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2 ≤ min z 1 := by
  have hpos : (0 : ℝ) < 1 + z := by linarith
  rcases le_or_gt z 1 with h | h
  · rw [min_eq_left h]
    have hrw : z ^ ((3 : ℝ) / 2) = z ^ ((1 : ℝ) / 2) * z := by
      rw [show (3 : ℝ) / 2 = (1 : ℝ) / 2 + 1 by norm_num, Real.rpow_add hz, Real.rpow_one]
    have hroot : z ^ ((1 : ℝ) / 2) ≤ 1 := Real.rpow_le_one hz.le h (by norm_num)
    have hsq : (1 : ℝ) ≤ (1 + z) ^ 2 := by nlinarith [sq_nonneg (1 + z), hz]
    have h4 : z ^ ((1 : ℝ) / 2) * z ≤ 1 * z := mul_le_mul_of_nonneg_right hroot hz.le
    have h5 : (1 : ℝ) * z ≤ z * (1 + z) ^ 2 := by nlinarith [hsq, hz]
    rw [div_le_iff₀ (by positivity)]
    linarith [hrw, h4, h5]
  · rw [min_eq_right h.le]
    have hroot : (1 : ℝ) ≤ z ^ ((1 : ℝ) / 2) := Real.one_le_rpow h.le (by norm_num)
    have hzr : z ^ ((1 : ℝ) / 2) ≤ z := by
      calc z ^ ((1 : ℝ) / 2) = z ^ ((1 : ℝ) / 2) * 1 := (mul_one _).symm
        _ ≤ z ^ ((1 : ℝ) / 2) * z ^ ((1 : ℝ) / 2) :=
            mul_le_mul_of_nonneg_left hroot (Real.rpow_nonneg hz.le ((1 : ℝ) / 2))
        _ = z := by
            rw [← Real.rpow_add hz, show (1 : ℝ) / 2 + 1 / 2 = 1 by norm_num, Real.rpow_one]
    have hrw : z ^ ((3 : ℝ) / 2) = z ^ ((1 : ℝ) / 2) * z := by
      rw [show (3 : ℝ) / 2 = (1 : ℝ) / 2 + 1 by norm_num, Real.rpow_add hz, Real.rpow_one]
    have hz2 : z ^ 2 ≤ (1 + z) ^ 2 := by nlinarith [hz]
    rw [div_le_one (by positivity)]
    rw [hrw]
    nlinarith [hzr, hz.le, Real.rpow_nonneg hz.le ((1 : ℝ) / 2), hz2,
      mul_le_mul_of_nonneg_right hzr hz.le]

/-- `w(z)² · z = (1+z)⁴/z³` for `z ≠ 0`. -/
theorem v2_wsq_mul_eq {z : ℝ} (hz : z ≠ 0) :
    (Work.Spaces.w z) ^ 2 * z = (1 + z) ^ 4 / z ^ 3 := by
  rw [Work.Spaces.w, div_pow]
  field_simp

/-- `w` is continuous on `(0,∞)`. -/
theorem v2_continuousOn_w : ContinuousOn Work.Spaces.w (Set.Ioi (0 : ℝ)) := by
  have h : (fun y : ℝ => (1 + y) ^ 2 / y ^ 2) = Work.Spaces.w := by
    funext y; rw [Work.Spaces.w]
  rw [← h]
  exact ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
    (continuousOn_id.pow 2) (fun y hy => pow_ne_zero 2 (ne_of_gt hy))

/-- The trace-free weighted `ℋ⁴ → L^∞` trade-off. -/
theorem v2_hkMem_pointwise_min {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : ℝ → ℝ → ℝ,
      ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0 →
      Work.Spaces.HkMem α 4 f →
      ∀ b a : ℕ, a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.mixed b a f z θ| ≤ C * min z 1 * Work.Spaces.HkNorm α 4 f := by
  obtain ⟨K, hK0, hsup⟩ := Work.FTS_RegExport.RXT.Slots.v2_theta_sup_uniform hα hα1
  refine ⟨Real.sqrt (5 * K), Real.sqrt_nonneg _, ?_⟩
  intro f h4 hmem b a hab z θ hz hθ0 hθ1
  have h5K : (0 : ℝ) ≤ 5 * K := by linarith
  have hθmem : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
  -- the radial function whose `Iz`-integral is `HkSq`
  have hHint : MeasureTheory.IntegrableOn
      (fun x : ℝ => ∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f x σ) Work.Spaces.Iz :=
    hmem.2
  have hHnonneg : ∀ x : ℝ, 0 ≤ ∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f x σ :=
    fun x => MeasureTheory.integral_nonneg (fun σ => Work.Spaces.HkIntegrand_nonneg α 4 f x σ)
  have hHsq : (∫ x in Work.Spaces.Iz,
        ∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f x σ)
      = Work.Spaces.HkSq α 4 f := rfl
  -- the two pointwise bounds from the angular sup lemma
  have hb1 : ∀ x : ℝ, 0 < x →
      (Work.Spaces.mixed b a f x θ * Work.Spaces.w x) ^ 2
        ≤ (∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f x σ) * K := by
    intro x hx
    have h := hsup f h4 hmem b a (by omega) x hx θ hθ0 hθ1
    rwa [mul_comm K] at h
  have hb2 : ∀ x : ℝ, 0 < x →
      (Work.Spaces.mixed (b + 1) a f x θ * Work.Spaces.w x) ^ 2
        ≤ (∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f x σ) * K := by
    intro x hx
    have h := hsup f h4 hmem (b + 1) a (by omega) x hx θ hθ0 hθ1
    rwa [mul_comm K] at h
  have hmul : ∀ x : ℝ, x ≠ 0 →
      x * (Work.Spaces.mixed (b + 1) a f x θ / x) = Work.Spaces.mixed (b + 1) a f x θ := by
    intro x hx
    field_simp
  -- continuity of the two slices
  have hcont1 : ContinuousOn (fun x : ℝ => Work.Spaces.mixed b a f x θ) (Set.Ioi (0 : ℝ)) :=
    (Work.FTS.StrongEps.EComparison.contDiffOn_slice_z hθmem
      (Work.FTS_RegExport.RXA1w.contDiffOn_uncurry_mixed_Q0 h4 b a 0 (by omega))).continuousOn
  have hcont2 : ContinuousOn (fun x : ℝ => Work.Spaces.mixed (b + 1) a f x θ)
      (Set.Ioi (0 : ℝ)) :=
    (Work.FTS.StrongEps.EComparison.contDiffOn_slice_z hθmem
      (Work.FTS_RegExport.RXA1w.contDiffOn_uncurry_mixed_Q0 h4 (b + 1) a 0 (by omega))).continuousOn
  -- integrability of the two `θ`-slices
  have hint1 : MeasureTheory.IntegrableOn
      (fun x : ℝ => (Work.Spaces.mixed b a f x θ * Work.Spaces.w x) ^ 2) Work.Spaces.Iz := by
    refine MeasureTheory.Integrable.mono'
      (MeasureTheory.Integrable.mul_const hHint K) ?_ ?_
    · rw [Work.Spaces.Iz, ← MeasureTheory.restrict_Ioi_eq_restrict_Ici]
      exact ((hcont1.mul v2_continuousOn_w).pow 2).aestronglyMeasurable measurableSet_Ioi
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici ?_
      intro x hx
      have hx' : (0 : ℝ) ≤ x := hx
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      rcases eq_or_lt_of_le hx' with h0 | hpos
      · subst h0
        have hw0 : Work.Spaces.w 0 = 0 := by simp [Work.Spaces.w]
        rw [hw0, mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
        exact mul_nonneg (hHnonneg 0) hK0
      · exact hb1 x hpos
  have hint2 : MeasureTheory.IntegrableOn
      (fun x : ℝ => (x * (Work.Spaces.mixed (b + 1) a f x θ / x) * Work.Spaces.w x) ^ 2)
      Work.Spaces.Iz := by
    refine MeasureTheory.Integrable.mono'
      (MeasureTheory.Integrable.mul_const hHint K) ?_ ?_
    · rw [Work.Spaces.Iz, ← MeasureTheory.restrict_Ioi_eq_restrict_Ici]
      refine (((continuousOn_id.mul ?_).mul v2_continuousOn_w).pow 2).aestronglyMeasurable
        measurableSet_Ioi
      exact ContinuousOn.div hcont2 continuousOn_id (fun x hx => ne_of_gt hx)
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici ?_
      intro x hx
      have hx' : (0 : ℝ) ≤ x := hx
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      rcases eq_or_lt_of_le hx' with h0 | hpos
      · subst h0
        have hw0 : Work.Spaces.w 0 = 0 := by simp [Work.Spaces.w]
        rw [hw0, mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
        exact mul_nonneg (hHnonneg 0) hK0
      · have hxne : x ≠ 0 := ne_of_gt hpos
        rw [hmul x hxne]
        exact hb2 x hpos
  -- the derivative identity for the Agmon inequality
  have hderiv : ∀ x ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun s : ℝ => Work.Spaces.mixed b a f s θ)
        (Work.Spaces.mixed (b + 1) a f x θ / x) x := by
    intro x hx
    have hz1 : 0 < x := hx
    have hcd : ContDiffOn ℝ 1 (fun s : ℝ => Work.Spaces.mixed b a f s θ) (Set.Ioi 0) :=
      Work.FTS.StrongEps.EComparison.contDiffOn_slice_z hθmem
        (Work.FTS_RegExport.RXA1w.contDiffOn_uncurry_mixed_Q0 h4 b a 1 (by omega))
    have hdiff : DifferentiableAt ℝ (fun s : ℝ => Work.Spaces.mixed b a f s θ) x :=
      (hcd.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioi.mem_nhds hz1)
    have hder : deriv (fun s : ℝ => Work.Spaces.mixed b a f s θ) x
        = Work.Spaces.mixed (b + 1) a f x θ / x := by
      have h1 : Work.Spaces.mixed (b + 1) a f x θ
          = x * deriv (fun s : ℝ => Work.Spaces.mixed b a f s θ) x := rfl
      rw [h1, mul_div_cancel_left₀ _ (ne_of_gt hz1)]
    have h := hdiff.hasDerivAt
    rw [hder] at h
    exact h
  -- the trace-free Agmon inequality
  have hag := Work.FTS_RegExport.RXT.Slots.v2_agmonZ_noDecay (v := fun s : ℝ => Work.Spaces.mixed b a f s θ)
    (v' := fun s : ℝ => Work.Spaces.mixed (b + 1) a f s θ / s) hz hderiv hint1 hint2
  -- the two tails, bounded by `K ∫ H = K HkSq`
  have ht1 : (∫ x in Set.Ioi z, (Work.Spaces.mixed b a f x θ * Work.Spaces.w x) ^ 2)
      ≤ K * Work.Spaces.HkSq α 4 f := by
    have hzsub : Set.Ioi z ⊆ Work.Spaces.Iz := fun x hx => le_of_lt (lt_trans hz hx)
    have hInt1 : MeasureTheory.IntegrableOn
        (fun x : ℝ => (Work.Spaces.mixed b a f x θ * Work.Spaces.w x) ^ 2) (Set.Ioi z) :=
      hint1.mono_set hzsub
    have hHsub : MeasureTheory.IntegrableOn
        (fun x : ℝ => ∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f x σ) (Set.Ioi z) :=
      MeasureTheory.Integrable.mono_measure hHint
        (MeasureTheory.Measure.restrict_mono hzsub le_rfl)
    have hInt2 : MeasureTheory.IntegrableOn
        (fun x : ℝ => (∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f x σ) * K)
        (Set.Ioi z) := MeasureTheory.Integrable.mul_const hHsub K
    have hmono := MeasureTheory.integral_mono_ae hInt1 hInt2
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi
        (fun x hx => hb1 x (lt_trans hz hx)))
    have hKint : (∫ x in Set.Ioi z,
          (∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f x σ) * K)
        = K * (∫ x in Set.Ioi z,
            ∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f x σ) := by
      rw [MeasureTheory.integral_mul_const]
      ring
    have hle : (∫ x in Set.Ioi z,
          ∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f x σ)
        ≤ ∫ x in Work.Spaces.Iz,
            ∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f x σ :=
      MeasureTheory.setIntegral_mono_set hHint
        (Filter.Eventually.of_forall hHnonneg)
        (Filter.Eventually.of_forall (fun x hx => hzsub hx))
    calc (∫ x in Set.Ioi z, (Work.Spaces.mixed b a f x θ * Work.Spaces.w x) ^ 2)
        ≤ ∫ x in Set.Ioi z,
            (∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f x σ) * K := hmono
      _ = K * (∫ x in Set.Ioi z,
            ∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f x σ) := hKint
      _ ≤ K * (∫ x in Work.Spaces.Iz,
            ∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f x σ) :=
          mul_le_mul_of_nonneg_left hle hK0
      _ = K * Work.Spaces.HkSq α 4 f := by rw [hHsq]
  have ht2 : (∫ x in Set.Ioi z,
        (x * (Work.Spaces.mixed (b + 1) a f x θ / x) * Work.Spaces.w x) ^ 2)
      ≤ K * Work.Spaces.HkSq α 4 f := by
    have hzsub : Set.Ioi z ⊆ Work.Spaces.Iz := fun x hx => le_of_lt (lt_trans hz hx)
    have hInt1 : MeasureTheory.IntegrableOn
        (fun x : ℝ => (x * (Work.Spaces.mixed (b + 1) a f x θ / x) * Work.Spaces.w x) ^ 2)
        (Set.Ioi z) := hint2.mono_set hzsub
    have hHsub : MeasureTheory.IntegrableOn
        (fun x : ℝ => ∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f x σ) (Set.Ioi z) :=
      MeasureTheory.Integrable.mono_measure hHint
        (MeasureTheory.Measure.restrict_mono hzsub le_rfl)
    have hInt2 : MeasureTheory.IntegrableOn
        (fun x : ℝ => (∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f x σ) * K)
        (Set.Ioi z) := MeasureTheory.Integrable.mul_const hHsub K
    have hmono := MeasureTheory.integral_mono_ae hInt1 hInt2
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun x hx => by
        show (x * (Work.Spaces.mixed (b + 1) a f x θ / x) * Work.Spaces.w x) ^ 2
          ≤ (∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f x σ) * K
        rw [hmul x (ne_of_gt (lt_trans hz hx))]
        exact hb2 x (lt_trans hz hx)))
    have hKint : (∫ x in Set.Ioi z,
          (∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f x σ) * K)
        = K * (∫ x in Set.Ioi z,
            ∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f x σ) := by
      rw [MeasureTheory.integral_mul_const]
      ring
    have hle : (∫ x in Set.Ioi z,
          ∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f x σ)
        ≤ ∫ x in Work.Spaces.Iz,
            ∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f x σ :=
      MeasureTheory.setIntegral_mono_set hHint
        (Filter.Eventually.of_forall hHnonneg)
        (Filter.Eventually.of_forall (fun x hx => hzsub hx))
    calc (∫ x in Set.Ioi z,
          (x * (Work.Spaces.mixed (b + 1) a f x θ / x) * Work.Spaces.w x) ^ 2)
        ≤ ∫ x in Set.Ioi z,
            (∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f x σ) * K := hmono
      _ = K * (∫ x in Set.Ioi z,
            ∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f x σ) := hKint
      _ ≤ K * (∫ x in Work.Spaces.Iz,
            ∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f x σ) :=
          mul_le_mul_of_nonneg_left hle hK0
      _ = K * Work.Spaces.HkSq α 4 f := by rw [hHsq]
  -- the Agmon conclusion
  have hbound : (Work.Spaces.mixed b a f z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * z
      ≤ 5 * K * Work.Spaces.HkSq α 4 f := by
    have h4t : 4 * (∫ x in Set.Ioi z, (Work.Spaces.mixed b a f x θ * Work.Spaces.w x) ^ 2)
        ≤ 4 * (K * Work.Spaces.HkSq α 4 f) :=
      mul_le_mul_of_nonneg_left ht1 (by norm_num)
    linarith [hag, h4t, ht2]
  -- convert to the pointwise bound
  have hstep : (Work.Spaces.mixed b a f z θ) ^ 2 * ((Work.Spaces.w z) ^ 2 * z)
      ≤ 5 * K * Work.Spaces.HkSq α 4 f := by
    rw [← mul_assoc]
    exact hbound
  rw [v2_wsq_mul_eq (ne_of_gt hz)] at hstep
  have hstep2 : (Work.Spaces.mixed b a f z θ) ^ 2
      ≤ 5 * K * Work.Spaces.HkSq α 4 f * (z ^ 3 / (1 + z) ^ 4) := by
    have h2 := mul_le_mul_of_nonneg_right hstep
      (le_of_lt (div_pos (pow_pos hz 3) (pow_pos (by linarith : (0 : ℝ) < 1 + z) 4)))
    have hone : ((1 + z) ^ 4 / z ^ 3) * (z ^ 3 / (1 + z) ^ 4) = 1 := by
      rw [div_mul_div_comm, mul_comm (z ^ 3) ((1 + z) ^ 4)]
      exact div_self (by positivity)
    have heq : (Work.Spaces.mixed b a f z θ) ^ 2 * ((1 + z) ^ 4 / z ^ 3)
          * (z ^ 3 / (1 + z) ^ 4) = (Work.Spaces.mixed b a f z θ) ^ 2 := by
      rw [mul_assoc, hone, mul_one]
    rwa [heq] at h2
  have hA2 : (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) ^ 2 = z ^ 3 / (1 + z) ^ 4 := by
    rw [div_pow]
    congr 1
    · rw [← Real.rpow_natCast (z ^ ((3 : ℝ) / 2)) 2, ← Real.rpow_mul hz.le]
      norm_num
    · ring
  have hAnonneg : (0 : ℝ) ≤ z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2 :=
    div_nonneg (Real.rpow_nonneg hz.le _) (by positivity)
  have hHknn : (0 : ℝ) ≤ Work.Spaces.HkSq α 4 f :=
    MeasureTheory.integral_nonneg hHnonneg
  have hNormsq : (Work.Spaces.HkNorm α 4 f) ^ 2 = Work.Spaces.HkSq α 4 f :=
    Real.sq_sqrt hHknn
  have hR : (Real.sqrt (5 * K) * Work.Spaces.HkNorm α 4 f
        * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2)) ^ 2
      = 5 * K * Work.Spaces.HkSq α 4 f * (z ^ 3 / (1 + z) ^ 4) := by
    rw [mul_pow, mul_pow, Real.sq_sqrt h5K, hNormsq, hA2]
  have hsq : (Work.Spaces.mixed b a f z θ) ^ 2
      ≤ (Real.sqrt (5 * K) * Work.Spaces.HkNorm α 4 f
          * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2)) ^ 2 := by
    rw [hR]
    exact hstep2
  have hprodnonneg : (0 : ℝ) ≤ Real.sqrt (5 * K) * Work.Spaces.HkNorm α 4 f
      * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Work.Spaces.HkNorm_nonneg α 4 f)) hAnonneg
  have hfinal : |Work.Spaces.mixed b a f z θ|
      ≤ Real.sqrt (5 * K) * Work.Spaces.HkNorm α 4 f
        * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) := by
    have h := Real.sqrt_le_sqrt hsq
    rw [Real.sqrt_sq_eq_abs, Real.sqrt_sq hprodnonneg] at h
    exact h
  have hmono : Real.sqrt (5 * K) * Work.Spaces.HkNorm α 4 f
        * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2)
      ≤ Real.sqrt (5 * K) * Work.Spaces.HkNorm α 4 f * min z 1 :=
    mul_le_mul_of_nonneg_left (v2_zpow_div_le_min hz)
      (mul_nonneg (Real.sqrt_nonneg _) (Work.Spaces.HkNorm_nonneg α 4 f))
  have hcomm : Real.sqrt (5 * K) * Work.Spaces.HkNorm α 4 f * min z 1
      = Real.sqrt (5 * K) * min z 1 * Work.Spaces.HkNorm α 4 f := by ring
  rw [hcomm] at hmono
  linarith [hfinal, hmono]

end Work.FTS_RegExport.RXT
