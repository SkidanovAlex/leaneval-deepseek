import Mathlib
import Submission.Work.Drive.needleAngVelAssembly

/-!
# `DoubleAverageData` from joint measurability and a uniform bound

`Work.Drive.DoubleAverageData b f g` collects the seven interval-integrability facts that the
angular-velocity assembly `Work.Drive.needle_num_pos_of_diag_osc` needs in order to compare the two
iterated weighted averages of `f` and of `g` with the iterated weighted average of `f * g`.

In the intended instantiation `b` is the (continuous) blur bump and `f`, `g` are the two coordinates
of a family of curves (or of their velocities) over the window `[-1,1]²`, jointly measurable and
uniformly bounded on the *square* `[-1,1] × [-1,1]` (the bounds are supplied by the compactness of
the curve family).  Everything in the structure is then automatic:

* each slice `v ↦ b v * f u v` is a measurable function, bounded by `Cf` on `[-1,1]`, hence
  interval-integrable;
* the parametrized integrals `u ↦ ∫ v, b v * f u v` are *measurable* (Fubini for measurable
  integrands, `MeasureTheory.StronglyMeasurable.integral_prod_right`), and bounded by `2 * Cf`
  (`intervalIntegral.norm_integral_le_of_norm_le_const`), so multiplying by the continuous `b`
  keeps them interval-integrable;
* the same for the product of the two parametrized integrals and for the parametrized integral of
  the product `f * g`.

No positivity, normalization or integrability of `b` is required beyond `|b u| ≤ 1`; the only
hypotheses on `f` and `g` are joint measurability and the two uniform bounds on the square.
-/

noncomputable section
namespace Work.Drive.Generic

open MeasureTheory

/-! ## Elementary helper lemmas -/

/-- The slice `v ↦ F u v` of a jointly measurable two-variable function is measurable. -/
lemma measurable_const_left {F : ℝ → ℝ → ℝ}
    (hF : Measurable fun p : ℝ × ℝ => F p.1 p.2) (u : ℝ) :
    Measurable fun v : ℝ => F u v :=
  hF.comp (measurable_const.prodMk measurable_id)

/-- The parametrized integral `u ↦ ∫ v in -1..1, H u v` of a jointly measurable function is
measurable.  (Fubini for a finite-measure set: it is the integral against `volume.restrict` of the
corresponding interval, and `MeasureTheory.StronglyMeasurable.integral_prod_right` applies.) -/
lemma measurable_intervalIntegral {H : ℝ → ℝ → ℝ}
    (hH : Measurable fun p : ℝ × ℝ => H p.1 p.2) :
    Measurable fun u : ℝ => ∫ v in (-1:ℝ)..1, H u v := by
  have hs : StronglyMeasurable fun u : ℝ => ∫ v, H u v ∂(volume.restrict (Set.uIoc (-1:ℝ) 1)) :=
    hH.stronglyMeasurable.integral_prod_right
  have heq : (fun u : ℝ => ∫ v, H u v ∂(volume.restrict (Set.uIoc (-1:ℝ) 1)))
      = (fun u : ℝ => ∫ v in (-1:ℝ)..1, H u v) := by
    funext u
    rw [intervalIntegral.integral_of_le (by norm_num : (-1:ℝ) ≤ 1),
      Set.uIoc_of_le (by norm_num : (-1:ℝ) ≤ 1)]
  rw [← heq]
  exact hs.measurable

/-- The parametrized interval integral of `b v * F u v` is bounded by `2 * C` when `|b| ≤ 1` and
`|F| ≤ C` on the square `[-1,1] × [-1,1]`. -/
lemma abs_intervalIntegral_le {b : ℝ → ℝ} {F : ℝ → ℝ → ℝ} {C : ℝ}
    (hb_le : ∀ u : ℝ, |b u| ≤ 1)
    (hFC : ∀ u : ℝ, ∀ v ∈ Set.Icc (-1 : ℝ) 1, |F u v| ≤ C) (u : ℝ) :
    |∫ v in (-1:ℝ)..1, b v * F u v| ≤ C * 2 := by
  have h : ‖∫ v in (-1:ℝ)..1, b v * F u v‖ ≤ C * |(1:ℝ) - (-1)| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (-1:ℝ)) (b := 1) (C := C) (f := fun v : ℝ => b v * F u v) fun v hv => ?_
    rw [Set.uIoc_of_le (by norm_num : (-1:ℝ) ≤ 1)] at hv
    rw [Real.norm_eq_abs, abs_mul]
    have h' := mul_le_mul (hb_le v) (hFC u v (Set.Ioc_subset_Icc_self hv)) (abs_nonneg _)
      (by norm_num : (0:ℝ) ≤ 1)
    simpa using h'
  rwa [Real.norm_eq_abs, show |(1:ℝ) - (-1)| = 2 by norm_num] at h

/-- A measurable function `Φ`, bounded by `K` on `[-1,1]`, is interval-integrable after
multiplication by the continuous function `b` with `|b| ≤ 1`. -/
lemma integrable_of_bounded_mul {b Φ : ℝ → ℝ} {K : ℝ}
    (hb : Continuous b) (hb_le : ∀ u : ℝ, |b u| ≤ 1)
    (hΦ : Measurable Φ) (hΦK : ∀ u ∈ Set.Icc (-1 : ℝ) 1, |Φ u| ≤ K) :
    IntervalIntegrable (fun u : ℝ => b u * Φ u) volume (-1) 1 := by
  refine IntervalIntegrable.mono_fun' (g := fun _ : ℝ => K) intervalIntegrable_const
    (hb.measurable.mul hΦ).aestronglyMeasurable ?_
  refine (ae_restrict_mem measurableSet_uIoc).mono fun u hu => ?_
  rw [Set.uIoc_of_le (by norm_num : (-1:ℝ) ≤ 1)] at hu
  simp only []
  rw [Real.norm_eq_abs, abs_mul]
  have h' := mul_le_mul (hb_le u) (hΦK u (Set.Ioc_subset_Icc_self hu)) (abs_nonneg _)
    (by norm_num : (0:ℝ) ≤ 1)
  simpa using h'

/-! ## The theorem -/

theorem doubleAverageData_of_jointly_measurable {b : ℝ → ℝ} (hb : Continuous b)
    (hb_le : ∀ u : ℝ, |b u| ≤ 1)
    {f g : ℝ → ℝ → ℝ}
    (hfm : Measurable fun p : ℝ × ℝ => f p.1 p.2)
    (hgm : Measurable fun p : ℝ × ℝ => g p.1 p.2)
    {Cf Cg : ℝ}
    (hf : ∀ u : ℝ, ∀ v ∈ Set.Icc (-1 : ℝ) 1, |f u v| ≤ Cf)
    (hg : ∀ u : ℝ, ∀ v ∈ Set.Icc (-1 : ℝ) 1, |g u v| ≤ Cg) :
    Work.Drive.DoubleAverageData b f g := by
  have hCf0 : 0 ≤ Cf := le_trans (abs_nonneg _) (hf 0 0 (by norm_num))
  have hCg0 : 0 ≤ Cg := le_trans (abs_nonneg _) (hg 0 0 (by norm_num))
  -- the joint measurability of the three integrands involving `b`
  have hfm_b : Measurable fun p : ℝ × ℝ => b p.2 * f p.1 p.2 :=
    (hb.measurable.comp measurable_snd).mul hfm
  have hgm_b : Measurable fun p : ℝ × ℝ => b p.2 * g p.1 p.2 :=
    (hb.measurable.comp measurable_snd).mul hgm
  have hfgm : Measurable fun p : ℝ × ℝ => f p.1 p.2 * g p.1 p.2 := hfm.mul hgm
  have hfgm_b : Measurable fun p : ℝ × ℝ => b p.2 * (f p.1 p.2 * g p.1 p.2) :=
    (hb.measurable.comp measurable_snd).mul hfgm
  -- the uniform bound of the product `f * g` on the square
  have hfgC : ∀ u : ℝ, ∀ v ∈ Set.Icc (-1 : ℝ) 1, |f u v * g u v| ≤ Cf * Cg := by
    intro u v hv
    rw [abs_mul]
    exact mul_le_mul (hf u v hv) (hg u v hv) (abs_nonneg _) hCf0
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the slice `v ↦ b v * f u v`
    intro u
    exact integrable_of_bounded_mul hb hb_le (measurable_const_left hfm u) (fun v hv => hf u v hv)
  · -- the slice `v ↦ b v * g u v`
    intro u
    exact integrable_of_bounded_mul hb hb_le (measurable_const_left hgm u) (fun v hv => hg u v hv)
  · -- the slice `v ↦ b v * (f u v * g u v)`
    intro u
    exact integrable_of_bounded_mul hb hb_le
      ((measurable_const_left hfm u).mul (measurable_const_left hgm u))
      (fun v hv => hfgC u v hv)
  · -- `u ↦ b u * ∫ v, b v * f u v`
    exact integrable_of_bounded_mul hb hb_le (measurable_intervalIntegral hfm_b)
      (fun _ _ => abs_intervalIntegral_le hb_le hf _)
  · -- `u ↦ b u * ∫ v, b v * g u v`
    exact integrable_of_bounded_mul hb hb_le (measurable_intervalIntegral hgm_b)
      (fun _ _ => abs_intervalIntegral_le hb_le hg _)
  · -- `u ↦ b u * ((∫ v, b v * f u v) * (∫ v, b v * g u v))`
    refine integrable_of_bounded_mul (K := (Cf * 2) * (Cg * 2)) hb hb_le
      ((measurable_intervalIntegral hfm_b).mul (measurable_intervalIntegral hgm_b)) ?_
    intro u _
    rw [abs_mul]
    exact mul_le_mul (abs_intervalIntegral_le hb_le hf u) (abs_intervalIntegral_le hb_le hg u)
      (abs_nonneg _) (by linarith)
  · -- `u ↦ b u * ∫ v, b v * (f u v * g u v)`
    exact integrable_of_bounded_mul hb hb_le (measurable_intervalIntegral hfgm_b)
      (fun _ _ => abs_intervalIntegral_le hb_le hfgC _)

end Work.Drive.Generic
