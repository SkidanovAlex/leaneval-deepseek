import Mathlib
import Submission.Work.CR.Flat.Cauchy
import Submission.Work.CR.Flat.Cauchy.integral_norm_rpow_ball
import Submission.Work.CR.Flat.Cauchy.integrableOn_norm_rpow_ball
import Submission.Work.CR.Flat.Cauchy.norm_cauchyTransform_sub_le
import Submission.Work.CR.Flat.Cauchy.norm_beurlingTransform_le

namespace Work.CR.Flat.Cauchy

open scoped NNReal ENNReal
open MeasureTheory Set

set_option maxHeartbeats 1000000

namespace CZaux


/-- The Beurling kernel `w ↦ w⁻¹ ^ 2` has mean zero on any annulus
`{a ≤ ‖w‖ < b}` centred at the origin: the rotation `w ↦ i·w` preserves the
annulus and Lebesgue measure, while `(i·w)⁻¹^2 = -(w⁻¹^2)`. -/
lemma integral_inv_sq_annulus (a b : ℝ) :
    ∫ w in {w : ℂ | a ≤ ‖w‖ ∧ ‖w‖ < b}, (w⁻¹) ^ 2 = 0 := by
  let θ : Circle := ⟨Complex.I, by simp [Submonoid.unitSphere]⟩
  set S : Set ℂ := {w : ℂ | a ≤ ‖w‖ ∧ ‖w‖ < b} with hS
  have hrot : ∀ w : ℂ, w ∈ S ↔ (rotation θ) w ∈ S := by
    intro w
    simp only [S, Set.mem_ofPred_eq, rotation_apply, norm_mul, Circle.norm_coe, one_mul]
  have hmp : MeasurePreserving (fun w : ℂ => (rotation θ) w) volume volume :=
    (LinearIsometryEquiv.measurePreserving (rotation θ))
  have hemb : MeasurableEmbedding (fun w : ℂ => (rotation θ) w) :=
    (rotation θ).toHomeomorph.measurableEmbedding
  have hsub := hmp.setIntegral_preimage_emb hemb (fun w : ℂ => (w⁻¹) ^ 2) S
  rw [show (fun w : ℂ => (rotation θ) w) ⁻¹' S = S from by ext w; exact (hrot w).symm] at hsub
  have hsimp : ∀ x : ℂ, (((rotation θ) x)⁻¹) ^ 2 = ((θ : ℂ)⁻¹) ^ 2 * (x⁻¹) ^ 2 := by
    intro x; rw [rotation_apply, mul_inv]; ring_nf
  simp_rw [hsimp] at hsub
  rw [integral_const_mul] at hsub
  have hθ : ((θ : ℂ)⁻¹) ^ 2 = -1 := by
    show ((Complex.I)⁻¹) ^ 2 = -1
    rw [Complex.inv_I]; ring_nf; rw [sq, Complex.I_mul_I]
  rw [hθ] at hsub
  have h2 : (-2 : ℂ) * (∫ y in S, (y⁻¹) ^ 2) = 0 := by linear_combination hsub
  exact (mul_eq_zero.mp h2).resolve_left (by norm_num)

/-- The radial integral over an annulus: for `0 < a ≤ b` and `s ≠ -2`,
`∫_{a ≤ ‖w‖ < b} ‖w‖^s = 2π (b^{s+2} - a^{s+2})/(s+2)`.  Unlike the disc case this
is valid also for `s ≤ -2`, which is what the far-field Calderón–Zygmund estimate
needs. -/
theorem integral_norm_rpow_annulus {a b s : ℝ} (ha : 0 < a) (hab : a ≤ b) (hs : s ≠ -2) :
    ∫ w in {w : ℂ | a ≤ ‖w‖ ∧ ‖w‖ < b}, ‖w‖ ^ s
      = 2 * Real.pi * (b ^ (s + 2) - a ^ (s + 2)) / (s + 2) := by
  have hmeas : MeasurableSet {w : ℂ | a ≤ ‖w‖ ∧ ‖w‖ < b} :=
    (isClosed_le continuous_const continuous_norm).measurableSet.inter
      (isOpen_lt continuous_norm continuous_const).measurableSet
  set g : ℝ → ℝ := fun y => if a ≤ y ∧ y < b then y ^ s else 0 with hg
  have step1 : ∫ w in {w : ℂ | a ≤ ‖w‖ ∧ ‖w‖ < b}, ‖w‖ ^ s = ∫ w : ℂ, g ‖w‖ := by
    rw [← integral_indicator hmeas]
    apply integral_congr_ae
    filter_upwards with w
    by_cases hw : w ∈ {w : ℂ | a ≤ ‖w‖ ∧ ‖w‖ < b}
    · rw [Set.indicator_of_mem hw]; simp only [hg]
      rw [if_pos (by simpa only [Set.mem_ofPred_eq] using hw)]
    · rw [Set.indicator_of_notMem hw]; simp only [hg]
      rw [if_neg (by simpa only [Set.mem_ofPred_eq] using hw)]
  rw [step1, MeasureTheory.integral_fun_norm_addHaar]
  rw [Complex.finrank_real_complex]
  have hreal : (volume : Measure ℂ).real (Metric.ball (0 : ℂ) 1) = Real.pi := by
    simp [MeasureTheory.Measure.real, Complex.volume_ball]
  rw [hreal]
  have h1 : ∫ y in Ioi (0:ℝ), y * g y = (b ^ (s + 2) - a ^ (s + 2)) / (s + 2) := by
    have hane : ∀ᵐ y ∂(volume : Measure ℝ), y ∈ Ioi (0:ℝ) →
        y * g y = (Ioo a b).indicator (fun y => y ^ (s + 1)) y := by
      have hne : ∀ᵐ y ∂(volume : Measure ℝ), y ≠ a := by
        rw [MeasureTheory.ae_iff]; simp
      filter_upwards [hne] with y hya hyIoi
      have hypos : 0 < y := hyIoi
      simp only [hg]
      by_cases hlt : y < b
      · by_cases hle : a ≤ y
        · rw [if_pos ⟨hle, hlt⟩,
            Set.indicator_of_mem (show y ∈ Ioo a b from ⟨lt_of_le_of_ne hle (Ne.symm hya), hlt⟩)]
          rw [show s + 1 = 1 + s from by ring, Real.rpow_add hypos, Real.rpow_one]
        · rw [if_neg (fun h => hle h.1), Set.indicator_of_notMem (fun h => hle h.1.le)]
          ring
      · rw [if_neg (fun h => hlt h.2), Set.indicator_of_notMem (fun h => hlt h.2)]
        ring
    rw [setIntegral_congr_ae measurableSet_Ioi hane, setIntegral_indicator measurableSet_Ioo]
    rw [show Ioi (0:ℝ) ∩ Ioo a b = Ioo a b from by
      ext y; simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ioo]
      exact ⟨fun h => h.2, fun h => ⟨ha.trans h.1, h⟩⟩]
    rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo]
    rw [← intervalIntegral.integral_of_le hab]
    rw [integral_rpow (Or.inr ⟨by intro h; exact hs (by linarith),
      by rw [Set.uIcc_of_le hab]; intro h; exact absurd h.1 (not_le.mpr ha)⟩)]
    rw [show s + 1 + 1 = s + 2 from by ring]
  have h2 : ∫ y in Ioi (0:ℝ), y ^ (2 - 1) • g y = ∫ y in Ioi (0:ℝ), y * g y := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y hy
    show y ^ ((2:ℕ) - 1) • g y = y * g y
    rw [show (2:ℕ) - 1 = 1 from by norm_num, pow_one, smul_eq_mul]
  rw [h2, h1]; simp only [smul_eq_mul]; ring

/-- Translation of a set integral: `∫_{w ∈ A} F (w + c) = ∫_{u ∈ c + A} F u`. -/
lemma setIntegral_translate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : ℂ) (F : ℂ → E) (A : Set ℂ) :
    ∫ w in A, F (w + c) = ∫ u in (fun x : ℂ => x + c) '' A, F u := by
  have hmp : MeasurePreserving (fun x : ℂ => x + c) volume volume :=
    MeasureTheory.measurePreserving_add_right volume c
  have hemb : MeasurableEmbedding (fun x : ℂ => x + c) :=
    (Homeomorph.addRight c).measurableEmbedding
  have h := hmp.setIntegral_preimage_emb hemb F ((fun x : ℂ => x + c) '' A)
  rw [show (fun x : ℂ => x + c) ⁻¹' ((fun x : ℂ => x + c) '' A) = A from by
    ext x; simp only [Set.mem_preimage, Set.mem_image]
    constructor
    · rintro ⟨a, ha, hax⟩; rwa [add_right_cancel hax] at ha
    · intro hx; exact ⟨x, hx, rfl⟩] at h
  exact h

/-- The Beurling integrand `w ↦ (f (z+w) - f z)/w^2` is absolutely integrable on a
disc, for `f` Hölder of positive order: it is dominated by `C ‖w‖^{α-2}` and
`α - 2 > -2 = -finrank ℝ ℂ`. -/
lemma integrableOn_beurlingIntegrand {ρ α C : ℝ} (hα : 0 < α) (hC : 0 ≤ C) {f : ℂ → ℂ}
    (hf : ∀ x y : ℂ, ‖f x - f y‖ ≤ C * ‖x - y‖ ^ α) (z : ℂ) :
    MeasureTheory.IntegrableOn (fun w : ℂ => (f (z + w) - f z) / w ^ 2) (Metric.ball 0 ρ) := by
  have hcont : Continuous f := continuous_of_holder hα hC hf
  have hmeas : AEStronglyMeasurable (fun w : ℂ => (f (z + w) - f z) / w ^ 2)
      (volume.restrict (Metric.ball 0 ρ)) := by
    have h1 : Continuous fun w : ℂ => f (z + w) - f z :=
      (hcont.comp (continuous_const.add continuous_id)).sub continuous_const
    exact ((h1.measurable.div (measurable_id.pow_const 2))).aestronglyMeasurable
  have hpt : ∀ w : ℂ, ‖(f (z + w) - f z) / w ^ 2‖ ≤ C * ‖w‖ ^ (α - 2) := by
    intro w
    by_cases hw : w = 0
    · subst hw
      simp only [add_zero, sub_self, norm_zero, zero_div]
      by_cases h : α - 2 = 0
      · rw [h, Real.rpow_zero]; simpa using hC
      · rw [Real.zero_rpow h]; simp
    · rw [norm_div, norm_pow]
      have hfw : ‖f (z + w) - f z‖ ≤ C * ‖w‖ ^ α := by
        have h := hf (z + w) z
        rwa [add_sub_cancel_left] at h
      have hw' : 0 < ‖w‖ := norm_pos_iff.mpr hw
      have hp : (‖w‖ : ℝ) ^ 2 = ‖w‖ ^ (2:ℝ) := (Real.rpow_natCast ‖w‖ 2).symm
      calc ‖f (z + w) - f z‖ / ‖w‖ ^ 2 ≤ C * ‖w‖ ^ α / ‖w‖ ^ 2 :=
            div_le_div_of_nonneg_right hfw (by positivity)
        _ = C * ‖w‖ ^ (α - 2) := by rw [hp, mul_div_assoc, ← Real.rpow_sub hw' α 2]
  have hmaj : MeasureTheory.IntegrableOn (fun w : ℂ => C * ‖w‖ ^ (α - 2)) (Metric.ball 0 ρ) :=
    (integrableOn_norm_rpow_ball (ρ := ρ) (s := α - 2) (by linarith)).const_mul C
  exact hmaj.mono' hmeas (Filter.Eventually.of_forall hpt)

/-- Bound for the norm of a set integral via a pointwise majorant. -/
lemma norm_setIntegral_le_of_norm_le {s : Set ℂ} (hs : MeasurableSet s) {F : ℂ → ℂ} {g : ℂ → ℝ}
    (hg : IntegrableOn g s volume) (h : ∀ x ∈ s, ‖F x‖ ≤ g x) :
    ‖∫ x in s, F x‖ ≤ ∫ x in s, g x := by
  rw [← integral_indicator hs (f := F), ← integral_indicator hs (f := g)]
  refine norm_integral_le_of_norm_le (hg.integrable_indicator hs)
    (Filter.Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ s
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]; exact h x hx
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]; simp

/-- Inner-region estimate: if `‖N w‖ ≤ 2 C ‖w‖^α` then the integral of `N w / w²`
over `(‖w‖ < 2δ)` is `O(δ^α)`. -/
lemma inner_bound {ρ α C δ : ℝ} (hα : 0 < α) (hα1 : α < 1) (hC : 0 ≤ C) (hδ : 0 < δ)
    {N : ℂ → ℂ} (hN : ∀ w, ‖N w‖ ≤ 2 * C * ‖w‖ ^ α) :
    ‖∫ w in Metric.ball (0:ℂ) ρ ∩ Metric.ball (0:ℂ) (2*δ), N w / w^2‖
      ≤ 2 * C * (2 * Real.pi * (2*δ) ^ α / α) := by
  have hpt : ∀ w : ℂ, ‖N w / w^2‖ ≤ 2 * C * ‖w‖ ^ (α - 2) := by
    intro w
    by_cases hw : w = 0
    · subst hw
      have h0 : ‖N 0 / (0:ℂ)^2‖ = 0 := by simp
      rw [h0, norm_zero, Real.zero_rpow (by linarith : α - 2 ≠ 0)]
      simp
    · rw [norm_div, norm_pow]
      have hw' : 0 < ‖w‖ := norm_pos_iff.mpr hw
      have hp : (‖w‖:ℝ)^2 = ‖w‖^(2:ℝ) := (Real.rpow_natCast ‖w‖ 2).symm
      calc ‖N w‖ / ‖w‖ ^ 2 ≤ 2*C*‖w‖^α / ‖w‖^2 :=
            div_le_div_of_nonneg_right (hN w) (by positivity)
        _ = 2*C*‖w‖^(α-2) := by rw [hp, mul_div_assoc, ← Real.rpow_sub hw' α 2]
  set s : Set ℂ := Metric.ball (0:ℂ) ρ ∩ Metric.ball (0:ℂ) (2*δ) with hs
  have hsm : MeasurableSet s := by rw [hs]; exact measurableSet_ball.inter measurableSet_ball
  have hmaj : IntegrableOn (fun w : ℂ => 2*C*‖w‖^(α-2)) s :=
    MeasureTheory.IntegrableOn.mono_set
      (Integrable.const_mul (integrableOn_norm_rpow_ball (ρ := 2*δ) (s := α-2) (by linarith)) (2*C))
      (by rw [hs]; exact inter_subset_right)
  have hb1 : ‖∫ w in s, N w/w^2‖ ≤ ∫ w in s, 2*C*‖w‖^(α-2) :=
    norm_setIntegral_le_of_norm_le hsm hmaj (fun w _ => hpt w)
  have hmono : ∫ w in s, 2*C*‖w‖^(α-2) ≤ ∫ w in Metric.ball (0:ℂ) (2*δ), 2*C*‖w‖^(α-2) := by
    rw [hs]
    exact setIntegral_mono_set
      (Integrable.const_mul (integrableOn_norm_rpow_ball (ρ := 2*δ) (s := α-2) (by linarith)) (2*C))
      (Filter.Eventually.of_forall fun w => by positivity)
      (Filter.Eventually.of_forall fun w hw => hw.2)
  have hval : ∫ w in Metric.ball (0:ℂ) (2*δ), 2*C*‖w‖^(α-2) = 2*C*(2*Real.pi*(2*δ)^α/α) := by
    rw [integral_const_mul, integral_norm_rpow_ball (by linarith) (by linarith : (-2:ℝ) < α - 2)]
    rw [show α - 2 + 2 = α from by ring]
  calc ‖∫ w in s, N w/w^2‖ ≤ ∫ w in s, 2*C*‖w‖^(α-2) := hb1
    _ ≤ ∫ w in Metric.ball (0:ℂ) (2*δ), 2*C*‖w‖^(α-2) := hmono
    _ = 2*C*(2*Real.pi*(2*δ)^α/α) := hval

/-! ### The far-field kernel-difference estimate -/


/-- A set contained in a disc has finite volume. -/
lemma volume_lt_top_of_subset_ball {s : Set ℂ} {c : ℂ} {R : ℝ}
    (h : s ⊆ Metric.ball c R) : volume s < ⊤ :=
  lt_of_le_of_lt (MeasureTheory.measure_mono h) (MeasureTheory.measure_ball_lt_top (μ := volume))

/-- A function bounded on a finite-measure measurable set is integrable. -/
lemma integrableOn_of_norm_le_const {s : Set ℂ} (hfin : volume s < ⊤) (hsm : MeasurableSet s)
    {F : ℂ → ℂ} (hm : AEStronglyMeasurable F (volume.restrict s)) {M : ℝ}
    (h : ∀ x ∈ s, ‖F x‖ ≤ M) : IntegrableOn F s volume := by
  exact MeasureTheory.IntegrableOn.of_bound hfin hm M
    ((MeasureTheory.ae_restrict_iff' hsm).mpr (Filter.Eventually.of_forall fun x hx => h x hx))

/-- Real-valued version of `integrableOn_of_norm_le_const`. -/
lemma integrableOn_of_bounded {s : Set ℂ} (hfin : volume s < ⊤) (hsm : MeasurableSet s)
    {F : ℂ → ℝ} (hm : AEStronglyMeasurable F (volume.restrict s)) {M : ℝ}
    (h : ∀ x ∈ s, ‖F x‖ ≤ M) : IntegrableOn F s volume :=
  MeasureTheory.IntegrableOn.of_bound hfin hm M
    ((MeasureTheory.ae_restrict_iff' hsm).mpr (Filter.Eventually.of_forall fun x hx => h x hx))

/-- Pointwise bound on the difference of the Beurling kernels: for `‖u - z‖ ≥ 2δ`
with `‖z - z'‖ = δ`, `‖(u-z)⁻² - (u-z')⁻²‖ ≤ 12 δ / ‖u-z‖³`. -/
private lemma norm_inv_sq_sub_le {δ : ℝ} {z z' u : ℂ} (hδ : 0 < δ) (hzz' : ‖z - z'‖ = δ)
    (hu : 2 * δ ≤ ‖u - z‖) :
    ‖(u - z)⁻¹ ^ 2 - (u - z')⁻¹ ^ 2‖ ≤ 12 * δ / ‖u - z‖ ^ 3 := by
  have ha : 0 < ‖u - z‖ := by linarith
  have hane : u - z ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt ha)
  have hbne : u - z' ≠ 0 := by
    intro h0
    have hz0 : ‖u - z'‖ = 0 := by rw [h0, norm_zero]
    have h := norm_add_le (u - z') (z' - z)
    rw [show (u - z') + (z' - z) = u - z from by ring,
      show ‖z' - z‖ = δ from by rw [norm_sub_rev, hzz'], hz0, zero_add] at h
    linarith
  have hbge : ‖u - z‖ / 2 ≤ ‖u - z'‖ := by
    have h := norm_add_le (u - z') (z' - z)
    rw [show (u - z') + (z' - z) = u - z from by ring,
      show ‖z' - z‖ = δ from by rw [norm_sub_rev, hzz']] at h
    linarith
  have hfac : (u - z)⁻¹ ^ 2 - (u - z')⁻¹ ^ 2
      = (z - z') * ((2*u - z - z') * ((u - z)⁻¹ * (u - z')⁻¹) ^ 2) := by
    field_simp
    ring
  have h2uz : ‖2*u - z - z'‖ ≤ 5/2 * ‖u - z‖ := by
    have h := norm_add_le (u - z) (u - z')
    rw [show (u - z) + (u - z') = 2*u - z - z' from by ring] at h
    have hupper : ‖u - z'‖ ≤ 3/2 * ‖u - z‖ := by
      have h2 := norm_sub_le (u - z) (z' - z)
      rw [show (u - z) - (z' - z) = u - z' from by ring,
        show ‖z' - z‖ = δ from by rw [norm_sub_rev, hzz']] at h2
      linarith
    linarith
  have hinv : ‖(u - z)⁻¹ * (u - z')⁻¹‖ ≤ 2 / ‖u - z‖^2 := by
    have h1 : ‖(u - z)⁻¹ * (u - z')⁻¹‖ = 1/(‖u-z‖ * ‖u-z'‖) := by
      rw [norm_mul, norm_inv, norm_inv, ← one_div, ← one_div, div_mul_div_comm, one_mul]
    rw [h1]
    have hge' : ‖u-z‖^2/2 ≤ ‖u-z‖ * ‖u-z'‖ := by nlinarith [hbge, ha]
    refine le_trans (one_div_le_one_div_of_le (by positivity) hge') ?_
    rw [one_div_div]
  have hb1 : ‖2*u - z - z'‖ * ‖(u-z)⁻¹ * (u-z')⁻¹‖^2 ≤ 10 / ‖u-z‖^3 := by
    have h1 : ‖(u-z)⁻¹ * (u-z')⁻¹‖^2 ≤ (2/‖u-z‖^2)^2 :=
      pow_le_pow_left₀ (norm_nonneg _) hinv 2
    have h2 : (2/‖u-z‖^2)^2 = 4/‖u-z‖^4 := by ring_nf
    rw [h2] at h1
    calc ‖2*u-z-z'‖ * ‖(u-z)⁻¹*(u-z')⁻¹‖^2
        ≤ (5/2*‖u-z‖) * (4/‖u-z‖^4) := mul_le_mul h2uz h1 (by positivity) (by positivity)
      _ = 10/‖u-z‖^3 := by
          have han : ‖u-z‖ ≠ 0 := ne_of_gt ha
          field_simp [han]
          ring
  rw [hfac, norm_mul, hzz', norm_mul, norm_pow]
  calc δ * (‖2*u - z - z'‖ * ‖(u - z)⁻¹ * (u - z')⁻¹‖ ^ 2)
      ≤ δ * (10 / ‖u-z‖^3) := mul_le_mul_of_nonneg_left hb1 (by positivity)
    _ = 10*δ/‖u-z‖^3 := by ring
    _ ≤ 12*δ/‖u-z‖^3 := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        linarith

lemma far_kernelDiff_bound {ρ α C δ : ℝ} (hα : 0 < α) (hα1 : α < 1) (hC : 0 ≤ C)
    (hδ : 0 < δ) (h2δρ : 2 * δ ≤ ρ) {z z' : ℂ} (hzz' : ‖z - z'‖ = δ) {φ : ℂ → ℂ}
    (hφ : ∀ u, ‖φ u‖ ≤ C * ‖u - z'‖ ^ α) :
    ‖∫ u in (fun x : ℂ => x + z) '' {w : ℂ | 2 * δ ≤ ‖w‖ ∧ ‖w‖ < ρ},
        φ u * ((u - z)⁻¹ ^ 2 - (u - z')⁻¹ ^ 2)‖
      ≤ 24 * Real.pi * C * (3 / 2) ^ α * 2 ^ (α - 1) * δ ^ α / (1 - α) := by
  set A : Set ℂ := {w : ℂ | 2 * δ ≤ ‖w‖ ∧ ‖w‖ < ρ} with hAdef
  set Az : Set ℂ := (fun x : ℂ => x + z) '' A with hAzdef
  have hAm : MeasurableSet A := by
    rw [hAdef]
    exact (isClosed_le continuous_const continuous_norm).measurableSet.inter
      (isOpen_lt continuous_norm continuous_const).measurableSet
  have hAzm : MeasurableSet Az := by
    rw [hAzdef]
    exact (Homeomorph.addRight z).measurableEmbedding.measurableSet_image' hAm
  have hAzfin : volume Az < ⊤ := by
    rw [hAzdef]
    refine lt_of_le_of_lt (MeasureTheory.measure_mono ?_)
      (MeasureTheory.measure_ball_lt_top (μ := volume) (x := z) (r := ρ))
    rintro u ⟨w, hw, rfl⟩
    rw [hAdef] at hw
    rw [Metric.mem_ball, dist_eq_norm]
    simpa using hw.2
  have hpt : ∀ u ∈ Az, ‖φ u * ((u - z)⁻¹ ^ 2 - (u - z')⁻¹ ^ 2)‖
      ≤ C * (3/2) ^ α * 12 * δ * ‖u - z‖ ^ (α - 3) := by
    intro u hu
    rw [hAzdef] at hu
    obtain ⟨w, hw, rfl⟩ := hu
    rw [hAdef] at hw
    set v : ℂ := (w+z) - z' with hvdef
    have hwpos : 0 < ‖w‖ := by linarith [hδ, hw.1]
    have huz : (w+z) - z = w := by ring
    have huz' : ‖v‖ ≤ 3/2 * ‖w‖ := by
      rw [hvdef]
      calc ‖(w+z) - z'‖ = ‖w - (z' - z)‖ := by congr 1; ring
        _ ≤ ‖w‖ + ‖z' - z‖ := norm_sub_le _ _
        _ = ‖w‖ + δ := by rw [show ‖z' - z‖ = δ from by rw [norm_sub_rev, hzz']]
        _ ≤ ‖w‖ + ‖w‖/2 := by linarith [hw.1]
        _ = (3/2) * ‖w‖ := by ring
    have hker : ‖w⁻¹^2 - v⁻¹^2‖ ≤ 12*δ/‖w‖^3 := by
      have h := norm_inv_sq_sub_le hδ hzz'
        (show 2*δ ≤ ‖(w+z) - z‖ from by rw [huz]; exact hw.1)
      rw [huz] at h
      rw [hvdef]; exact h
    have hφ' : ‖φ (w+z)‖ ≤ C*(3/2)^α*‖w‖^α := by
      calc ‖φ (w+z)‖ ≤ C * ‖v‖^α := by rw [hvdef]; exact hφ (w+z)
        _ ≤ C * (3/2*‖w‖)^α :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) huz' hα.le) hC
        _ = C*(3/2)^α*‖w‖^α := by rw [Real.mul_rpow (by norm_num) (by positivity)]; ring
    rw [show (w+z)-z = w from by ring, norm_mul]
    calc ‖φ (w+z)‖ * ‖w⁻¹^2 - v⁻¹^2‖
        ≤ (C*(3/2)^α*‖w‖^α) * (12*δ/‖w‖^3) :=
          mul_le_mul hφ' hker (norm_nonneg _) (by positivity)
      _ = C*(3/2)^α*12*δ*‖w‖^(α-3) := by
          rw [show (C*(3/2)^α*‖w‖^α)*(12*δ/‖w‖^3) = C*(3/2)^α*12*δ*(‖w‖^α/‖w‖^3) from by ring]
          rw [show ‖w‖^α/‖w‖^3 = ‖w‖^(α-3) from by
            rw [← Real.rpow_natCast ‖w‖ 3, ← Real.rpow_sub hwpos]
            rfl]
  have hmajint : IntegrableOn (fun u : ℂ => C * (3/2)^α * 12 * δ * ‖u - z‖ ^ (α - 3)) Az := by
    have hm : AEStronglyMeasurable
        (fun u : ℂ => C * (3/2)^α * 12 * δ * ‖u - z‖ ^ (α - 3)) (volume.restrict Az) := by
      apply Measurable.aestronglyMeasurable; fun_prop
    refine integrableOn_of_bounded hAzfin hAzm hm
      (M := C * (3/2)^α * 12 * δ * (2*δ)^(α-3)) ?_
    intro u hu
    have hu2 : 2 * δ ≤ ‖u - z‖ := by
      rw [hAzdef] at hu
      obtain ⟨w, hw, rfl⟩ := hu
      rw [hAdef] at hw
      simpa using hw.1
    rw [Real.norm_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos (by linarith) hu2 (by linarith)) (by positivity)
  have hbound := norm_setIntegral_le_of_norm_le hAzm hmajint hpt
  have hval : ∫ u in Az, C * (3/2)^α * 12 * δ * ‖u - z‖ ^ (α-3)
      = C * (3/2)^α * 12 * δ * (2 * Real.pi * (ρ^(α-1) - (2*δ)^(α-1))/(α-1)) := by
    rw [integral_const_mul]
    rw [hAzdef]
    rw [← setIntegral_translate z (fun u : ℂ => ‖u - z‖ ^ (α-3)) A]
    simp only [add_sub_cancel_right]
    rw [integral_norm_rpow_annulus (by linarith) h2δρ (by linarith : α - 3 ≠ -2),
      show α - 3 + 2 = α - 1 from by ring]
  have hle2 : 2 * Real.pi * (ρ^(α-1) - (2*δ)^(α-1))/(α-1)
      ≤ 2 * Real.pi * (2*δ)^(α-1)/(1-α) := by
    have h1 : 2*Real.pi*(ρ^(α-1)-(2*δ)^(α-1))/(α-1)
        = 2*Real.pi*((2*δ)^(α-1)-ρ^(α-1))/(1-α) := by
      rw [div_eq_div_iff (by linarith : (α-1) ≠ 0) (by linarith : (1-α) ≠ 0)]; ring
    rw [h1]
    apply div_le_div_of_nonneg_right _ (by linarith : (0:ℝ) ≤ 1-α)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith [Real.rpow_nonneg (by linarith : (0:ℝ) ≤ ρ) (α-1)]
  have hfin : C * (3/2)^α * 12 * δ * (2*Real.pi*(2*δ)^(α-1)/(1-α))
      = 24 * Real.pi * C * (3/2)^α * 2^(α-1) * δ^α / (1-α) := by
    rw [show (2*δ)^(α-1) = 2^(α-1)*δ^(α-1) from by rw [Real.mul_rpow (by norm_num) (le_of_lt hδ)]]
    have hrp : δ * δ^(α-1) = δ^α := by
      rw [show δ^α = δ^(1+(α-1)) from by congr 1; ring,
        Real.rpow_add hδ, Real.rpow_one]
    rw [show C*(3/2)^α*12*δ*(2*Real.pi*(2^(α-1)*δ^(α-1))/(1-α))
        = (C*(3/2)^α*12*2*Real.pi*2^(α-1)/(1-α)) * (δ*δ^(α-1)) from by ring]
    rw [hrp]; ring
  calc ‖∫ u in Az, φ u * ((u - z)⁻¹ ^ 2 - (u - z')⁻¹ ^ 2)‖
      ≤ ∫ u in Az, C * (3/2)^α * 12 * δ * ‖u - z‖ ^ (α - 3) := hbound
    _ = C * (3/2)^α * 12 * δ * (2 * Real.pi * (ρ^(α-1) - (2*δ)^(α-1))/(α-1)) := hval
    _ ≤ C * (3/2)^α * 12 * δ * (2 * Real.pi * (2*δ)^(α-1)/(1-α)) :=
        mul_le_mul_of_nonneg_left hle2 (by positivity)
    _ = 24 * Real.pi * C * (3/2)^α * 2^(α-1) * δ^α / (1-α) := hfin

end CZaux

end Work.CR.Flat.Cauchy
