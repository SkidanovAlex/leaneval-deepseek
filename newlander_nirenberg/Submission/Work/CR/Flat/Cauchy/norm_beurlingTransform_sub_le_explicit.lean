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

/-! ### Self-contained Calderón--Zygmund development for the Beurling transform -/

namespace BeurlingCZ

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

lemma crescent_bound {ρ α C δ r : ℝ} (hα : 0 < α) (hα1 : α < 1) (hC : 0 ≤ C)
    (hδ : 0 < δ) (hr : 0 < r) (hrρ : 2 * r ≤ ρ) (hδ4 : δ ≤ ρ / 4)
    {z z' : ℂ} (hz : ‖z‖ < r) (hz' : ‖z'‖ < r) (hzz' : ‖z - z'‖ = δ) {f : ℂ → ℂ}
    (hfb : ∀ x, ‖f x‖ ≤ C * ρ ^ α)
    (hf : ∀ x y : ℂ, ‖f x - f y‖ ≤ C * ‖x - y‖ ^ α) (hfsupp : SupportedInBall (ρ / 2) f) :
    ‖(∫ u in (fun x : ℂ => x + z) '' {w : ℂ | 2 * δ ≤ ‖w‖ ∧ ‖w‖ < ρ},
          (f u - f z') * ((u - z')⁻¹ ^ 2))
        - (∫ u in (fun x : ℂ => x + z') '' {w : ℂ | 2 * δ ≤ ‖w‖ ∧ ‖w‖ < ρ},
          (f u - f z') * ((u - z')⁻¹ ^ 2))‖
      ≤ (2 * Real.pi * C * 4 ^ α / α + 9 * Real.pi * C) * δ ^ α := by
  have hρ : 0 < ρ := by linarith
  have hδρ : δ ≤ ρ := by linarith
  have hcont : Continuous f := continuous_of_holder hα hC hf
  set A : Set ℂ := {w : ℂ | 2 * δ ≤ ‖w‖ ∧ ‖w‖ < ρ} with hAdef
  set Az : Set ℂ := (fun x : ℂ => x + z) '' A with hAzdef
  set Az' : Set ℂ := (fun x : ℂ => x + z') '' A with hAz'def
  set G : ℂ → ℂ := fun u => (f u - f z') * ((u - z')⁻¹ ^ 2) with hGdef
  have hAm : MeasurableSet A := by rw [hAdef]; measurability
  have hAzm : MeasurableSet Az := by
    rw [hAzdef]
    exact (Homeomorph.addRight z).measurableEmbedding.measurableSet_image' hAm
  have hAz'm : MeasurableSet Az' := by
    rw [hAz'def]
    exact (Homeomorph.addRight z').measurableEmbedding.measurableSet_image' hAm
  have hGmeas : Measurable G := by
    rw [hGdef]
    exact (hcont.measurable.sub measurable_const).mul
      ((measurable_id.sub_const z').inv.pow_const 2)
  have hmemAz : ∀ u : ℂ, u ∈ Az ↔ 2 * δ ≤ ‖u - z‖ ∧ ‖u - z‖ < ρ := by
    intro u
    rw [hAzdef]
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [hAdef] at hw
      simpa using hw
    · intro hu
      exact ⟨u - z, by rw [hAdef]; simpa using hu, by ring⟩
  have hmemAz' : ∀ u : ℂ, u ∈ Az' ↔ 2 * δ ≤ ‖u - z'‖ ∧ ‖u - z'‖ < ρ := by
    intro u
    rw [hAz'def]
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [hAdef] at hw
      simpa using hw
    · intro hu
      exact ⟨u - z', by rw [hAdef]; simpa using hu, by ring⟩
  have hGbound : ∀ u : ℂ, u ≠ z' → ‖G u‖ ≤ C * ‖u - z'‖ ^ (α - 2) := by
    intro u hu
    have hpos : 0 < ‖u - z'‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hu)
    have hle : ‖f u - f z'‖ ≤ C * ‖u - z'‖ ^ α := hf u z'
    have h2 : ‖(u - z')⁻¹ ^ 2‖ = (‖u - z'‖ ^ 2)⁻¹ := by
      rw [norm_pow, norm_inv, inv_pow]
    rw [hGdef, norm_mul, h2]
    calc ‖f u - f z'‖ * (‖u - z'‖ ^ 2)⁻¹
        ≤ (C * ‖u - z'‖ ^ α) * (‖u - z'‖ ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_right hle (by positivity)
      _ = C * ‖u - z'‖ ^ (α - 2) := by
          rw [← Real.rpow_two ‖u - z'‖, Real.rpow_sub hpos α 2, div_eq_mul_inv]
          ring
  have hGpt_all : ∀ u : ℂ, ‖G u‖ ≤ C * ‖u - z'‖ ^ (α - 2) := by
    intro u
    by_cases h : u = z'
    · subst h
      rw [hGdef]
      simp [Real.zero_rpow (by linarith : α - 2 ≠ 0)]
    · exact hGbound u h
  have hzδ : ∀ u ∈ Az, δ ≤ ‖u - z'‖ := by
    intro u hu
    rw [hmemAz] at hu
    have h1 : ‖u - z‖ ≤ ‖u - z'‖ + δ := by
      have h2 := norm_add_le (u - z') (z' - z)
      rw [show (u - z') + (z' - z) = u - z from by ring,
        show ‖z' - z‖ = δ from by rw [norm_sub_rev, hzz']] at h2
      exact h2
    linarith [hu.1]
  have hAzfin : volume Az < ⊤ := by
    rw [hAzdef]
    refine volume_lt_top_of_subset_ball (c := z) (R := ρ) ?_
    rintro u ⟨w, hw, rfl⟩
    rw [hAdef] at hw
    rw [Metric.mem_ball, dist_eq_norm]
    simpa using hw.2
  have hAz'fin : volume Az' < ⊤ := by
    rw [hAz'def]
    refine volume_lt_top_of_subset_ball (c := z') (R := ρ) ?_
    rintro u ⟨w, hw, rfl⟩
    rw [hAdef] at hw
    rw [Metric.mem_ball, dist_eq_norm]
    simpa using hw.2
  have hGAz : IntegrableOn G Az volume := by
    refine integrableOn_of_norm_le_const hAzfin hAzm
      (hGmeas.aestronglyMeasurable.mono_measure Measure.restrict_le_self)
      (M := C * ρ ^ α / δ ^ 2) ?_
    intro u hu
    have hne : u ≠ z' := by
      intro h
      have h1 := hzδ u hu
      rw [h, sub_self, norm_zero] at h1
      linarith
    refine le_trans (hGbound u hne) ?_
    have hle : ‖u - z'‖ ^ (α - 2) ≤ ρ ^ α / δ ^ 2 := by
      have h1 : ‖u - z'‖ ^ (α - 2) ≤ δ ^ (α - 2) :=
        Real.rpow_le_rpow_of_nonpos hδ (hzδ u hu) (by linarith)
      have h2 : δ ^ (α - 2) = δ ^ α / δ ^ 2 := by
        rw [Real.rpow_sub hδ α 2, Real.rpow_two, div_eq_mul_inv]
      rw [h2] at h1
      exact le_trans h1
        (div_le_div_of_nonneg_right (Real.rpow_le_rpow hδ.le hδρ hα.le) (by positivity))
    calc C * ‖u - z'‖ ^ (α - 2) ≤ C * (ρ ^ α / δ ^ 2) := mul_le_mul_of_nonneg_left hle hC
      _ = C * ρ ^ α / δ ^ 2 := by ring
  have hGAz' : IntegrableOn G Az' volume := by
    refine integrableOn_of_norm_le_const hAz'fin hAz'm
      (hGmeas.aestronglyMeasurable.mono_measure Measure.restrict_le_self)
      (M := C * ρ ^ α / δ ^ 2) ?_
    intro u hu
    rw [hmemAz'] at hu
    have hne : u ≠ z' := by
      intro h
      rw [h, sub_self, norm_zero] at hu
      linarith [hu.1]
    refine le_trans (hGbound u hne) ?_
    have hle : ‖u - z'‖ ^ (α - 2) ≤ ρ ^ α / δ ^ 2 := by
      have h1 : ‖u - z'‖ ^ (α - 2) ≤ δ ^ (α - 2) :=
        Real.rpow_le_rpow_of_nonpos hδ (by linarith [hu.1]) (by linarith)
      have h2 : δ ^ (α - 2) = δ ^ α / δ ^ 2 := by
        rw [Real.rpow_sub hδ α 2, Real.rpow_two, div_eq_mul_inv]
      rw [h2] at h1
      exact le_trans h1
        (div_le_div_of_nonneg_right (Real.rpow_le_rpow hδ.le hδρ hα.le) (by positivity))
    calc C * ‖u - z'‖ ^ (α - 2) ≤ C * (ρ ^ α / δ ^ 2) := mul_le_mul_of_nonneg_left hle hC
      _ = C * ρ ^ α / δ ^ 2 := by ring
  have hsplit : (∫ u in Az, G u) - (∫ u in Az', G u)
      = (∫ u in Az \ Az', G u) - (∫ u in Az' \ Az, G u) := by
    have h1 := setIntegral_sdiff (f := G) (s := Az) (t := Az' ∩ Az) (hAz'm.inter hAzm) hGAz
      Set.inter_subset_right
    rw [Set.sdiff_inter_self_eq_sdiff] at h1
    have h2 := setIntegral_sdiff (f := G) (s := Az') (t := Az ∩ Az') (hAzm.inter hAz'm) hGAz'
      Set.inter_subset_right
    rw [Set.sdiff_inter_self_eq_sdiff] at h2
    rw [h1, h2, Set.inter_comm Az' Az]
    abel
  -- inner / outer decomposition of the two halves
  set I0 : Set ℂ := Metric.ball z' (4 * δ) with hI0def
  set O0 : Set ℂ := {u : ℂ | 4 * δ ≤ ‖u - z'‖} with hO0def
  have hI0m : MeasurableSet I0 := by rw [hI0def]; exact measurableSet_ball
  have hO0m : MeasurableSet O0 := by rw [hO0def]; measurability
  have hcover : ∀ u : ℂ, u ∈ I0 ∨ u ∈ O0 := by
    intro u
    rcases lt_or_ge ‖u - z'‖ (4 * δ) with h | h
    · exact Or.inl (by rw [hI0def, Metric.mem_ball, dist_eq_norm]; exact h)
    · exact Or.inr (by rw [hO0def]; exact h)
  have hS : MeasurableSet (Az \ Az') := hAzm.diff hAz'm
  have hS' : MeasurableSet (Az' \ Az) := hAz'm.diff hAzm
  have hiS : IntegrableOn G (Az \ Az') volume := hGAz.mono_set Set.diff_subset
  have hiS' : IntegrableOn G (Az' \ Az) volume := hGAz'.mono_set Set.diff_subset
  have hnS : IntegrableOn (fun u : ℂ => ‖G u‖) (Az \ Az') volume := hiS.norm
  have hnS' : IntegrableOn (fun u : ℂ => ‖G u‖) (Az' \ Az) volume := hiS'.norm
  have hSsplit : (∫ u in Az \ Az', ‖G u‖)
      = (∫ u in (Az \ Az') ∩ I0, ‖G u‖) + (∫ u in (Az \ Az') ∩ O0, ‖G u‖) := by
    have hc : Az \ Az' = ((Az \ Az') ∩ I0) ∪ ((Az \ Az') ∩ O0) := by
      ext u
      constructor
      · intro hu
        rcases hcover u with h | h
        · exact Or.inl ⟨hu, h⟩
        · exact Or.inr ⟨hu, h⟩
      · rintro (⟨h1, _⟩ | ⟨h1, _⟩) <;> exact h1
    have hd : Disjoint ((Az \ Az') ∩ I0) ((Az \ Az') ∩ O0) := by
      rw [Set.disjoint_left]
      intro u hu hu'
      have h1 : ‖u - z'‖ < 4 * δ := by simpa [hI0def, Metric.mem_ball, dist_eq_norm] using hu.2
      have h2 : 4 * δ ≤ ‖u - z'‖ := by simpa [hO0def] using hu'.2
      linarith
    conv_lhs => rw [hc]
    exact setIntegral_union hd (hS.inter hO0m) (hnS.mono_set Set.inter_subset_left)
      (hnS.mono_set Set.inter_subset_left)
  have hS'split : (∫ u in Az' \ Az, ‖G u‖)
      = (∫ u in (Az' \ Az) ∩ I0, ‖G u‖) + (∫ u in (Az' \ Az) ∩ O0, ‖G u‖) := by
    have hc : Az' \ Az = ((Az' \ Az) ∩ I0) ∪ ((Az' \ Az) ∩ O0) := by
      ext u
      constructor
      · intro hu
        rcases hcover u with h | h
        · exact Or.inl ⟨hu, h⟩
        · exact Or.inr ⟨hu, h⟩
      · rintro (⟨h1, _⟩ | ⟨h1, _⟩) <;> exact h1
    have hd : Disjoint ((Az' \ Az) ∩ I0) ((Az' \ Az) ∩ O0) := by
      rw [Set.disjoint_left]
      intro u hu hu'
      have h1 : ‖u - z'‖ < 4 * δ := by simpa [hI0def, Metric.mem_ball, dist_eq_norm] using hu.2
      have h2 : 4 * δ ≤ ‖u - z'‖ := by simpa [hO0def] using hu'.2
      linarith
    conv_lhs => rw [hc]
    exact setIntegral_union hd (hS'.inter hO0m) (hnS'.mono_set Set.inter_subset_left)
      (hnS'.mono_set Set.inter_subset_left)
  have hcomb : (∫ u in (Az \ Az') ∩ I0, ‖G u‖) + (∫ u in (Az' \ Az) ∩ I0, ‖G u‖)
      = ∫ u in ((Az \ Az') ∪ (Az' \ Az)) ∩ I0, ‖G u‖ := by
    have hc : ((Az \ Az') ∩ I0) ∪ ((Az' \ Az) ∩ I0)
        = ((Az \ Az') ∪ (Az' \ Az)) ∩ I0 := by
      ext u
      constructor
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact ⟨Or.inl h1, h2⟩
        · exact ⟨Or.inr h1, h2⟩
      · rintro ⟨h1 | h1, h2⟩
        · exact Or.inl ⟨h1, h2⟩
        · exact Or.inr ⟨h1, h2⟩
    have hd : Disjoint ((Az \ Az') ∩ I0) ((Az' \ Az) ∩ I0) := by
      rw [Set.disjoint_left]
      intro u hu hu'
      exact hu.1.2 hu'.1.1
    have hu := setIntegral_union hd (hS'.inter hI0m)
      (hnS.mono_set Set.inter_subset_left) (hnS'.mono_set Set.inter_subset_left)
    rw [hc] at hu
    exact hu.symm
  set T1 : ℝ := ∫ u in ((Az \ Az') ∪ (Az' \ Az)) ∩ I0, ‖G u‖ with hT1def
  set T2 : ℝ := ∫ u in (Az \ Az') ∩ O0, ‖G u‖ with hT2def
  set T3 : ℝ := ∫ u in (Az' \ Az) ∩ O0, ‖G u‖ with hT3def
  have htri : ‖(∫ u in Az \ Az', G u) - (∫ u in Az' \ Az, G u)‖ ≤ T1 + T2 + T3 := by
    rw [hT1def, hT2def, hT3def]
    have h1 : ‖∫ u in Az \ Az', G u‖ ≤ ∫ u in Az \ Az', ‖G u‖ :=
      norm_setIntegral_le_of_norm_le hS hnS (fun u _ => le_rfl)
    have h2 : ‖∫ u in Az' \ Az, G u‖ ≤ ∫ u in Az' \ Az, ‖G u‖ :=
      norm_setIntegral_le_of_norm_le hS' hnS' (fun u _ => le_rfl)
    have h3 := norm_sub_le (∫ u in Az \ Az', G u) (∫ u in Az' \ Az, G u)
    linarith [h1, h2, h3, hSsplit, hS'split, hcomb]
  -- the inner region
  have himg : (fun x : ℂ => x + z') '' Metric.ball (0:ℂ) (4 * δ) = Metric.ball z' (4 * δ) := by
    ext u
    constructor
    · rintro ⟨w, hw, rfl⟩
      simpa [Metric.mem_ball, dist_eq_norm, add_sub_cancel_right] using hw
    · intro hu
      exact ⟨u - z', by simpa [Metric.mem_ball, dist_eq_norm] using hu, by ring⟩
  have hmaj_int : IntegrableOn (fun u : ℂ => C * ‖u - z'‖ ^ (α - 2)) I0 volume := by
    rw [hI0def]
    have hkey := (MeasureTheory.measurePreserving_add_right volume z').integrableOn_comp_preimage
      (Homeomorph.addRight z').measurableEmbedding
      (f := fun u : ℂ => C * ‖u - z'‖ ^ (α - 2)) (s := Metric.ball z' (4 * δ))
    have hpre : (fun x : ℂ => x + z') ⁻¹' Metric.ball z' (4 * δ) = Metric.ball (0:ℂ) (4 * δ) := by
      ext w
      simp [Metric.mem_ball, dist_eq_norm]
    have hcomp : ((fun u : ℂ => C * ‖u - z'‖ ^ (α - 2)) ∘ (fun x : ℂ => x + z'))
        = fun w : ℂ => C * ‖w‖ ^ (α - 2) := by
      funext w; simp [add_sub_cancel_right]
    rw [hpre, hcomp] at hkey
    refine hkey.mp ?_
    exact (integrableOn_norm_rpow_ball (ρ := 4 * δ) (s := α - 2) (by linarith)).const_mul C
  have hnI0 : IntegrableOn (fun u : ℂ => ‖G u‖) I0 volume := by
    refine Integrable.mono' hmaj_int ?_ ?_
    · exact (hGmeas.norm.aestronglyMeasurable).mono_measure Measure.restrict_le_self
    · filter_upwards with u
      simpa using hGpt_all u
  have hT1 : T1 ≤ 2 * Real.pi * C * 4 ^ α / α * δ ^ α := by
    rw [hT1def]
    have h1 : (∫ u in ((Az \ Az') ∪ (Az' \ Az)) ∩ I0, ‖G u‖) ≤ ∫ u in I0, ‖G u‖ :=
      setIntegral_mono_set hnI0 (Filter.Eventually.of_forall fun _ => norm_nonneg _)
        (Filter.Eventually.of_forall fun _ hu => hu.2)
    have h2 : (∫ u in I0, ‖G u‖) ≤ ∫ u in I0, C * ‖u - z'‖ ^ (α - 2) :=
      setIntegral_mono_on hnI0 hmaj_int hI0m (fun u _ => hGpt_all u)
    have h3 : (∫ u in I0, C * ‖u - z'‖ ^ (α - 2)) = 2 * Real.pi * C * 4 ^ α / α * δ ^ α := by
      rw [hI0def, integral_const_mul, ← himg]
      rw [← setIntegral_translate z' (fun u : ℂ => ‖u - z'‖ ^ (α - 2)) (Metric.ball (0:ℂ) (4 * δ))]
      have htrans : (∫ w in Metric.ball (0:ℂ) (4 * δ), ‖(w + z') - z'‖ ^ (α - 2))
          = ∫ w in Metric.ball (0:ℂ) (4 * δ), ‖w‖ ^ (α - 2) :=
        setIntegral_congr_fun measurableSet_ball (fun w _ => by simp [add_sub_cancel_right])
      rw [htrans, integral_norm_rpow_ball (by linarith) (by linarith : (-2:ℝ) < α - 2)]
      rw [show α - 2 + 2 = α from by ring, Real.mul_rpow (by norm_num) (le_of_lt hδ)]
      ring
    linarith
  -- the outer region
  set Annu : Set ℂ := {w : ℂ | ρ - δ ≤ ‖w‖ ∧ ‖w‖ < ρ} with hAnnudef
  have hAnnum : MeasurableSet Annu := by rw [hAnnudef]; measurability
  set shelz : Set ℂ := (fun x : ℂ => x + z) '' Annu with hshelzdef
  set shelz' : Set ℂ := (fun x : ℂ => x + z') '' Annu with hshelz'def
  set E1 : Set ℂ := {u : ℂ | ρ - δ ≤ ‖u - z‖ ∧ (‖u - z‖ < ρ ∧ ρ ≤ ‖u - z'‖)} with hE1def
  have hE1m : MeasurableSet E1 := by rw [hE1def]; measurability
  have hE1sub : E1 ⊆ shelz := by
    intro u hu
    rw [hE1def] at hu
    obtain ⟨h1, h2, h3⟩ := hu
    rw [hshelzdef]
    exact ⟨u - z, by rw [hAnnudef]; exact ⟨h1, h2⟩, by ring⟩
  have hshelz_ball : shelz ⊆ Metric.ball z ρ := by
    rintro u ⟨w, hw, rfl⟩
    rw [hAnnudef] at hw
    rw [Metric.mem_ball, dist_eq_norm]
    simpa using hw.2
  have hshelz'_ball : shelz' ⊆ Metric.ball z' ρ := by
    rintro u ⟨w, hw, rfl⟩
    rw [hAnnudef] at hw
    rw [Metric.mem_ball, dist_eq_norm]
    simpa using hw.2
  have hvol_annu : ∀ c : ℂ, (volume ((fun x : ℂ => x + c) '' Annu)).toReal
      = Real.pi * (ρ ^ 2 - (ρ - δ) ^ 2) := by
    intro c
    have hvol : (∫ u in (fun x : ℂ => x + c) '' Annu, (1:ℝ))
        = (volume ((fun x : ℂ => x + c) '' Annu)).toReal := by
      rw [setIntegral_const, Measure.real_def]
      simp
    have h1 : (∫ u in (fun x : ℂ => x + c) '' Annu, (1:ℝ)) = (∫ w in Annu, (1:ℝ)) :=
      (setIntegral_translate c (fun _ : ℂ => (1:ℝ)) Annu).symm
    have h2 : (∫ w in Annu, (1:ℝ)) = Real.pi * (ρ ^ 2 - (ρ - δ) ^ 2) := by
      have hc : (∫ w in Annu, (1:ℝ)) = (∫ w in Annu, ‖w‖ ^ (0:ℝ)) := by
        refine setIntegral_congr_fun hAnnum (fun w _ => ?_)
        exact (Real.rpow_zero ‖w‖).symm
      rw [hc]
      rw [show Annu = {w : ℂ | ρ - δ ≤ ‖w‖ ∧ ‖w‖ < ρ} from hAnnudef]
      rw [integral_norm_rpow_annulus (a := ρ - δ) (b := ρ) (s := 0) (by linarith) (by linarith)
        (by norm_num : (0:ℝ) ≠ -2)]
      norm_num
      ring
    rw [← hvol, h1, h2]
  have hvol_shelz : (volume shelz).toReal ≤ 2 * Real.pi * ρ * δ := by
    rw [hshelzdef, hvol_annu z]
    rw [show (2:ℝ) * Real.pi * ρ * δ = Real.pi * (2 * ρ * δ) from by ring]
    refine mul_le_mul_of_nonneg_left ?_ Real.pi_pos.le
    nlinarith [sq_nonneg δ, Real.pi_pos.le]
  have hvol_shelz' : (volume shelz').toReal ≤ 2 * Real.pi * ρ * δ := by
    rw [hshelz'def, hvol_annu z']
    rw [show (2:ℝ) * Real.pi * ρ * δ = Real.pi * (2 * ρ * δ) from by ring]
    refine mul_le_mul_of_nonneg_left ?_ Real.pi_pos.le
    nlinarith [sq_nonneg δ, Real.pi_pos.le]
  have hvol_E1 : (volume E1).toReal ≤ 2 * Real.pi * ρ * δ := by
    have hfin : volume shelz < ⊤ := volume_lt_top_of_subset_ball hshelz_ball
    exact le_trans (@ENNReal.toReal_mono (volume E1) (volume shelz) (ne_of_lt hfin)
      (measure_mono hE1sub)) hvol_shelz
  have hE1_pt : ∀ u ∈ E1, ‖G u‖ ≤ C * ρ ^ (α - 2) := by
    intro u hu
    rw [hE1def] at hu
    obtain ⟨h1, h2, h3⟩ := hu
    have hne : u ≠ z' := by
      intro h
      rw [h, sub_self, norm_zero] at h3
      linarith
    refine le_trans (hGbound u hne) ?_
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hρ h3 (by linarith)) hC
  have hshelz'_pt : ∀ u ∈ shelz', ‖G u‖ ≤ (16/9) * C * ρ ^ (α - 2) := by
    rintro u ⟨w, hw, rfl⟩
    rw [hAnnudef] at hw
    have hsub : (w + z') - z' = w := by ring
    have hne : w + z' ≠ z' := by
      intro h
      have h0 : ‖w‖ = 0 := by rw [← hsub, h, sub_self, norm_zero]
      linarith [hw.1, hδ]
    refine le_trans (hGbound (w + z') hne) ?_
    rw [hsub]
    have h6 : (3/4 : ℝ) ^ (α - 2) ≤ 16/9 := by
      have h7 : (3/4 : ℝ) ^ (α - 2) ≤ (3/4 : ℝ) ^ (-2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by linarith)
      have h8 : (3/4 : ℝ) ^ (-2 : ℝ) = 16/9 := by
        rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 3/4), Real.rpow_two]
        norm_num
      linarith
    have h9 : ‖w‖ ^ (α - 2) ≤ (16/9) * ρ ^ (α - 2) := by
      have h10 : ‖w‖ ^ (α - 2) ≤ (3 * ρ / 4) ^ (α - 2) :=
        Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith [hw.1]) (by linarith)
      have h11 : (3 * ρ / 4) ^ (α - 2) = (3/4 : ℝ) ^ (α - 2) * ρ ^ (α - 2) := by
        rw [show (3 * ρ / 4) = (3/4) * ρ by ring, Real.mul_rpow (by norm_num) (le_of_lt hρ)]
      rw [h11] at h10
      exact le_trans h10
        (mul_le_mul_of_nonneg_right h6 (Real.rpow_nonneg (le_of_lt hρ) _))
    calc C * ‖w‖ ^ (α - 2) ≤ C * ((16/9) * ρ ^ (α - 2)) := mul_le_mul_of_nonneg_left h9 hC
      _ = (16/9) * C * ρ ^ (α - 2) := by ring
  have hSO0sub : (Az \ Az') ∩ O0 ⊆ E1 := by
    rintro u ⟨huS, huO⟩
    have hAz := (hmemAz u).mp huS.1
    have hnAz' : ¬ (2 * δ ≤ ‖u - z'‖ ∧ ‖u - z'‖ < ρ) := fun h => huS.2 ((hmemAz' u).mpr h)
    have hO : 4 * δ ≤ ‖u - z'‖ := by simpa [hO0def] using huO
    have hge : ρ ≤ ‖u - z'‖ := by
      by_contra h
      rw [not_le] at h
      exact hnAz' ⟨by linarith, h⟩
    have hlow : ρ - δ ≤ ‖u - z‖ := by
      have h1 := norm_add_le (u - z) (z - z')
      rw [show (u - z) + (z - z') = u - z' from by ring, hzz'] at h1
      linarith
    rw [hE1def]
    exact ⟨hlow, hAz.2, hge⟩
  have hS'O0sub : (Az' \ Az) ∩ O0 ⊆ shelz' := by
    rintro u ⟨huS, huO⟩
    have hAz' := (hmemAz' u).mp huS.1
    have hnAz : ¬ (2 * δ ≤ ‖u - z‖ ∧ ‖u - z‖ < ρ) := fun h => huS.2 ((hmemAz u).mpr h)
    have hO : 4 * δ ≤ ‖u - z'‖ := by simpa [hO0def] using huO
    have h2δ : 2 * δ ≤ ‖u - z‖ := by
      by_contra h
      rw [not_le] at h
      have hle : ‖u - z'‖ ≤ ‖u - z‖ + δ := by
        have h1 := norm_add_le (u - z) (z - z')
        rw [show (u - z) + (z - z') = u - z' from by ring, hzz'] at h1
        exact h1
      linarith
    have hge : ρ ≤ ‖u - z‖ := by
      by_contra h
      rw [not_le] at h
      exact hnAz ⟨h2δ, h⟩
    have hlow : ρ - δ ≤ ‖u - z'‖ := by
      have h1 := norm_add_le (u - z') (z' - z)
      rw [show (u - z') + (z' - z) = u - z from by ring,
        show ‖z' - z‖ = δ from by rw [norm_sub_rev, hzz']] at h1
      linarith
    rw [hshelz'def]
    exact ⟨u - z', by rw [hAnnudef]; exact ⟨hlow, hAz'.2⟩, by ring⟩
  have hrp : ρ ^ (α - 2) * ρ = ρ ^ (α - 1) := by
    have h : ρ ^ ((α - 2) + 1) = ρ ^ (α - 1) := by congr 1; ring
    rwa [Real.rpow_add hρ, Real.rpow_one] at h
  have hkey : ρ ^ (α - 1) * δ ≤ δ ^ α := by
    have h1 : ρ ^ (α - 1) ≤ δ ^ (α - 1) :=
      Real.rpow_le_rpow_of_nonpos hδ hδρ (by linarith)
    have h2 : δ ^ (α - 1) * δ = δ ^ α := by
      have h : δ ^ ((α - 1) + 1) = δ ^ α := by congr 1; ring
      rwa [Real.rpow_add hδ, Real.rpow_one] at h
    calc ρ ^ (α - 1) * δ ≤ δ ^ (α - 1) * δ := mul_le_mul_of_nonneg_right h1 hδ.le
      _ = δ ^ α := h2
  have hT2 : T2 ≤ 2 * Real.pi * C * δ ^ α := by
    rw [hT2def]
    have hIntC : IntegrableOn (fun _ : ℂ => (C * ρ ^ (α - 2) : ℝ)) E1 volume :=
      integrableOn_const (ne_of_lt (volume_lt_top_of_subset_ball (hE1sub.trans hshelz_ball)))
    have h1 : (∫ u in (Az \ Az') ∩ O0, ‖G u‖)
        ≤ ∫ u in (Az \ Az') ∩ O0, (C * ρ ^ (α - 2) : ℝ) :=
      setIntegral_mono_on (hnS.mono_set Set.inter_subset_left) (hIntC.mono_set hSO0sub)
        (hS.inter hO0m) (fun u hu => hE1_pt u (hSO0sub hu))
    have h2 : (∫ u in (Az \ Az') ∩ O0, (C * ρ ^ (α - 2) : ℝ))
        = C * ρ ^ (α - 2) * (volume ((Az \ Az') ∩ O0)).toReal := by
      rw [setIntegral_const, Measure.real_def]
      simp only [smul_eq_mul]
      ring
    have h3 : (volume ((Az \ Az') ∩ O0)).toReal ≤ 2 * Real.pi * ρ * δ := by
      have hfin : volume E1 < ⊤ := volume_lt_top_of_subset_ball (hE1sub.trans hshelz_ball)
      exact le_trans (@ENNReal.toReal_mono (volume ((Az \ Az') ∩ O0)) (volume E1)
        (ne_of_lt hfin) (measure_mono hSO0sub)) hvol_E1
    calc (∫ u in (Az \ Az') ∩ O0, ‖G u‖)
        ≤ ∫ u in (Az \ Az') ∩ O0, (C * ρ ^ (α - 2) : ℝ) := h1
      _ = C * ρ ^ (α - 2) * (volume ((Az \ Az') ∩ O0)).toReal := h2
      _ ≤ C * ρ ^ (α - 2) * (2 * Real.pi * ρ * δ) := mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = 2 * Real.pi * C * (ρ ^ (α - 2) * ρ) * δ := by ring
      _ = 2 * Real.pi * C * ρ ^ (α - 1) * δ := by rw [hrp]
      _ = 2 * Real.pi * C * (ρ ^ (α - 1) * δ) := by ring
      _ ≤ 2 * Real.pi * C * δ ^ α := mul_le_mul_of_nonneg_left hkey (by positivity)
  have hT3 : T3 ≤ (32/9) * Real.pi * C * δ ^ α := by
    rw [hT3def]
    have hIntC : IntegrableOn (fun _ : ℂ => ((16/9) * C * ρ ^ (α - 2) : ℝ)) shelz' volume :=
      integrableOn_const (ne_of_lt (volume_lt_top_of_subset_ball hshelz'_ball))
    have h1 : (∫ u in (Az' \ Az) ∩ O0, ‖G u‖)
        ≤ ∫ u in (Az' \ Az) ∩ O0, ((16/9) * C * ρ ^ (α - 2) : ℝ) :=
      setIntegral_mono_on (hnS'.mono_set Set.inter_subset_left) (hIntC.mono_set hS'O0sub)
        (hS'.inter hO0m) (fun u hu => hshelz'_pt u (hS'O0sub hu))
    have h2 : (∫ u in (Az' \ Az) ∩ O0, ((16/9) * C * ρ ^ (α - 2) : ℝ))
        = (16/9) * C * ρ ^ (α - 2) * (volume ((Az' \ Az) ∩ O0)).toReal := by
      rw [setIntegral_const, Measure.real_def]
      simp only [smul_eq_mul]
      ring
    have h3 : (volume ((Az' \ Az) ∩ O0)).toReal ≤ 2 * Real.pi * ρ * δ := by
      have hfin : volume shelz' < ⊤ := volume_lt_top_of_subset_ball hshelz'_ball
      exact le_trans (@ENNReal.toReal_mono (volume ((Az' \ Az) ∩ O0)) (volume shelz')
        (ne_of_lt hfin) (measure_mono hS'O0sub)) hvol_shelz'
    calc (∫ u in (Az' \ Az) ∩ O0, ‖G u‖)
        ≤ ∫ u in (Az' \ Az) ∩ O0, ((16/9) * C * ρ ^ (α - 2) : ℝ) := h1
      _ = (16/9) * C * ρ ^ (α - 2) * (volume ((Az' \ Az) ∩ O0)).toReal := h2
      _ ≤ (16/9) * C * ρ ^ (α - 2) * (2 * Real.pi * ρ * δ) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = (32/9) * Real.pi * C * (ρ ^ (α - 2) * ρ) * δ := by ring
      _ = (32/9) * Real.pi * C * ρ ^ (α - 1) * δ := by rw [hrp]
      _ = (32/9) * Real.pi * C * (ρ ^ (α - 1) * δ) := by ring
      _ ≤ (32/9) * Real.pi * C * δ ^ α := mul_le_mul_of_nonneg_left hkey (by positivity)
  have htri2 : ‖(∫ u in Az \ Az', G u) - (∫ u in Az' \ Az, G u)‖
      ≤ 2 * Real.pi * C * 4 ^ α / α * δ ^ α + 2 * Real.pi * C * δ ^ α
        + (32/9) * Real.pi * C * δ ^ α := by
    linarith [htri, hT1, hT2, hT3]
  have hcd : (0:ℝ) ≤ C * δ ^ α := mul_nonneg hC (Real.rpow_nonneg hδ.le α)
  have hlast : 2 * Real.pi * C * δ ^ α + (32/9) * Real.pi * C * δ ^ α
      ≤ 9 * Real.pi * C * δ ^ α := by
    have hfac : 2 * Real.pi * C * δ ^ α + (32/9) * Real.pi * C * δ ^ α
        = (50/9) * (Real.pi * (C * δ ^ α)) := by ring
    have h0 : (0:ℝ) ≤ Real.pi * (C * δ ^ α) := mul_nonneg Real.pi_pos.le hcd
    rw [hfac]
    nlinarith
  have hexp : (2 * Real.pi * C * 4 ^ α / α + 9 * Real.pi * C) * δ ^ α
      = 2 * Real.pi * C * 4 ^ α / α * δ ^ α + 9 * Real.pi * C * δ ^ α := by ring
  have hfinal : ‖(∫ u in Az \ Az', G u) - (∫ u in Az' \ Az, G u)‖
      ≤ (2 * Real.pi * C * 4 ^ α / α + 9 * Real.pi * C) * δ ^ α := by
    rw [hexp]
    linarith [htri2, hlast]
  rw [hsplit]
  exact hfinal

open MeasureTheory Set in
lemma outer_region_bound {ρ α C : ℝ} (hα : 0 < α) (hα1 : α < 1) (hC : 0 ≤ C)
    {δ : ℝ} (hδ : 0 < δ) (hδ4 : δ ≤ ρ / 4)
    {z z' : ℂ} (hzz' : ‖z - z'‖ = δ) (hz : ‖z‖ < ρ / 2) (hz' : ‖z'‖ < ρ / 2)
    {f : ℂ → ℂ} (hfb : ∀ x, ‖f x‖ ≤ C * ρ ^ α)
    (hf : ∀ x y : ℂ, ‖f x - f y‖ ≤ C * ‖x - y‖ ^ α) (hfsupp : SupportedInBall (ρ / 2) f) :
    ‖∫ w in {w : ℂ | 2 * δ ≤ ‖w‖ ∧ ‖w‖ < ρ},
        ((f (z + w) - f z) - (f (z' + w) - f z')) / w ^ 2‖
      ≤ (24 * Real.pi * C * (3 / 2) ^ α * 2 ^ (α - 1) / (1 - α)
          + 2 * Real.pi * C * 4 ^ α / α + 9 * Real.pi * C) * δ ^ α := by
  have hρ : 0 < ρ := by linarith
  have h2δρ : 2 * δ ≤ ρ := by linarith
  have hcont : Continuous f := continuous_of_holder hα hC hf
  set A : Set ℂ := {w : ℂ | 2 * δ ≤ ‖w‖ ∧ ‖w‖ < ρ} with hAdef
  set Az : Set ℂ := (fun x : ℂ => x + z) '' A with hAzdef
  set Az' : Set ℂ := (fun x : ℂ => x + z') '' A with hAz'def
  have hAm : MeasurableSet A := by rw [hAdef]; measurability
  have hAzm : MeasurableSet Az := by
    rw [hAzdef]
    exact (Homeomorph.addRight z).measurableEmbedding.measurableSet_image' hAm
  have hAz'm : MeasurableSet Az' := by
    rw [hAz'def]
    exact (Homeomorph.addRight z').measurableEmbedding.measurableSet_image' hAm
  have hAball : A ⊆ Metric.ball (0:ℂ) ρ := by
    intro w hw
    rw [hAdef] at hw
    rw [Metric.mem_ball, dist_eq_norm]
    simpa using hw.2
  have hAzfin : volume Az < ⊤ := by
    rw [hAzdef]
    refine volume_lt_top_of_subset_ball (c := z) (R := ρ) ?_
    rintro u ⟨w, hw, rfl⟩
    rw [hAdef] at hw
    rw [Metric.mem_ball, dist_eq_norm]
    simpa using hw.2
  have hAz'fin : volume Az' < ⊤ := by
    rw [hAz'def]
    refine volume_lt_top_of_subset_ball (c := z') (R := ρ) ?_
    rintro u ⟨w, hw, rfl⟩
    rw [hAdef] at hw
    rw [Metric.mem_ball, dist_eq_norm]
    simpa using hw.2
  have hmemAz : ∀ u : ℂ, u ∈ Az ↔ 2 * δ ≤ ‖u - z‖ ∧ ‖u - z‖ < ρ := by
    intro u
    rw [hAzdef]
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [hAdef] at hw
      simpa using hw
    · intro hu
      exact ⟨u - z, by rw [hAdef]; simpa using hu, by ring⟩
  have hmemAz' : ∀ u : ℂ, u ∈ Az' ↔ 2 * δ ≤ ‖u - z'‖ ∧ ‖u - z'‖ < ρ := by
    intro u
    rw [hAz'def]
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [hAdef] at hw
      simpa using hw
    · intro hu
      exact ⟨u - z', by rw [hAdef]; simpa using hu, by ring⟩
  have hδz' : ∀ u ∈ Az, δ ≤ ‖u - z'‖ := by
    intro u hu
    rw [hmemAz] at hu
    have h1 : ‖u - z‖ ≤ ‖u - z'‖ + δ := by
      have h2 := norm_add_le (u - z') (z' - z)
      rw [show (u - z') + (z' - z) = u - z from by ring,
        show ‖z' - z‖ = δ from by rw [norm_sub_rev, hzz']] at h2
      exact h2
    linarith [hu.1]
  -- pointwise bound helper
  have hbdd : ∀ u : ℂ, ‖f u - f z‖ ≤ 2 * C * ρ ^ α := by
    intro u
    calc ‖f u - f z‖ ≤ ‖f u‖ + ‖f z‖ := norm_sub_le _ _
      _ ≤ C * ρ ^ α + C * ρ ^ α := add_le_add (hfb u) (hfb z)
      _ = 2 * C * ρ ^ α := by ring
  have hbdd' : ∀ u : ℂ, ‖f u - f z'‖ ≤ 2 * C * ρ ^ α := by
    intro u
    calc ‖f u - f z'‖ ≤ ‖f u‖ + ‖f z'‖ := norm_sub_le _ _
      _ ≤ C * ρ ^ α + C * ρ ^ α := add_le_add (hfb u) (hfb z')
      _ = 2 * C * ρ ^ α := by ring
  -- integrability on A of the two halves (divisive form)
  have hIw1 : IntegrableOn (fun w : ℂ => (f (z + w) - f z) / w ^ 2) A volume :=
    (integrableOn_beurlingIntegrand hα hC hf z).mono_set hAball
  have hIw2 : IntegrableOn (fun w : ℂ => (f (z' + w) - f z') / w ^ 2) A volume :=
    (integrableOn_beurlingIntegrand hα hC hf z').mono_set hAball
  have hIp1 : IntegrableOn (fun w : ℂ => (f (z + w) - f z) * (w⁻¹ ^ 2)) A volume :=
    (integrableOn_congr_fun (f := fun w : ℂ => (f (z + w) - f z) / w ^ 2)
      (g := fun w : ℂ => (f (z + w) - f z) * (w⁻¹ ^ 2))
      (fun w _ => by simp only [div_eq_mul_inv, inv_pow]) hAm).mp hIw1
  have hIp2 : IntegrableOn (fun w : ℂ => (f (z' + w) - f z') * (w⁻¹ ^ 2)) A volume :=
    (integrableOn_congr_fun (f := fun w : ℂ => (f (z' + w) - f z') / w ^ 2)
      (g := fun w : ℂ => (f (z' + w) - f z') * (w⁻¹ ^ 2))
      (fun w _ => by simp only [div_eq_mul_inv, inv_pow]) hAm).mp hIw2
  have hstep1 : (∫ w in A, ((f (z + w) - f z) - (f (z' + w) - f z')) / w ^ 2)
      = (∫ w in A, (f (z + w) - f z) * (w⁻¹ ^ 2))
        - (∫ w in A, (f (z' + w) - f z') * (w⁻¹ ^ 2)) := by
    rw [show (∫ w in A, ((f (z + w) - f z) - (f (z' + w) - f z')) / w ^ 2)
        = ∫ w in A, ((f (z + w) - f z) * (w⁻¹ ^ 2)
            - (f (z' + w) - f z') * (w⁻¹ ^ 2)) from
      setIntegral_congr_fun hAm (fun w _ => by rw [div_eq_mul_inv, inv_pow]; ring)]
    exact integral_sub hIp1 hIp2
  have hsub1 : (∫ w in A, (f (z + w) - f z) * (w⁻¹ ^ 2))
      = ∫ u in Az, (f u - f z) * ((u - z)⁻¹ ^ 2) := by
    rw [show (∫ w in A, (f (z + w) - f z) * (w⁻¹ ^ 2))
        = ∫ w in A, (f (w + z) - f z) * (((w + z) - z)⁻¹ ^ 2) from
      setIntegral_congr_fun hAm (fun w _ => by rw [add_comm, add_sub_cancel_right])]
    exact setIntegral_translate z (fun u : ℂ => (f u - f z) * ((u - z)⁻¹ ^ 2)) A
  have hsub2 : (∫ w in A, (f (z' + w) - f z') * (w⁻¹ ^ 2))
      = ∫ u in Az', (f u - f z') * ((u - z')⁻¹ ^ 2) := by
    rw [show (∫ w in A, (f (z' + w) - f z') * (w⁻¹ ^ 2))
        = ∫ w in A, (f (w + z') - f z') * (((w + z') - z')⁻¹ ^ 2) from
      setIntegral_congr_fun hAm (fun w _ => by rw [add_comm, add_sub_cancel_right])]
    exact setIntegral_translate z' (fun u : ℂ => (f u - f z') * ((u - z')⁻¹ ^ 2)) A
  have hmean : (∫ u in Az, ((u - z)⁻¹ ^ 2)) = 0 := by
    have h := setIntegral_translate z (fun u : ℂ => ((u - z)⁻¹ ^ 2)) A
    rw [show (∫ w in A, (((w + z) - z)⁻¹ ^ 2)) = (∫ w in A, (w⁻¹ ^ 2)) from
      setIntegral_congr_fun hAm (fun w _ => by rw [add_sub_cancel_right])] at h
    rw [← h]
    exact integral_inv_sq_annulus (2 * δ) ρ
  -- integrability of the Az-forms
  have hsm1 : AEStronglyMeasurable (fun u : ℂ => (f u - f z) * ((u - z)⁻¹ ^ 2))
      (volume.restrict Az) := ((hcont.measurable.sub measurable_const).mul
        ((measurable_id.sub_const z).inv.pow_const 2)).aestronglyMeasurable.mono_measure
        Measure.restrict_le_self
  have hsm2 : AEStronglyMeasurable (fun u : ℂ => (f u - f z') * ((u - z)⁻¹ ^ 2))
      (volume.restrict Az) := ((hcont.measurable.sub measurable_const).mul
        ((measurable_id.sub_const z).inv.pow_const 2)).aestronglyMeasurable.mono_measure
        Measure.restrict_le_self
  have hsm2' : AEStronglyMeasurable (fun u : ℂ => (f u - f z') * ((u - z')⁻¹ ^ 2))
      (volume.restrict Az) := ((hcont.measurable.sub measurable_const).mul
        ((measurable_id.sub_const z').inv.pow_const 2)).aestronglyMeasurable.mono_measure
        Measure.restrict_le_self
  have hsm2'' : AEStronglyMeasurable (fun u : ℂ => (f u - f z') * ((u - z')⁻¹ ^ 2))
      (volume.restrict Az') := ((hcont.measurable.sub measurable_const).mul
        ((measurable_id.sub_const z').inv.pow_const 2)).aestronglyMeasurable.mono_measure
        Measure.restrict_le_self
  have hIAz1 : IntegrableOn (fun u : ℂ => (f u - f z) * ((u - z)⁻¹ ^ 2)) Az volume := by
    refine integrableOn_of_norm_le_const hAzfin hAzm hsm1 (M := 2 * C * ρ ^ α / (2 * δ) ^ 2) ?_
    intro u hu
    have h1 : 2 * δ ≤ ‖u - z‖ := (hmemAz u).mp hu |>.1
    have h2 : ‖u - z‖⁻¹ ≤ (2 * δ)⁻¹ := by
      rw [inv_le_inv₀ (by linarith : (0:ℝ) < ‖u - z‖) (by linarith : (0:ℝ) < 2 * δ)]
      exact h1
    rw [norm_mul, norm_pow, norm_inv]
    calc ‖f u - f z‖ * ‖u - z‖⁻¹ ^ 2 ≤ (2 * C * ρ ^ α) * ((2 * δ)⁻¹ ^ 2) :=
          mul_le_mul (hbdd u) (pow_le_pow_left₀ (by positivity) h2 2) (by positivity) (by positivity)
      _ = 2 * C * ρ ^ α / (2 * δ) ^ 2 := by ring
  have hIAz2 : IntegrableOn (fun u : ℂ => (f u - f z') * ((u - z)⁻¹ ^ 2)) Az volume := by
    refine integrableOn_of_norm_le_const hAzfin hAzm hsm2 (M := 2 * C * ρ ^ α / (2 * δ) ^ 2) ?_
    intro u hu
    have h1 : 2 * δ ≤ ‖u - z‖ := (hmemAz u).mp hu |>.1
    have h2 : ‖u - z‖⁻¹ ≤ (2 * δ)⁻¹ := by
      rw [inv_le_inv₀ (by linarith : (0:ℝ) < ‖u - z‖) (by linarith : (0:ℝ) < 2 * δ)]
      exact h1
    rw [norm_mul, norm_pow, norm_inv]
    calc ‖f u - f z'‖ * ‖u - z‖⁻¹ ^ 2 ≤ (2 * C * ρ ^ α) * ((2 * δ)⁻¹ ^ 2) :=
          mul_le_mul (hbdd' u) (pow_le_pow_left₀ (by positivity) h2 2) (by positivity) (by positivity)
      _ = 2 * C * ρ ^ α / (2 * δ) ^ 2 := by ring
  have hIR2 : IntegrableOn (fun u : ℂ => (f u - f z') * ((u - z')⁻¹ ^ 2)) Az volume := by
    refine integrableOn_of_norm_le_const hAzfin hAzm hsm2' (M := 2 * C * ρ ^ α / δ ^ 2) ?_
    intro u hu
    have h1 : δ ≤ ‖u - z'‖ := hδz' u hu
    have h2 : ‖u - z'‖⁻¹ ≤ δ⁻¹ := by
      rw [inv_le_inv₀ (by linarith : (0:ℝ) < ‖u - z'‖) (by linarith : (0:ℝ) < δ)]
      exact h1
    rw [norm_mul, norm_pow, norm_inv]
    calc ‖f u - f z'‖ * ‖u - z'‖⁻¹ ^ 2 ≤ (2 * C * ρ ^ α) * (δ⁻¹ ^ 2) :=
          mul_le_mul (hbdd' u) (pow_le_pow_left₀ (by positivity) h2 2) (by positivity) (by positivity)
      _ = 2 * C * ρ ^ α / δ ^ 2 := by ring
  have hIR2' : IntegrableOn (fun u : ℂ => (f u - f z') * ((u - z')⁻¹ ^ 2)) Az' volume := by
    refine integrableOn_of_norm_le_const hAz'fin hAz'm hsm2'' (M := 2 * C * ρ ^ α / (2 * δ) ^ 2) ?_
    intro u hu
    have h1 : 2 * δ ≤ ‖u - z'‖ := (hmemAz' u).mp hu |>.1
    have h2 : ‖u - z'‖⁻¹ ≤ (2 * δ)⁻¹ := by
      rw [inv_le_inv₀ (by linarith : (0:ℝ) < ‖u - z'‖) (by linarith : (0:ℝ) < 2 * δ)]
      exact h1
    rw [norm_mul, norm_pow, norm_inv]
    calc ‖f u - f z'‖ * ‖u - z'‖⁻¹ ^ 2 ≤ (2 * C * ρ ^ α) * ((2 * δ)⁻¹ ^ 2) :=
          mul_le_mul (hbdd' u) (pow_le_pow_left₀ (by positivity) h2 2) (by positivity) (by positivity)
      _ = 2 * C * ρ ^ α / (2 * δ) ^ 2 := by ring
  have hsmR : AEStronglyMeasurable
      (fun u : ℂ => (f u - f z') * ((u - z)⁻¹ ^ 2 - (u - z')⁻¹ ^ 2)) (volume.restrict Az) :=
    ((hcont.measurable.sub measurable_const).mul
      (((measurable_id.sub_const z).inv.pow_const 2).sub
        ((measurable_id.sub_const z').inv.pow_const 2))).aestronglyMeasurable.mono_measure
      Measure.restrict_le_self
  have hIR1 : IntegrableOn
      (fun u : ℂ => (f u - f z') * ((u - z)⁻¹ ^ 2 - (u - z')⁻¹ ^ 2)) Az volume := by
    refine integrableOn_of_norm_le_const hAzfin hAzm hsmR
      (M := 2 * C * ρ ^ α * ((2 * δ)⁻¹ ^ 2 + δ⁻¹ ^ 2)) ?_
    intro u hu
    have h1 : 2 * δ ≤ ‖u - z‖ := (hmemAz u).mp hu |>.1
    have h3 : δ ≤ ‖u - z'‖ := hδz' u hu
    have h2 : ‖u - z‖⁻¹ ≤ (2 * δ)⁻¹ := by
      rw [inv_le_inv₀ (by linarith : (0:ℝ) < ‖u - z‖) (by linarith : (0:ℝ) < 2 * δ)]
      exact h1
    have h4 : ‖u - z'‖⁻¹ ≤ δ⁻¹ := by
      rw [inv_le_inv₀ (by linarith : (0:ℝ) < ‖u - z'‖) (by linarith : (0:ℝ) < δ)]
      exact h3
    have hpos : (0:ℝ) < 2 * δ := by linarith
    have hpos' : (0:ℝ) < δ := hδ
    rw [norm_mul]
    calc ‖f u - f z'‖ * ‖(u - z)⁻¹ ^ 2 - (u - z')⁻¹ ^ 2‖
        ≤ (2 * C * ρ ^ α) * (‖u - z‖⁻¹ ^ 2 + ‖u - z'‖⁻¹ ^ 2) := by
          refine mul_le_mul (hbdd' u) ?_ (norm_nonneg _) (by positivity)
          calc ‖(u - z)⁻¹ ^ 2 - (u - z')⁻¹ ^ 2‖ ≤ ‖(u - z)⁻¹ ^ 2‖ + ‖(u - z')⁻¹ ^ 2‖ :=
                norm_sub_le _ _
            _ = ‖u - z‖⁻¹ ^ 2 + ‖u - z'‖⁻¹ ^ 2 := by rw [norm_pow, norm_inv, norm_pow, norm_inv]
      _ ≤ (2 * C * ρ ^ α) * ((2 * δ)⁻¹ ^ 2 + δ⁻¹ ^ 2) :=
          mul_le_mul_of_nonneg_left
            (add_le_add (pow_le_pow_left₀ (by positivity) h2 2) (pow_le_pow_left₀ (by positivity) h4 2))
            (by positivity)
      _ = 2 * C * ρ ^ α * ((2 * δ)⁻¹ ^ 2 + δ⁻¹ ^ 2) := by ring
  -- the substitution of f z by f z' on Az
  have hY : (∫ u in Az, (f u - f z) * ((u - z)⁻¹ ^ 2))
      = ∫ u in Az, (f u - f z') * ((u - z)⁻¹ ^ 2) := by
    have hdiff : (∫ u in Az, ((f u - f z) * ((u - z)⁻¹ ^ 2)
        - (f u - f z') * ((u - z)⁻¹ ^ 2))) = 0 := by
      rw [show (∫ u in Az, ((f u - f z) * ((u - z)⁻¹ ^ 2)
            - (f u - f z') * ((u - z)⁻¹ ^ 2)))
          = ∫ u in Az, (f z' - f z) * ((u - z)⁻¹ ^ 2) from
        setIntegral_congr_fun hAzm (fun u _ => by ring)]
      rw [integral_const_mul, hmean, mul_zero]
    have h0 : (∫ u in Az, (f u - f z) * ((u - z)⁻¹ ^ 2))
        - (∫ u in Az, (f u - f z') * ((u - z)⁻¹ ^ 2)) = 0 := by
      rw [← integral_sub hIAz1 hIAz2]
      exact hdiff
    exact sub_eq_zero.mp h0
  -- the split using the kernel (u - z')⁻¹^2
  have hsplitY : (∫ u in Az, (f u - f z') * ((u - z)⁻¹ ^ 2))
      = (∫ u in Az, (f u - f z') * ((u - z)⁻¹ ^ 2 - (u - z')⁻¹ ^ 2))
        + (∫ u in Az, (f u - f z') * ((u - z')⁻¹ ^ 2)) := by
    rw [show (∫ u in Az, (f u - f z') * ((u - z)⁻¹ ^ 2))
        = ∫ u in Az, ((f u - f z') * ((u - z)⁻¹ ^ 2 - (u - z')⁻¹ ^ 2)
            + (f u - f z') * ((u - z')⁻¹ ^ 2)) from
      setIntegral_congr_fun hAzm (fun u _ => by ring)]
    exact integral_add hIR1 hIR2
  have hJ : (∫ w in A, ((f (z + w) - f z) - (f (z' + w) - f z')) / w ^ 2)
      = (∫ u in Az, (f u - f z') * ((u - z)⁻¹ ^ 2 - (u - z')⁻¹ ^ 2))
        + ((∫ u in Az, (f u - f z') * ((u - z')⁻¹ ^ 2))
            - (∫ u in Az', (f u - f z') * ((u - z')⁻¹ ^ 2))) := by
    rw [hstep1, hsub1, hsub2, hY, hsplitY]
    abel
  have hfar := far_kernelDiff_bound hα hα1 hC hδ h2δρ hzz'
    (φ := fun u : ℂ => f u - f z') (fun u => hf u z')
  have hcres := crescent_bound hα hα1 hC hδ (by positivity) (by linarith) hδ4 hz hz' hzz' hfb hf hfsupp
  rw [hJ]
  calc ‖(∫ u in Az, (f u - f z') * ((u - z)⁻¹ ^ 2 - (u - z')⁻¹ ^ 2))
          + ((∫ u in Az, (f u - f z') * ((u - z')⁻¹ ^ 2))
              - (∫ u in Az', (f u - f z') * ((u - z')⁻¹ ^ 2)))‖
      ≤ ‖∫ u in Az, (f u - f z') * ((u - z)⁻¹ ^ 2 - (u - z')⁻¹ ^ 2)‖
        + ‖(∫ u in Az, (f u - f z') * ((u - z')⁻¹ ^ 2))
            - (∫ u in Az', (f u - f z') * ((u - z')⁻¹ ^ 2))‖ := norm_add_le _ _
    _ ≤ 24 * Real.pi * C * (3 / 2) ^ α * 2 ^ (α - 1) * δ ^ α / (1 - α)
        + (2 * Real.pi * C * 4 ^ α / α + 9 * Real.pi * C) * δ ^ α := add_le_add hfar hcres
    _ = (24 * Real.pi * C * (3 / 2) ^ α * 2 ^ (α - 1) / (1 - α)
          + 2 * Real.pi * C * 4 ^ α / α + 9 * Real.pi * C) * δ ^ α := by ring


/-- Explicit constant for the Calderón–Zygmund `far-field` plus `crescent` estimate:
`4π2^α/α + 24π(3/2)^α 2^{α-1}/(1-α) + 2π4^α/α + 9π`. -/
noncomputable def czAcoef (α : ℝ) : ℝ :=
  4 * Real.pi * 2 ^ α / α + 24 * Real.pi * (3 / 2) ^ α * 2 ^ (α - 1) / (1 - α)
    + 2 * Real.pi * 4 ^ α / α + 9 * Real.pi

/-- The uniform constant of the Hölder estimate for the Beurling transform:
`π⁻¹ * czAcoef α + 4 * 4^α/α`.  It depends only on `α`. -/
noncomputable def czConst (α : ℝ) : ℝ := Real.pi⁻¹ * czAcoef α + 4 * 4 ^ α / α

/-- **Hölder estimate for the Beurling transform with explicit constant.**
For `f` `α`-Hölder with constant `C`, supported in the disc of radius `ρ/2`, and
`z, z'` in the disc of radius `r` (`2r ≤ ρ`),
`‖S f z - S f z'‖ ≤ C * czConst α * ‖z - z'‖^α`. -/
theorem holder_estimate_explicit {ρ α C r : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hC : 0 ≤ C) (hr : 0 < r) (hrρ : 2 * r ≤ ρ) {f : ℂ → ℂ}
    (hf : ∀ x y : ℂ, ‖f x - f y‖ ≤ C * ‖x - y‖ ^ α) (hfsupp : SupportedInBall (ρ / 2) f) :
    ∀ z ∈ Metric.ball (0 : ℂ) r, ∀ z' ∈ Metric.ball (0 : ℂ) r,
      ‖beurlingTransform ρ f z - beurlingTransform ρ f z'‖ ≤ C * czConst α * ‖z - z'‖ ^ α := by
  have hρ : 0 < ρ := by linarith
  have hcont : Continuous f := continuous_of_holder hα hC hf
  have hbdd : ∀ x : ℂ, ‖f x‖ ≤ C * ρ ^ α := by
    intro x
    by_cases hx : ‖x‖ < ρ / 2
    · have h1 : f (((ρ / 2 : ℝ)) : ℂ) = 0 := by
        apply hfsupp
        rw [Complex.norm_real, Real.norm_of_nonneg (by linarith : (0:ℝ) ≤ ρ / 2)]
      have h2 : ‖(((ρ / 2 : ℝ)) : ℂ)‖ = ρ / 2 := by
        rw [Complex.norm_real, Real.norm_of_nonneg (by linarith : (0:ℝ) ≤ ρ / 2)]
      have hd : ‖x - (((ρ / 2 : ℝ)) : ℂ)‖ ≤ ρ := by
        calc ‖x - (((ρ/2:ℝ)) : ℂ)‖ ≤ ‖x‖ + ‖(((ρ/2:ℝ)) : ℂ)‖ := norm_sub_le _ _
          _ = ‖x‖ + ρ/2 := by rw [h2]
          _ ≤ ρ/2 + ρ/2 := by linarith
          _ = ρ := by ring
      calc ‖f x‖ = ‖f x - f (((ρ/2:ℝ)) : ℂ)‖ := by rw [h1, sub_zero]
        _ ≤ C * ‖x - (((ρ/2:ℝ)) : ℂ)‖ ^ α := hf x _
        _ ≤ C * ρ ^ α := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) hd hα.le) hC
    · rw [hfsupp x (not_lt.mp hx), norm_zero]
      exact mul_nonneg hC (Real.rpow_nonneg hρ.le α)
  intro z hz z' hz'
  have hzr : ‖z‖ < r := by simpa [Metric.mem_ball, dist_eq_norm] using hz
  have hz'r : ‖z'‖ < r := by simpa [Metric.mem_ball, dist_eq_norm] using hz'
  by_cases hzz : z = z'
  · subst hzz
    simp [Real.zero_rpow (ne_of_gt hα)]
  · have hδpos : 0 < ‖z - z'‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzz)
    set δ := ‖z - z'‖ with hδ
    have hδp : 0 < δ := hδpos
    by_cases hδ4 : δ ≤ ρ / 4
    · -- ===== CASE A =====
      have h2δρ : 2 * δ ≤ ρ := by linarith
      set N : ℂ → ℂ := fun w => (f (z + w) - f z) - (f (z' + w) - f z') with hN
      have hN_bound : ∀ w : ℂ, ‖N w‖ ≤ 2 * C * ‖w‖ ^ α := by
        intro w
        have ha : ‖f (z + w) - f z‖ ≤ C * ‖w‖ ^ α := by
          have h := hf (z + w) z; rwa [add_sub_cancel_left] at h
        have hb : ‖f (z' + w) - f z'‖ ≤ C * ‖w‖ ^ α := by
          have h := hf (z' + w) z'; rwa [add_sub_cancel_left] at h
        calc ‖N w‖ = ‖(f (z + w) - f z) - (f (z' + w) - f z')‖ := by rw [hN]
          _ ≤ ‖f (z + w) - f z‖ + ‖f (z' + w) - f z'‖ := norm_sub_le _ _
          _ ≤ C * ‖w‖ ^ α + C * ‖w‖ ^ α := add_le_add ha hb
          _ = 2 * C * ‖w‖ ^ α := by ring
      have hIntz : IntegrableOn (fun w : ℂ => (f (z + w) - f z) / w^2) (Metric.ball 0 ρ) :=
        integrableOn_beurlingIntegrand hα hC hf z
      have hIntz' : IntegrableOn (fun w : ℂ => (f (z' + w) - f z') / w^2) (Metric.ball 0 ρ) :=
        integrableOn_beurlingIntegrand hα hC hf z'
      have hSf : beurlingTransform ρ f z - beurlingTransform ρ f z'
          = -((Real.pi : ℂ))⁻¹ * ((∫ w in Metric.ball 0 ρ, (f (z + w) - f z) / w^2)
            - (∫ w in Metric.ball 0 ρ, (f (z' + w) - f z') / w^2)) := by
        simp only [beurlingTransform]; ring
      have hdiff : (∫ w in Metric.ball 0 ρ, (f (z + w) - f z) / w^2)
            - (∫ w in Metric.ball 0 ρ, (f (z' + w) - f z') / w^2)
          = ∫ w in Metric.ball 0 ρ, N w / w^2 := by
        rw [← integral_sub hIntz hIntz']
        refine setIntegral_congr_fun measurableSet_ball (fun w _ => ?_)
        simp only [hN]; ring
      have hIntN_ball : IntegrableOn (fun w : ℂ => N w / w^2) (Metric.ball 0 ρ) :=
        (integrableOn_congr_fun
          (f := fun w : ℂ => (f (z + w) - f z) / w^2 - (f (z' + w) - f z') / w^2)
          (g := fun w : ℂ => N w / w^2) (fun w _ => by simp only [hN]; ring)
          measurableSet_ball).mp (hIntz.sub hIntz')
      set Areg : Set ℂ := {w : ℂ | 2 * δ ≤ ‖w‖ ∧ ‖w‖ < ρ} with hAreg
      set S1 : Set ℂ := Metric.ball (0:ℂ) ρ ∩ Metric.ball (0:ℂ) (2*δ) with hS1
      have hAregm : MeasurableSet Areg := by rw [hAreg]; measurability
      have hS1m : MeasurableSet S1 := by
        rw [hS1]; exact measurableSet_ball.inter measurableSet_ball
      have hAreg_ball : Areg ⊆ Metric.ball (0:ℂ) ρ := by
        intro w hw
        rw [hAreg] at hw
        rw [Metric.mem_ball, dist_zero_right]
        exact hw.2
      have hS1_ball : S1 ⊆ Metric.ball (0:ℂ) ρ := by rw [hS1]; exact inter_subset_left
      have hball_eq : Metric.ball (0:ℂ) ρ = S1 ∪ Areg := by
        ext w
        simp only [hS1, hAreg, Metric.mem_ball, dist_zero_right, Set.mem_union,
          Set.mem_inter_iff, Set.mem_setOf_eq]
        constructor
        · intro hw
          rcases lt_or_ge (‖w‖) (2*δ) with h | h
          · exact Or.inl ⟨hw, h⟩
          · exact Or.inr ⟨h, hw⟩
        · rintro (⟨h1, _⟩ | ⟨_, h2⟩)
          · exact h1
          · exact h2
      have hdisj : Disjoint S1 Areg := by
        rw [Set.disjoint_left]
        intro w hw1 hw2
        rw [hS1] at hw1
        rw [hAreg] at hw2
        simp only [Set.mem_inter_iff, Metric.mem_ball, dist_zero_right, Set.mem_setOf_eq] at hw1 hw2
        linarith [hw1.2, hw2.1]
      have hIntS1 : IntegrableOn (fun w : ℂ => N w / w^2) S1 := hIntN_ball.mono_set hS1_ball
      have hIntAreg : IntegrableOn (fun w : ℂ => N w / w^2) Areg := hIntN_ball.mono_set hAreg_ball
      have hsplit : ∫ w in Metric.ball 0 ρ, N w / w^2
          = (∫ w in S1, N w / w^2) + (∫ w in Areg, N w / w^2) := by
        rw [hball_eq]
        simpa using setIntegral_union hdisj hAregm hIntS1 hIntAreg
      have hinner : ‖∫ w in S1, N w / w^2‖ ≤ 2 * C * (2 * Real.pi * (2*δ) ^ α / α) := by
        rw [hS1]; exact inner_bound hα hα1 hC hδp hN_bound
      have houter : ‖∫ w in Areg, N w / w^2‖
          ≤ (24 * Real.pi * C * (3 / 2) ^ α * 2 ^ (α - 1) / (1 - α)
              + 2 * Real.pi * C * 4 ^ α / α + 9 * Real.pi * C) * δ ^ α := by
        have h := outer_region_bound hα hα1 hC hδp hδ4 hδ.symm (by linarith) (by linarith)
          hbdd hf hfsupp
        rw [hAreg]
        simpa [hN] using h
      have hmain : ‖∫ w in Metric.ball 0 ρ, N w / w^2‖ ≤ C * czAcoef α * δ ^ α := by
        rw [hsplit]
        calc ‖(∫ w in S1, N w / w^2) + (∫ w in Areg, N w / w^2)‖
            ≤ ‖∫ w in S1, N w / w^2‖ + ‖∫ w in Areg, N w / w^2‖ := norm_add_le _ _
          _ ≤ 2 * C * (2 * Real.pi * (2*δ) ^ α / α)
              + (24 * Real.pi * C * (3 / 2) ^ α * 2 ^ (α - 1) / (1 - α)
                  + 2 * Real.pi * C * 4 ^ α / α + 9 * Real.pi * C) * δ ^ α :=
                add_le_add hinner houter
          _ = C * czAcoef α * δ ^ α := by
                rw [show (2*δ)^α = 2^α * δ^α from by
                  rw [Real.mul_rpow (by norm_num) (le_of_lt hδp)]]
                simp only [czAcoef]; ring
      rw [hSf, hdiff, norm_mul, norm_neg]
      have hpi : ‖((Real.pi:ℂ))⁻¹‖ = Real.pi⁻¹ := by
        rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
      rw [hpi]
      have hcz : Real.pi⁻¹ * (C * czAcoef α) ≤ C * czConst α := by
        rw [czConst]
        have h6 : (0:ℝ) ≤ 4 * 4 ^ α / α := by positivity
        calc Real.pi⁻¹ * (C * czAcoef α) = C * (Real.pi⁻¹ * czAcoef α) := by ring
          _ ≤ C * (Real.pi⁻¹ * czAcoef α + 4 * 4 ^ α / α) :=
              mul_le_mul_of_nonneg_left (le_add_of_nonneg_right h6) hC
      calc Real.pi⁻¹ * ‖∫ w in Metric.ball 0 ρ, N w / w^2‖
          ≤ Real.pi⁻¹ * (C * czAcoef α * δ ^ α) :=
            mul_le_mul_of_nonneg_left hmain (by positivity)
        _ = (Real.pi⁻¹ * (C * czAcoef α)) * δ ^ α := by ring
        _ ≤ (C * czConst α) * δ ^ α :=
            mul_le_mul_of_nonneg_right hcz (Real.rpow_nonneg hδp.le α)
    · -- ===== CASE B =====
      push_neg at hδ4
      have hδge : ρ / 4 ≤ δ := le_of_lt hδ4
      have h1 : ‖beurlingTransform ρ f z‖ ≤ 2 * C * ρ ^ α / α :=
        norm_beurlingTransform_le hα hC hf (by linarith [hzr])
      have h2 : ‖beurlingTransform ρ f z'‖ ≤ 2 * C * ρ ^ α / α :=
        norm_beurlingTransform_le hα hC hf (by linarith [hz'r])
      have hbd : ‖beurlingTransform ρ f z - beurlingTransform ρ f z'‖ ≤ 4 * C * ρ ^ α / α := by
        calc _ ≤ ‖beurlingTransform ρ f z‖ + ‖beurlingTransform ρ f z'‖ := norm_sub_le _ _
          _ ≤ 2*C*ρ^α/α + 2*C*ρ^α/α := add_le_add h1 h2
          _ = 4*C*ρ^α/α := by ring
      have hpow : ρ^α / 4^α ≤ δ^α := by
        rw [← Real.div_rpow hρ.le (by norm_num : (0:ℝ) ≤ 4)]
        exact Real.rpow_le_rpow (by positivity) hδge hα.le
      have hfac : 4 * C * 4 ^ α / α * (ρ^α / 4^α) = 4 * C * ρ ^ α / α := by
        have h4α : (4:ℝ)^α ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos (by norm_num) α)
        rw [div_mul_div_comm]
        rw [show (4 * C * 4 ^ α) * ρ^α = (4 * C * ρ^α) * 4^α from by ring]
        rw [mul_div_mul_right _ _ h4α]
      have hmain : 4 * C * ρ ^ α / α ≤ C * czConst α * δ ^ α := by
        have h4 : (0:ℝ) ≤ 4 * C * 4 ^ α / α := by positivity
        have h5 : 4 * C * 4 ^ α / α ≤ C * czConst α := by
          rw [czConst]
          have h6 : (0:ℝ) ≤ Real.pi⁻¹ * czAcoef α := by rw [czAcoef]; positivity
          calc 4 * C * 4 ^ α / α = C * (4 * 4 ^ α / α) := by ring
            _ ≤ C * (Real.pi⁻¹ * czAcoef α + 4 * 4 ^ α / α) :=
                mul_le_mul_of_nonneg_left (le_add_of_nonneg_left h6) hC
        calc 4 * C * ρ ^ α / α = 4 * C * 4 ^ α / α * (ρ^α / 4^α) := hfac.symm
          _ ≤ 4 * C * 4 ^ α / α * δ^α := mul_le_mul_of_nonneg_left hpow h4
          _ ≤ C * czConst α * δ ^ α := mul_le_mul_of_nonneg_right h5 (Real.rpow_nonneg hδp.le α)
      linarith [hbd, hmain]

end BeurlingCZ

/-- **Hölder (Calderón–Zygmund) estimate for the Beurling transform, with a constant uniform
in `f`.**

There is `C = C(ρ,α) > 0` — depending only on `ρ` and `α`, in particular not on `f` nor on its
Hölder constant — such that for every `f : ℂ → ℂ` that is `α`-Hölder with constant `K` and
supported in the disc of radius `ρ/2`, the Beurling transform `S f = beurlingTransform ρ f` of
`Submission/Work/CR/Flat/Cauchy.lean` satisfies `‖S f x - S f y‖ ≤ C K ‖x - y‖^α` for all
`x, y` in the disc of radius `ρ/2`.

Uniformity of the constant in `f` (with the bound *linear* in `K`) is the whole point: it is what
the Schauder estimate `holderNorm 1 α (cauchyTransform ρ f) (ball 0 (ρ/2)) ≤ C' (‖f‖_∞ + [f]_α)`
needs, whereas the existential-constant statement `norm_beurlingTransform_sub_le` is not enough
for it.

Proof route (classical Calderón–Zygmund).  Put `δ = ‖x - y‖`, `N w = (f (x+w) - f x) - (f (y+w) - f y)`,
so that `S f x - S f y = -(1/π) ∫_{‖w‖<ρ} N w / w² dw` and
`‖N w‖ ≤ 2 K ‖w‖^α` (four-point) as well as `‖N w‖ ≤ 2 K δ^α`.  Split at `‖w‖ = 2δ`:
`∫_{‖w‖<2δ} ‖N w‖/‖w‖² ≤ 2K · 2π(2δ)^α/α = O(Kδ^α)`, and for the outer region rewrite
`∫_{2δ ≤ ‖w‖ < ρ} N w / w² dw` by the translation substitution `w ↦ w + (x-y)` as a difference of
two integrals with the *same* numerator against the two kernels `(ζ-x)⁻²` and `(ζ-y)⁻²`; on
`‖ζ - x‖ ≥ 2δ` the kernel difference obeys `‖(ζ-x)⁻² - (ζ-y)⁻²‖ ≤ 16 δ ‖ζ-x‖⁻³`, which against the
Hölder bound `‖f ζ - f x‖ ≤ K ‖ζ-x‖^α` gives
`16 K δ ∫_{2δ}^{…} r^{α-3} r dr = O(K δ^α/(1-α))` (the constant term of the numerator is killed by
`∫_{annulus} dw/w² = 0`; the remaining "crescent"/domain mismatch contributes `O(Kδ^α)` as well,
since `‖f - f x‖ ≤ K ρ^α` there).  All constants are functions of `α` and `ρ` only — this is
exactly the computation `norm_beurlingTransform_sub_le.lean` performs with an explicit constant
`Acoef` (linear in the Hölder constant `C`); if that module is already sorry-free you may import
it and reuse its auxiliary lemmas (`inner_bound`, `far_kernelDiff_bound`, `crescent_bound`,
`integral_inv_sq_annulus`, `integral_norm_rpow_annulus`, `setIntegral_translate`,
`integrableOn_beurlingIntegrand`, ...) and its explicit `Acoef`, replacing the existential `K` by
the explicit constant.  Otherwise this file must be self-contained. -/
theorem norm_beurlingTransform_sub_le_explicit {ρ α : ℝ} (hρ : 0 < ρ) (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ {K : ℝ}, 0 ≤ K → ∀ {f : ℂ → ℂ},
      (∀ x y : ℂ, ‖f x - f y‖ ≤ K * ‖x - y‖ ^ α) → SupportedInBall (ρ / 2) f →
      ∀ x ∈ Metric.ball (0 : ℂ) (ρ / 2), ∀ y ∈ Metric.ball (0 : ℂ) (ρ / 2),
        ‖beurlingTransform ρ f x - beurlingTransform ρ f y‖ ≤ C * K * ‖x - y‖ ^ α := by
  refine ⟨BeurlingCZ.czConst α, ?_, ?_⟩
  · rw [BeurlingCZ.czConst]
    have h1 : (0:ℝ) ≤ Real.pi⁻¹ * BeurlingCZ.czAcoef α := by
      rw [BeurlingCZ.czAcoef]; positivity
    have h2 : (0:ℝ) < 4 * 4 ^ α / α := by positivity
    linarith
  · intro K hK f hf hfsupp x hx y hy
    have h := BeurlingCZ.holder_estimate_explicit hα hα1 hK (by linarith) (by linarith)
      hf hfsupp x hx y hy
    calc ‖beurlingTransform ρ f x - beurlingTransform ρ f y‖
        ≤ K * BeurlingCZ.czConst α * ‖x - y‖ ^ α := h
      _ = BeurlingCZ.czConst α * K * ‖x - y‖ ^ α := by ring

end Work.CR.Flat.Cauchy
