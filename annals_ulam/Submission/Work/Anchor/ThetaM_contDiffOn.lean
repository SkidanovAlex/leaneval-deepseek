import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.KernelExt.Defs
import Submission.Work.OddVolterra.Kernel.Diag
import Submission.Work.OddVolterra.KernelExt.Rnu_contDiff
import Submission.Work.OddVolterra.Existence.hquot_contDiff
import Submission.Work.Analysis.Calculus.contDiff_dslope
import Submission.Work.Geometry.Ulam.ulam_g2ds

/-!
# Smoothness of the manifest odd `Θ`-data on the transition-slope state region

The manifest (smooth) representative `KernelExt.ThetaM n h s σ z` of the odd-case `Θ`-data is

`ThetaM = ![-z 2, -z 3, -(∂_s G2M(·,σ,z)) s (row 0), -(∂_s G2M(·,σ,z)) s (row 1)]`,

where `G2M` is the `τ`-average `∫_0^1 KvecM n h (s+τ(σ-s)) σ z / √(τ(1-τ)) dτ` of the manifest Abel
kernel.  This file proves that `(s,σ,z) ↦ ThetaM n h s σ z` is `C^∞` on the state region

`9/20 < s < 21/20`, `9/20 < σ < 21/20`, `|z 0| > 1/5`, `|z 1| > 1/5`,

which contains the region of the statement (there `s,σ ∈ (481/1000, 97/100)` and
`‖z - baseState σ‖ < 9/20`, while `profileX σ > 13/20`, so `|z i| > 13/20 - 9/20 = 1/5`).

The ingredients are

* positivity of the Abel radicand `krad h σ t a` whenever `σ + a > 1/10` and `|t| ≥ 1/5`, which uses
  only the `C⁰`/`C¹`-smallness of `h` (the support hypothesis is *not* needed, and is absent from
  the statement of `ThetaM_contDiffOn`);
* smoothness of the manifest kernels `J1M`, `J2M`, `Kden` and hence of `KvecM`, in the abstract form
  `contDiffOn_KvecM_comp` (composing the manifest kernel with `C^∞` parameter maps);
* the `τ = sin²θ` substitution `AbelWeight_subst`, which removes the endpoint singularity of the
  `τ`-weight `(√(τ(1-τ)))⁻¹`, reducing the smoothness of `G2M` in the parameters to the smoothness
  of a parametric interval integral over the *compact* interval `[0, π/2]`
  (`contDiffOn_intervalIntegral_parametric`);
* the identification of the first-slot derivative with the first Fréchet partial derivative
  (`contDiffOn_deriv_slice_fst`).
-/

namespace Work.Anchor

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

noncomputable section

open Work.OddVolterra

/-! ## The region -/

/-- The open region on which the manifest odd `Θ`-data is smooth: the two slope slots in
`(9/20, 21/20)` and the two chord endpoints of modulus `> 1/5`. -/
def Good : Set (ℝ × ℝ × St) :=
  {q | 9 / 20 < q.1 ∧ q.1 < 21 / 20 ∧ 9 / 20 < q.2.1 ∧ q.2.1 < 21 / 20 ∧
    1 / 5 < |q.2.2 0| ∧ 1 / 5 < |q.2.2 1|}

lemma isOpen_Good : IsOpen Good := by
  have hc2 : Continuous (fun q : ℝ × ℝ × St => q.2.1) := by fun_prop
  have hc0 : Continuous (fun q : ℝ × ℝ × St => |q.2.2 0|) := by fun_prop
  have hc1 : Continuous (fun q : ℝ × ℝ × St => |q.2.2 1|) := by fun_prop
  rw [Good]
  repeat' apply IsOpen.inter
  · exact isOpen_lt continuous_const continuous_fst
  · exact isOpen_lt continuous_fst continuous_const
  · exact isOpen_lt continuous_const hc2
  · exact isOpen_lt hc2 continuous_const
  · exact isOpen_lt continuous_const hc0
  · exact isOpen_lt continuous_const hc1

/-- On the slope window `(481/1000, 97/100)` the ball profile is larger than `13/20`. -/
lemma profileX_gt_thirteen_twentieths {σ : ℝ} (h1 : 481 / 1000 < σ) (h2 : σ < 97 / 100) :
    13 / 20 < Commons.Geometry.Ulam.profileX σ := by
  have hσ2 : σ ^ 2 < 1 := by
    have h3 : |σ| < 1 := by rw [abs_lt]; constructor <;> linarith
    nlinarith [abs_nonneg σ, h3]
  have hsq : (13 / 20 : ℝ) ^ 2 < Commons.Geometry.Ulam.profileX σ ^ 2 := by
    rw [Commons.Geometry.Ulam.profileX_sq]
    have h4 : (1 : ℝ) / 2 < 1 / (1 + σ ^ 2) := by
      rw [div_lt_div_iff₀ (by norm_num) (by positivity)]
      linarith
    have h5 : (13 / 20 : ℝ) ^ 2 < 1 / 2 := by norm_num
    linarith
  nlinarith [hsq, Commons.Geometry.Ulam.profileX_pos σ (by linarith)]

/-- The region of the statement is contained in `Good`. -/
lemma target_subset_Good {p : ℝ × ℝ × St}
    (hp1 : p.1 ∈ Set.Ioo (481 / 1000 : ℝ) (97 / 100))
    (hp2 : p.2.1 ∈ Set.Ioo (481 / 1000 : ℝ) (97 / 100))
    (hp3 : ‖p.2.2 - baseState p.2.1‖ < 9 / 20) : p ∈ Good := by
  refine ⟨by linarith [hp1.1], by linarith [hp1.2], by linarith [hp2.1], by linarith [hp2.2],
    ?_, ?_⟩
  · have h2 : |p.2.2 0 - Commons.Geometry.Ulam.profileX p.2.1| < 9 / 20 := by
      have h := norm_le_pi_norm (p.2.2 - baseState p.2.1) 0
      rw [Pi.sub_apply, Real.norm_eq_abs] at h
      have hb : baseState p.2.1 0 = Commons.Geometry.Ulam.profileX p.2.1 := rfl
      rw [hb] at h
      exact lt_of_le_of_lt h hp3
    have hprof : 13 / 20 < Commons.Geometry.Ulam.profileX p.2.1 :=
      profileX_gt_thirteen_twentieths hp2.1 hp2.2
    have h4 : (1 : ℝ) / 5 < p.2.2 0 := by
      have h5 : Commons.Geometry.Ulam.profileX p.2.1 - 9 / 20 < p.2.2 0 := by
        have := (abs_lt.mp h2).1
        linarith
      linarith
    exact lt_of_lt_of_le h4 (le_abs_self _)
  · have h2 : |p.2.2 1 - Commons.Geometry.Ulam.profileX p.2.1| < 9 / 20 := by
      have h := norm_le_pi_norm (p.2.2 - baseState p.2.1) 1
      rw [Pi.sub_apply, Real.norm_eq_abs] at h
      have hb : baseState p.2.1 1 = Commons.Geometry.Ulam.profileX p.2.1 := rfl
      rw [hb] at h
      exact lt_of_le_of_lt h hp3
    have hprof : 13 / 20 < Commons.Geometry.Ulam.profileX p.2.1 :=
      profileX_gt_thirteen_twentieths hp2.1 hp2.2
    have h4 : (1 : ℝ) / 5 < p.2.2 1 := by
      have h5 : Commons.Geometry.Ulam.profileX p.2.1 - 9 / 20 < p.2.2 1 := by
        have := (abs_lt.mp h2).1
        linarith
      linarith
    exact lt_of_lt_of_le h4 (le_abs_self _)

/-! ## Positivity of the Abel radicand

Only the `C⁰`/`C¹` smallness of `h` is used; no support hypothesis is needed. -/

/-- The mean `hquot h s σ = ∫_0^1 h'(s + τ(σ-s)) dτ` is bounded by any bound of `|h'|`. -/
lemma abs_hquot_le' {h : ℝ → ℝ} {C : ℝ} (hC : ∀ x : ℝ, |deriv h x| ≤ C) (s σ : ℝ) :
    |hquot h s σ| ≤ C := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun τ : ℝ => deriv h (s + τ * (σ - s))) (C := C) (a := (0 : ℝ)) (b := 1)
    (fun x _ => by simpa [Real.norm_eq_abs] using hC (s + x * (σ - s)))
  rw [hquot]
  simpa using h

/-- **Positivity of the Abel radicand.**  If `|h|, |h'| ≤ 1/100` then for `σ + a > 1/10` and
`|t| ≥ 1/5` both factors of `krad h σ t a = (t + H(a,σ)) (L_σ(t) + L_a(t))` have the sign of `t`,
hence their product is positive. -/
theorem krad_pos_of_add_pos' {h : ℝ → ℝ}
    (hsmall : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100)
    {a σ t : ℝ} (hS : 1 / 10 < σ + a) (ht : 1 / 5 ≤ |t|) : 0 < krad h σ t a := by
  have hh0 : ∀ x : ℝ, |h x| ≤ 1 / 100 := fun x => hsmall 0 (by norm_num) x
  have hh1 : ∀ x : ℝ, |deriv h x| ≤ 1 / 100 := by
    intro x; simpa using hsmall 1 (by norm_num) x
  have hbnd : |hquot h a σ| ≤ 1 / 100 := abs_hquot_le' hh1 a σ
  have hb := abs_le.mp hbnd
  have hhl : |h σ + h a| ≤ 1 / 50 := by
    have h1 := abs_le.mp (hh0 σ)
    have h2 := abs_le.mp (hh0 a)
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hSpos : 0 < σ + a := by linarith
  have hsumlt : |h σ + h a| < (σ + a) * (1 / 5) := by
    have h1 : (1 / 10 : ℝ) * (1 / 5) ≤ (σ + a) * (1 / 5) :=
      mul_le_mul_of_nonneg_right (le_of_lt hS) (by norm_num)
    have h2 : (1 / 10 : ℝ) * (1 / 5) = 1 / 50 := by norm_num
    linarith [hhl, h1, h2]
  have hhline : line h σ t + line h a t = (σ + a) * t + (h σ + h a) := by
    unfold line; ring
  rw [krad_apply, hhline]
  rcases lt_trichotomy t 0 with htn | htz | htp
  · have htle : t ≤ -(1 / 5) := by
      have h := ht; rw [abs_of_neg htn] at h; linarith
    have h1 : t + hquot h a σ < 0 := by linarith [hb.2]
    have hmul : (σ + a) * t ≤ -((σ + a) * (1 / 5)) := by
      have h := mul_le_mul_of_nonneg_left htle (le_of_lt hSpos)
      rwa [show (σ + a) * (-(1 / 5)) = -((σ + a) * (1 / 5)) by ring] at h
    have h2 : (σ + a) * t + (h σ + h a) < 0 := by
      have h3 : h σ + h a < (σ + a) * (1 / 5) := lt_of_le_of_lt (le_abs_self _) hsumlt
      linarith
    exact mul_pos_of_neg_of_neg h1 h2
  · rw [htz] at ht; norm_num at ht
  · have htge : 1 / 5 ≤ t := by
      have h := ht; rwa [abs_of_pos htp] at h
    have h1 : 0 < t + hquot h a σ := by linarith [hb.1]
    have hmul : (σ + a) * (1 / 5) ≤ (σ + a) * t :=
      mul_le_mul_of_nonneg_left htge (le_of_lt hSpos)
    have h2 : 0 < (σ + a) * t + (h σ + h a) := by
      have h3 : -((σ + a) * (1 / 5)) < h σ + h a := by
        have h4 : -((σ + a) * (1 / 5)) < -|h σ + h a| := by linarith
        linarith [neg_abs_le (h σ + h a)]
      linarith
    exact mul_pos h1 h2

end

end Work.Anchor


namespace Work.Anchor

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

noncomputable section

/-! ## The `τ = sin²θ` substitution for the Abel weight -/

/-- Derivative of `sin²`. -/
lemma hasDerivAt_sin_sq (x : ℝ) :
    HasDerivAt (fun θ : ℝ => Real.sin θ ^ 2) (2 * Real.sin x * Real.cos x) x := by
  have h : HasDerivAt (fun θ : ℝ => Real.sin θ * Real.sin θ)
      (Real.cos x * Real.sin x + Real.sin x * Real.cos x) x :=
    (Real.hasDerivAt_sin x).mul (Real.hasDerivAt_sin x)
  have h2 : Real.cos x * Real.sin x + Real.sin x * Real.cos x
      = 2 * Real.sin x * Real.cos x := by ring
  rw [h2] at h
  have hfun : (fun θ : ℝ => Real.sin θ * Real.sin θ) = fun θ : ℝ => Real.sin θ ^ 2 := by
    funext θ; ring
  rwa [hfun] at h

/-- **The `τ = sin²θ` change of variables for the Abel weight.**  For a kernel `K` continuous on
`[0,1]`, the singular weighted integral `∫_0^1 K τ (τ(1-τ))^{-1/2} dτ` equals the continuous
parametric integral `2 ∫_0^{π/2} K (sin²θ) dθ`; this removes the endpoint singularity. -/
theorem AbelWeight_subst {K : ℝ → ℝ} (hK : ContinuousOn K (Set.Icc (0 : ℝ) 1)) :
    (∫ τ in (0 : ℝ)..1, K τ / Real.sqrt (τ * (1 - τ))) =
      ∫ θ in (0 : ℝ)..(Real.pi / 2), 2 * K (Real.sin θ ^ 2) := by
  have hpi : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hK
  have hCnn : 0 ≤ C := le_trans (norm_nonneg (K 0)) (hC 0 ⟨le_rfl, by norm_num⟩)
  have hw : Integrable (fun τ : ℝ => (Real.sqrt (τ * (1 - τ)))⁻¹)
      (volume.restrict (Set.Ioo (0 : ℝ) 1)) := by
    have h := (intervalIntegrable_iff.mp (Commons.Geometry.Ulam.intervalIntegrable_abel_weight))
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1), IntegrableOn,
      ← Measure.restrict_congr_set (Ioo_ae_eq_Ioc (μ := volume) (a := (0 : ℝ)) (b := 1))] at h
    exact h
  have hgIoo : Integrable (fun τ : ℝ => K τ / Real.sqrt (τ * (1 - τ)))
      (volume.restrict (Set.Ioo (0 : ℝ) 1)) := by
    refine Integrable.mono' (hw.const_mul C) ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioo
      refine ContinuousOn.div ?_ ?_ ?_
      · exact hK.mono (fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩)
      · exact ContinuousOn.sqrt (by fun_prop)
      · intro x hx
        exact ne_of_gt (Real.sqrt_pos.mpr (by nlinarith [hx.1, hx.2]))
    · rw [ae_restrict_iff' measurableSet_Ioo]
      filter_upwards with τ hτ
      have hsqrt_pos : 0 < Real.sqrt (τ * (1 - τ)) := Real.sqrt_pos.mpr (by nlinarith [hτ.1, hτ.2])
      have h1 : |K τ| ≤ C := by
        have := hC τ ⟨le_of_lt hτ.1, le_of_lt hτ.2⟩
        rwa [Real.norm_eq_abs] at this
      rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (Real.sqrt_nonneg _), div_le_iff₀ hsqrt_pos,
        mul_assoc, inv_mul_cancel₀ (ne_of_gt hsqrt_pos), mul_one]
      exact h1
  have hgIcc : IntegrableOn (fun τ : ℝ => K τ / Real.sqrt (τ * (1 - τ)))
      (Set.Icc (0 : ℝ) 1) := by
    rw [IntegrableOn]
    rw [← Measure.restrict_congr_set (Ioc_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := 1)),
      ← Measure.restrict_congr_set (Ioo_ae_eq_Ioc (μ := volume) (a := (0 : ℝ)) (b := 1))]
    exact hgIoo
  set g : ℝ → ℝ := fun τ => K τ / Real.sqrt (τ * (1 - τ)) with hgdef
  set f : ℝ → ℝ := fun θ => Real.sin θ ^ 2 with hfdef
  set f' : ℝ → ℝ := fun θ => 2 * Real.sin θ * Real.cos θ with hf'def
  have hf : ContinuousOn f (Set.uIcc (0 : ℝ) (Real.pi / 2)) := by
    rw [hfdef]; fun_prop
  have hff' : ∀ x ∈ Set.Ioo (min (0 : ℝ) (Real.pi / 2)) (max (0 : ℝ) (Real.pi / 2)),
      HasDerivWithinAt f (f' x) (Set.Ioi x) x := by
    intro x _
    rw [hfdef, hf'def]
    exact (hasDerivAt_sin_sq x).hasDerivWithinAt
  have hprod : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      0 < Real.sin θ ^ 2 * (1 - Real.sin θ ^ 2) := by
    intro θ hθ
    have hsin_pos : 0 < Real.sin θ :=
      Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
    have hcos_pos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1], hθ.2⟩
    have h1 : 1 - Real.sin θ ^ 2 = Real.cos θ ^ 2 := by linarith [Real.sin_sq_add_cos_sq θ]
    rw [h1]
    exact mul_pos (by positivity) (by positivity)
  have hmemIoo : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Real.sin θ ^ 2 ∈ Set.Ioo (0 : ℝ) 1 := by
    intro θ hθ
    have hsin_pos : 0 < Real.sin θ :=
      Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
    have hcos_pos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1], hθ.2⟩
    refine ⟨by positivity, ?_⟩
    nlinarith [Real.sin_sq_add_cos_sq θ, sq_pos_of_ne_zero hcos_pos.ne']
  have hg_cont : ContinuousOn g (f '' Set.Ioo (min (0 : ℝ) (Real.pi / 2))
      (max (0 : ℝ) (Real.pi / 2))) := by
    rw [min_eq_left hpi, max_eq_right hpi, hgdef]
    refine ContinuousOn.div ?_ ?_ ?_
    · refine hK.mono ?_
      rintro x ⟨θ, hθ, rfl⟩
      exact ⟨le_of_lt (hmemIoo θ hθ).1, le_of_lt (hmemIoo θ hθ).2⟩
    · exact ContinuousOn.sqrt (by fun_prop)
    · rintro x ⟨θ, hθ, rfl⟩
      exact ne_of_gt (Real.sqrt_pos.mpr (hprod θ hθ))
  have hg1 : IntegrableOn g (f '' Set.uIcc (0 : ℝ) (Real.pi / 2)) := by
    have hsub : f '' Set.uIcc (0 : ℝ) (Real.pi / 2) ⊆ Set.uIcc (0 : ℝ) 1 := by
      rintro τ ⟨θ, -, rfl⟩
      rw [hfdef, Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      exact ⟨sq_nonneg _, Real.sin_sq_le_one θ⟩
    have : IntegrableOn g (Set.uIcc (0 : ℝ) 1) := by
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      exact hgdef ▸ hgIcc
    exact this.mono_set hsub
  have hcontRHS : ContinuousOn (fun θ : ℝ => 2 * K (Real.sin θ ^ 2))
      (Set.uIcc (0 : ℝ) (Real.pi / 2)) := by
    rw [Set.uIcc_of_le hpi]
    refine continuousOn_const.mul ?_
    refine hK.comp (Real.continuous_sin.pow 2).continuousOn ?_
    intro θ _
    exact ⟨sq_nonneg _, Real.sin_sq_le_one θ⟩
  have hg2 : IntegrableOn (fun x : ℝ => (g ∘ f) x * f' x) (Set.uIcc (0 : ℝ) (Real.pi / 2)) := by
    rw [Set.uIcc_of_le hpi, IntegrableOn,
      ← Measure.restrict_congr_set (Ioc_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := Real.pi / 2))]
    have hint : IntervalIntegrable (fun θ : ℝ => (g ∘ f) θ * f' θ) volume (0 : ℝ)
        (Real.pi / 2) := by
      refine (hcontRHS.intervalIntegrable).congr_ae ?_
      rw [Set.uIoc_of_le hpi, ← Measure.restrict_congr_set (Ioo_ae_eq_Ioc (μ := volume)
        (a := (0 : ℝ)) (b := Real.pi / 2))]
      change ∀ᵐ θ ∂(volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))),
        2 * K (Real.sin θ ^ 2) = (g ∘ f) θ * f' θ
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
      filter_upwards with θ hθ
      have hsin_pos : 0 < Real.sin θ :=
        Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
      have hcos_pos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1], hθ.2⟩
      have hsqrt : Real.sqrt (Real.sin θ ^ 2 * (1 - Real.sin θ ^ 2))
          = Real.sin θ * Real.cos θ := by
        have h1 : 1 - Real.sin θ ^ 2 = Real.cos θ ^ 2 := by
          linarith [Real.sin_sq_add_cos_sq θ]
        rw [h1, show Real.sin θ ^ 2 * Real.cos θ ^ 2 = (Real.sin θ * Real.cos θ) ^ 2 by ring,
          Real.sqrt_sq (by positivity)]
      simp only [Function.comp_apply, hgdef, hfdef, hf'def]
      rw [hsqrt]
      have hsin_ne : Real.sin θ ≠ 0 := ne_of_gt hsin_pos
      have hcos_ne : Real.cos θ ≠ 0 := ne_of_gt hcos_pos
      field_simp
    rw [intervalIntegrable_iff, Set.uIoc_of_le hpi, IntegrableOn] at hint
    exact hint
  have hmain := intervalIntegral.integral_comp_mul_deriv''' (f := f) (f' := f') (g := g)
    (a := (0 : ℝ)) (b := Real.pi / 2) hf hff' hg_cont hg1 hg2
  have hf0 : f 0 = 0 := by rw [hfdef]; norm_num
  have hf1 : f (Real.pi / 2) = 1 := by
    rw [hfdef]; simp
  rw [hf0, hf1] at hmain
  have hLHS : (∫ θ in (0 : ℝ)..(Real.pi / 2), (g ∘ f) θ * f' θ)
      = ∫ θ in (0 : ℝ)..(Real.pi / 2), 2 * K (Real.sin θ ^ 2) := by
    refine intervalIntegral.integral_congr_Ioo_of_le hpi (fun θ hθ => ?_)
    have hsin_pos : 0 < Real.sin θ :=
      Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
    have hcos_pos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1], hθ.2⟩
    have hsqrt : Real.sqrt (Real.sin θ ^ 2 * (1 - Real.sin θ ^ 2))
        = Real.sin θ * Real.cos θ := by
      have h1 : 1 - Real.sin θ ^ 2 = Real.cos θ ^ 2 := by
        linarith [Real.sin_sq_add_cos_sq θ]
      rw [h1, show Real.sin θ ^ 2 * Real.cos θ ^ 2 = (Real.sin θ * Real.cos θ) ^ 2 by ring,
        Real.sqrt_sq (by positivity)]
    simp only [Function.comp_apply, hgdef, hfdef, hf'def]
    rw [hsqrt]
    have hne : Real.sin θ * Real.cos θ ≠ 0 := by positivity
    field_simp
  rw [← hmain, hLHS]

end

end Work.Anchor
namespace Work.Anchor

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

noncomputable section

open Work.OddVolterra Work.OddVolterra.KernelExt

/-! ## The first-slot derivative as a first partial derivative -/

/-- For `F` smooth on an open set, the first-slot derivative of the slices
`q ↦ deriv (fun u => F (u, q.2)) q.1` is again smooth. -/
theorem contDiffOn_deriv_slice_fst {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {F : ℝ × P → ℝ} {U : Set (ℝ × P)} (hU : IsOpen U)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F U) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × P => deriv (fun u : ℝ => F (u, q.2)) q.1) U := by
  have hfd : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ F) U := hF.fderiv_of_isOpen hU (by simp)
  have hmain : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : ℝ × P => (fderiv ℝ F q) ((1 : ℝ), (0 : P))) U :=
    hfd.clm_apply contDiffOn_const
  refine hmain.congr (fun q hq => ?_)
  have hdiff : DifferentiableAt ℝ F q :=
    (hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hq)
  have hφ : HasFDerivAt (fun u : ℝ => (u, q.2)) (ContinuousLinearMap.inl ℝ ℝ P) q.1 :=
    hasFDerivAt_prodMk_left q.1 q.2
  have hcomp := hdiff.hasFDerivAt.comp q.1 hφ
  have hfun : fderiv ℝ (fun u : ℝ => F (u, q.2)) q.1
      = (fderiv ℝ F q).comp (ContinuousLinearMap.inl ℝ ℝ P) := by
    simpa only [Function.comp_def] using hcomp.fderiv
  calc deriv (fun u : ℝ => F (u, q.2)) q.1
      = (fderiv ℝ (fun u : ℝ => F (u, q.2)) q.1) 1 := by rw [fderiv_apply_one_eq_deriv]
    _ = (((fderiv ℝ F q).comp (ContinuousLinearMap.inl ℝ ℝ P)) 1) := by rw [hfun]
    _ = (fderiv ℝ F q) ((1 : ℝ), (0 : P)) := by simp

/-! ## A parametric interval integral over a fixed interval, localised -/

/-- **Smoothness of a parametric interval integral.**  If `G : P × ℝ → ℝ` is `C^∞` on the product
of an *open* set `U ⊆ P` with `ℝ`, then `q ↦ ∫_a^b G (q,t) dt` is `C^∞` on `U`.  The proof
localises with a smooth bump in the parameter space so that the *global* version
(`Work.Analysis.Calculus.contDiff_intervalIntegral_parametric_top`) applies. -/
theorem contDiffOn_intervalIntegral_parametric
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [ProperSpace P] [HasContDiffBump P]
    {G : P × ℝ → ℝ} {U : Set P} (hU : IsOpen U) {a b : ℝ}
    (hG : ContDiffOn ℝ (⊤ : ℕ∞) G (U ×ˢ Set.univ)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun q : P => ∫ t in a..b, G (q, t)) U := by
  intro q₀ hq₀
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hq₀)
  let β : ContDiffBump q₀ := ⟨r / 4, r / 2, by linarith, by linarith⟩
  have hrIn : β.rIn = r / 4 := rfl
  have hrOut : β.rOut = r / 2 := rfl
  have hball : ∀ x : P, x ∈ Metric.closedBall q₀ β.rOut → x ∈ U := fun x hx => by
    refine hsub (Metric.closedBall_subset_ball (by linarith) ?_)
    rwa [hrOut] at hx
  have hsm : ContDiff ℝ (⊤ : ℕ∞) (fun p : P × ℝ => (β : P → ℝ) p.1 * G p) := by
    rw [contDiff_iff_contDiffAt]
    intro p
    rcases le_or_gt (dist p.1 q₀) β.rOut with hle | hlt
    · have hpU : p.1 ∈ U := hball p.1 (Metric.mem_closedBall.mpr hle)
      have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun p : P × ℝ => (β : P → ℝ) p.1) p :=
        (β.contDiff (n := (⊤ : ℕ∞))).contDiffAt.comp p contDiffAt_fst
      have h2 : ContDiffAt ℝ (⊤ : ℕ∞) G p :=
        hG.contDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨hpU, Set.mem_univ _⟩)
      exact h1.mul h2
    · have hev : (fun p' : P × ℝ => (β : P → ℝ) p'.1 * G p') =ᶠ[𝓝 p] (fun _ => (0 : ℝ)) := by
        have hopen : IsOpen {x : P | β.rOut < dist x q₀} :=
          isOpen_lt continuous_const (continuous_id.dist continuous_const)
        filter_upwards [hopen.prod isOpen_univ |>.mem_nhds ⟨hlt, Set.mem_univ _⟩] with p' hp'
        rw [ContDiffBump.zero_of_le_dist β (le_of_lt hp'.1), zero_mul]
      exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq hev
  have hint : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : P => ∫ t in a..b, (β : P → ℝ) q * G (q, t)) :=
    Work.Analysis.Calculus.contDiff_intervalIntegral_parametric_top
      (f := fun q t => (β : P → ℝ) q * G (q, t)) hsm
  have heq : (fun q : P => ∫ t in a..b, G (q, t)) =ᶠ[𝓝 q₀]
      (fun q : P => ∫ t in a..b, (β : P → ℝ) q * G (q, t)) := by
    filter_upwards [Metric.ball_mem_nhds q₀ (ε := β.rIn) (by rw [hrIn]; linarith)] with q hq
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    have h1 : (β : P → ℝ) q = 1 := by
      refine ContDiffBump.one_of_mem_closedBall β (Metric.mem_closedBall.mpr ?_)
      rw [Metric.mem_ball, hrIn] at hq
      exact le_of_lt hq
    rw [h1, one_mul]
  exact (hint.contDiffAt.congr_of_eventuallyEq heq).contDiffWithinAt

end

end Work.Anchor

namespace Work.Anchor

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

noncomputable section

open Work.OddVolterra Work.OddVolterra.KernelExt

/-! ## Smoothness of the manifest Abel kernel along smooth parameter maps -/

/-- **The manifest Abel kernel composed with smooth parameter maps.**  With `h : ℝ → ℝ` smooth
and arbitrary `C^∞` parameter maps `s, σ, x, y, x', y'`, the function
`p ↦ KvecM n h (s p) (σ p) (x p) (y p) (x' p) (y' p)` is `C^∞` on any set on which the two
radicands `krad h (σ p) (-(x p)) (s p)` and `krad h (σ p) (y p) (s p)` are positive (so that the
denominator `Kden` of the manifest kernels does not vanish). -/
theorem contDiffOn_KvecM_comp {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    {B : Set P} {s σ x y x' y' : P → ℝ}
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) s B) (hσ : ContDiffOn ℝ (⊤ : ℕ∞) σ B)
    (hx : ContDiffOn ℝ (⊤ : ℕ∞) x B) (hy : ContDiffOn ℝ (⊤ : ℕ∞) y B)
    (hx' : ContDiffOn ℝ (⊤ : ℕ∞) x' B) (hy' : ContDiffOn ℝ (⊤ : ℕ∞) y' B)
    (hposx : ∀ p ∈ B, 0 < krad h (σ p) (-(x p)) (s p))
    (hposy : ∀ p ∈ B, 0 < krad h (σ p) (y p) (s p)) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p => KvecM n h (s p) (σ p) (x p) (y p) (x' p) (y' p)) B := by
  have hkrad : ∀ {v : P → ℝ} (_ : ContDiffOn ℝ (⊤ : ℕ∞) v B),
      ContDiffOn ℝ (⊤ : ℕ∞) (fun p => krad h (σ p) (v p) (s p)) B := by
    intro v hv
    have hq : ContDiffOn ℝ (⊤ : ℕ∞) (fun p => hquot h (s p) (σ p)) B :=
      (Work.OddVolterra.Existence.hquot_contDiff hh).contDiffOn.comp (hs.prodMk hσ)
        (fun _ _ => Set.mem_univ _)
    have hline1 : ContDiffOn ℝ (⊤ : ℕ∞) (fun p => line h (σ p) (v p)) B :=
      (Work.OddVolterra.line_contDiff hh).contDiffOn.comp (hσ.prodMk hv)
        (fun _ _ => Set.mem_univ _)
    have hline2 : ContDiffOn ℝ (⊤ : ℕ∞) (fun p => line h (s p) (v p)) B :=
      (Work.OddVolterra.line_contDiff hh).contDiffOn.comp (hs.prodMk hv)
        (fun _ _ => Set.mem_univ _)
    refine ((hv.add hq).mul (hline1.add hline2)).congr (fun p _ => ?_)
    simp only [krad_apply]
  have hKden : ∀ {v : P → ℝ} (hv : ContDiffOn ℝ (⊤ : ℕ∞) v B)
      (_ : ∀ p ∈ B, 0 < krad h (σ p) (v p) (s p)),
      ContDiffOn ℝ (⊤ : ℕ∞) (fun p => Kden h (s p) (σ p) (v p)) B := by
    intro v hv hpos
    refine ((hkrad hv).sqrt (fun p hp => ne_of_gt (hpos p hp))).congr (fun p _ => ?_)
    rw [Kden_eq_sqrt_krad]
  have hJ1 : ∀ {v : P → ℝ} (_ : ContDiffOn ℝ (⊤ : ℕ∞) v B),
      ContDiffOn ℝ (⊤ : ℕ∞) (fun p => J1M n h (s p) (σ p) (v p)) B := by
    intro v hv
    have hR : ContDiffOn ℝ (⊤ : ℕ∞)
        (Rnu ((n : ℝ) + 1 / 2) h (fun _ : ℝ × ℝ × ℝ => (1 : ℝ)) (n + 1)) Set.univ :=
      (Rnu_contDiff ((n : ℝ) + 1 / 2) hh contDiff_const (n + 1)).contDiffOn
    have hΦ : ContDiffOn ℝ (⊤ : ℕ∞) (fun p => (s p, (σ p, v p))) B := hs.prodMk (hσ.prodMk hv)
    have := hR.comp hΦ (fun _ _ => Set.mem_univ _)
    simpa only [J1M, Function.comp_def] using this
  have hJ2 : ∀ {v : P → ℝ} (_ : ContDiffOn ℝ (⊤ : ℕ∞) v B),
      ContDiffOn ℝ (⊤ : ℕ∞) (fun p => J2M n h (s p) (σ p) (v p)) B := by
    intro v hv
    have hinit : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ × ℝ => lineSlope h q.1 q.2.2) := by
      unfold lineSlope; fun_prop
    have hR : ContDiffOn ℝ (⊤ : ℕ∞)
        (Rnu ((n : ℝ) - 1 / 2) h (fun q : ℝ × ℝ × ℝ => lineSlope h q.1 q.2.2) n) Set.univ :=
      (Rnu_contDiff ((n : ℝ) - 1 / 2) hh hinit n).contDiffOn
    have hΦ : ContDiffOn ℝ (⊤ : ℕ∞) (fun p => (s p, (σ p, v p))) B := hs.prodMk (hσ.prodMk hv)
    have := hR.comp hΦ (fun _ _ => Set.mem_univ _)
    simpa only [J2M, Function.comp_def] using this
  have hK1 : ∀ {v : P → ℝ} (hv : ContDiffOn ℝ (⊤ : ℕ∞) v B)
      (hpos : ∀ p ∈ B, 0 < krad h (σ p) (v p) (s p)),
      ContDiffOn ℝ (⊤ : ℕ∞) (fun p => K1M n h (s p) (σ p) (v p)) B := fun hv hpos =>
    (hJ1 hv).div (hKden hv hpos)
      (fun p hp => ne_of_gt (by rw [Kden_eq_sqrt_krad]; exact Real.sqrt_pos.mpr (hpos p hp)))
  have hK2 : ∀ {v : P → ℝ} (hv : ContDiffOn ℝ (⊤ : ℕ∞) v B)
      (hpos : ∀ p ∈ B, 0 < krad h (σ p) (v p) (s p)),
      ContDiffOn ℝ (⊤ : ℕ∞) (fun p => K2M n h (s p) (σ p) (v p)) B := fun hv hpos =>
    (hJ2 hv).div (hKden hv hpos)
      (fun p hp => ne_of_gt (by rw [Kden_eq_sqrt_krad]; exact Real.sqrt_pos.mpr (hpos p hp)))
  have hpx : ContDiffOn ℝ (⊤ : ℕ∞) (fun p => krad h (σ p) (-(x p)) (s p)) B := hkrad hx.neg
  rw [contDiffOn_pi]
  intro i
  fin_cases i
  · refine (((hK1 hx.neg hposx).mul hx').add ((hK1 hy hposy).mul hy')).neg.congr
      (fun p _ => ?_)
    simp [KvecM]
  · refine (((hK2 hx.neg hposx).mul hx').add ((hK2 hy hposy).mul hy')).neg.congr
      (fun p _ => ?_)
    simp [KvecM]

end

end Work.Anchor

namespace Work.Anchor

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

noncomputable section

open Work.OddVolterra Work.OddVolterra.KernelExt

/-! ## The target -/

theorem ThetaM_contDiffOn (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsmall : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × ℝ × Work.OddVolterra.St =>
        Work.OddVolterra.KernelExt.ThetaM n h p.1 p.2.1 p.2.2)
      {p : ℝ × ℝ × Work.OddVolterra.St | p.1 ∈ Set.Ioo (481 / 1000) (97 / 100) ∧
        p.2.1 ∈ Set.Ioo (481 / 1000) (97 / 100) ∧
        ‖p.2.2 - Work.OddVolterra.baseState p.2.1‖ < 9 / 20} := by
  have hconv : ∀ {c a₁ a₂ : ℝ}, 0 ≤ c → c ≤ 1 → 9 / 20 < a₁ → 9 / 20 < a₂ →
      9 / 20 < a₁ + c * (a₂ - a₁) := by
    intro c a₁ a₂ hc0 hc1 ha₁ ha₂
    have h3 : 9 / 20 < min a₁ a₂ := lt_min ha₁ ha₂
    have h5 : (1 - c) * min a₁ a₂ + c * min a₁ a₂ ≤ (1 - c) * a₁ + c * a₂ := by
      have h6 : 0 ≤ 1 - c := by linarith
      have h7 := mul_le_mul_of_nonneg_left (min_le_left a₁ a₂) h6
      have h8 := mul_le_mul_of_nonneg_left (min_le_right a₁ a₂) hc0
      linarith
    have h9 : (1 - c) * a₁ + c * a₂ = a₁ + c * (a₂ - a₁) := by ring
    linarith
  -- the `τ`-parametrised manifest kernel is smooth
  have hKτ : ∀ i : Fin 2, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : (ℝ × ℝ × St) × ℝ => (KvecM n h (p.1.1 + p.2 * (p.1.2.1 - p.1.1)) p.1.2.1
        (p.1.2.2 0) (p.1.2.2 1) (p.1.2.2 2) (p.1.2.2 3)) i)
      (Good ×ˢ Set.Icc (0 : ℝ) 1) := by
    intro i
    have hK := contDiffOn_KvecM_comp (n := n) (hh := hh) (B := Good ×ˢ Set.Icc (0 : ℝ) 1)
      (s := fun p : (ℝ × ℝ × St) × ℝ => p.1.1 + p.2 * (p.1.2.1 - p.1.1))
      (σ := fun p => p.1.2.1) (x := fun p => p.1.2.2 0) (y := fun p => p.1.2.2 1)
      (x' := fun p => p.1.2.2 2) (y' := fun p => p.1.2.2 3)
      (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
      (fun p hp => by
        obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hp.1
        exact krad_pos_of_add_pos' hsmall
          (by have := hconv hp.2.1 hp.2.2 h1 h3; linarith) (by simpa using h5.le))
      (fun p hp => by
        obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hp.1
        exact krad_pos_of_add_pos' hsmall
          (by have := hconv hp.2.1 hp.2.2 h1 h3; linarith) (by simpa using h6.le))
    exact (contDiffOn_pi.mp hK) i
  -- the `θ`-parametrised manifest kernel is smooth
  have hKθ : ∀ i : Fin 2, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : (ℝ × ℝ × St) × ℝ => (KvecM n h (p.1.1 + Real.sin p.2 ^ 2 * (p.1.2.1 - p.1.1))
        p.1.2.1 (p.1.2.2 0) (p.1.2.2 1) (p.1.2.2 2) (p.1.2.2 3)) i)
      (Good ×ˢ Set.univ) := by
    intro i
    have hsin : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : (ℝ × ℝ × St) × ℝ => (p.1, Real.sin p.2 ^ 2))
        (Good ×ˢ Set.univ) :=
      (((contDiff_fst : ContDiff ℝ (⊤ : ℕ∞) (fun p : (ℝ × ℝ × St) × ℝ => p.1)).prodMk
        ((Real.contDiff_sin.pow 2).comp contDiff_snd))).contDiffOn
    have hcomp := (hKτ i).comp hsin (fun p hp => ⟨hp.1, ⟨sq_nonneg _, Real.sin_sq_le_one _⟩⟩)
    simpa only [Function.comp_def] using hcomp
  -- the `θ`-integral is smooth
  have hInt : ∀ i : Fin 2, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : ℝ × ℝ × St => ∫ θ in (0 : ℝ)..(Real.pi / 2),
        2 * (KvecM n h (q.1 + Real.sin θ ^ 2 * (q.2.1 - q.1)) q.2.1
          (q.2.2 0) (q.2.2 1) (q.2.2 2) (q.2.2 3)) i) Good := by
    intro i
    refine contDiffOn_intervalIntegral_parametric (hU := isOpen_Good) (a := 0) (b := Real.pi / 2)
      (G := fun (p : (ℝ × ℝ × St) × ℝ) => 2 * (KvecM n h
        (p.1.1 + Real.sin p.2 ^ 2 * (p.1.2.1 - p.1.1)) p.1.2.1
        (p.1.2.2 0) (p.1.2.2 1) (p.1.2.2 2) (p.1.2.2 3)) i) ?_
    exact (contDiffOn_const (c := (2 : ℝ))).mul (by simpa using hKθ i)
  -- `G2M` is smooth on `Good`
  have hG2 : ∀ i : Fin 2, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : ℝ × ℝ × St =>
        (G2M n h q.1 q.2.1 (q.2.2 0) (q.2.2 1) (q.2.2 2) (q.2.2 3)) i) Good := by
    intro i
    refine (hInt i).congr (fun q hq => ?_)
    have hcont : ContinuousOn (fun τ : ℝ => (KvecM n h (q.1 + τ * (q.2.1 - q.1)) q.2.1
        (q.2.2 0) (q.2.2 1) (q.2.2 2) (q.2.2 3)) i) (Set.Icc (0 : ℝ) 1) := by
      have h := (hKτ i).continuousOn.comp
        (by fun_prop : ContinuousOn (fun τ : ℝ => (q, τ)) (Set.Icc (0 : ℝ) 1))
        (fun τ hτ => ⟨hq, hτ⟩)
      simpa only [Function.comp_def] using h
    have h := AbelWeight_subst (K := fun τ : ℝ => (KvecM n h (q.1 + τ * (q.2.1 - q.1)) q.2.1
        (q.2.2 0) (q.2.2 1) (q.2.2 2) (q.2.2 3)) i) hcont
    simpa only [G2M] using h
  -- the derivative rows
  have hderiv : ∀ i : Fin 2, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : ℝ × ℝ × St => deriv (fun u : ℝ =>
        (G2M n h u q.2.1 (q.2.2 0) (q.2.2 1) (q.2.2 2) (q.2.2 3)) i) q.1) Good := by
    intro i
    exact contDiffOn_deriv_slice_fst (P := ℝ × St) (U := Good) isOpen_Good (hG2 i)
  -- assembly
  have hcoord : ∀ k : Fin 4, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : ℝ × ℝ × St => q.2.2 k) Good := by
    intro k
    have h : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ × St => q.2.2) Good := by fun_prop
    exact (contDiffOn_pi.mp h) k
  have hTheta : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : ℝ × ℝ × St => ThetaM n h q.1 q.2.1 q.2.2) Good := by
    rw [contDiffOn_pi]
    intro i
    fin_cases i
    · simpa [ThetaM] using (hcoord 2).neg
    · simpa [ThetaM] using (hcoord 3).neg
    · simpa [ThetaM] using (hderiv 0).neg
    · simpa [ThetaM] using (hderiv 1).neg
  refine hTheta.mono (fun p hp => ?_)
  exact target_subset_Good hp.1 hp.2.1 hp.2.2

end

end Work.Anchor
