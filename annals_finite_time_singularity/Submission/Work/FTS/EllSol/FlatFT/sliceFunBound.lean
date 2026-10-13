import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllSol.FlatFT.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.CurrySmooth
import Submission.Work.FTS.EllipticEst.RegQ.pthU_slot_alg
import Submission.Work.Blocks.IMC.cs_integral_mul_le
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo
import Submission.Work.FTS.EllSol.slice_zero_slot_finite

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The slice bound `∫ g²σ ≤ (2(π/2)∫(∂_θg)²σ + 2g(θ₁)²)·∫σ`

For a function `g` of class `C²` on the open strip `ℝ × (0,π/2)` and a point
`θ₁ ∈ (0,π/2)` the θ-slice `θ ↦ g z θ` is controlled by its derivative:

  `∫_{Iθ} (g z θ)² sin(2θ)^{-η} ≤ (2(π/2)∫_{Iθ}(∂_θg z θ)² sin(2θ)^{-η} + 2(g z θ₁)²)·∫_{Iθ}sin(2θ)^{-η}`

`(η = 99/100)`, provided the derivative slot is finite.  This is the zeroth-order member of the
chain `sliceFunBound → slicePthBound → …` and the `θ`-companion of the `z`-slice bounds of
`Submission/Work/FTS/EllSol/FlatFT/`.

The proof is the elementary "fundamental theorem of calculus + Cauchy–Schwarz" step, with the
*point* `θ₁` as the reference value:

* `g z θ - g z θ₁ = ∫_{θ₁}^{θ} ∂_θg z` (FTC on the open interval, where the slice is `C²`);
* hence `|g z θ - g z θ₁| ≤ ∫_{Iθ}|∂_θg z| =: S`, because `[θ₁,θ]` lies in `Iθ`;
* `S² ≤ (π/2)∫_{Iθ}(∂_θg z)² ≤ (π/2)∫_{Iθ}(∂_θg z)²sin(2θ)^{-η}` by Cauchy–Schwarz on `Iθ`
  (`Work.Blocks.IMC.cs_integral_mul_le`) and `sin(2θ)^{-η} ≥ 1` on the open interval;
* `(x+y)² ≤ 2x² + 2y²` and `|θ - θ₁| ≤ π/2` produce the stated constants.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/

namespace Work.FTS.EllSol.FlatFT

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

/-- **Weighted Cauchy–Schwarz on the angular interval.**  For a function of class `C²` on
`(0,π/2)` whose weighted derivative slot is finite, the total mass of `|∂_θf|` is finite and

  `(∫_{Iθ} |∂_θf|)² ≤ (π/2) · ∫_{Iθ} (∂_θf)² sin(2θ)^{-η}`.

(`η = 99/100`; the weight is `≥ 1` on the open interval, so the weighted slot dominates the
plain one, and Cauchy–Schwarz on `Iθ` costs exactly the length `π/2`.) -/
private lemma sliceCS_deriv (f : ℝ → ℝ) (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)))
    (hint : MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv f θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun t : ℝ => |deriv f t|) Work.Spaces.Iθ ∧
      (∫ t in Work.Spaces.Iθ, |deriv f t|) ^ 2
        ≤ (Real.pi / 2) * ∫ t in Work.Spaces.Iθ, (deriv f t) ^ 2
            * (Real.sin (2 * t)) ^ (-(Work.Spaces.eta)) := by
  have hIθ_meas : MeasurableSet Work.Spaces.Iθ := by rw [Work.Spaces.Iθ]; exact measurableSet_Icc
  -- the weight is `≥ 1` off the two endpoints
  have hone_le : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2),
      1 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
    intro θ hθ
    have hsin : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    have h := Real.rpow_le_rpow_of_nonpos (z := -(Work.Spaces.eta)) hsin
      (Real.sin_le_one (2 * θ)) (by norm_num [Work.Spaces.eta])
    rwa [Real.one_rpow] at h
  have hcont : ContinuousOn (fun t => deriv f t) (Set.Ioo 0 (Real.pi / 2)) :=
    (hf.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)).continuousOn
  -- the plain squared-derivative slot is finite
  have hP2 : IntegrableOn (fun t : ℝ => (deriv f t) ^ 2) Work.Spaces.Iθ := by
    refine MeasureTheory.Integrable.mono' hint
      (Work.FTS.EllSol.aesm_of_continuousOn_Ioo (hcont.pow 2)) ?_
    refine Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ => ?_)
    show ‖(deriv f θ) ^ 2‖ ≤ (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact le_mul_of_one_le_right (sq_nonneg _) (hone_le θ hθ)
  -- and so is the absolute first-derivative slot, by `|x| ≤ x² + 1/4`
  have habs : IntegrableOn (fun t : ℝ => |deriv f t|) Work.Spaces.Iθ := by
    have hconst : IntegrableOn (fun _ : ℝ => (1/4 : ℝ)) Work.Spaces.Iθ :=
      MeasureTheory.integrableOn_const
        (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top) (by simp)
    refine MeasureTheory.Integrable.mono' (hP2.add hconst)
      (Work.FTS.EllSol.aesm_of_continuousOn_Ioo (hcont.abs)) ?_
    refine Eventually.of_forall (fun θ => ?_)
    have := Work.FTS.EllSol.abs_le_sq_add_quarter (deriv f θ)
    simpa only [Pi.add_apply, Real.norm_eq_abs, abs_abs] using this
  refine ⟨habs, ?_⟩
  have hSnn : 0 ≤ ∫ t in Work.Spaces.Iθ, |deriv f t| :=
    MeasureTheory.setIntegral_nonneg hIθ_meas (fun t _ => abs_nonneg _)
  have hXnn : 0 ≤ ∫ t in Work.Spaces.Iθ, (deriv f t) ^ 2 :=
    MeasureTheory.setIntegral_nonneg hIθ_meas (fun t _ => sq_nonneg _)
  have hvol : (∫ _ in Work.Spaces.Iθ, (1:ℝ)) = Real.pi / 2 := by
    have hvol : volume.real Work.Spaces.Iθ = Real.pi / 2 := by
      rw [MeasureTheory.measureReal_def, Work.Spaces.Iθ, Real.volume_Icc,
        ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
      ring
    rw [MeasureTheory.setIntegral_const, hvol]; simp
  -- Cauchy–Schwarz: `(∫|f'|)² ≤ (∫(f')²)(∫1)`
  have hcs := Work.Blocks.IMC.cs_integral_mul_le (volume.restrict Work.Spaces.Iθ)
    (f := fun t : ℝ => |deriv f t|) (g := fun _ : ℝ => (1:ℝ))
    (habs.aestronglyMeasurable) aestronglyMeasurable_const
    (by simpa only [sq_abs, MeasureTheory.IntegrableOn] using hP2)
    (by simpa using (integrable_const (1:ℝ) :
      Integrable (fun _ : ℝ => (1:ℝ)) (volume.restrict Work.Spaces.Iθ)))
  simp only [mul_one] at hcs
  have h1 : (∫ x in Work.Spaces.Iθ, |deriv f x| ^ 2)
      = (∫ x in Work.Spaces.Iθ, (deriv f x) ^ 2) :=
    MeasureTheory.setIntegral_congr_fun hIθ_meas (fun x _ => sq_abs (deriv f x))
  rw [h1] at hcs
  simp only [one_pow] at hcs
  have hkey : (∫ t in Work.Spaces.Iθ, |deriv f t|) ^ 2 ≤
      (∫ t in Work.Spaces.Iθ, (deriv f t) ^ 2) * (Real.pi / 2) := by
    calc (∫ t in Work.Spaces.Iθ, |deriv f t|) ^ 2
        ≤ (Real.sqrt (∫ t in Work.Spaces.Iθ, (deriv f t)^2) * Real.sqrt (Real.pi/2)) ^ 2 :=
          pow_le_pow_left₀ hSnn (by simpa only [abs_of_nonneg hSnn, hvol] using hcs) 2
      _ = (∫ t in Work.Spaces.Iθ, (deriv f t)^2) * (Real.pi/2) := by
          rw [mul_pow, Real.sq_sqrt hXnn, Real.sq_sqrt (by linarith [Real.pi_pos])]
  -- the weight is `≥ 1` on the open interval, so it can be inserted
  have hle : ∫ t in Work.Spaces.Iθ, (deriv f t) ^ 2 ≤
      ∫ t in Work.Spaces.Iθ, (deriv f t) ^ 2 * (Real.sin (2 * t)) ^ (-(Work.Spaces.eta)) := by
    refine MeasureTheory.integral_mono_ae hP2 hint
      (Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ => ?_))
    show (deriv f θ) ^ 2 ≤ (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
    exact le_mul_of_one_le_right (sq_nonneg _) (hone_le θ hθ)
  calc (∫ t in Work.Spaces.Iθ, |deriv f t|) ^ 2
      ≤ (∫ t in Work.Spaces.Iθ, (deriv f t) ^ 2) * (Real.pi / 2) := hkey
    _ ≤ (∫ t in Work.Spaces.Iθ, (deriv f t) ^ 2
          * (Real.sin (2 * t)) ^ (-(Work.Spaces.eta))) * (Real.pi / 2) :=
        mul_le_mul_of_nonneg_right hle (by linarith [Real.pi_pos])
    _ = (Real.pi / 2) * ∫ t in Work.Spaces.Iθ, (deriv f t) ^ 2
          * (Real.sin (2 * t)) ^ (-(Work.Spaces.eta)) := by ring

/-- **The fundamental-theorem-of-calculus slice bound.**  For a function of class `C¹` on
`(0,π/2)` with finite `L¹`-mass of `|∂_θf|`,

  `|f θ - f θ₁| ≤ ∫_{Iθ} |∂_θf|`  for all `θ, θ₁ ∈ (0,π/2)`.

The two cases `θ₁ ≤ θ` and `θ ≤ θ₁` are handled by the FTC
`intervalIntegral.integral_deriv_of_contDiffOn_Icc` on `Icc`, followed by monotonicity of the
set integral (the interval `[θ,θ₁]` is contained in `Iθ`). -/
private lemma sliceFTC_le (f : ℝ → ℝ) (hf : ContDiffOn ℝ 1 f (Set.Ioo 0 (Real.pi / 2)))
    (hint : MeasureTheory.IntegrableOn (fun t : ℝ => |deriv f t|) Work.Spaces.Iθ)
    {θ₁ θ : ℝ} (hθ₁ : θ₁ ∈ Set.Ioo 0 (Real.pi / 2)) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    |f θ - f θ₁| ≤ ∫ t in Work.Spaces.Iθ, |deriv f t| := by
  rcases le_total θ₁ θ with hle | hle
  · have hcd : ContDiffOn ℝ 1 f (Set.Icc θ₁ θ) :=
      hf.mono (fun x hx => ⟨by linarith [hx.1, hθ₁.1], by linarith [hx.2, hθ.2]⟩)
    have hftc : ∫ t in θ₁..θ, deriv f t = f θ - f θ₁ :=
      intervalIntegral.integral_deriv_of_contDiffOn_Icc hcd hle
    have hmono : ∫ t in θ₁..θ, |deriv f t| ≤ ∫ t in Work.Spaces.Iθ, |deriv f t| := by
      rw [intervalIntegral.integral_of_le hle]
      refine MeasureTheory.setIntegral_mono_set hint (Eventually.of_forall (fun x => abs_nonneg _))
        (Eventually.of_forall ?_)
      intro x hx
      rw [Set.mem_Ioc] at hx
      exact ⟨by linarith [hx.1, hθ₁.1], by linarith [hx.2, hθ.2]⟩
    calc |f θ - f θ₁| = |∫ t in θ₁..θ, deriv f t| := by rw [hftc]
      _ ≤ ∫ t in θ₁..θ, |deriv f t| := intervalIntegral.abs_integral_le_integral_abs hle
      _ ≤ ∫ t in Work.Spaces.Iθ, |deriv f t| := hmono
  · have hcd : ContDiffOn ℝ 1 f (Set.Icc θ θ₁) :=
      hf.mono (fun x hx => ⟨by linarith [hx.1, hθ.1], by linarith [hx.2, hθ₁.2]⟩)
    have hftc : ∫ t in θ..θ₁, deriv f t = f θ₁ - f θ :=
      intervalIntegral.integral_deriv_of_contDiffOn_Icc hcd hle
    have hmono : ∫ t in θ..θ₁, |deriv f t| ≤ ∫ t in Work.Spaces.Iθ, |deriv f t| := by
      rw [intervalIntegral.integral_of_le hle]
      refine MeasureTheory.setIntegral_mono_set hint (Eventually.of_forall (fun x => abs_nonneg _))
        (Eventually.of_forall ?_)
      intro x hx
      rw [Set.mem_Ioc] at hx
      exact ⟨by linarith [hx.1, hθ.1], by linarith [hx.2, hθ₁.2]⟩
    have h2 : |f θ - f θ₁| = |∫ t in θ..θ₁, deriv f t| := by
      rw [hftc, abs_sub_comm]
    calc |f θ - f θ₁| = |∫ t in θ..θ₁, deriv f t| := h2
      _ ≤ ∫ t in θ..θ₁, |deriv f t| := intervalIntegral.abs_integral_le_integral_abs hle
      _ ≤ ∫ t in Work.Spaces.Iθ, |deriv f t| := hmono

theorem sliceFunBound (g : ℝ → ℝ → ℝ)
    (hg : ContDiffOn ℝ 2 (Function.uncurry g) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)))
    {z θ₁ : ℝ} (hθ₁ : θ₁ ∈ Set.Ioo 0 (Real.pi / 2))
    (hint : MeasureTheory.IntegrableOn (fun θ : ℝ => (Work.Spaces.pth g z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => (g z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        ≤ (2 * (Real.pi / 2) * (∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.pth g z θ) ^ 2
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
            + 2 * (g z θ₁) ^ 2)
          * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
  have hIθ_meas : MeasurableSet Work.Spaces.Iθ := by rw [Work.Spaces.Iθ]; exact measurableSet_Icc
  -- the `θ`-slice at `z` is `C²` on the open angular interval
  have hf2 : ContDiffOn ℝ 2 (fun θ : ℝ => g z θ) (Set.Ioo 0 (Real.pi / 2)) := by
    have hcurve : ContDiffOn ℝ 2 (fun θ : ℝ => (z, θ)) (Set.Ioo 0 (Real.pi / 2)) := by fun_prop
    have h := hg.comp hcurve (fun θ hθ => ⟨Set.mem_univ z, hθ⟩)
    simpa [Function.comp_def, Function.uncurry] using h
  have hf1 : ContDiffOn ℝ 1 (fun θ : ℝ => g z θ) (Set.Ioo 0 (Real.pi / 2)) :=
    hf2.of_le (m := 1) (by norm_num)
  -- the mass of `|∂_θg|` is finite, and its square is dominated by the weighted derivative slot
  obtain ⟨habs, hS2⟩ := sliceCS_deriv (fun θ : ℝ => g z θ) hf2 hint
  let A : ℝ := ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth g z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
  let B : ℝ := ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
  let S : ℝ := ∫ t in Work.Spaces.Iθ, |deriv (fun θ : ℝ => g z θ) t|
  have hS2' : S ^ 2 ≤ (Real.pi / 2) * A := hS2
  have hσnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
    fun θ hθ => Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc (x := 2 * θ)
      ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩) _
  have hA_nonneg : 0 ≤ A :=
    MeasureTheory.setIntegral_nonneg hIθ_meas
      (fun θ hθ => mul_nonneg (sq_nonneg _) (hσnn θ hθ))
  -- the pointwise bound, on the open interval
  have hpoint : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      (g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        ≤ (2 * (Real.pi / 2) * A + 2 * (g z θ₁) ^ 2)
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
    intro θ hθ
    have hbd : (g z θ) ^ 2 ≤ 2 * (Real.pi / 2) * A + 2 * (g z θ₁) ^ 2 := by
      have hd : |g z θ - g z θ₁| ≤ S := sliceFTC_le (fun θ : ℝ => g z θ) hf1 habs hθ₁ hθ
      have h1 : (g z θ) ^ 2 ≤ (|g z θ₁| + S) ^ 2 := by
        have hbase : |g z θ| ≤ |g z θ₁| + S := by
          calc |g z θ| = |g z θ₁ + (g z θ - g z θ₁)| := by
                rw [show g z θ₁ + (g z θ - g z θ₁) = g z θ from by ring]
            _ ≤ |g z θ₁| + |g z θ - g z θ₁| := abs_add_le _ _
            _ ≤ |g z θ₁| + S := add_le_add (le_refl _) hd
        calc (g z θ) ^ 2 = |g z θ| ^ 2 := (sq_abs _).symm
          _ ≤ (|g z θ₁| + S) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hbase 2
      have h2 : (|g z θ₁| + S) ^ 2 ≤ 2 * (g z θ₁) ^ 2 + 2 * S ^ 2 := by
        nlinarith [two_mul_le_add_sq |g z θ₁| S, sq_abs (g z θ₁)]
      have h3 : 2 * S ^ 2 ≤ 2 * (Real.pi / 2) * A := by
        calc 2 * S ^ 2 ≤ 2 * ((Real.pi / 2) * A) := mul_le_mul_of_nonneg_left hS2' (by norm_num)
          _ = 2 * (Real.pi / 2) * A := by ring
      calc (g z θ) ^ 2 ≤ 2 * (g z θ₁) ^ 2 + 2 * S ^ 2 := le_trans h1 h2
        _ ≤ 2 * (g z θ₁) ^ 2 + 2 * (Real.pi / 2) * A := add_le_add (le_refl _) h3
        _ = 2 * (Real.pi / 2) * A + 2 * (g z θ₁) ^ 2 := by ring
    exact mul_le_mul_of_nonneg_right hbd (hσnn θ ⟨hθ.1.le, hθ.2.le⟩)
  -- integrability of the majorant
  have hσ_int : MeasureTheory.IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      Work.Spaces.Iθ :=
    (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta)) (by norm_num [Work.Spaces.eta])
      (by norm_num [Work.Spaces.eta])).1
  have hK_int : MeasureTheory.IntegrableOn (fun θ : ℝ => (2 * (Real.pi / 2) * A + 2 * (g z θ₁) ^ 2)
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ :=
    MeasureTheory.Integrable.const_mul hσ_int (2 * (Real.pi / 2) * A + 2 * (g z θ₁) ^ 2)
  -- the integrand itself
  have hF_int : MeasureTheory.IntegrableOn (fun θ : ℝ => (g z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ := by
    have hcontσ : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        (Set.Ioo 0 (Real.pi / 2)) :=
      ContinuousOn.rpow_const
        (Real.continuous_sin.comp_continuousOn (continuousOn_const.mul continuousOn_id))
        (fun x hx => Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1])
          (by linarith [hx.2, Real.pi_pos]))))
    refine MeasureTheory.Integrable.mono' hK_int
      (Work.FTS.EllSol.aesm_of_continuousOn_Ioo ((hf1.continuousOn.pow 2).mul hcontσ)) ?_
    refine Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ => ?_)
    have hp := hpoint θ hθ
    have hnn : 0 ≤ (g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
      mul_nonneg (sq_nonneg _) (hσnn θ ⟨hθ.1.le, hθ.2.le⟩)
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    exact hp
  refine ⟨hF_int, ?_⟩
  have hineq : ∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      ≤ ∫ θ in Work.Spaces.Iθ, (2 * (Real.pi / 2) * A + 2 * (g z θ₁) ^ 2)
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
    MeasureTheory.integral_mono_ae hF_int hK_int
      (Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ => hpoint θ hθ))
  calc ∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      ≤ ∫ θ in Work.Spaces.Iθ, (2 * (Real.pi / 2) * A + 2 * (g z θ₁) ^ 2)
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := hineq
    _ = (2 * (Real.pi / 2) * A + 2 * (g z θ₁) ^ 2) * B := by
        rw [MeasureTheory.integral_const_mul]
    _ = (2 * (Real.pi / 2) * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth g z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
            + 2 * (g z θ₁) ^ 2)
          * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := rfl

end

end Work.FTS.EllSol.FlatFT
