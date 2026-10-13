import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol

set_option autoImplicit false

local notation "Iθ" => Work.Spaces.Iθ

/-- The angular weight `sin(2θ)^{-η}` (`η = 99/100`) of the zero-th angular slot. -/
def sEta (θ : ℝ) : ℝ := (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))

/-- `sEta` is nonnegative on the angular interval. -/
lemma sEta_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Iθ) : 0 ≤ sEta θ :=
  Real.rpow_nonneg (x := Real.sin (2 * θ)) (y := -(Work.Spaces.eta))
    (Real.sin_nonneg_of_mem_Icc (x := 2 * θ)
      ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩)

/-- `sEta` is positive on the interior of the angular interval. -/
lemma sEta_pos_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) : 0 < sEta θ :=
  Real.rpow_pos_of_pos (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
    (by linarith [hθ.2, Real.pi_pos])) _

/-- `sEta ≥ 1` on the interior of the angular interval. -/
lemma one_le_sEta_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    1 ≤ sEta θ := by
  have h := Real.rpow_le_rpow_of_nonpos (z := -(Work.Spaces.eta))
    (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos]))
    (Real.sin_le_one (2 * θ)) (by norm_num [Work.Spaces.eta])
  rwa [Real.one_rpow] at h

/-- `sEta` is integrable on the angular interval. -/
lemma sEta_integrableOn : MeasureTheory.IntegrableOn sEta Iθ :=
  (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta)) (by norm_num [Work.Spaces.eta])
    (by norm_num [Work.Spaces.eta])).1

/-- `sEta` is continuous on the interior of the angular interval. -/
lemma continuousOn_sEta : ContinuousOn sEta (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
  ContinuousOn.rpow_const
    (Real.continuous_sin.comp_continuousOn (continuousOn_const.mul continuousOn_id))
    (fun x hx => Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1])
      (by linarith [hx.2, Real.pi_pos]))))

/-- A function continuous on the open angle interval is almost everywhere strongly measurable
for the restriction of Lebesgue measure to `Iθ` (the two sets differ by the null set
`{0, π/2}`). -/
lemma aesm_of_continuousOn_Ioo {g : ℝ → ℝ}
    (hg : ContinuousOn g (Set.Ioo (0 : ℝ) (Real.pi / 2))) :
    AEStronglyMeasurable g (volume.restrict Iθ) := by
  have hθ : Iθ =ᵐ[volume] Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    (MeasureTheory.Ioo_ae_eq_Icc).symm
  rw [MeasureTheory.Measure.restrict_congr_set hθ]
  exact hg.aestronglyMeasurable measurableSet_Ioo

/-- The elementary pointwise inequality `|x| ≤ x² + 1/4`. -/
lemma abs_le_sq_add_quarter (x : ℝ) : |x| ≤ x ^ 2 + 1 / 4 := by
  nlinarith [sq_nonneg (2 * |x| - 1), sq_abs x]

/-- The second derivative is continuous on the open interval, for a `C²` function. -/
lemma continuousOn_derivDeriv {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 2 f (Set.Ioo (0 : ℝ) (Real.pi / 2))) :
    ContinuousOn (deriv (deriv f)) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  have h1 : ContDiffOn ℝ 1 (deriv f) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hf.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)
  exact (h1.deriv_of_isOpen isOpen_Ioo (m := 0) (by norm_num)).continuousOn

/-- **The squared second-derivative slot is finite.**  From the integrability of
`(f'')² · sin(2θ)^{-η}` we get the integrability of `(f'')²` itself, since the weight is `≥ 1`
off the two endpoints. -/
lemma integrableOn_derivDeriv_sq {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 2 f (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (h2 : MeasureTheory.IntegrableOn (fun θ => (deriv (deriv f) θ) ^ 2 * sEta θ) Iθ) :
    MeasureTheory.IntegrableOn (fun θ => (deriv (deriv f) θ) ^ 2) Iθ := by
  refine MeasureTheory.Integrable.mono' h2
    (aesm_of_continuousOn_Ioo ((continuousOn_derivDeriv hf).pow 2)) ?_
  refine Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ => ?_)
  have h1 : 1 ≤ sEta θ := one_le_sEta_of_mem_Ioo hθ
  have h0 : 0 ≤ (deriv (deriv f) θ) ^ 2 := sq_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  exact le_mul_of_one_le_right h0 h1

/-- **The absolute first-derivative slot is finite.**  `|f''| ≤ (f'')² + 1/4` and `Iθ` has
finite measure. -/
lemma integrableOn_abs_derivDeriv {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 2 f (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (h2 : MeasureTheory.IntegrableOn (fun θ => (deriv (deriv f) θ) ^ 2 * sEta θ) Iθ) :
    MeasureTheory.IntegrableOn (fun θ => |deriv (deriv f) θ|) Iθ := by
  have hU2 := integrableOn_derivDeriv_sq hf h2
  have hconst : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 / 4 : ℝ)) Iθ := by
    refine MeasureTheory.integrableOn_const (μ := volume) (s := Iθ) (C := (1 / 4 : ℝ)) ?_ ?_
    · rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top
    · simp
  have hmaj : MeasureTheory.IntegrableOn (fun θ => (deriv (deriv f) θ) ^ 2 + 1 / 4) Iθ :=
    hU2.add hconst
  refine MeasureTheory.Integrable.mono' hmaj ?_ (Filter.Eventually.of_forall (fun θ => ?_))
  · simpa only [Real.norm_eq_abs, abs_abs] using
      (aesm_of_continuousOn_Ioo (continuousOn_derivDeriv hf)).norm
  · simpa only [Real.norm_eq_abs, abs_abs] using abs_le_sq_add_quarter (deriv (deriv f) θ)

/-- **Main lemma.**  If `f` is `C²` on the open angular interval and the second-derivative slot
`(f'')² sin(2θ)^{-η}` is integrable, then `f` is bounded, hence the zero-th slot
`f² sin(2θ)^{-η}` is integrable. -/
theorem slice_zero_slot_finite {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)))
    (h2 : MeasureTheory.IntegrableOn
      (fun θ => (deriv (deriv f) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn
      (fun θ => (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ := by
  change MeasureTheory.IntegrableOn (fun θ => (f θ) ^ 2 * sEta θ) Iθ
  -- elementary facts about the interval
  have hIθ_meas : MeasurableSet Iθ := by rw [Work.Spaces.Iθ]; exact measurableSet_Icc
  have hIθ_lt_top : (volume Iθ) < ⊤ := by
    rw [lt_top_iff_ne_top, Work.Spaces.Iθ, Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  have h4mem : (Real.pi / 4) ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  -- differentiability facts
  have hd1 : ContDiffOn ℝ 1 (deriv f) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hf.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)
  have hd1cont : ContinuousOn (deriv f) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := hd1.continuousOn
  -- the fundamental theorem of calculus for `f` and for `deriv f`, on subintervals
  have hftc_f : ∀ {a b : ℝ}, a ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      b ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) → a ≤ b →
      ∫ t in a..b, deriv f t = f b - f a := by
    intro a b ha hb hab
    have hcd : ContDiffOn ℝ 1 f (Set.Icc a b) :=
      (hf.of_le (m := 1) (by norm_num)).mono
        (fun x hx => ⟨by linarith [hx.1, ha.1], by linarith [hx.2, hb.2]⟩)
    exact intervalIntegral.integral_deriv_of_contDiffOn_Icc hcd hab
  have hftc_d : ∀ {a b : ℝ}, a ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      b ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) → a ≤ b →
      ∫ t in a..b, deriv (deriv f) t = deriv f b - deriv f a := by
    intro a b ha hb hab
    have hcd : ContDiffOn ℝ 1 (deriv f) (Set.Icc a b) :=
      hd1.mono (fun x hx => ⟨by linarith [hx.1, ha.1], by linarith [hx.2, hb.2]⟩)
    exact intervalIntegral.integral_deriv_of_contDiffOn_Icc hcd hab
  -- the total mass of `|f''|`
  set M : ℝ := ∫ θ in Iθ, |deriv (deriv f) θ| with hM
  have hMnn : 0 ≤ M := by
    rw [hM]
    exact setIntegral_nonneg hIθ_meas (fun θ _ => abs_nonneg _)
  have hU1 : MeasureTheory.IntegrableOn (fun θ => |deriv (deriv f) θ|) Iθ :=
    integrableOn_abs_derivDeriv hf h2
  -- comparing the integral of `|f''|` over a subinterval with the full one
  have hMassMono : ∀ {a b : ℝ}, a ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      b ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) → a ≤ b →
      ∫ s in a..b, |deriv (deriv f) s| ≤ M := by
    intro a b ha hb hab
    rw [hM, intervalIntegral.integral_of_le hab]
    refine MeasureTheory.setIntegral_mono_set hU1
      (Filter.Eventually.of_forall (fun x => abs_nonneg (deriv (deriv f) x))) (Filter.Eventually.of_forall ?_)
    intro x hx
    rw [Set.mem_Ioc] at hx
    exact ⟨by linarith [hx.1, ha.1], by linarith [hx.2, hb.2]⟩
  -- `deriv f` is bounded
  have hderiv_bound : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |deriv f t| ≤ |deriv f (Real.pi / 4)| + M := by
    intro t ht
    rcases le_total (Real.pi / 4) t with h4t | ht4
    · have hftc := hftc_d h4mem ht h4t
      calc |deriv f t| = |deriv f (Real.pi / 4) + (deriv f t - deriv f (Real.pi / 4))| := by
            rw [show deriv f (Real.pi / 4) + (deriv f t - deriv f (Real.pi / 4)) = deriv f t
              from by ring]
        _ ≤ |deriv f (Real.pi / 4)| + |deriv f t - deriv f (Real.pi / 4)| := abs_add_le _ _
        _ = |deriv f (Real.pi / 4)| + |∫ s in (Real.pi / 4)..t, deriv (deriv f) s| := by
            rw [hftc]
        _ ≤ |deriv f (Real.pi / 4)| + ∫ s in (Real.pi / 4)..t, |deriv (deriv f) s| :=
            add_le_add_right (intervalIntegral.abs_integral_le_integral_abs h4t) _
        _ ≤ |deriv f (Real.pi / 4)| + M := add_le_add_right (hMassMono h4mem ht h4t) _
    · have hftc := hftc_d ht h4mem ht4
      calc |deriv f t| = |deriv f (Real.pi / 4) - (deriv f (Real.pi / 4) - deriv f t)| := by
            rw [show deriv f (Real.pi / 4) - (deriv f (Real.pi / 4) - deriv f t) = deriv f t
              from by ring]
        _ ≤ |deriv f (Real.pi / 4)| + |deriv f (Real.pi / 4) - deriv f t| := abs_sub _ _
        _ = |deriv f (Real.pi / 4)| + |∫ s in t..(Real.pi / 4), deriv (deriv f) s| := by
            rw [hftc]
        _ ≤ |deriv f (Real.pi / 4)| + ∫ s in t..(Real.pi / 4), |deriv (deriv f) s| :=
            add_le_add_right (intervalIntegral.abs_integral_le_integral_abs ht4) _
        _ ≤ |deriv f (Real.pi / 4)| + M := add_le_add_right (hMassMono ht h4mem ht4) _
  -- integrability of `|deriv f|`, and its total mass
  have hIntDerivF : MeasureTheory.IntegrableOn (fun t => |deriv f t|) Iθ := by
    refine MeasureTheory.IntegrableOn.of_bound (f := fun t => |deriv f t|) hIθ_lt_top ?_
      (|deriv f (Real.pi / 4)| + M) ?_
    · simpa only [Real.norm_eq_abs] using (aesm_of_continuousOn_Ioo hd1cont).norm
    · refine Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ => ?_)
      simpa only [Real.norm_eq_abs, abs_abs] using hderiv_bound θ hθ
  have hIntDerivF_le :
      ∫ t in Iθ, |deriv f t| ≤ (Real.pi / 2) * (|deriv f (Real.pi / 4)| + M) := by
    have hvol_meas : volume.real Iθ = Real.pi / 2 := by
      rw [MeasureTheory.measureReal_def, Work.Spaces.Iθ, Real.volume_Icc,
        ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
      ring
    have hconst : MeasureTheory.IntegrableOn
        (fun _ : ℝ => (|deriv f (Real.pi / 4)| + M)) Iθ := by
      refine MeasureTheory.integrableOn_const (μ := volume) (s := Iθ)
        (C := |deriv f (Real.pi / 4)| + M) ?_ ?_
      · rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top
      · simp
    calc ∫ t in Iθ, |deriv f t| ≤ ∫ t in Iθ, (|deriv f (Real.pi / 4)| + M) :=
          MeasureTheory.integral_mono_ae hIntDerivF hconst
            (Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo
              (fun θ hθ => hderiv_bound θ hθ))
      _ = (Real.pi / 2) * (|deriv f (Real.pi / 4)| + M) := by
          rw [MeasureTheory.setIntegral_const, hvol_meas]
          simp [smul_eq_mul]
  -- comparing the integral of `|deriv f|` over a subinterval with the full one
  have hFMassMono : ∀ {a b : ℝ}, a ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      b ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) → a ≤ b →
      ∫ t in a..b, |deriv f t| ≤ ∫ t in Iθ, |deriv f t| := by
    intro a b ha hb hab
    rw [intervalIntegral.integral_of_le hab]
    refine MeasureTheory.setIntegral_mono_set hIntDerivF
      (Filter.Eventually.of_forall (fun x => abs_nonneg (deriv f x))) (Filter.Eventually.of_forall ?_)
    intro x hx
    rw [Set.mem_Ioc] at hx
    exact ⟨by linarith [hx.1, ha.1], by linarith [hx.2, hb.2]⟩
  -- `f` is bounded
  have hf_bound : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |f θ| ≤ |f (Real.pi / 4)| + (Real.pi / 2) * (|deriv f (Real.pi / 4)| + M) := by
    intro θ hθ
    rcases le_total (Real.pi / 4) θ with h4θ | hθ4
    · have hftc := hftc_f h4mem hθ h4θ
      calc |f θ| = |f (Real.pi / 4) + (f θ - f (Real.pi / 4))| := by
            rw [show f (Real.pi / 4) + (f θ - f (Real.pi / 4)) = f θ from by ring]
        _ ≤ |f (Real.pi / 4)| + |f θ - f (Real.pi / 4)| := abs_add_le _ _
        _ = |f (Real.pi / 4)| + |∫ t in (Real.pi / 4)..θ, deriv f t| := by rw [hftc]
        _ ≤ |f (Real.pi / 4)| + ∫ t in (Real.pi / 4)..θ, |deriv f t| :=
            add_le_add_right (intervalIntegral.abs_integral_le_integral_abs h4θ) _
        _ ≤ |f (Real.pi / 4)| + ∫ t in Iθ, |deriv f t| :=
            add_le_add_right (hFMassMono h4mem hθ h4θ) _
        _ ≤ |f (Real.pi / 4)| + (Real.pi / 2) * (|deriv f (Real.pi / 4)| + M) :=
            add_le_add_right hIntDerivF_le _
    · have hftc := hftc_f hθ h4mem hθ4
      calc |f θ| = |f (Real.pi / 4) - (f (Real.pi / 4) - f θ)| := by
            rw [show f (Real.pi / 4) - (f (Real.pi / 4) - f θ) = f θ from by ring]
        _ ≤ |f (Real.pi / 4)| + |f (Real.pi / 4) - f θ| := abs_sub _ _
        _ = |f (Real.pi / 4)| + |∫ t in θ..(Real.pi / 4), deriv f t| := by rw [hftc]
        _ ≤ |f (Real.pi / 4)| + ∫ t in θ..(Real.pi / 4), |deriv f t| :=
            add_le_add_right (intervalIntegral.abs_integral_le_integral_abs hθ4) _
        _ ≤ |f (Real.pi / 4)| + ∫ t in Iθ, |deriv f t| :=
            add_le_add_right (hFMassMono hθ h4mem hθ4) _
        _ ≤ |f (Real.pi / 4)| + (Real.pi / 2) * (|deriv f (Real.pi / 4)| + M) :=
            add_le_add_right hIntDerivF_le _
  -- conclude by domination against `B² · sEta`
  set B : ℝ := |f (Real.pi / 4)| + (Real.pi / 2) * (|deriv f (Real.pi / 4)| + M) with hB
  have hBnn : 0 ≤ B := by
    rw [hB]
    have h1 : 0 ≤ (Real.pi / 2) * (|deriv f (Real.pi / 4)| + M) := by positivity
    linarith [abs_nonneg (f (Real.pi / 4))]
  have hmaj : MeasureTheory.IntegrableOn (fun θ => B ^ 2 * sEta θ) Iθ :=
    sEta_integrableOn.const_mul (B ^ 2)
  refine MeasureTheory.Integrable.mono' hmaj (aesm_of_continuousOn_Ioo ?_) ?_
  · exact (hf.continuousOn.pow 2).mul continuousOn_sEta
  · refine Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ => ?_)
    have hb := hf_bound θ hθ
    have hsnn : 0 ≤ sEta θ := le_of_lt (sEta_pos_of_mem_Ioo hθ)
    have hsq : (f θ) ^ 2 ≤ B ^ 2 := by
      rw [hB]
      have h := pow_le_pow_left₀ (abs_nonneg (f θ)) hb 2
      rwa [sq_abs] at h
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hsnn)]
    exact mul_le_mul_of_nonneg_right hsq hsnn

end Work.FTS.EllSol
