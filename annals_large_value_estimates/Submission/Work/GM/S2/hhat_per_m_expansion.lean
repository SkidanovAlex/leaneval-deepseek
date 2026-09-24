import Mathlib
import Submission.Work.GM.S2.Defs
import Submission.Work.GM.S2.hhat_decay
import Submission.Work.GM.S2.log_window1

/-!
# The reflection identity for a single `m` (the engine of GM Lemma 6.2)

Let `ψ = w²` (`psi`) be the weight inside `hfun`, and let `hinv` be the log-Fourier
representation `ψ(u) = (1/u) ∫ ĝ₁(ξ) u^{2πiξ} dξ` of the weight for `u > 0`
(available from `Work.GM.S2.log_window1`).  Then, for `N ≥ 1`, `1 ≤ m ≤ M`, `t : ℝ`
arbitrary and with `σ = t + 2πξ`,

`ĥ_t(mN) = ∫ ξ, ĝ₁(ξ) · (mN)^{-iσ} · ∫_N^{2MN} v^{iσ-1} e(-v) dv`.

The proof is the standard Fourier–Fubini computation:

1. `ĥ_t(mN) = ∫_{1/m}^{2M/m} hhatAmp (mN) u · hhatPhase t u du` (the amplitude vanishes
   off `[1,2] ⊆ [1/m, 2M/m]`),
2. pointwise on `u > 0` the log-Fourier representation of `ψ` turns the integrand into
   `∫ ξ, oscG t (mN) u ξ`,
3. Fubini (`oscG_integrable_prod` supplies the domination `‖oscG u ξ‖ ≤ ‖ĝ₁ ξ‖ / a`),
4. the substitution `v = mN u` in `∫ u, oscU (mN) σ u` (`integral_oscU_subst`).
-/

open MeasureTheory
open scoped Real BigOperators

set_option autoImplicit false

namespace Work.GM.S2

/-! ## Elementary rewritings -/

/-- `ĥ_t(ξ)` as the full-line integral of amplitude times phase. -/
theorem hhat_eq_integral_amp_full (t ξ : ℝ) :
    Submission.GM.hhat t ξ = ∫ u, hhatAmp ξ u * hhatPhase t u := by
  rw [Submission.GM.hhat, Real.fourier_real_eq_integral_exp_smul]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun v => ?_))
  simp only []
  rw [smul_eq_mul, hhatKernel_eq ξ v, hfun_eq_amp_phase t v, hhatAmp]
  ring

/-- `ĥ_t(ξ) = ∫_a^b hhatAmp ξ u · hhatPhase t u du` whenever `[1,2] ⊆ [a,b]`
(the integrand is supported in `[1,2]`). -/
theorem hhat_eq_setIntegral_Icc (t ξ a b : ℝ) (ha : a ≤ 1) (hb : 2 ≤ b) :
    Submission.GM.hhat t ξ = ∫ u in Set.Icc a b, hhatAmp ξ u * hhatPhase t u := by
  rw [hhat_eq_integral_amp_full]
  refine (setIntegral_eq_integral_of_forall_compl_eq_zero ?_).symm
  intro u hu
  have hmem : u ∉ Set.Icc (1 : ℝ) 2 := fun h => hu ⟨le_trans ha h.1, le_trans h.2 hb⟩
  rw [hhatAmp_zero_of_notMem ξ u hmem, zero_mul]

/-! ## The oscillatory kernels -/

/-- The oscillatory kernel `u ↦ u^{iσ-1} e(-cu)` of the reflected `m`-sum. -/
noncomputable def oscU (c σ : ℝ) (u : ℝ) : ℂ :=
  (u : ℂ) ^ (Complex.I * (σ : ℂ) - 1) *
    Complex.exp (-(2 * Real.pi * Complex.I * ((c * u : ℝ) : ℂ)))

/-- The oscillatory kernel `v ↦ v^{iσ-1} e(-v)`. -/
noncomputable def oscV (σ : ℝ) (v : ℝ) : ℂ :=
  (v : ℂ) ^ (Complex.I * (σ : ℂ) - 1) *
    Complex.exp (-(2 * Real.pi * Complex.I * ((v : ℝ) : ℂ)))

/-- The double integrand of the Fourier–Fubini step,
`oscG t c u ξ = ĝ₁(ξ) · u^{i(t+2πξ)-1} e(-cu)`. -/
noncomputable def oscG (t c : ℝ) (u ξ : ℝ) : ℂ :=
  ghat1 ξ * ((u : ℂ) ^ (Complex.I * ((t + 2 * Real.pi * ξ : ℝ) : ℂ) - 1) *
    Complex.exp (-(2 * Real.pi * Complex.I * ((c * u : ℝ) : ℂ))))

/-- The exponent is additive: `u^{2πiξ} u^{it} / u = u^{i(t+2πξ)-1}` for `u > 0`. -/
lemma cpow_osc_aux (u : ℝ) (hu : 0 < u) (t ξ : ℝ) :
    (u : ℂ) ^ (2 * Real.pi * Complex.I * (ξ : ℂ)) *
        ((1 / (u : ℂ)) * (u : ℂ) ^ (Complex.I * (t : ℂ)))
      = (u : ℂ) ^ (Complex.I * ((t + 2 * Real.pi * ξ : ℝ) : ℂ) - 1) := by
  have hune : (u : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hu
  rw [one_div, mul_comm ((u : ℂ)⁻¹) ((u : ℂ) ^ (Complex.I * (t : ℂ))), ← mul_assoc,
    ← Complex.cpow_add (2 * Real.pi * Complex.I * (ξ : ℂ)) (Complex.I * (t : ℂ)) hune,
    Complex.cpow_sub _ 1 hune, Complex.cpow_one, div_eq_mul_inv]
  congr 1
  push_cast
  ring_nf

/-- **The pointwise log-Fourier representation of the amplitude.**  For `u > 0` the
integrand `hhatAmp c u · hhatPhase t u = ψ(u) u^{it} e(-cu)` equals
`∫ ξ, oscG t c u ξ`. -/
lemma hhatAmp_mul_hhatPhase_eq_integral
    (hinv : ∀ u : ℝ, 0 < u →
      ((psi u : ℝ) : ℂ) = (1 / (u : ℂ)) * MeasureTheory.integral MeasureTheory.volume
        (fun ξ : ℝ => ghat1 ξ * (u : ℂ) ^ (2 * Real.pi * Complex.I * (ξ : ℂ))))
    (t c u : ℝ) (hu : 0 < u) :
    hhatAmp c u * hhatPhase t u = ∫ ξ, oscG t c u ξ := by
  have hune : (u : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hu
  have hp : hhatPhase t u = (u : ℂ) ^ (Complex.I * (t : ℂ)) := by
    rw [hhatPhase]
    conv_rhs => rw [Complex.cpow_def_of_ne_zero hune, ← Complex.ofReal_log hu.le]
    congr 1
    ring
  have hk : hhatKernel c u = Complex.exp (-(2 * Real.pi * Complex.I * ((c * u : ℝ) : ℂ))) := by
    rw [hhatKernel]
    congr 1
    push_cast
    ring
  have hL : hhatAmp c u * hhatPhase t u
      = ((psi u : ℝ) : ℂ) * (u : ℂ) ^ (Complex.I * (t : ℂ)) *
          Complex.exp (-(2 * Real.pi * Complex.I * ((c * u : ℝ) : ℂ))) := by
    rw [hhatAmp, hk, hp, psi]
    ring
  rw [hL, hinv u hu]
  rw [show ((1 / (u : ℂ)) * ∫ (ξ : ℝ), ghat1 ξ * (u : ℂ) ^ (2 * Real.pi * Complex.I * (ξ : ℂ))) *
        (u : ℂ) ^ (Complex.I * (t : ℂ)) *
          Complex.exp (-(2 * Real.pi * Complex.I * ((c * u : ℝ) : ℂ)))
      = (∫ (ξ : ℝ), ghat1 ξ * (u : ℂ) ^ (2 * Real.pi * Complex.I * (ξ : ℂ))) *
        ((1 / (u : ℂ)) * (u : ℂ) ^ (Complex.I * (t : ℂ)) *
          Complex.exp (-(2 * Real.pi * Complex.I * ((c * u : ℝ) : ℂ)))) by ring]
  rw [← integral_mul_const]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun ξ => ?_))
  simp only []
  rw [oscG]
  rw [show ghat1 ξ * (u : ℂ) ^ (2 * Real.pi * Complex.I * (ξ : ℂ)) *
        ((1 / (u : ℂ)) * (u : ℂ) ^ (Complex.I * (t : ℂ)) *
          Complex.exp (-(2 * Real.pi * Complex.I * ((c * u : ℝ) : ℂ))))
      = (ghat1 ξ * ((u : ℂ) ^ (2 * Real.pi * Complex.I * (ξ : ℂ)) *
          ((1 / (u : ℂ)) * (u : ℂ) ^ (Complex.I * (t : ℂ))))) *
          Complex.exp (-(2 * Real.pi * Complex.I * ((c * u : ℝ) : ℂ))) by ring,
    cpow_osc_aux u hu t ξ]
  ring

/-- **The substitution `v = m N u`** in the oscillatory integral. -/
lemma integral_oscU_subst (m M N : ℕ) (σ : ℝ) (hm : 1 ≤ m) (hmM : m ≤ M) (hN : 1 ≤ N) :
    ∫ u in ((1 : ℝ) / (m : ℝ))..(2 * (M : ℝ) / (m : ℝ)), oscU ((m : ℝ) * (N : ℝ)) σ u
      = (((m : ℂ) * (N : ℂ)) ^ (-(Complex.I * (σ : ℂ)))) *
        ∫ v in (N : ℝ)..(2 * (M : ℝ) * (N : ℝ)), oscV σ v := by
  set c : ℝ := (m : ℝ) * (N : ℝ) with hc
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hcpos : 0 < c := by rw [hc]; positivity
  have hcne : c ≠ 0 := ne_of_gt hcpos
  have hcne' : (c : ℂ) ≠ 0 := by exact_mod_cast hcne
  have hca : c * ((1 : ℝ) / (m : ℝ)) = (N : ℝ) := by rw [hc]; field_simp
  have hcb : c * (2 * (M : ℝ) / (m : ℝ)) = 2 * (M : ℝ) * (N : ℝ) := by rw [hc]; field_simp
  have hpoint : ∀ u : ℝ, 0 < u → oscU c σ u
      = ((c : ℂ) ^ (-(Complex.I * (σ : ℂ) - 1))) * oscV σ (c * u) := by
    intro u hu
    have hu0 : (0 : ℝ) ≤ u := le_of_lt hu
    have hcc : (0 : ℝ) ≤ c := le_of_lt hcpos
    have h1 : ((c * u : ℝ) : ℂ) = (c : ℂ) * (u : ℂ) := by push_cast; ring
    have hcu : (c : ℂ) ^ (Complex.I * (σ : ℂ) - 1) ≠ 0 :=
      Complex.cpow_ne_zero_iff.mpr (Or.inl hcne')
    rw [oscU, oscV, h1, Complex.mul_cpow_ofReal_nonneg hcc hu0, Complex.cpow_neg]
    conv_rhs => rw [mul_assoc]
    rw [inv_mul_cancel_left₀ hcu]
  have hM1 : (1 : ℝ) ≤ M := by
    have h1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have h2 : (m : ℝ) ≤ (M : ℝ) := by exact_mod_cast hmM
    linarith
  have hmin : (0 : ℝ) < min ((1 : ℝ) / (m : ℝ)) (2 * (M : ℝ) / (m : ℝ)) := by
    refine lt_min (by positivity) (div_pos (by linarith : (0:ℝ) < 2 * (M:ℝ)) hm0)
  have hab : ((1 : ℝ) / (m : ℝ)) ≤ (2 * (M : ℝ) / (m : ℝ)) := by
    rw [div_le_div_iff_of_pos_right hm0]; linarith
  calc ∫ u in ((1 : ℝ) / (m : ℝ))..(2 * (M : ℝ) / (m : ℝ)), oscU c σ u
      = ∫ u in ((1 : ℝ) / (m : ℝ))..(2 * (M : ℝ) / (m : ℝ)),
          ((c : ℂ) ^ (-(Complex.I * (σ : ℂ) - 1))) * oscV σ (c * u) := by
        apply intervalIntegral.integral_congr
        intro u hu
        exact hpoint u (lt_of_lt_of_le hmin hu.1)
    _ = ((c : ℂ) ^ (-(Complex.I * (σ : ℂ) - 1))) *
          ∫ u in ((1 : ℝ) / (m : ℝ))..(2 * (M : ℝ) / (m : ℝ)), oscV σ (c * u) := by
        rw [intervalIntegral.integral_const_mul]
    _ = ((c : ℂ) ^ (-(Complex.I * (σ : ℂ) - 1))) *
          (c⁻¹ • ∫ v in (c * ((1 : ℝ) / (m : ℝ)))..(c * (2 * (M : ℝ) / (m : ℝ))), oscV σ v) := by
        congr 1
        rw [← intervalIntegral.smul_integral_comp_mul_left (oscV σ) c, inv_smul_smul₀ hcne]
    _ = ((c : ℂ) ^ (-(Complex.I * (σ : ℂ) - 1))) *
          (c⁻¹ • ∫ v in (N : ℝ)..(2 * (M : ℝ) * (N : ℝ)), oscV σ v) := by rw [hca, hcb]
    _ = (((m : ℂ) * (N : ℂ)) ^ (-(Complex.I * (σ : ℂ)))) *
          ∫ v in (N : ℝ)..(2 * (M : ℝ) * (N : ℝ)), oscV σ v := by
        rw [Complex.real_smul, Complex.ofReal_inv, ← mul_assoc]
        have hkey : (c : ℂ) ^ (-(Complex.I * (σ : ℂ) - 1)) * (c : ℂ)⁻¹
            = (c : ℂ) ^ (-(Complex.I * (σ : ℂ))) := by
          rw [show -(Complex.I * (σ : ℂ)) = -(Complex.I * (σ : ℂ) - 1) + (-1) by ring,
            Complex.cpow_add _ (-1) hcne', Complex.cpow_neg (c : ℂ) 1, Complex.cpow_one]
        rw [hkey, hc]
        push_cast
        ring


/-- **Domination of the Fourier–Fubini integrand.**  `oscG` is integrable on
`(volume ↾ [a,b]) × volume` for `a > 0`: on `u ≥ a > 0` its modulus is
`‖ĝ₁(ξ)‖ / u ≤ ‖ĝ₁(ξ)‖ / a`. -/
lemma oscG_integrable_prod (hint : Integrable ghat1) (t c a b : ℝ) (ha : 0 < a) :
    Integrable (Function.uncurry (fun u ξ : ℝ => oscG t c u ξ))
      ((volume.restrict (Set.Icc a b)).prod volume) := by
  have hdom : Integrable (fun p : ℝ × ℝ => a⁻¹ * ‖ghat1 p.2‖)
      ((volume.restrict (Set.Icc a b)).prod volume) :=
    (integrableOn_const (μ := volume) (s := Set.Icc a b) (C := a⁻¹)
      (ne_of_lt measure_Icc_lt_top)).mul_prod hint.norm
  have hcont : ContinuousOn (Function.uncurry (fun u ξ : ℝ => oscG t c u ξ))
      (Set.Icc a b ×ˢ (Set.univ : Set ℝ)) := by
    rw [show Function.uncurry (fun u ξ : ℝ => oscG t c u ξ)
        = (fun p : ℝ × ℝ => ghat1 p.2 *
            ((p.1 : ℂ) ^ (Complex.I * ((t + 2 * Real.pi * p.2 : ℝ) : ℂ) - 1) *
              Complex.exp (-(2 * Real.pi * Complex.I * ((c * p.1 : ℝ) : ℂ)))))
        from rfl]
    refine ContinuousOn.mul ?_ (ContinuousOn.mul ?_ ?_)
    · exact (ghat1_continuous.comp continuous_snd).continuousOn
    · refine ContinuousOn.cpow ?_ ?_ ?_
      · exact (Complex.continuous_ofReal.comp continuous_fst).continuousOn
      · exact ((continuous_const.mul (Complex.continuous_ofReal.comp
          (continuous_const.add (continuous_const.mul continuous_snd)))).sub
          continuous_const).continuousOn
      · intro p hp
        rw [Complex.mem_slitPlane_iff]
        left
        exact_mod_cast (lt_of_lt_of_le ha hp.1.1)
    · exact Complex.continuous_exp.comp_continuousOn (by fun_prop)
  have hπ : (volume.restrict (Set.Icc a b)).prod (volume : Measure ℝ)
      = ((volume : Measure ℝ).prod (volume : Measure ℝ)).restrict
          (Set.Icc a b ×ˢ (Set.univ : Set ℝ)) := by
    rw [← Measure.prod_restrict (Set.Icc a b) (Set.univ), Measure.restrict_univ]
  have hmeas : MeasurableSet (Set.Icc a b ×ˢ (Set.univ : Set ℝ)) :=
    measurableSet_Icc.prod MeasurableSet.univ
  refine hdom.mono' ?_ ?_
  · rw [hπ]
    exact hcont.aestronglyMeasurable hmeas
  · rw [hπ]
    refine ae_restrict_of_forall_mem hmeas (fun p hp => ?_)
    have hp1 : 0 < p.1 := lt_of_lt_of_le ha hp.1.1
    show ‖oscG t c p.1 p.2‖ ≤ a⁻¹ * ‖ghat1 p.2‖
    rw [oscG, norm_mul, norm_mul]
    have h1 : ‖(p.1 : ℂ) ^ (Complex.I * ((t + 2 * Real.pi * p.2 : ℝ) : ℂ) - 1)‖ =
        (p.1)⁻¹ := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hp1]
      have hre : (Complex.I * ((t + 2 * Real.pi * p.2 : ℝ) : ℂ) - 1).re = -1 := by simp
      rw [hre, Real.rpow_neg_one]
    have h2 : ‖Complex.exp (-(2 * Real.pi * Complex.I * ((c * p.1 : ℝ) : ℂ)))‖ = 1 := by
      rw [Complex.norm_exp]
      have hre : (-(2 * Real.pi * Complex.I * ((c * p.1 : ℝ) : ℂ))).re = 0 := by simp
      rw [hre, Real.exp_zero]
    rw [h1, h2, mul_one]
    have hinv : (p.1)⁻¹ ≤ a⁻¹ := (inv_le_inv₀ hp1 ha).mpr hp.1.1
    calc ‖ghat1 p.2‖ * (p.1)⁻¹ ≤ ‖ghat1 p.2‖ * a⁻¹ :=
          mul_le_mul_of_nonneg_left hinv (norm_nonneg _)
      _ = a⁻¹ * ‖ghat1 p.2‖ := by ring

/-! ## The reflection identity for one `m` -/

/-- **The reflection identity for one `m`** (the engine of GM Lemma 6.2).

Let `ψ = w² = hfun`'s weight, `hhat t ξ = 𝓕(h_t) ξ` (so `hhat t ξ = ∫_u hhatAmp ξ u * hhatPhase t u`,
available as `Work.GM.S2.hhat_eq_integral_amp` in `hhat_decay`) and `hinv` the log-Fourier
representation `ψ(u) = (1/u) ∫ ξ, ĝ₁(ξ) u^{2πiξ} dξ` of the weight (`u > 0`, from `log_window1`).
Let `N ≥ 1`, `1 ≤ m ≤ M`, `t : ℝ` be arbitrary and put `σ = t + 2πξ`.

Then `ĥ_t(mN)` equals the `ξ`-integral of `ĝ₁(ξ) · (mN)^{-iσ} · ∫_N^{2MN} v^{iσ-1} e(-v) dv`. -/
theorem hhat_per_m_expansion
    (hinv : ∀ u : ℝ, 0 < u →
      ((Work.GM.S2.psi u : ℝ) : ℂ) = (1 / (u : ℂ)) * MeasureTheory.integral MeasureTheory.volume
        (fun ξ : ℝ => Work.GM.S2.ghat1 ξ * (u : ℂ) ^ (2 * Real.pi * Complex.I * (ξ : ℂ))))
    (hint : MeasureTheory.Integrable Work.GM.S2.ghat1)
    (N M m : ℕ) (hN : 1 ≤ N) (hm : 1 ≤ m) (hmM : m ≤ M) (t : ℝ) :
    Submission.GM.hhat t ((m : ℝ) * (N : ℝ))
      = ∫ ξ, Work.GM.S2.ghat1 ξ * ((m : ℂ) * (N : ℂ)) ^ (-(Complex.I * ((t + 2 * Real.pi * ξ : ℝ) : ℂ))) *
          (∫ v in (N : ℝ)..(2 * (M : ℝ) * (N : ℝ)),
            (v : ℂ) ^ (Complex.I * ((t + 2 * Real.pi * ξ : ℝ) : ℂ) - 1) *
              Complex.exp (-(2 * Real.pi * Complex.I * (v : ℂ)))) := by
  set c : ℝ := (m : ℝ) * (N : ℝ) with hc
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hcpos : 0 < c := by rw [hc]; positivity
  have hcC : (c : ℂ) = (m : ℂ) * (N : ℂ) := by rw [hc]; push_cast; ring
  have ha : (0 : ℝ) < (1 : ℝ) / (m : ℝ) := by positivity
  have ha1 : (1 : ℝ) / (m : ℝ) ≤ 1 := by rw [div_le_one hm0]; exact_mod_cast hm
  have hmM' : (m : ℝ) ≤ (M : ℝ) := by exact_mod_cast hmM
  have hb2 : (2 : ℝ) ≤ 2 * (M : ℝ) / (m : ℝ) := by
    rw [le_div_iff₀ hm0]; linarith
  have hab : ((1 : ℝ) / (m : ℝ)) ≤ (2 * (M : ℝ) / (m : ℝ)) := le_trans ha1 (by linarith)
  -- (1) `ĥ_t(c)` is the integral of the amplitude times the phase over `[1/m, 2M/m]`
  have hstep1 : Submission.GM.hhat t c
      = ∫ u in Set.Icc ((1 : ℝ) / (m : ℝ)) (2 * (M : ℝ) / (m : ℝ)), hhatAmp c u * hhatPhase t u :=
    hhat_eq_setIntegral_Icc t c _ _ ha1 hb2
  -- (2) pointwise log-Fourier representation
  have hstep2 : ∫ u in Set.Icc ((1 : ℝ) / (m : ℝ)) (2 * (M : ℝ) / (m : ℝ)),
        hhatAmp c u * hhatPhase t u
      = ∫ u in Set.Icc ((1 : ℝ) / (m : ℝ)) (2 * (M : ℝ) / (m : ℝ)), ∫ ξ, oscG t c u ξ := by
    refine setIntegral_congr_fun measurableSet_Icc (fun u hu => ?_)
    exact hhatAmp_mul_hhatPhase_eq_integral hinv t c u
      (lt_of_lt_of_le ha hu.1)
  -- (3) Fubini
  have hInt : Integrable (Function.uncurry (fun u ξ : ℝ => oscG t c u ξ))
      ((volume.restrict (Set.Icc ((1 : ℝ) / (m : ℝ)) (2 * (M : ℝ) / (m : ℝ)))).prod volume) :=
    oscG_integrable_prod hint t c _ _ ha
  have hstep3 : ∫ u in Set.Icc ((1 : ℝ) / (m : ℝ)) (2 * (M : ℝ) / (m : ℝ)), ∫ ξ, oscG t c u ξ
      = ∫ ξ, ∫ u in Set.Icc ((1 : ℝ) / (m : ℝ)) (2 * (M : ℝ) / (m : ℝ)), oscG t c u ξ :=
    integral_integral_swap (f := fun u ξ : ℝ => oscG t c u ξ) hInt
  -- (4) factorisation of the inner integral and the substitution `v = c u`
  have hstep4 : ∀ ξ : ℝ,
      ∫ u in Set.Icc ((1 : ℝ) / (m : ℝ)) (2 * (M : ℝ) / (m : ℝ)), oscG t c u ξ
        = ghat1 ξ * ((c : ℂ) ^ (-(Complex.I * ((t + 2 * Real.pi * ξ : ℝ) : ℂ))) *
            ∫ v in (N : ℝ)..(2 * (M : ℝ) * (N : ℝ)), oscV ((t + 2 * Real.pi * ξ : ℝ)) v) := by
    intro ξ
    set σ : ℝ := (t + 2 * Real.pi * ξ : ℝ) with hσ
    have h1 : ∫ u in Set.Icc ((1 : ℝ) / (m : ℝ)) (2 * (M : ℝ) / (m : ℝ)), oscG t c u ξ
        = ghat1 ξ * ∫ u in Set.Icc ((1 : ℝ) / (m : ℝ)) (2 * (M : ℝ) / (m : ℝ)), oscU c σ u := by
      rw [show (fun u : ℝ => oscG t c u ξ) = (fun u : ℝ => ghat1 ξ * oscU c σ u) from
        funext (fun u => rfl)]
      rw [integral_const_mul]
    rw [h1]
    have h2 : ∫ u in Set.Icc ((1 : ℝ) / (m : ℝ)) (2 * (M : ℝ) / (m : ℝ)), oscU c σ u
        = ∫ u in ((1 : ℝ) / (m : ℝ))..(2 * (M : ℝ) / (m : ℝ)), oscU c σ u := by
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
    rw [h2]
    rw [hcC]
    rw [integral_oscU_subst m M N σ hm hmM hN]
  -- (5) reassemble
  have hstep5 : ∫ ξ, ∫ u in Set.Icc ((1 : ℝ) / (m : ℝ)) (2 * (M : ℝ) / (m : ℝ)), oscG t c u ξ
      = ∫ ξ, ghat1 ξ * (c : ℂ) ^ (-(Complex.I * ((t + 2 * Real.pi * ξ : ℝ) : ℂ))) *
          ∫ v in (N : ℝ)..(2 * (M : ℝ) * (N : ℝ)), oscV ((t + 2 * Real.pi * ξ : ℝ)) v := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun ξ => ?_))
    simp only []
    rw [hstep4 ξ]
    ring
  calc Submission.GM.hhat t c
      = ∫ u in Set.Icc ((1 : ℝ) / (m : ℝ)) (2 * (M : ℝ) / (m : ℝ)), hhatAmp c u * hhatPhase t u :=
        hstep1
    _ = ∫ u in Set.Icc ((1 : ℝ) / (m : ℝ)) (2 * (M : ℝ) / (m : ℝ)), ∫ ξ, oscG t c u ξ := hstep2
    _ = ∫ ξ, ∫ u in Set.Icc ((1 : ℝ) / (m : ℝ)) (2 * (M : ℝ) / (m : ℝ)), oscG t c u ξ := hstep3
    _ = ∫ ξ, ghat1 ξ * (c : ℂ) ^ (-(Complex.I * ((t + 2 * Real.pi * ξ : ℝ) : ℂ))) *
          ∫ v in (N : ℝ)..(2 * (M : ℝ) * (N : ℝ)), oscV ((t + 2 * Real.pi * ξ : ℝ)) v := hstep5
    _ = ∫ ξ, Work.GM.S2.ghat1 ξ *
          ((m : ℂ) * (N : ℂ)) ^ (-(Complex.I * ((t + 2 * Real.pi * ξ : ℝ) : ℂ))) *
          (∫ v in (N : ℝ)..(2 * (M : ℝ) * (N : ℝ)),
            (v : ℂ) ^ (Complex.I * ((t + 2 * Real.pi * ξ : ℝ) : ℂ) - 1) *
              Complex.exp (-(2 * Real.pi * Complex.I * (v : ℂ)))) := by
        refine integral_congr_ae (Filter.Eventually.of_forall (fun ξ => ?_))
        simp only []
        rw [hcC]
        simp only [oscV]

end Work.GM.S2
