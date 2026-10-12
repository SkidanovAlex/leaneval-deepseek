import Mathlib.Tactic.Have
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Submission.Work.BoseFixR.LatGreen.ExistsRadialShadow
import Submission.Work.BoseFixR.LatGreen.InvOneAddNormSubIntegralLe
import Submission.Work.BoseFixR.LatGreen.RadialWeightFourierDecayExplicit
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.LatGreen.RadialSmoothCosDecaySchwartz`

The angular decay of a radial weight against a smooth compactly supported factor, via the
Fourier/convolution route (an alternative to `Work.BoseFixR.LatGreen.RadialSmoothCosDecay`, which
assumes only `ContDiff ℝ 1 F` and instead slices the sphere and integrates by parts in the
latitude).

Contents:

* `exists_schwartz_inversion` — for `F` smooth with compact support, `𝓕F` is Schwartz and `F` is
  the pointwise inverse Fourier integral of `𝓕F`;
* `fubini_mul_fourierChar` — the Parseval/Fubini step
  `∫_x W x Ψ x 𝐞(-⟪ν,x⟫) = ∫_η (𝓕⁻Ψ) η · 𝓕W (ν - η)` for integrable `W` and `Ψ = 𝓕⁻G`;
* `integrable_radial_abs_of_integrableOn` — `|ψ| ‖·‖` is integrable from `IntegrableOn (r ↦ r|ψ r|)`
  (only the *magnitude* of `ψ` has to be a.e. measurable, which the hypothesis supplies);
* `decay_radial_pair` — the decay `|∫ ρ ‖x‖ F x cos⟪q,x⟫| ≤ C/(1+‖q‖)` for a *measurable* radial
  profile `ρ` vanishing on `[R,∞)`, with the *explicit* constant
  `C = (8π(R+1)+8)·(∫₀^∞ r|ρ r|)·(2π)²·∫ (1+‖η‖)‖𝓕F η‖` (so the estimate is uniform over a
  family of profiles with bounded first moments);
* `RadialSmoothCosDecaySchwartz` — the target, assembled by splitting on the a.e. strong
  measurability of the integrand: where it fails the Bochner integral is `0`
  (`MeasureTheory.integral_undef`), and where it holds the (not assumed measurable!) profile `ψ`
  is replaced by the radial shadow `ρ` of `Work.BoseFixR.LatGreen.ExistsRadialShadow`.

The measurability discussion matters: without it, the *sign* of `ψ` is invisible to the
hypotheses `IntegrableOn (r ↦ r|ψ r|)` and `ψ = 0` on `[R,∞)`, so `ψ` may fail to be a.e. strongly
measurable; the integrand is then not in the domain of the Bochner integral and contributes `0`.
-/

noncomputable section

open MeasureTheory
open scoped Real FourierTransform ContDiff

namespace Work.BoseFixR.LatGreen

local notation "E" => EuclideanSpace ℝ (Fin 3)

/-! ## Auxiliary identities on the Fourier character -/

/-- `𝐞 (a+b) = 𝐞 a · 𝐞 b` for the complexified Fourier character. -/
lemma fourierChar_mul (a b : ℝ) :
    (Real.fourierChar (a + b) : ℂ) = (Real.fourierChar a : ℂ) * (Real.fourierChar b : ℂ) := by
  rw [AddChar.map_add_eq_mul, Circle.coe_mul]

/-- Real part of the Fourier character. -/
lemma fourierChar_re (a : ℝ) : (Real.fourierChar a : ℂ).re = Real.cos (2 * Real.pi * a) := by
  rw [Real.fourierChar_apply, Complex.exp_re]
  simp [Complex.mul_re, Complex.mul_im]

/-- Real part of `s·t·𝐞 a` for real `s`, `t`. -/
lemma re_ofReal_mul_ofReal_mul_fourierChar (s t a : ℝ) :
    ((((s : ℝ) : ℂ) * ((t : ℝ) : ℂ) * (Real.fourierChar a : ℂ))).re
      = s * t * Real.cos (2 * Real.pi * a) := by
  rw [Complex.mul_re, Complex.mul_re, Complex.mul_im, fourierChar_re]
  simp

/-- Product identity for the character evaluated on inner products. -/
lemma fourierChar_inner_prod (η ν x : E) :
    (Real.fourierChar (inner ℝ η x) : ℂ) * (Real.fourierChar (-(inner ℝ ν x)) : ℂ)
      = (Real.fourierChar (-(inner ℝ x (ν - η))) : ℂ) := by
  rw [← fourierChar_mul]
  congr 1
  rw [← real_inner_comm x (ν - η), inner_sub_left]
  congr 1
  ring

/-- **Fourier inversion packaging.**  For `F : ℝ³ → ℝ` smooth and compactly supported there is a
Schwartz function `Φ` (namely `𝓕 F` as a complex function) with
`F x = ∫ η, 𝐞⟪η,x⟫ • Φ η` pointwise. -/
theorem exists_schwartz_inversion {F : E → ℝ} (hF : ∀ n : ℕ, ContDiff ℝ n F)
    (hFsupp : HasCompactSupport F) :
    ∃ Φ : SchwartzMap E ℂ, ∀ x : E, (F x : ℂ) = ∫ η : E, 𝐞 (inner ℝ η x) • Φ η := by
  have hFtop : ContDiff ℝ ∞ F := contDiff_infty.mpr hF
  have hFcsupp : HasCompactSupport (fun x : E => (F x : ℂ)) :=
    hFsupp.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  have hFcdiff : ContDiff ℝ ∞ (fun x : E => (F x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hFtop
  refine ⟨𝓕 (HasCompactSupport.toSchwartzMap hFcsupp hFcdiff), ?_⟩
  have hcoe : ((HasCompactSupport.toSchwartzMap hFcsupp hFcdiff : SchwartzMap E ℂ) : E → ℂ)
      = fun x : E => (F x : ℂ) := rfl
  have hcont : Continuous (fun x : E => (F x : ℂ)) := Complex.continuous_ofReal.comp hFtop.continuous
  have hint1 : Integrable (fun x : E => (F x : ℂ)) := by
    have h := SchwartzMap.integrable (μ := volume) (HasCompactSupport.toSchwartzMap hFcsupp hFcdiff)
    rwa [hcoe] at h
  have hint2 : Integrable (𝓕 (fun x : E => (F x : ℂ))) := by
    have h := SchwartzMap.integrable (μ := volume) (𝓕 (HasCompactSupport.toSchwartzMap hFcsupp hFcdiff))
    rwa [SchwartzMap.fourier_coe, hcoe] at h
  have hfun : 𝓕⁻ (𝓕 (fun x : E => (F x : ℂ))) = (fun x : E => (F x : ℂ)) :=
    Continuous.fourierInv_fourier_eq hcont hint1 hint2
  intro x
  rw [← congrFun hfun x, Real.fourierInv_eq]
  simp [SchwartzMap.fourier_coe, hcoe]

/-- **The Fubini/Parseval step.**  If `Ψ` is the pointwise inverse Fourier integral of an integrable
`G` and `W` is integrable, then the product integral of `W` against `Ψ` twisted by `𝐞⟪ν,·⟫` equals
the frequency integral of `G` against `𝓕W` shifted by `ν`. -/
theorem fubini_mul_fourierChar {W Ψ G : E → ℂ} (hW : Integrable W) (hG : Integrable G)
    (hΨ : ∀ x : E, Ψ x = ∫ η : E, 𝐞 (inner ℝ η x) • G η) (ν : E) :
    (∫ x : E, W x * Ψ x * (Real.fourierChar (-(inner ℝ ν x)) : ℂ))
      = ∫ η : E, G η * 𝓕 W (ν - η) := by
  set g : E × E → ℂ := fun p => W p.1 * G p.2 * (Real.fourierChar (inner ℝ p.2 p.1) : ℂ)
      * (Real.fourierChar (-(inner ℝ ν p.1)) : ℂ) with hg
  have huncurry : Function.uncurry (fun x η => g (x, η)) = g := by
    funext p
    cases p
    rfl
  have hgint : Integrable g (volume.prod volume) := by
    refine (Integrable.mul_prod hW.norm hG.norm).mono' ?_ ?_
    · have h1 : AEStronglyMeasurable (fun p : E × E => W p.1) (volume.prod volume) :=
        hW.aestronglyMeasurable.comp_fst
      have h2 : AEStronglyMeasurable (fun p : E × E => G p.2) (volume.prod volume) :=
        hG.aestronglyMeasurable.comp_snd
      have h3 : AEStronglyMeasurable (fun p : E × E => (Real.fourierChar (inner ℝ p.2 p.1) : ℂ))
          (volume.prod volume) := by
        apply Continuous.aestronglyMeasurable
        exact continuous_subtype_val.comp (Real.continuous_fourierChar.comp (by fun_prop))
      have h4 : AEStronglyMeasurable (fun p : E × E => (Real.fourierChar (-(inner ℝ ν p.1)) : ℂ))
          (volume.prod volume) := by
        apply Continuous.aestronglyMeasurable
        exact continuous_subtype_val.comp (Real.continuous_fourierChar.comp (by fun_prop))
      have hfun : (fun p : E × E => W p.1 * G p.2 * (Real.fourierChar (inner ℝ p.2 p.1) : ℂ)
            * (Real.fourierChar (-(inner ℝ ν p.1)) : ℂ))
          = (fun p : E × E => W p.1) * (fun p : E × E => G p.2)
            * (fun p : E × E => (Real.fourierChar (inner ℝ p.2 p.1) : ℂ))
            * (fun p : E × E => (Real.fourierChar (-(inner ℝ ν p.1)) : ℂ)) := rfl
      rw [hg, hfun]
      exact ((h1.mul h2).mul h3).mul h4
    · filter_upwards with p
      simp only [hg, norm_mul, Circle.norm_coe, mul_one]
      exact le_rfl
  have hstep1 : (∫ x : E, W x * Ψ x * (Real.fourierChar (-(inner ℝ ν x)) : ℂ))
      = ∫ x : E, ∫ η : E, g (x, η) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show W x * Ψ x * (Real.fourierChar (-(inner ℝ ν x)) : ℂ) = ∫ η : E, g (x, η)
    have hpt : (∫ η : E, 𝐞 (inner ℝ η x) • G η)
        = ∫ η : E, G η * (Real.fourierChar (inner ℝ η x) : ℂ) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
      show 𝐞 (inner ℝ η x) • G η = G η * (Real.fourierChar (inner ℝ η x) : ℂ)
      rw [Circle.smul_def, smul_eq_mul, mul_comm]
    rw [hΨ x, hpt, ← integral_const_mul, ← integral_mul_const]
    congr 1
    funext η
    simp only [hg]
    ring
  have hstep2 : (∫ x : E, ∫ η : E, g (x, η)) = ∫ η : E, ∫ x : E, g (x, η) :=
    integral_integral_swap (f := fun x η => g (x, η)) (by rw [huncurry]; exact hgint)
  have hstep3 : (∫ η : E, ∫ x : E, g (x, η)) = ∫ η : E, G η * 𝓕 W (ν - η) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
    show (∫ x : E, g (x, η)) = G η * 𝓕 W (ν - η)
    have hpt : (fun x : E => g (x, η))
        = fun x : E => G η * (W x * (Real.fourierChar (-(inner ℝ x (ν - η))) : ℂ)) := by
      funext x
      simp only [hg]
      rw [mul_assoc, fourierChar_inner_prod]
      ring
    rw [hpt, integral_const_mul]
    congr 1
    rw [Real.fourier_eq]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show W x * (Real.fourierChar (-(inner ℝ x (ν - η))) : ℂ)
      = 𝐞 (-(inner ℝ x (ν - η))) • W x
    rw [Circle.smul_def, smul_eq_mul]
    ring
  rw [hstep1, hstep2, hstep3]

/-- The function `x ↦ |ψ| ‖x‖` is integrable when `r ↦ r|ψ r|` is integrable on `(0,∞)` and `ψ`
vanishes on `[R,∞)`.  (Only the *magnitude* of `ψ` has to be a.e. measurable, which the
integrability hypothesis supplies.) -/
private theorem integrable_radial_abs_of_integrableOn {ψ : ℝ → ℝ} {R : ℝ}
    (hψR : ∀ r : ℝ, R ≤ r → ψ r = 0)
    (hint : IntegrableOn (fun r : ℝ => r * |ψ r|) (Set.Ioi (0 : ℝ))) :
    Integrable (fun x : E => |ψ| ‖x‖) := by
  -- the magnitude is a.e. measurable on `(0,∞)`
  have habs : AEStronglyMeasurable (fun r : ℝ => |ψ r|) (volume.restrict (Set.Ioi (0 : ℝ))) := by
    have h1 := hint.aestronglyMeasurable
    have h2 : (fun r : ℝ => r * |ψ r|) =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
        fun r : ℝ => r * |ψ r| := Filter.EventuallyEq.rfl
    have h3 : (fun r : ℝ => (r * |ψ r|) / r) =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
        fun r : ℝ => |ψ r| := by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
      have hr0 : r ≠ 0 := ne_of_gt hr
      field_simp
    have h4 : AEStronglyMeasurable (fun r : ℝ => (r * |ψ r|) / r)
        (volume.restrict (Set.Ioi (0 : ℝ))) := by
      have h5 : (fun r : ℝ => (r * |ψ r|) / r)
          = fun r : ℝ => (r * |ψ r|) * r⁻¹ := by
        funext r
        rw [div_eq_mul_inv]
      rw [h5]
      exact h1.mul (measurable_id.inv.aestronglyMeasurable)
    exact h4.congr h3
  -- `r ↦ r²|ψ r|` is integrable
  have hsq : IntegrableOn (fun r : ℝ => r ^ 2 * |ψ r|) (Set.Ioi (0 : ℝ)) := by
    have hdom : Integrable (fun r : ℝ => max R 1 * (r * |ψ r|))
        (volume.restrict (Set.Ioi (0 : ℝ))) := hint.const_mul (max R 1)
    refine hdom.mono' (((continuous_id.pow 2).aestronglyMeasurable).mul habs) ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
    have hrp : 0 < r := hr
    by_cases hRr : R ≤ r
    · simp [hψR r hRr]
    · have h1 : ‖r ^ 2 * |ψ r|‖ = r ^ 2 * |ψ r| := by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg r) (abs_nonneg _))]
      rw [h1, show r ^ 2 * |ψ r| = r * (r * |ψ r|) from by ring]
      exact mul_le_mul_of_nonneg_right
        (le_trans (le_of_lt (lt_of_not_ge hRr)) (le_max_left R 1))
        (mul_nonneg hrp.le (abs_nonneg _))
  exact (Submission.BoseGases.integrable_radial_r3 (f := fun r => |ψ r|)).mpr hsq

/-! ## The decay for a measurable radial weight paired against a smooth compactly supported factor -/

/-- **The Fourier/convolution decay for a measurable radial profile.**  For `ρ` measurable,
vanishing on `[R,∞)` with `r ↦ r|ρ r|` integrable, and `F` smooth with compact support, the pairing
against `F cos⟪q,·⟫` decays like `1/(1+‖q‖)` with an *explicit* constant
`(8π(R+1)+8)·(∫₀^∞ r|ρ r|)·(2π)²·M_F`, where `M_F = ∫ (1+‖η‖)‖𝓕F η‖`. -/
private theorem decay_radial_pair {ρ : ℝ → ℝ} {F : E → ℝ} {R : ℝ} (hR : 0 < R)
    (hρR : ∀ r : ℝ, R ≤ r → ρ r = 0) (hρmeas : Measurable ρ)
    (hρint : IntegrableOn (fun r : ℝ => r * |ρ r|) (Set.Ioi (0 : ℝ)))
    (hF : ∀ n : ℕ, ContDiff ℝ n F) (hFsupp : HasCompactSupport F) :
    ∃ C : ℝ, 0 ≤ C ∧
      C ≤ (8 * Real.pi * (R + 1) + 8) * (∫ r in Set.Ioi (0 : ℝ), r * |ρ r|)
          * (2 * Real.pi) ^ 2 * (∫ η : E, (1 + ‖η‖) * ‖𝓕 (fun x : E => (F x : ℂ)) η‖) ∧
      ∀ q : E, |∫ x : E, ρ ‖x‖ * F x * Real.cos (inner ℝ q x)| ≤ C / (1 + ‖q‖) := by
  have hFtop : ContDiff ℝ ∞ F := contDiff_infty.mpr hF
  have hFcsupp : HasCompactSupport (fun x : E => (F x : ℂ)) :=
    hFsupp.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  have hFcdiff : ContDiff ℝ ∞ (fun x : E => (F x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hFtop
  let Fs : SchwartzMap E ℂ := HasCompactSupport.toSchwartzMap hFcsupp hFcdiff
  have hFs : (Fs : E → ℂ) = fun x : E => (F x : ℂ) := rfl
  let Φ : SchwartzMap E ℂ := 𝓕 Fs
  have hΦcoe : (Φ : E → ℂ) = 𝓕 (fun x : E => (F x : ℂ)) := by
    rw [show (Φ : E → ℂ) = 𝓕 (Fs : E → ℂ) from SchwartzMap.fourier_coe Fs, hFs]
  have hΦint : Integrable (fun η : E => (Φ : E → ℂ) η) := SchwartzMap.integrable (μ := volume) Φ
  have hΦmom : Integrable (fun η : E => (1 + ‖η‖) * ‖(Φ : E → ℂ) η‖) := by
    have h0 := SchwartzMap.integrable (μ := volume) Φ
    have h1 := SchwartzMap.integrable_pow_mul (μ := volume) Φ 1
    have heq : (fun η : E => (1 + ‖η‖) * ‖(Φ : E → ℂ) η‖)
        = fun η : E => ‖(Φ : E → ℂ) η‖ + ‖η‖ ^ 1 * ‖(Φ : E → ℂ) η‖ := by
      funext η
      ring
    rw [heq]
    exact h0.norm.add h1
  set M : ℝ := ∫ η : E, (1 + ‖η‖) * ‖(Φ : E → ℂ) η‖ with hM
  -- the F-side inversion, with `Φ` explicit
  have hΦinv : ∀ x : E, (F x : ℂ) = ∫ η : E, 𝐞 (inner ℝ η x) • (Φ : E → ℂ) η := by
    intro x
    have hcont : Continuous (fun x : E => (F x : ℂ)) :=
      Complex.continuous_ofReal.comp hFtop.continuous
    have hint1 : Integrable (fun x : E => (F x : ℂ)) := by
      have h := SchwartzMap.integrable (μ := volume) Fs
      rwa [hFs] at h
    have hint2 : Integrable (𝓕 (fun x : E => (F x : ℂ))) := by
      rw [← hΦcoe]
      exact hΦint
    have hfun : 𝓕⁻ (𝓕 (fun x : E => (F x : ℂ))) = (fun x : E => (F x : ℂ)) :=
      Continuous.fourierInv_fourier_eq hcont hint1 hint2
    rw [← congrFun hfun x, Real.fourierInv_eq]
    simp [hΦcoe]
  -- the radial Fourier decay for `ρ`, with the explicit constant
  have hρm : AEStronglyMeasurable ρ (volume.restrict (Set.Ioi (0 : ℝ))) :=
    hρmeas.aestronglyMeasurable
  obtain ⟨hρWint, hρdecay⟩ := radialWeight_fourier_decay_explicit hR hρR hρm hρint
  set L : ℝ := ∫ r in Set.Ioi (0 : ℝ), r * |ρ r| with hL
  have hLnn : 0 ≤ L := by
    rw [hL]
    exact setIntegral_nonneg measurableSet_Ioi (fun r hr => mul_nonneg hr.le (abs_nonneg _))
  have hMnn : 0 ≤ M := by
    rw [hM]
    exact integral_nonneg (fun η => by positivity)
  refine ⟨((8 * Real.pi * (R + 1) + 8) * L) * (2 * Real.pi) ^ 2 * M, by positivity, ?_, ?_⟩
  · rw [hL, hM]
    simp only [hΦcoe]
    exact le_rfl
  · intro q
    have hFbdd : ∃ MF : ℝ, ∀ x : E, ‖F x‖ ≤ MF :=
      hFsupp.exists_bound_of_continuous hFtop.continuous
    obtain ⟨MF, hMF⟩ := hFbdd
    set ν : E := (2 * Real.pi)⁻¹ • q with hν
    have hinner : ∀ x : E, (2 * Real.pi) * (inner ℝ ν x) = inner ℝ q x := by
      intro x
      rw [hν, real_inner_smul_left]
      field_simp
    set φ : E → ℂ := fun x => ((ρ ‖x‖ : ℝ) : ℂ) * ((F x : ℝ) : ℂ)
      * (Real.fourierChar (-(inner ℝ ν x)) : ℂ) with hφ
    have hFc_asm : AEStronglyMeasurable (fun x : E => (F x : ℂ)) volume :=
      (Complex.continuous_ofReal.comp hFtop.continuous).aestronglyMeasurable
    have hch_asm : AEStronglyMeasurable
        (fun x : E => (Real.fourierChar (-(inner ℝ ν x)) : ℂ)) volume := by
      apply Continuous.aestronglyMeasurable
      exact continuous_subtype_val.comp (Real.continuous_fourierChar.comp (by fun_prop))
    have hφint : Integrable φ := by
      have hWc : Integrable (fun x : E => ((ρ ‖x‖ : ℝ) : ℂ)) := hρWint.ofReal
      have hb : ∀ᵐ x : E ∂volume,
          ‖(F x : ℂ) * (Real.fourierChar (-(inner ℝ ν x)) : ℂ)‖ ≤ MF := by
        filter_upwards with x
        rw [norm_mul, Circle.norm_coe, mul_one, Complex.norm_real]
        exact hMF x
      have h1 : Integrable (fun x : E => ((ρ ‖x‖ : ℝ) : ℂ)
          * ((F x : ℂ) * (Real.fourierChar (-(inner ℝ ν x)) : ℂ))) :=
        hWc.mul_bdd (hFc_asm.mul hch_asm) hb
      refine h1.congr (Filter.Eventually.of_forall fun x => ?_)
      simp only [hφ]
      ring
    have hJeq : (∫ x : E, ρ ‖x‖ * F x * Real.cos (inner ℝ q x)) = (∫ x : E, φ x).re := by
      have hcomp : (∫ x : E, (φ x).re) = (∫ x : E, φ x).re :=
        ContinuousLinearMap.integral_comp_comm Complex.reCLM hφint
      have hpt : (fun x : E => (φ x).re)
          = fun x : E => ρ ‖x‖ * F x * Real.cos (inner ℝ q x) := by
        funext x
        rw [hφ, re_ofReal_mul_ofReal_mul_fourierChar,
          show (2 : ℝ) * Real.pi * (-(inner ℝ ν x)) = -(inner ℝ q x) by
            rw [← hinner x]; ring,
          Real.cos_neg]
      rw [← hpt, hcomp]
    have hfub := fubini_mul_fourierChar (W := fun x : E => ((ρ ‖x‖ : ℝ) : ℂ))
      (Ψ := fun x : E => (F x : ℂ))
      (G := fun η : E => (Φ : E → ℂ) η) hρWint.ofReal hΦint hΦinv ν
    have hcontmid : Continuous fun η : E => (8 * Real.pi * (R + 1) + 8) * L / (1 + ‖ν - η‖) :=
      continuous_const.div (by fun_prop) (fun η => by positivity)
    have hmid : Integrable (fun η : E =>
        ‖(Φ : E → ℂ) η‖ * ((8 * Real.pi * (R + 1) + 8) * L / (1 + ‖ν - η‖))) := by
      refine (hΦint.norm.mul_const ((8 * Real.pi * (R + 1) + 8) * L)).mono' ?_ ?_
      · exact hΦint.norm.aestronglyMeasurable.mul hcontmid.aestronglyMeasurable
      · filter_upwards with η
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (by positivity))]
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        rw [div_le_iff₀ (by positivity)]
        nlinarith [hLnn, mul_nonneg (by positivity : (0:ℝ) ≤ 8 * Real.pi * (R + 1) + 8) hLnn,
          norm_nonneg (ν - η)]
    have hDB := InvOneAddNormSubIntegralLe (Φ := fun η : E => (Φ : E → ℂ) η) hΦint hΦmom q
    calc |∫ x : E, ρ ‖x‖ * F x * Real.cos (inner ℝ q x)|
        = |(∫ x : E, φ x).re| := by rw [hJeq]
      _ ≤ ‖∫ x : E, φ x‖ := Complex.abs_re_le_norm _
      _ = ‖∫ η : E, (Φ : E → ℂ) η * 𝓕 (fun x : E => ((ρ ‖x‖ : ℝ) : ℂ)) (ν - η)‖ := by
            rw [show (∫ x : E, φ x)
                = ∫ η : E, (Φ : E → ℂ) η * 𝓕 (fun x : E => ((ρ ‖x‖ : ℝ) : ℂ)) (ν - η)
              from hfub]
      _ ≤ ∫ η : E, ‖(Φ : E → ℂ) η * 𝓕 (fun x : E => ((ρ ‖x‖ : ℝ) : ℂ)) (ν - η)‖ :=
            norm_integral_le_integral_norm _
      _ = ∫ η : E, ‖(Φ : E → ℂ) η‖ * ‖𝓕 (fun x : E => ((ρ ‖x‖ : ℝ) : ℂ)) (ν - η)‖ := by
            refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
            show ‖(Φ : E → ℂ) η * 𝓕 (fun x : E => ((ρ ‖x‖ : ℝ) : ℂ)) (ν - η)‖
              = ‖(Φ : E → ℂ) η‖ * ‖𝓕 (fun x : E => ((ρ ‖x‖ : ℝ) : ℂ)) (ν - η)‖
            rw [norm_mul]
      _ ≤ ∫ η : E, ‖(Φ : E → ℂ) η‖ * (((8 * Real.pi * (R + 1) + 8) * L) / (1 + ‖ν - η‖)) := by
            refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun η => ?_) hmid
              (Filter.Eventually.of_forall fun η => ?_)
            · positivity
            · refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
              have hd := hρdecay (ν - η)
              rw [hL] at hd
              exact hd
      _ = ((8 * Real.pi * (R + 1) + 8) * L) * ∫ η : E, ‖(Φ : E → ℂ) η‖ / (1 + ‖ν - η‖) := by
            rw [show (fun η : E => ‖(Φ : E → ℂ) η‖
                  * (((8 * Real.pi * (R + 1) + 8) * L) / (1 + ‖ν - η‖)))
                = (fun η : E => ((8 * Real.pi * (R + 1) + 8) * L)
                  * (‖(Φ : E → ℂ) η‖ / (1 + ‖ν - η‖))) by
              funext η
              rw [div_eq_mul_inv]
              ring]
            exact integral_const_mul _ _
      _ ≤ ((8 * Real.pi * (R + 1) + 8) * L)
            * ((2 * Real.pi) ^ 2 * M / (1 + ‖q‖)) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            rw [hM, hν]
            exact hDB
      _ = (((8 * Real.pi * (R + 1) + 8) * L) * (2 * Real.pi) ^ 2 * M) / (1 + ‖q‖) := by ring

/-- **The angular decay of a radial weight against a smooth compactly supported factor
(Fourier/convolution route).**

For a profile `ψ` supported in `[0,R]` with `r ↦ r * ψ r` integrable on `(0,∞)`,
and a compactly supported function `F` which is `C^n` for every `n : ℕ` (in
particular Schwartz),

`|∫_x ψ ‖x‖ · F x · cos⟪q,x⟫| ≤ C/(1 + ‖q‖)`  for all `q`, for some `C ≥ 0`.

This is an *alternative route* to `Work.BoseFixR.LatGreen.RadialSmoothCosDecay`
(same conclusion, stronger hypothesis on `F`): instead of slicing the sphere and
integrating by parts in the latitude, it uses the Fourier representation of `F`
and the *radial* Fourier transform of `ψ(‖·‖)`.

Route (constants free; `L := ∫₀^∞ r|ψ r|`):

1. `Ghat0 p := ∫_x ψ ‖x‖ · e^{-i⟪p,x⟫} dx = ∫_x ψ ‖x‖ · cos⟪p,x⟫ dx` (the weight
   `ψ ‖·‖` is even, so the sine part vanishes) is real, even, and
   `|Ghat0 p| ≤ C₀/(1+‖p‖)` with `C₀ := 4π max(R,1) L`:
   `|Ghat0 p| ≤ ∫|ψ ‖x‖| = 4π∫₀^R r²|ψ| ≤ 4πRL`, and for `p ≠ 0`
   `|Ghat0 p| = 4π|∫₀^R r²ψ r sincR(‖p‖ r) dr| ≤ (4π/‖p‖)∫₀^R r|ψ r| dr`
   (`Work.BoseFixR.Rb5Lin.radial_fourier_sinc`, `|sincR u| ≤ 1/|u|`, `sincR 0 = 1`).

2. Fourier inversion for the Schwartz function `F` (`SchwartzMap.fourierInv_fourier_eq`,
   Mathlib's convention `𝓕⁻g x = ∫_ξ g ξ · e^{2πi⟪ξ,x⟫} dξ`) plus Fubini
   (dominated by `‖𝓕F‖₁·‖ψ‖₁ < ∞`) give
   `∫_x ψ‖x‖ F x cos⟪q,x⟫ = ½∫_ξ 𝓕F ξ · (Ghat0 (q - 2πξ) + Ghat0 (q + 2πξ)) dξ`.

3. The estimate `∫_ξ |𝓕F ξ|/(1 + ‖q - 2πξ‖) dξ ≤ C₁/(1 + ‖q‖)`: substitute
   `η = q - 2πξ` and use that `G := 𝓕F(·/2π)` is Schwartz: split `ℝ³` into
   `‖η‖ ≤ ‖q‖/2` (there `|G(q-η)| ≤ A(1+‖q‖/2)^{-N}`, so the contribution is
   `≤ A(4π/3)(‖q‖/2)³(1+‖q‖/2)^{-N} ≤ A'(1+‖q‖)^{-1}` for `N ≥ 4`) and
   `‖η‖ ≥ ‖q‖/2` (there `(1+‖η‖)^{-1} ≤ 2/(1+‖q‖)`, so the contribution is
   `≤ 2‖G‖₁/(1+‖q‖)`); the same with `q + 2πξ`. -/
theorem RadialSmoothCosDecaySchwartz {ψ : ℝ → ℝ} {F : EuclideanSpace ℝ (Fin 3) → ℝ} {R : ℝ}
    (hR : 0 < R) (hψ : ∀ r : ℝ, R ≤ r → ψ r = 0)
    (hInt : MeasureTheory.IntegrableOn (fun r : ℝ => r * |ψ r|) (Set.Ioi (0 : ℝ)))
    (hF : ∀ n : ℕ, ContDiff ℝ n F) (hFsupp : HasCompactSupport F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : EuclideanSpace ℝ (Fin 3),
      |∫ x : EuclideanSpace ℝ (Fin 3), ψ ‖x‖ * F x * Real.cos (inner ℝ q x)| ≤ C / (1 + ‖q‖) := by
  have hFtop : ContDiff ℝ ∞ F := contDiff_infty.mpr hF
  have hFbdd : ∃ MF : ℝ, ∀ x : E, ‖F x‖ ≤ MF :=
    hFsupp.exists_bound_of_continuous hFtop.continuous
  obtain ⟨MF, hMF⟩ := hFbdd
  have hMFnn : 0 ≤ MF := le_trans (norm_nonneg (F 0)) (hMF 0)
  have hψabs : Integrable (fun x : E => |ψ| ‖x‖) := integrable_radial_abs_of_integrableOn hψ hInt
  have hLnn : (0 : ℝ) ≤ ∫ r in Set.Ioi (0 : ℝ), r * |ψ r| :=
    setIntegral_nonneg measurableSet_Ioi (fun r hr => mul_nonneg hr.le (abs_nonneg _))
  have hMnn : (0 : ℝ) ≤ ∫ η : E, (1 + ‖η‖) * ‖𝓕 (fun x : E => (F x : ℂ)) η‖ :=
    integral_nonneg (fun η => by positivity)
  refine ⟨(8 * Real.pi * (R + 1) + 8) * (∫ r in Set.Ioi (0 : ℝ), r * |ψ r|)
      * (2 * Real.pi) ^ 2 * (∫ η : E, (1 + ‖η‖) * ‖𝓕 (fun x : E => (F x : ℂ)) η‖),
    by positivity, fun q => ?_⟩
  by_cases hgood : AEStronglyMeasurable
      (fun x : E => ψ ‖x‖ * F x * Real.cos (inner ℝ q x)) volume
  · -- ## the integrand is a.e. strongly measurable: replace `ψ` by its radial shadow
    -- the integrand is integrable, hence so is its representative `w`
    have hhint : Integrable (fun x : E => ψ ‖x‖ * F x * Real.cos (inner ℝ q x)) := by
      refine (hψabs.const_mul MF).mono' hgood ?_
      filter_upwards with x
      have hc : |Real.cos (inner ℝ q x)| ≤ 1 := Real.abs_cos_le_one _
      have h1 : |ψ ‖x‖| * |F x| ≤ |ψ ‖x‖| * MF :=
        mul_le_mul_of_nonneg_left (hMF x) (abs_nonneg _)
      have h2 : |ψ ‖x‖| * |F x| * |Real.cos (inner ℝ q x)| ≤ |ψ ‖x‖| * MF * 1 :=
        mul_le_mul h1 hc (abs_nonneg _) (by positivity)
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      calc |ψ ‖x‖| * |F x| * |Real.cos (inner ℝ q x)| ≤ |ψ ‖x‖| * MF * 1 := h2
        _ = MF * |ψ ‖x‖| := by ring
    obtain ⟨w, hwsm, hweq⟩ := hgood
    have hwint : Integrable w := hhint.congr hweq
    -- the shadow of `w`
    have hveq : w =ᵐ[volume] fun x : E => ψ ‖x‖ * (F x * Real.cos (inner ℝ q x)) :=
      hweq.symm.trans (Filter.Eventually.of_forall fun x => by ring)
    have hvcont : Continuous fun x : E => F x * Real.cos (inner ℝ q x) := by fun_prop
    have hvbd : ∃ Mv : ℝ, ∀ x : E, |F x * Real.cos (inner ℝ q x)| ≤ Mv :=
      ⟨MF, fun x => by
        rw [abs_mul]
        calc |F x| * |Real.cos (inner ℝ q x)| ≤ MF * 1 :=
              mul_le_mul (hMF x) (Real.abs_cos_le_one _) (abs_nonneg _) hMFnn
          _ = MF := mul_one _⟩
    obtain ⟨ρ, hρmeas, hρsupp, hρeq, hρint, hρbnd⟩ :=
      ExistsRadialShadow (ψ := ψ) (v := fun x : E => F x * Real.cos (inner ℝ q x))
        (w := w) (R := R) hψ hInt hwsm.aestronglyMeasurable hwint hvcont hvbd hveq
    -- the decay for the shadow
    obtain ⟨C, hCnn, hCbnd, hCdecay⟩ :=
      decay_radial_pair (ρ := ρ) (F := F) (R := R) hR hρsupp hρmeas hρint hF hFsupp
    have hCbnd2 : C ≤ (8 * Real.pi * (R + 1) + 8) * (∫ r in Set.Ioi (0 : ℝ), r * |ψ r|)
        * (2 * Real.pi) ^ 2 * (∫ η : E, (1 + ‖η‖) * ‖𝓕 (fun x : E => (F x : ℂ)) η‖) := by
      refine hCbnd.trans ?_
      refine mul_le_mul_of_nonneg_right ?_ hMnn
      refine mul_le_mul_of_nonneg_right ?_ (by positivity : (0:ℝ) ≤ (2 * Real.pi) ^ 2)
      exact mul_le_mul_of_nonneg_left hρbnd (by positivity)
    calc |∫ x : E, ψ ‖x‖ * F x * Real.cos (inner ℝ q x)|
        = |∫ x : E, w x| := by rw [integral_congr_ae hweq]
      _ = |∫ x : E, ρ ‖x‖ * (F x * Real.cos (inner ℝ q x))| := by rw [hρeq]
      _ = |∫ x : E, ρ ‖x‖ * F x * Real.cos (inner ℝ q x)| := by
            congr 1
            exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
      _ ≤ C / (1 + ‖q‖) := hCdecay q
      _ ≤ ((8 * Real.pi * (R + 1) + 8) * (∫ r in Set.Ioi (0 : ℝ), r * |ψ r|)
            * (2 * Real.pi) ^ 2
            * (∫ η : E, (1 + ‖η‖) * ‖𝓕 (fun x : E => (F x : ℂ)) η‖)) / (1 + ‖q‖) :=
          div_le_div_of_nonneg_right hCbnd2 (by positivity)
  · -- ## the integrand is not a.e. strongly measurable: the Bochner integral vanishes
    have hzero : (∫ x : E, ψ ‖x‖ * F x * Real.cos (inner ℝ q x)) = 0 :=
      integral_undef (fun hI => hgood hI.1)
    rw [hzero, abs_zero]
    have h1 : (0 : ℝ) ≤ (8 * Real.pi * (R + 1) + 8) * (∫ r in Set.Ioi (0 : ℝ), r * |ψ r|)
        * (2 * Real.pi) ^ 2 * (∫ η : E, (1 + ‖η‖) * ‖𝓕 (fun x : E => (F x : ℂ)) η‖) := by
      positivity
    positivity

end Work.BoseFixR.LatGreen
