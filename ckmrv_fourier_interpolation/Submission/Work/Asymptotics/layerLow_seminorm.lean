/-
# Seminorm bounds for the `low` part of the CKMRV layer

The `low` part of the CKMRV layer is the contribution of the compact piece `(0,1]` of the
contour,

  `layerLow ℓ d τ r = sinSq r · ∫_0^1 K(τ,it) e^{-πr²t} dt`.

This file proves that its `r`-seminorms grow at most moderately in `τ` on the fundamental domain
`𝒟`, using only the flatness of the kernel at the cusp `0`
(`Work.Asymptotics.Kaxis_cusp_flat`): differentiating under the integral sign produces the
integrand `sinSq · e^{-πr²t}`, whose derivatives are controlled by
`Work.Asymptotics.sinSq_gauss_seminorm` (a sum of three complex Gaussians) against the flatness
bound `t^N`.

## Main results

* `Work.Asymptotics.measurable_iteratedDeriv_fst_meas`, `Work.Asymptotics.hasDerivAt_intervalIntegral_iteratedDeriv_meas`,
  `Work.Asymptotics.iteratedDeriv_intervalIntegral_of_meas_bound` : differentiation under the
  integral sign for a smooth family with *measurable* (not necessarily continuous) integrand in
  the integration variable and an *integrable, `u`-dependent* dominating function.
* `Work.Asymptotics.layerLow_seminorm` : the requested seminorm bound.
-/
import Mathlib
import Submission.Work.Asymptotics.DomainD
import Submission.Work.Asymptotics.F2LayerDefs
import Submission.Work.Kernels.Kernels
import Submission.Work.Kernels.ModerateGrowth
import Submission.Work.Asymptotics.gaussian_bound
import Submission.Work.Asymptotics.sinSq_seminorm
import Submission.Work.Asymptotics.measurable_Kfun_snd_all

noncomputable section

open MeasureTheory Filter Topology UpperHalfPlane
open Work.Kernels
open scoped Topology ContDiff

namespace Work.Asymptotics

/-! ## Differentiation under the integral sign with measurable integrands -/

/-- In a family `k` smooth in its first variable, the `j`-th iterated derivative in the first
variable is again smooth in the first variable. -/
lemma contDiff_iteratedDeriv_fst_meas {k : ℝ → ℝ → ℂ}
    (hk_smooth : ∀ u, ContDiff ℝ ∞ (fun r : ℝ => k r u)) (j : ℕ) (u : ℝ) :
    ContDiff ℝ ∞ (fun r : ℝ => iteratedDeriv j (fun r' : ℝ => k r' u) r) := by
  rw [iteratedDeriv_eq_iterate]
  exact ContDiff.iterate_deriv j (by simpa using hk_smooth u)

/-- If `k` is smooth in its first variable and *measurable* in its second (no continuity needed),
then the `j`-th iterated derivative of `k` in its first variable is measurable in the second. -/
lemma measurable_iteratedDeriv_fst_meas {k : ℝ → ℝ → ℂ}
    (hk_meas : ∀ r : ℝ, Measurable (fun u : ℝ => k r u))
    (hk_smooth : ∀ u, ContDiff ℝ ∞ (fun r : ℝ => k r u)) :
    ∀ j : ℕ, ∀ r : ℝ, Measurable (fun u : ℝ => iteratedDeriv j (fun r' : ℝ => k r' u) r) := by
  intro j
  induction j with
  | zero =>
    intro r
    simpa [iteratedDeriv_zero] using hk_meas r
  | succ j ih =>
    intro r
    simp only [iteratedDeriv_succ]
    set t : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with ht
    set φ : ℕ → ℝ → ℂ := fun n u =>
      (t n)⁻¹ * (iteratedDeriv j (fun r' : ℝ => k r' u) (r + t n)
        - iteratedDeriv j (fun r' : ℝ => k r' u) r) with hφ
    have hφ_meas : ∀ n : ℕ, Measurable (φ n) := by
      intro n
      have h1 : Measurable (fun u : ℝ =>
          iteratedDeriv j (fun r' : ℝ => k r' u) (r + t n)
            - iteratedDeriv j (fun r' : ℝ => k r' u) r) := (ih (r + t n)).sub (ih r)
      simpa [hφ] using h1.const_mul ((t n)⁻¹ : ℂ)
    have htend : Tendsto t atTop (𝓝[≠] (0 : ℝ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · simpa [ht] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      · filter_upwards with n
        rw [ht]
        exact ne_of_gt (one_div_pos.mpr (by positivity))
    have hlim : Tendsto φ atTop
        (𝓝 (fun u : ℝ => deriv (fun r' : ℝ => iteratedDeriv j (fun x : ℝ => k x u) r') r)) := by
      rw [tendsto_pi_nhds]
      intro u
      have hdiff : Differentiable ℝ (fun r' : ℝ => iteratedDeriv j (fun x : ℝ => k x u) r') :=
        (contDiff_iteratedDeriv_fst_meas (k := k) hk_smooth j u).differentiable (by decide)
      have hd_at : DifferentiableAt ℝ (fun r' : ℝ => iteratedDeriv j (fun x : ℝ => k x u) r') r :=
        hdiff.differentiableAt
      have hslope := hasDerivAt_iff_tendsto_slope_zero.mp hd_at.hasDerivAt
      have hcomp := hslope.comp htend
      simpa [hφ, Function.comp_def] using hcomp
    exact measurable_of_tendsto_metrizable hφ_meas hlim

/-- Differentiation under the integral sign for the family
`r ↦ iteratedDeriv j (fun r' => k r' u) r`, with an integrable `u`-dependent dominator. -/
lemma hasDerivAt_intervalIntegral_iteratedDeriv_meas {k : ℝ → ℝ → ℂ} {j : ℕ}
    (hk_meas : ∀ j : ℕ, ∀ r : ℝ, Measurable (fun u : ℝ => iteratedDeriv j (fun r' : ℝ => k r' u) r))
    (hk_smooth : ∀ u, ContDiff ℝ ∞ (fun r : ℝ => k r u))
    (hint : ∃ bd : ℝ → ℝ, IntegrableOn bd (Set.Ioc (0 : ℝ) 1) ∧
      ∀ᵐ u ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)),
        ∀ r : ℝ, ‖iteratedDeriv j (fun r' : ℝ => k r' u) r‖ ≤ bd u)
    (hint_succ : ∃ bd : ℝ → ℝ, IntegrableOn bd (Set.Ioc (0 : ℝ) 1) ∧
      ∀ᵐ u ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)),
        ∀ r : ℝ, ‖iteratedDeriv (j + 1) (fun r' : ℝ => k r' u) r‖ ≤ bd u)
    (r : ℝ) :
    HasDerivAt (fun x : ℝ => ∫ u in (0 : ℝ)..1, iteratedDeriv j (fun r' : ℝ => k r' u) x)
      (∫ u in (0 : ℝ)..1, iteratedDeriv (j + 1) (fun r' : ℝ => k r' u) r) r := by
  obtain ⟨bdj, hbdj_int, hbdj⟩ := hint
  obtain ⟨bd, hbd_int, hbd⟩ := hint_succ
  have hIoc : Set.uIoc (0 : ℝ) 1 = Set.Ioc (0 : ℝ) 1 := Set.uIoc_of_le (by norm_num)
  have hIoc_sub : Set.uIoc (0 : ℝ) 1 ⊆ Set.Icc (0 : ℝ) 1 := by
    rw [hIoc]; exact fun x hx => ⟨le_of_lt hx.1, hx.2⟩
  have hbdj_int' : Integrable bdj (volume.restrict (Set.uIoc (0 : ℝ) 1)) := by
    rw [← hIoc] at hbdj_int; exact hbdj_int
  have hbd_int' : Integrable bd (volume.restrict (Set.uIoc (0 : ℝ) 1)) := by
    rw [← hIoc] at hbd_int; exact hbd_int
  have hF_meas : ∀ᶠ x in 𝓝 r,
      AEStronglyMeasurable (fun u : ℝ => iteratedDeriv j (fun r' : ℝ => k r' u) x)
        (volume.restrict (Set.uIoc (0 : ℝ) 1)) :=
    Filter.Eventually.of_forall (fun x => (hk_meas j x).aestronglyMeasurable)
  have hF_int : Integrable (fun u : ℝ => iteratedDeriv j (fun r' : ℝ => k r' u) r)
      (volume.restrict (Set.uIoc (0 : ℝ) 1)) := by
    refine hbdj_int'.mono' (hk_meas j r).aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_uIoc]
    refine ((ae_restrict_iff' measurableSet_Ioc).mp hbdj).mono ?_
    intro u hu H
    exact hu (hIoc ▸ H) r
  have hF'_meas : AEStronglyMeasurable
      (fun u : ℝ => iteratedDeriv (j + 1) (fun r' : ℝ => k r' u) r)
      (volume.restrict (Set.uIoc (0 : ℝ) 1)) :=
    (hk_meas (j + 1) r).aestronglyMeasurable
  have h_bound : ∀ᵐ a ∂(volume.restrict (Set.uIoc (0 : ℝ) 1)),
      ∀ x ∈ (Set.univ : Set ℝ), ‖iteratedDeriv (j + 1) (fun r' : ℝ => k r' a) x‖ ≤ bd a := by
    rw [ae_restrict_iff' measurableSet_uIoc]
    refine ((ae_restrict_iff' measurableSet_Ioc).mp hbd).mono ?_
    intro u hu H
    exact fun x _ => hu (hIoc ▸ H) x
  have h_diff : ∀ᵐ a ∂(volume.restrict (Set.uIoc (0 : ℝ) 1)),
      ∀ x ∈ (Set.univ : Set ℝ),
        HasDerivAt (fun x : ℝ => iteratedDeriv j (fun r' : ℝ => k r' a) x)
          (iteratedDeriv (j + 1) (fun r' : ℝ => k r' a) x) x := by
    rw [ae_restrict_iff' measurableSet_uIoc]
    refine Filter.Eventually.of_forall (fun a _ x _ => ?_)
    have hd : Differentiable ℝ (fun x : ℝ => iteratedDeriv j (fun r' : ℝ => k r' a) x) :=
      (contDiff_iteratedDeriv_fst_meas (k := k) hk_smooth j a).differentiable (by decide)
    have hd_at : DifferentiableAt ℝ (fun x : ℝ => iteratedDeriv j (fun r' : ℝ => k r' a) x) x :=
      hd.differentiableAt
    have h' : HasDerivAt (fun x : ℝ => iteratedDeriv j (fun r' : ℝ => k r' a) x)
        (deriv (iteratedDeriv j (fun r' : ℝ => k r' a)) x) x := hd_at.hasDerivAt
    exact h'.congr_deriv (congrFun (iteratedDeriv_succ (n := j)
      (f := fun r' : ℝ => k r' a)) x).symm
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.uIoc (0 : ℝ) 1))
    (F := fun x u : ℝ => iteratedDeriv j (fun r' : ℝ => k r' u) x)
    (F' := fun x u : ℝ => iteratedDeriv (j + 1) (fun r' : ℝ => k r' u) x)
    (x₀ := r) (s := Set.univ) (bound := bd)
    Filter.univ_mem hF_meas hF_int hF'_meas h_bound hbd_int' h_diff
  have hconv : ∀ f : ℝ → ℂ,
      (∫ u : ℝ, f u ∂(volume.restrict (Set.uIoc (0 : ℝ) 1))) = ∫ u in (0 : ℝ)..1, f u := by
    intro f
    rw [intervalIntegral.intervalIntegral_eq_integral_uIoc]
    simp
  have hfun : (fun x : ℝ => ∫ u in (0 : ℝ)..1, iteratedDeriv j (fun r' : ℝ => k r' u) x)
      = fun x : ℝ => ∫ u : ℝ, iteratedDeriv j (fun r' : ℝ => k r' u) x
          ∂(volume.restrict (Set.uIoc (0 : ℝ) 1)) :=
    funext (fun x => (hconv (fun u => iteratedDeriv j (fun r' : ℝ => k r' u) x)).symm)
  have hval : (∫ u in (0 : ℝ)..1, iteratedDeriv (j + 1) (fun r' : ℝ => k r' u) r)
      = ∫ u : ℝ, iteratedDeriv (j + 1) (fun r' : ℝ => k r' u) r
          ∂(volume.restrict (Set.uIoc (0 : ℝ) 1)) :=
    (hconv (fun u => iteratedDeriv (j + 1) (fun r' : ℝ => k r' u) r)).symm
  rw [hfun, hval]
  exact hmain.2

/-- **Iterated differentiation under the integral sign**, for a smooth family with measurable
integrand in the integration variable and integrable `u`-dependent dominations. -/
theorem iteratedDeriv_intervalIntegral_of_meas_bound (k : ℝ → ℝ → ℂ) (l : ℕ)
    (hk_meas : ∀ r : ℝ, Measurable (fun u : ℝ => k r u))
    (hk_smooth : ∀ u, ContDiff ℝ ∞ (fun r : ℝ => k r u))
    (hbd : ∀ j ≤ l, ∃ bd : ℝ → ℝ, IntegrableOn bd (Set.Ioc (0 : ℝ) 1) ∧
      ∀ᵐ u ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)),
        ∀ r : ℝ, ‖iteratedDeriv j (fun r' : ℝ => k r' u) r‖ ≤ bd u) :
    ∀ j ≤ l, iteratedDeriv j (fun r : ℝ => ∫ u in (0 : ℝ)..1, k r u)
      = fun r : ℝ => ∫ u in (0 : ℝ)..1, iteratedDeriv j (fun r' : ℝ => k r' u) r := by
  have hmeas := measurable_iteratedDeriv_fst_meas hk_meas hk_smooth
  have hkey : ∀ j, j ≤ l → iteratedDeriv j (fun r : ℝ => ∫ u in (0 : ℝ)..1, k r u)
      = fun r : ℝ => ∫ u in (0 : ℝ)..1, iteratedDeriv j (fun r' : ℝ => k r' u) r := by
    intro j
    induction j with
    | zero =>
      intro _
      funext r
      simp [iteratedDeriv_zero]
    | succ j ih =>
      intro hj
      rw [iteratedDeriv_succ, ih (by omega)]
      funext r
      exact (hasDerivAt_intervalIntegral_iteratedDeriv_meas (j := j) hmeas hk_smooth
        (hbd j (by omega)) (hbd (j + 1) hj) r).deriv
  exact hkey

/-- **The `r`-seminorms of the `low` part of the CKMRV layer** are bounded, with moderate growth
in `τ` on `𝒟`; the only input is the flatness of the kernel along the contour at the cusp `0`
(`Work.Asymptotics.Kaxis_cusp_flat`). -/
theorem layerLow_seminorm (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (hflat : ∀ N : ℝ, 0 ≤ N → ∃ c N' : ℝ, 0 ≤ c ∧ ∀ (τ : UpperHalfPlane) (t : ℝ),
      τ ∈ Work.Asymptotics.DomainD → 0 < t → t ≤ 1 →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖
          ≤ c * (Work.Kernels.scale τ) ^ N' * t ^ N) :
    ∀ k l : ℕ, ∃ c N : ℝ, 0 ≤ c ∧ ∀ (τ : UpperHalfPlane) (r : ℝ),
      τ ∈ Work.Asymptotics.DomainD →
      (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => Work.Asymptotics.layerLow ℓ d τ s) r‖
        ≤ c * (Work.Kernels.scale τ) ^ N := by
  intro k l
  obtain ⟨Γ, hΓ0, hΓ⟩ := sinSq_gauss_seminorm k l
  set P : ℝ := ((k + l : ℕ) : ℝ) + 1 with hPdef
  have hP0 : 0 ≤ P := by rw [hPdef]; positivity
  have hPnat : P = ((k + l + 1 : ℕ) : ℝ) := by rw [hPdef]; push_cast; ring
  obtain ⟨c₀, N', hc₀, hflat'⟩ := hflat P hP0
  refine ⟨c₀ * Γ, N', mul_nonneg hc₀ hΓ0, ?_⟩
  intro τ r hτ
  have hscale : (0 : ℝ) ≤ (scale τ) ^ N' := Real.rpow_nonneg (le_of_lt (scale_pos τ)) N'
  have hw_meas : Measurable (fun u : ℝ => Kaxis (Kfun ℓ d) τ u) :=
    measurable_Kaxis_of_measurable (Kfun ℓ d) τ (measurable_Kfun_snd_all ℓ d hd τ)
  set w : ℝ → ℂ := fun u => Kaxis (Kfun ℓ d) τ u with hwdef
  have hw_meas' : Measurable w := by rw [hwdef]; exact hw_meas
  set G : ℝ → ℝ → ℂ := fun u x => Complex.exp (-(Real.pi * (x : ℂ) ^ 2 * (u : ℂ))) with hGdef
  set kfun : ℝ → ℝ → ℂ := fun x u => w u * (G u x * sinSq x) with hkfundef
  have hlayer : ∀ x : ℝ, layerLow ℓ d τ x = ∫ u in (0 : ℝ)..1, kfun x u := by
    intro x
    rw [layerLow, hkfundef, hwdef, hGdef]
    have h1 : (fun u : ℝ => Kaxis (Kfun ℓ d) τ u
          * (Complex.exp (-(Real.pi * (x : ℂ) ^ 2 * (u : ℂ))) * sinSq x))
        = fun u : ℝ => (Kaxis (Kfun ℓ d) τ u
          * Complex.exp (-(Real.pi * (x : ℂ) ^ 2 * (u : ℂ)))) * sinSq x := by
      funext u; ring
    rw [h1, intervalIntegral.integral_mul_const]
    ring
  have hopR : ContDiff ℝ ∞ (fun x : ℝ => (x : ℂ)) := Complex.ofRealCLM.contDiff
  have hsinSmooth : ContDiff ℝ ∞ (fun x : ℝ => sinSq x) := by
    rw [show (fun x : ℝ => sinSq x) = fun x : ℝ => 2
        - Complex.exp (-((-Complex.I * Real.pi) * (x : ℂ) ^ 2))
        - Complex.exp (-((Complex.I * Real.pi) * (x : ℂ) ^ 2)) by
      funext x; exact sinSq_eq_complex x]
    fun_prop
  have hGsin_smooth : ∀ u : ℝ, ContDiff ℝ ∞ (fun x : ℝ => G u x * sinSq x) := by
    intro u
    have hGu : ContDiff ℝ ∞ (fun x : ℝ => G u x) := by rw [hGdef]; fun_prop
    exact hGu.mul hsinSmooth
  have hmeas_kfun : ∀ x : ℝ, Measurable (fun u : ℝ => kfun x u) := by
    intro x
    have h1 : (fun u : ℝ => kfun x u) = fun u : ℝ => (w u * G u x) * sinSq x := by
      funext u; rw [hkfundef]; ring
    rw [h1]
    exact (hw_meas'.mul (by fun_prop)).mul_const _
  have hkfun_smooth : ∀ u : ℝ, ContDiff ℝ ∞ (fun x : ℝ => kfun x u) := by
    intro u
    have h1 : (fun x : ℝ => kfun x u) = fun x : ℝ => w u * (G u x * sinSq x) := by
      funext x; rw [hkfundef]
    rw [h1]
    exact contDiff_const.mul (hGsin_smooth u)
  -- dominations
  have hdom : ∀ j ≤ l, ∃ bd : ℝ → ℝ, IntegrableOn bd (Set.Ioc (0 : ℝ) 1) ∧
      ∀ᵐ u ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)), ∀ r : ℝ,
        ‖iteratedDeriv j (fun r' : ℝ => kfun r' u) r‖ ≤ bd u := by
    intro j hj
    obtain ⟨Γj, hΓj0, hΓj⟩ := sinSq_gauss_seminorm 0 j
    refine ⟨fun _ => c₀ * (scale τ) ^ N' * Γj, ?_, ?_⟩
    · exact integrableOn_const (by simp)
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with u hu
      obtain ⟨hu1, hu2⟩ := hu
      intro r
      -- step 1: factor out `w u`
      have hG_at : ContDiffAt ℝ ((j : ℕ∞) : ℕ∞ω) (fun r' : ℝ => G u r' * sinSq r') r :=
        ((hGsin_smooth u).contDiffAt).of_le (WithTop.coe_le_coe.mpr le_top)
      have hstep1 : iteratedDeriv j (fun r' : ℝ => kfun r' u) r
          = w u * iteratedDeriv j (fun r' : ℝ => G u r' * sinSq r') r := by
        have h1 : (fun r' : ℝ => kfun r' u) = fun r' : ℝ => w u * (G u r' * sinSq r') := by
          funext x; rw [hkfundef]
        rw [h1, iteratedDeriv_const_mul (w u) hG_at]
      rw [hstep1, norm_mul]
      -- step 2: bound `‖w u‖`
      have hw' : ‖w u‖ ≤ c₀ * (scale τ) ^ N' * u ^ P := by
        rw [hwdef]; exact hflat' τ u hτ hu1 hu2
      -- step 3: bound the second factor
      have hsin' : (fun r' : ℝ => G u r' * sinSq r') = fun r' : ℝ => sinSq r' * G u r' := by
        funext x; ring
      have hb2 : ‖iteratedDeriv j (fun r' : ℝ => G u r' * sinSq r') r‖ ≤ Γj * (u ^ j)⁻¹ := by
        rw [hsin']
        have h := hΓj u hu1 hu2 r
        simpa using h
      -- step 4: `u^P * (u^j)⁻¹ ≤ 1`
      have hup : u ^ P * (u ^ j)⁻¹ ≤ 1 := by
        rw [hPnat, Real.rpow_natCast]
        have h1 : k + l + 1 = (k + l + 1 - j) + j := by omega
        rw [h1, pow_add, mul_assoc, mul_inv_cancel₀ (pow_ne_zero j (ne_of_gt hu1)), mul_one]
        exact pow_le_one₀ hu1.le hu2
      -- combine
      calc ‖w u‖ * ‖iteratedDeriv j (fun r' : ℝ => G u r' * sinSq r') r‖
          ≤ (c₀ * (scale τ) ^ N' * u ^ P) * (Γj * (u ^ j)⁻¹) :=
            mul_le_mul hw' hb2 (norm_nonneg _)
              (mul_nonneg (mul_nonneg hc₀ hscale) (by positivity))
        _ = c₀ * (scale τ) ^ N' * Γj * (u ^ P * (u ^ j)⁻¹) := by ring
        _ ≤ c₀ * (scale τ) ^ N' * Γj := by
            have hC : (0 : ℝ) ≤ c₀ * (scale τ) ^ N' * Γj :=
              mul_nonneg (mul_nonneg hc₀ (by positivity)) hΓj0
            nlinarith [hup, hC]
  -- apply the parametric-differentiation theorem
  have hfun_eq : (fun s : ℝ => layerLow ℓ d τ s) = fun s : ℝ => ∫ u in (0 : ℝ)..1, kfun s u :=
    funext hlayer
  rw [hfun_eq,
    iteratedDeriv_intervalIntegral_of_meas_bound kfun l hmeas_kfun hkfun_smooth hdom l le_rfl]
  -- pointwise weighted bound for the differentiated integrand
  have hptw : ∀ u ∈ Set.Ioc (0 : ℝ) 1, ∀ x : ℝ,
      |x| ^ k * ‖iteratedDeriv l (fun r' : ℝ => kfun r' u) x‖
        ≤ c₀ * (scale τ) ^ N' * (Γ * u) := by
    intro u hu x
    obtain ⟨hu1, hu2⟩ := hu
    have hG_at : ContDiffAt ℝ ((l : ℕ∞) : ℕ∞ω) (fun r' : ℝ => G u r' * sinSq r') x :=
      ((hGsin_smooth u).contDiffAt).of_le (WithTop.coe_le_coe.mpr le_top)
    have hstep1 : iteratedDeriv l (fun r' : ℝ => kfun r' u) x
        = w u * iteratedDeriv l (fun r' : ℝ => G u r' * sinSq r') x := by
      have h1 : (fun r' : ℝ => kfun r' u) = fun r' : ℝ => w u * (G u r' * sinSq r') := by
        funext y; rw [hkfundef]
      rw [h1, iteratedDeriv_const_mul (w u) hG_at]
    rw [hstep1, norm_mul]
    have hw' : ‖w u‖ ≤ c₀ * (scale τ) ^ N' * u ^ P := by
      rw [hwdef]; exact hflat' τ u hτ hu1 hu2
    have hsin' : (fun r' : ℝ => G u r' * sinSq r') = fun r' : ℝ => sinSq r' * G u r' := by
      funext y; ring
    have hb2 : |x| ^ k * ‖iteratedDeriv l (fun r' : ℝ => G u r' * sinSq r') x‖
        ≤ Γ * (u ^ (k + l))⁻¹ := by
      rw [hsin']
      have h := hΓ u hu1 hu2 x
      simpa using h
    have hup : u ^ P * (u ^ (k + l))⁻¹ ≤ u := by
      rw [hPnat, Real.rpow_natCast, pow_succ, mul_comm (u ^ (k + l)) u, mul_assoc,
        mul_inv_cancel₀ (pow_ne_zero (k + l) (ne_of_gt hu1)), mul_one]
    calc |x| ^ k * (‖w u‖ * ‖iteratedDeriv l (fun r' : ℝ => G u r' * sinSq r') x‖)
        = ‖w u‖ * (|x| ^ k * ‖iteratedDeriv l (fun r' : ℝ => G u r' * sinSq r') x‖) := by
          ring
      _ ≤ (c₀ * (scale τ) ^ N' * u ^ P) * (Γ * (u ^ (k + l))⁻¹) :=
          mul_le_mul hw' hb2 (mul_nonneg (by positivity) (norm_nonneg _))
            (mul_nonneg (mul_nonneg hc₀ hscale) (by positivity))
      _ = c₀ * (scale τ) ^ N' * Γ * (u ^ P * (u ^ (k + l))⁻¹) := by ring
      _ ≤ c₀ * (scale τ) ^ N' * Γ * u :=
          mul_le_mul_of_nonneg_left hup (mul_nonneg (mul_nonneg hc₀ hscale) hΓ0)
      _ = c₀ * (scale τ) ^ N' * (Γ * u) := by ring
  -- bound the integral
  have hIoc : Set.uIoc (0 : ℝ) 1 = Set.Ioc (0 : ℝ) 1 := Set.uIoc_of_le (by norm_num)
  have hg_bound : ∀ u ∈ Set.uIoc (0 : ℝ) 1,
      ‖((((|r| ^ k : ℝ)) : ℂ)) • iteratedDeriv l (fun r' : ℝ => kfun r' u) r‖
        ≤ c₀ * (scale τ) ^ N' * Γ := by
    intro u hu
    have hu' : u ∈ Set.Ioc (0 : ℝ) 1 := hIoc ▸ hu
    have hnc : ‖((((|r| ^ k : ℝ)) : ℂ))‖ = |r| ^ k := by
      have h : ‖(((|r| ^ k : ℝ)) : ℂ)‖ = |(|r| ^ k : ℝ)| := RCLike.norm_ofReal (K := ℂ) (|r| ^ k)
      rw [h, abs_of_nonneg (by positivity)]
    rw [norm_smul, hnc]
    have h := hptw u hu' r
    have hu3 : Γ * u ≤ Γ := by
      nlinarith [hΓ0, hu'.1.le, hu'.2]
    calc |r| ^ k * ‖iteratedDeriv l (fun r' : ℝ => kfun r' u) r‖
        ≤ c₀ * (scale τ) ^ N' * (Γ * u) := h
      _ ≤ c₀ * (scale τ) ^ N' * Γ := mul_le_mul_of_nonneg_left hu3 (mul_nonneg hc₀ hscale)
  calc |r| ^ k * ‖∫ u in (0 : ℝ)..1, iteratedDeriv l (fun r' : ℝ => kfun r' u) r‖
      = ‖∫ u in (0 : ℝ)..1, ((((|r| ^ k : ℝ)) : ℂ)) • iteratedDeriv l (fun r' : ℝ => kfun r' u) r‖ := by
        have hnc : ‖((((|r| ^ k : ℝ)) : ℂ))‖ = |r| ^ k := by
          have h : ‖(((|r| ^ k : ℝ)) : ℂ)‖ = |(|r| ^ k : ℝ)| := RCLike.norm_ofReal (K := ℂ) (|r| ^ k)
          rw [h, abs_of_nonneg (by positivity)]
        rw [intervalIntegral.integral_smul, norm_smul, hnc]
    _ ≤ c₀ * (scale τ) ^ N' * Γ * |1 - (0 : ℝ)| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hg_bound
    _ = (c₀ * Γ) * (scale τ) ^ N' := by norm_num; ring

end Work.Asymptotics
