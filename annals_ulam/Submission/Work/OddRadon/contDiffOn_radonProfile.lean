import Mathlib
import Submission.Work.OddRadon.Core
import Submission.Work.Analysis.Calculus.contDiff_intervalIntegral_fixed
import Submission.Work.OddCurve.LowSlope.radon_data_interface
import Submission.Commons.Geometry.Ulam.even_profile_perturbation_from_smooth_bump_aux_independent_core

/-!
# Smoothness of the one-variable Radon profile

If `γ` is `C^∞` on `(-1,1)` (continuity on the closed interval `[-1,1]` is part of the
interface, but is not needed), then the one-variable spherical Radon profile
`c ↦ radonProfile (2n+1) γ c` is `C^∞` on `(0,1)`.

For odd `d = 2n+1` the exponent `(d:ℝ)/2 - 2 = n - 3/2` in the defining integral of
`radonProfile` is half-integral, so the integrand is singular at the endpoints `ν = ±1`.  The
substitution `ν = sin θ` removes the singularity:

  `radonProfile (2n+1) γ c = |S^{2n-2}| ∫_{θ=-π/2}^{π/2} cos^{2n-2} θ · γ (c sin θ) dθ`;

the weight `(1-ν²)^{n-1}/√(1-ν²) dν` becomes the *polynomial* weight `cos^{2n-2} θ dθ`.  The
integrand is then jointly smooth in `(c, θ)` near every point of `(0,1) × [-π/2, π/2]` (the
argument `c sin θ` stays in the open interval `(-1,1)`), so the smoothness follows from
differentiation under the integral sign (`Work.Analysis.Calculus.contDiff_intervalIntegral_fixed`).
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

namespace Work.OddRadon

/-- **The substitution `ν = sin θ` for the Radon profile integral.**  The integral of
`(1-ν²)^{n-1}/√(1-ν²) · γ (c ν)` over `[-1,1]` equals the integral of the smooth integrand
`cos^{2n-2} θ · γ (c sin θ)` over `[-π/2, π/2]`.  No regularity of `γ` is needed: the
change-of-variables formula for the monotone function `sin` holds for arbitrary integrands. -/
lemma integral_one_sub_sq_eq_cos (n : ℕ) (hn : 1 ≤ n) (γ : ℝ → ℝ) (c : ℝ) :
    (∫ ν in (-1 : ℝ)..1, (1 - ν ^ 2) ^ (n - 1) * γ (c * ν) / Real.sqrt (1 - ν ^ 2))
      = ∫ θ in (-(Real.pi / 2))..(Real.pi / 2),
          Real.cos θ ^ (2 * n - 2) * γ (c * Real.sin θ) := by
  have hmin : min (-(Real.pi / 2)) (Real.pi / 2) = -(Real.pi / 2) :=
    min_eq_left (by linarith [Real.pi_pos])
  have hmax : max (-(Real.pi / 2)) (Real.pi / 2) = (Real.pi / 2) :=
    max_eq_right (by linarith [Real.pi_pos])
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := -(Real.pi / 2)) (b := Real.pi / 2)
    (f := Real.sin) (f' := Real.cos)
    (g := fun ν : ℝ => (1 - ν ^ 2) ^ (n - 1) * γ (c * ν) / Real.sqrt (1 - ν ^ 2))
    Real.continuous_sin.continuousOn
    (fun x _ => Real.hasDerivAt_sin x)
    (fun x hx => by
      rw [hmin, hmax] at hx
      exact (Real.cos_pos_of_mem_Ioo hx).le)
  rw [Real.sin_neg, Real.sin_pi_div_two] at hsub
  rw [← hsub]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [Measure.ae_ne volume (Real.pi / 2)] with θ hne hin
  rw [Set.uIoc_of_le (by linarith [Real.pi_pos])] at hin
  have hθ : θ ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := ⟨hin.1, lt_of_le_of_ne hin.2 hne⟩
  have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo hθ
  have h1 : 1 - Real.sin θ ^ 2 = Real.cos θ ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  have h2 : Real.sqrt (Real.cos θ ^ 2) = Real.cos θ := by
    rw [Real.sqrt_sq_eq_abs, abs_of_pos hcos]
  have h3 : 2 * (n - 1) = 2 * n - 2 := by omega
  simp only [Function.comp_apply]
  rw [h1, h2, ← pow_mul, h3]
  field_simp

/-- **The Radon profile as a smooth trigonometric integral**: for `c > 0`,

  `radonProfile (2n+1) γ c = |S^{2n-2}| ∫_{-π/2}^{π/2} cos^{2n-2} θ · γ (c sin θ) dθ`. -/
lemma radonProfile_eq_cos_integral (n : ℕ) (hn : 1 ≤ n) (γ : ℝ → ℝ) {c : ℝ} (hc : 0 < c) :
    radonProfile (2 * n + 1) γ c
      = sphereArea (2 * n - 2) *
        ∫ θ in (-(Real.pi / 2))..(Real.pi / 2),
          Real.cos θ ^ (2 * n - 2) * γ (c * Real.sin θ) := by
  rw [Work.OddCurve.LowSlope.radonProfile_eq_natpow n hn γ hc,
    integral_one_sub_sq_eq_cos n hn γ c]

theorem contDiffOn_radonProfile (n : ℕ) (hn : 1 ≤ n) {γ : ℝ → ℝ}
    (hγ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) γ (Set.Ioo (-1 : ℝ) 1))
    (hcont : ContinuousOn γ (Set.Icc (-1 : ℝ) 1)) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun c : ℝ => Work.OddRadon.radonProfile (2 * n + 1) γ c) (Set.Ioo (0 : ℝ) 1) := by
  rw [contDiffOn_infty]
  intro N
  -- `ContDiffOn` is local on the open set `(0,1)`, so it suffices to work near a point `x`
  refine contDiffOn_of_locally_contDiffOn (fun x hx => ?_)
  obtain ⟨hx0, hx1⟩ := hx
  -- a radius `ρ < 1` strictly bigger than `x`: on `(0,ρ)` the integrand only sees `γ` on
  -- the compact subinterval `[-ρ,ρ] ⊂ (-1,1)`
  set ρ : ℝ := (x + 1) / 2 with hρ
  have hxρ : x < ρ := by rw [hρ]; linarith
  have hρ1 : ρ < 1 := by rw [hρ]; linarith
  have hρ0 : 0 < ρ := by rw [hρ]; linarith
  refine ⟨Set.Ioo (-ρ) ρ, isOpen_Ioo, ⟨by linarith, hxρ⟩, ?_⟩
  -- restrict `γ` to the compact subinterval `[-ρ,ρ]` and extend it to a global `C^N` function
  have hsub : Set.Icc (-ρ) ρ ⊆ Set.Ioo (-1 : ℝ) 1 := fun t ht =>
    ⟨by linarith [ht.1, hρ1], by linarith [ht.2, hρ1]⟩
  have hγρ : ContDiffOn ℝ (N : WithTop ℕ∞) γ (Set.Icc (-ρ) ρ) :=
    (hγ.mono hsub).of_le (by exact_mod_cast (le_top : (N : ℕ∞) ≤ (⊤ : ℕ∞)))
  obtain ⟨G, hGsm, hGeq⟩ : ∃ G : ℝ → ℝ, ContDiff ℝ (N : WithTop ℕ∞) G ∧
      Set.EqOn G γ (Set.Icc (-ρ) ρ) :=
    ⟨Commons.Analysis.Calculus.taylorExtend γ N (-ρ) ρ,
      Commons.Analysis.Calculus.contDiff_taylorExtend N (by linarith) hγρ,
      Commons.Analysis.Calculus.taylorExtend_eqOn_Icc⟩
  -- the parametric integrand, smooth on all of `ℝ × ℝ`
  set F : ℝ → ℝ → ℝ := fun c θ => Real.cos θ ^ (2 * n - 2) * G (c * Real.sin θ) with hF
  have hFsm : ContDiff ℝ (N : WithTop ℕ∞) (fun p : ℝ × ℝ => F p.1 p.2) := by
    rw [hF]
    exact ((Real.contDiff_cos.comp contDiff_snd).pow (2 * n - 2)).mul
      (hGsm.comp (contDiff_fst.mul (Real.contDiff_sin.comp contDiff_snd)))
  have hK : ContDiff ℝ (N : WithTop ℕ∞)
      (fun c : ℝ => ∫ θ in (-(Real.pi / 2))..(Real.pi / 2), F c θ) :=
    Work.Analysis.Calculus.contDiff_intervalIntegral_fixed N hFsm
  -- on `(0,ρ)` the smooth integral is the Radon profile
  have hEqOn : Set.EqOn (fun c : ℝ => sphereArea (2 * n - 2) *
      ∫ θ in (-(Real.pi / 2))..(Real.pi / 2), F c θ)
      (fun c : ℝ => radonProfile (2 * n + 1) γ c) (Set.Ioo 0 ρ) := by
    intro c hc
    have hcpos : 0 < c := hc.1
    change sphereArea (2 * n - 2) * (∫ θ in (-(Real.pi / 2))..(Real.pi / 2), F c θ)
      = radonProfile (2 * n + 1) γ c
    rw [radonProfile_eq_cos_integral n hn γ hcpos]
    congr 1
    -- the two integrands agree because `|c sin θ| ≤ c < ρ`
    apply intervalIntegral.integral_congr
    intro θ hθ
    rw [Set.uIcc_of_le (by linarith [Real.pi_pos])] at hθ
    rw [hF]
    simp only
    have hsin1 : |Real.sin θ| ≤ 1 := by
      rw [abs_le]
      exact ⟨Real.neg_one_le_sin θ, Real.sin_le_one θ⟩
    have hmem : c * Real.sin θ ∈ Set.Icc (-ρ) ρ := by
      have hle : |c * Real.sin θ| ≤ ρ := by
        rw [abs_mul, abs_of_pos hcpos]
        calc c * |Real.sin θ| ≤ c * 1 := mul_le_mul_of_nonneg_left hsin1 hcpos.le
          _ = c := by ring
          _ ≤ ρ := hc.2.le
      exact ⟨le_trans (neg_le_neg hle) (neg_abs_le _), le_trans (le_abs_self _) hle⟩
    rw [hGeq hmem]
  have hT : ContDiffOn ℝ (N : WithTop ℕ∞) (fun c : ℝ => radonProfile (2 * n + 1) γ c)
      (Set.Ioo 0 1 ∩ Set.Ioo (-ρ) ρ) := by
    refine ((hK.const_smul (sphereArea (2 * n - 2))).contDiffOn).congr (fun c hc => ?_)
    exact (hEqOn ⟨hc.1.1, hc.2.2⟩).symm
  exact hT

end Work.OddRadon
