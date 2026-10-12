import ChallengeDeps
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.ProfileLocInt
import Submission.ProfileTendsto
import Submission.RadialTest
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Radial-profile 1D equations from the exterior weak equation (Layer 3)

Let `w` be radial with profile `f := radialProfile w` (so `w x = f ‖x‖`).
Suppose `w` is weakly harmonic in the exterior region `{x | R ≤ ‖x‖}`
(`∫ w·Δφ = 0` for every smooth compactly-supported `φ` with
`tsupport φ ⊆ {x | R ≤ ‖x‖}`) — as is the case for a scattering solution
`w` with `tsupport v ⊆ ball 0 R` (see `ScatHarmonic.scattering_harmonic_exterior`).

Then the radial test functions of `RadialTest.radial_weakHarmonic_1D` give,
for the *rescaled* profile

    u(r) := r · f(r) = r · radialProfile w r ,

the clean 1D statement

    ∫_{r > R} u(r) · χ''(r) dr = 0      for all χ ∈ C∞c((R, ∞)),

obtained by testing with `ψ := χ/r` (smooth because `χ` vanishes on
`(-∞, R]` and `R > 0`) and rewriting the integrand

    r²·f·ψ'' + 2·r·f·ψ' = r·f·χ'' = u·χ''.

This is exactly the hypothesis of `SndClassify.affine_ae_of_snd_annihilates`
(the 1D classification: `u` affine a.e. on `(R, ∞)`), which together with
the decay `w → 0` at infinity forces `w x = c/‖x‖` a.e. on the exterior —
the core of the scattering-fact `omega_outside_support`.

This module also proves the local integrability of `u` on `(R, ∞)` from the
local integrability of `w` in `ℝ³` (via the radial-integral identity of
`Submission.RadialIntegral`), so that the classification applies, and the
decay statement for the profile.
-/

noncomputable section

open _root_.BoseGases
set_option autoImplicit false

namespace Submission.BoseGases

open Filter Metric MeasureTheory Laplacian
open scoped ContDiff Topology Real

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- A profile `χ` supported inside `(R, ∞)` (so `χ = 0` for `r ≤ R`) gives
a smooth function `r ↦ χ r / r` (the quotient is constant zero near `0`
because `R > 0` and `χ` vanishes there). -/
lemma contDiff_div_self {R : ℝ} (hR : 0 < R) {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hχsup : ∀ r : ℝ, χ r ≠ 0 → R < r) :
    ContDiff ℝ ∞ (fun r : ℝ => χ r / r) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst x
    have hzero : (fun r : ℝ => χ r / r) =ᶠ[𝓝 (0 : ℝ)] (fun _ : ℝ => (0 : ℝ)) := by
      rw [Filter.EventuallyEq]
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hR] with r hr
      have hrR : |r| < R := by simpa [Metric.mem_ball, dist_zero_right] using hr
      have hχr : χ r = 0 := by
        by_contra h
        have hlt : R < r := hχsup r h
        have hle : r ≤ |r| := le_abs_self r
        linarith
      simp [hχr]
    exact ContDiffAt.congr_of_eventuallyEq
      ((contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => (0 : ℝ))).contDiffAt) hzero
  · have hxχ : ContDiffAt ℝ ∞ χ x := hχ.contDiffAt
    have hinv : ContDiffAt ℝ ∞ (fun r : ℝ => r⁻¹) x := by
      exact contDiffAt_inv ℝ hx
    simpa [div_eq_mul_inv] using hxχ.mul hinv

/-- The quotient `r ↦ χ r / r` has compact support when `χ` does (it vanishes
wherever `χ` vanishes, including at `0`). -/
lemma hasCompactSupport_div_self {χ : ℝ → ℝ} (hχcs : HasCompactSupport χ) :
    HasCompactSupport (fun r : ℝ => χ r / r) := by
  rw [HasCompactSupport]
  have hK : IsCompact (tsupport χ) := by
    simpa [HasCompactSupport] using hχcs
  have hsup_sub : Function.support (fun r : ℝ => χ r / r) ⊆ tsupport χ := by
    intro r hr
    have hχr : χ r ≠ 0 := by
      intro h0
      have : (fun r : ℝ => χ r / r) r = 0 := by simp [h0]
      exact hr this
    exact subset_closure (Function.mem_support.mpr hχr)
  have htsub : tsupport (fun r : ℝ => χ r / r) ⊆ tsupport χ := by
    rw [tsupport]
    exact closure_minimal hsup_sub (isClosed_tsupport χ)
  exact IsCompact.of_isClosed_subset hK (isClosed_tsupport (fun r : ℝ => χ r / r)) htsub

/-- The support of `r ↦ χ r / r` lies in the support region of `χ`. -/
lemma support_div_self_gt {R : ℝ} {χ : ℝ → ℝ}
    (hχsup : ∀ r : ℝ, χ r ≠ 0 → R < r) :
    ∀ r : ℝ, (fun t : ℝ => χ t / t) r ≠ 0 → R < r := by
  intro r hr
  have hχr : χ r ≠ 0 := by
    intro h0
    have : (fun t : ℝ => χ t / t) r = 0 := by simp [h0]
    exact hr this
  exact hχsup r hχr

/-- The derivative of `χ/t` at a nonzero point, by the quotient rule. -/
lemma deriv_div_self {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) {r : ℝ} (hr : r ≠ 0) :
    deriv (fun t : ℝ => χ t / t) r = (deriv χ r * r - χ r) / r ^ 2 := by
  have hc : DifferentiableAt ℝ χ r := by
    exact (hχ.differentiable (by norm_num : (∞ : ℕ∞ω) ≠ 0)).differentiableAt
  have hid : DifferentiableAt ℝ (fun t : ℝ => t) r := differentiableAt_id
  have hder := deriv_fun_div hc hid hr
  simpa using hder

/-- Derivative of a smooth function is differentiable. -/
lemma differentiableAt_deriv_contDiff_infty {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (r : ℝ) :
    DifferentiableAt ℝ (deriv χ) r := by
  have h2 : ContDiff ℝ 2 χ := contDiff_infty.mp hχ 2
  exact (ContDiff.differentiable_deriv_two h2).differentiableAt

/-- Around a nonzero `r`, `t ↦ t²·(χ/t)′(t)` coincides with `t ↦ t·χ′(t) − χ(t)`. -/
lemma eventuallyEq_sq_mul_deriv_div {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (r : ℝ)
    (hr : r ≠ 0) :
    (fun t : ℝ => t ^ 2 * deriv (fun s : ℝ => χ s / s) t)
      =ᶠ[𝓝 r] (fun t : ℝ => t * deriv χ t - χ t) := by
  rw [Filter.EventuallyEq]
  filter_upwards [isOpen_ne.mem_nhds hr] with t ht
  have hd := deriv_div_self hχ ht
  rw [hd]
  field_simp [ht]

/-- `d/dt (t·χ′(t) − χ(t)) = r·χ″(r)`. -/
lemma deriv_lin_sub {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (r : ℝ) :
    deriv (fun t : ℝ => t * deriv χ t - χ t) r = r * deriv (deriv χ) r := by
  have hχd : DifferentiableAt ℝ (deriv χ) r := differentiableAt_deriv_contDiff_infty hχ r
  have hid : DifferentiableAt ℝ (fun t : ℝ => t) r := differentiableAt_id
  have hχd0 : DifferentiableAt ℝ χ r := by
    exact (hχ.differentiable (by norm_num : (∞ : ℕ∞ω) ≠ 0)).differentiableAt
  have hprod : deriv (fun t : ℝ => t * deriv χ t) r =
      deriv χ r + r * deriv (deriv χ) r := by
    have hm := deriv_fun_mul hid hχd
    simpa using hm
  calc
    deriv (fun t : ℝ => t * deriv χ t - χ t) r
        = deriv (fun t : ℝ => t * deriv χ t) r - deriv χ r := by
          rw [deriv_fun_sub]
          · exact DifferentiableAt.mul hid hχd
          · exact hχd0
    _ = (deriv χ r + r * deriv (deriv χ) r) - deriv χ r := by rw [hprod]
    _ = r * deriv (deriv χ) r := by ring

/-- Product-rule expansion of `d/dt (t²·ψ′(t))`. -/
lemma deriv_prod_sq_deriv {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (r : ℝ) :
    deriv (fun t : ℝ => t ^ 2 * deriv ψ t) r =
      r ^ 2 * deriv (deriv ψ) r + 2 * r * deriv ψ r := by
  have hψd : DifferentiableAt ℝ (deriv ψ) r := by
    have h2 : ContDiff ℝ 2 ψ := contDiff_infty.mp hψ 2
    exact (ContDiff.differentiable_deriv_two h2).differentiableAt
  have hsq : DifferentiableAt ℝ (fun t : ℝ => t ^ 2) r := by
    exact (hasDerivAt_pow (𝕜 := ℝ) 2 r).differentiableAt
  have hm := deriv_fun_mul hsq hψd
  rw [hm]
  simp
  ring

/-- If a function is eventually constantly zero at `x`, its derivative there
vanishes. -/
lemma deriv_zero_of_eventually_zero {f : ℝ → ℝ} {x : ℝ}
    (hx : f =ᶠ[𝓝 x] fun _ => (0 : ℝ)) : deriv f x = 0 := by
  have h := hx.deriv_eq
  simpa using h

/-- If `g` vanishes pointwise on the open interval `(a,b)`, then `g′` vanishes
at every point of that interval. -/
lemma deriv_eq_zero_of_eq_zero_on_Ioo {g : ℝ → ℝ} {a b x : ℝ}
    (hx : a < x) (hxb : x < b) (hg : ∀ t, a < t → t < b → g t = 0) :
    deriv g x = 0 := by
  have h_ev : g =ᶠ[𝓝 x] fun _ : ℝ => (0 : ℝ) := by
    rw [Filter.EventuallyEq]
    filter_upwards [isOpen_Ioo.mem_nhds (show x ∈ Set.Ioo a b from ⟨hx, hxb⟩)] with t ht
    exact hg t ht.1 ht.2
  exact deriv_zero_of_eventually_zero h_ev

/-- `χ″` vanishes on `(0, R)` when `χ` is supported inside `(R, ∞)`. -/
lemma deriv_chi_second_zero_on_Ioo {χ : ℝ → ℝ} {R : ℝ}
    (hχsup : ∀ r : ℝ, χ r ≠ 0 → R < r) (x : ℝ)
    (hx : x ∈ Set.Ioo (0 : ℝ) R) : deriv (deriv χ) x = 0 := by
  have hχ0 : ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) R → χ t = 0 := by
    intro t ht
    by_contra h
    have : R < t := hχsup t h
    have htR : t < R := ht.2
    linarith
  have h1 : ∀ t : ℝ, 0 < t → t < R → deriv χ t = 0 :=
    fun t ht0 htR => deriv_eq_zero_of_eq_zero_on_Ioo ht0 htR (fun s hs1 hs2 => hχ0 s ⟨hs1, hs2⟩)
  exact deriv_eq_zero_of_eq_zero_on_Ioo hx.1 hx.2 (fun t ht0 htR => h1 t ht0 htR)

/-- The 1D identity `r²·ψ″ + 2r·ψ′ = r·χ″` for `ψ := χ/r` (equivalently
`(r²·ψ′)′ = r·χ″`).  Holds at every `r` (both sides vanish at `r = 0`). -/
lemma snd_identity_div {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hψ : ContDiff ℝ ∞ (fun t : ℝ => χ t / t)) (r : ℝ) :
    r ^ 2 * deriv (deriv (fun t : ℝ => χ t / t)) r + 2 * r * deriv (fun t : ℝ => χ t / t) r
      = r * deriv (deriv χ) r := by
  by_cases hr : r = 0
  · subst r
    simp
  · have hpe : deriv (fun t : ℝ => t ^ 2 * deriv (fun s : ℝ => χ s / s) t) r =
        r ^ 2 * deriv (deriv (fun s : ℝ => χ s / s)) r + 2 * r * deriv (fun s : ℝ => χ s / s) r := by
      exact deriv_prod_sq_deriv hψ r
    have hev := eventuallyEq_sq_mul_deriv_div hχ r hr
    have hP : deriv (fun t : ℝ => t ^ 2 * deriv (fun s : ℝ => χ s / s) t) r =
        r * deriv (deriv χ) r := by
      have hd1 := hev.deriv_eq
      rw [hd1]
      exact deriv_lin_sub hχ r
    calc
      r ^ 2 * deriv (deriv (fun t : ℝ => χ t / t)) r + 2 * r * deriv (fun t : ℝ => χ t / t) r
          = deriv (fun t : ℝ => t ^ 2 * deriv (fun s : ℝ => χ s / s) t) r := by
            rw [← hpe]
      _ = r * deriv (deriv χ) r := hP

/-- Integrals over `(0,∞)` and over `(R,∞)` of a function vanishing on
`(0,R)` agree (`R > 0`). -/
lemma integral_Ioi_eq_Ioi_of_zero_on_Ioo {f : ℝ → ℝ} {R : ℝ} (hR : 0 < R)
    (hf0 : ∀ r : ℝ, r ∈ Set.Ioo (0 : ℝ) R → f r = 0) :
    (∫ r in Set.Ioi (0 : ℝ), f r) = (∫ r in Set.Ioi R, f r) := by
  have hpt : ∀ r : ℝ, r ≠ R →
      (Set.Ioi (0 : ℝ)).indicator f r = (Set.Ioi R).indicator f r := by
    intro r hrne
    by_cases h1 : r ∈ Set.Ioi (0 : ℝ)
    · by_cases h2 : r ∈ Set.Ioi R
      · simp [h1, h2]
      · have hrle : r ≤ R := le_of_not_gt h2
        have hrlt : r < R := lt_of_le_of_ne hrle hrne
        have hfr : f r = 0 := hf0 r ⟨h1, hrlt⟩
        simp [h1, h2, hfr]
    · have hnotR : r ∉ Set.Ioi R := by
        intro hR'
        have : r ≤ 0 := le_of_not_gt h1
        have hRr : R < r := hR'
        linarith
      simp [h1, hnotR]
  have h_ae : (fun r : ℝ => (Set.Ioi (0 : ℝ)).indicator f r) =ᵐ[volume]
      (fun r : ℝ => (Set.Ioi R).indicator f r) := by
    change ∀ᵐ (r : ℝ) ∂(volume : Measure ℝ),
      (Set.Ioi (0 : ℝ)).indicator f r = (Set.Ioi R).indicator f r
    rw [MeasureTheory.ae_iff]
    apply MeasureTheory.measure_mono_null
    · intro x hx
      rw [Set.mem_singleton_iff]
      by_contra hxR
      exact hx (hpt x hxR)
    · exact MeasureTheory.NullSingletonClass.measure_singleton (x := R)
  rw [← MeasureTheory.integral_indicator (s := Set.Ioi (0 : ℝ)) (f := f)
      (μ := (volume : Measure ℝ)) (by measurability)]
  rw [← MeasureTheory.integral_indicator (s := Set.Ioi R) (f := f)
      (μ := (volume : Measure ℝ)) (by measurability)]
  exact integral_congr_ae h_ae


/-- From exterior weak harmonicity of a radial `w` to the 1D annihilation
statement for `u(r) := r·(radialProfile w r)`:

    ∫ r in Set.Ioi R, (r * radialProfile w r) * deriv (deriv χ) r = 0

for every smooth compactly supported profile `χ` supported inside `(R, ∞)`. -/
theorem profile_second_annihilates_R {w : ℝ³ → ℝ} {R : ℝ} (hR : 0 < R)
    (hrad : IsRadial w) (hwli : LocallyIntegrable w)
    (hwh : ∀ φ : ℝ³ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ {x : ℝ³ | R ≤ ‖x‖} → (∫ x : ℝ³, w x * (Δ φ) x) = 0) :
    ∀ (χ : ℝ → ℝ), ContDiff ℝ ∞ χ → HasCompactSupport χ →
      (∀ r : ℝ, χ r ≠ 0 → R < r) →
      (∫ r in Set.Ioi R, (r * radialProfile w r) * deriv (deriv χ) r) = 0 := by
  intro χ hχ hχcs hχsup
  -- the radial test profile ψ := χ/r (smooth, compactly supported, in (R,∞))
  let ψ : ℝ → ℝ := fun r : ℝ => χ r / r
  have hψc : ContDiff ℝ ∞ ψ := by
    dsimp [ψ]
    exact contDiff_div_self hR hχ hχsup
  have hψcs : HasCompactSupport ψ := by
    dsimp [ψ]
    exact hasCompactSupport_div_self hχcs
  have hψsup : ∀ r : ℝ, ψ r ≠ 0 → R < r := by
    dsimp [ψ]
    exact support_div_self_gt hχsup
  -- 1D weak equation for ψ (RadialTest.radial_weakHarmonic_1D)
  have hmain := radial_weakHarmonic_1D (w := w) (R := R) hR hrad hwli hwh ψ hψc hψcs hψsup
  have hψ0 : ContDiff ℝ ∞ (fun t : ℝ => χ t / t) := by
    simpa [ψ] using hψc
  -- rewrite the 1D integrand r²·f·ψ″ + 2r·f·ψ′ = r·f·χ″ pointwise (all r)
  have hfun : (fun r : ℝ =>
        r ^ 2 * radialProfile w r * deriv (deriv ψ) r + 2 * r * radialProfile w r * deriv ψ r)
      = (fun r : ℝ => (r * radialProfile w r) * deriv (deriv χ) r) := by
    funext r
    have hsid := snd_identity_div hχ hψ0 r
    dsimp [ψ]
    calc
      r ^ 2 * radialProfile w r * deriv (deriv (fun t : ℝ => χ t / t)) r
          + 2 * r * radialProfile w r * deriv (fun t : ℝ => χ t / t) r
          = radialProfile w r * (r ^ 2 * deriv (deriv (fun t : ℝ => χ t / t)) r
              + 2 * r * deriv (fun t : ℝ => χ t / t) r) := by ring
      _ = radialProfile w r * (r * deriv (deriv χ) r) := by rw [hsid]
      _ = (r * radialProfile w r) * deriv (deriv χ) r := by ring
  have hint0 : (∫ r in Set.Ioi (0 : ℝ),
        r ^ 2 * radialProfile w r * deriv (deriv ψ) r + 2 * r * radialProfile w r * deriv ψ r)
      = (∫ r in Set.Ioi (0 : ℝ), (r * radialProfile w r) * deriv (deriv χ) r) := by
    exact congrArg (fun h : ℝ → ℝ => ∫ r : ℝ in Set.Ioi (0 : ℝ), h r) hfun
  -- integrals over (0,∞) and (R,∞) agree since χ″ = 0 on (0,R)
  have hrestr : (∫ r in Set.Ioi (0 : ℝ), (r * radialProfile w r) * deriv (deriv χ) r)
      = (∫ r in Set.Ioi R, (r * radialProfile w r) * deriv (deriv χ) r) := by
    apply integral_Ioi_eq_Ioi_of_zero_on_Ioo hR
    intro r hr
    have hχ0 : deriv (deriv χ) r = 0 := deriv_chi_second_zero_on_Ioo hχsup r hr
    simp [hχ0]
  calc
    (∫ r in Set.Ioi R, (r * radialProfile w r) * deriv (deriv χ) r)
        = (∫ r in Set.Ioi (0 : ℝ), (r * radialProfile w r) * deriv (deriv χ) r) := by
          exact hrestr.symm
    _ = (∫ r in Set.Ioi (0 : ℝ),
          r ^ 2 * radialProfile w r * deriv (deriv ψ) r + 2 * r * radialProfile w r * deriv ψ r) := by
          exact hint0.symm
    _ = 0 := hmain

end Submission.BoseGases
