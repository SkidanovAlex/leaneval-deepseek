/-
Copyright: work module for the Elgindi finite-time singularity project.

# `lzero1SliceGrowth` — the pointwise growth bound for a slice of `Lzero1 u = g`

Target: if `u` is `C^∞` on the open interval `(0, π/2)` and the weighted source
`sinθ cos²θ · |Lzero1 u θ|` is integrable on `[0, π/2]`, then

  `|u θ| ≤ C · (θ⁻¹ + (π/2 - θ)⁻¹)`  on `(0, π/2)`

for one constant `C` (depending on `u`).  Since `sinθcos²θ = O(θ)` at `θ = 0` and
`= O((π/2-θ)²)` at `θ = π/2`, the hypothesis only controls `Lzero1 u` near the endpoints by a
*barely* integrable weight; the content is that `Lzero1` has an ordinary point at `θ = 0` and a
regular singular point with indicial exponents `±1` at `θ = π/2`, so that solutions grow at
worst like the reciprocal distance to the endpoint.

## The proof (the Wronskian / reduction-of-order argument)

Write `y θ = sin 2θ` (the regular solution of `Lzero1 y = 0`), `g = Lzero1 u` and put

  `D u θ = cos θ · (u θ · y' θ - u' θ · y θ)`   (a Wronskian-type functional),
  `R u θ = u θ / y θ`.

Two exact identities drive everything:

* `(D u)' θ = 2 · g θ · sinθcos²θ`, so `|D u θ| ≤ B u := |D u (π/4)| + 2 ∫ sinθcos²θ|g|`;
* `(R u)' θ = - D u θ / (cos θ · y θ ^ 2)`.

The second is integrated over `[θ, π/4]` and `[π/4, θ]` with the bound on `D u`: since
`cos s sin²(2s) = 4 sin²s cos³s` behaves like `s²` near `0` and like `4(π/2-s)³` near `π/2`,
`∫_θ^{π/4} ds/(cos s sin²2s) ≤ (π²/8)/θ` and
`∫_{π/4}^{θ} ds/(cos s sin²2s) ≤ (π³/64)/(π/2-θ)²` (the two kernel lemmas
`lzeroGrowthKernelLeft`, `lzeroGrowthKernelRight`).  Multiplying `|R u θ|` by
`y θ = O(θ)` resp. `y θ = O(π/2-θ)` gives the claim, with the explicit constant
`|u(π/4)| π²/8 + B u π³/16 + B u π³/32 + 1`.

Everything here is a re-run of the chain of `H2W.lzeroGrowthSlice` (there stated for
*analytic* `u`) with the honest hypothesis `ContDiffOn ℝ 2 u`: only two derivatives are ever
used, so no analyticity is needed.  (That module proves only the resulting `L¹`-integrability;
the pointwise bound above is what is extracted here.)
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.H2W.lzeroGrowthSlice

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! The `C²`-version of the Wronskian chain of `H2W.lzeroGrowthSlice`.  The definitions
`Dfun`, `Rfun`, `Mfun`, `Bfun` and the smoothness-free elementary lemmas are imported from
`Work.FTS.EllipticEst.H2W.LzeroGrowth`; only the lemmas whose proof consumed the smoothness
hypothesis are redone here, at `ContDiffOn ℝ 2`. -/
namespace Lzero1Growth

open LzeroGrowth

/-! ## Derivative bookkeeping at `C²` -/

theorem hasDerivAt_u {u : ℝ → ℝ} (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2))) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : HasDerivAt u (deriv u θ) θ :=
  (hasDerivAt_of_contDiffOn isOpen_Ioo hu).1 θ hθ

theorem hasDerivAt_deriv_u {u : ℝ → ℝ} (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    HasDerivAt (deriv u) (deriv (deriv u) θ) θ :=
  (hasDerivAt_of_contDiffOn isOpen_Ioo hu).2 θ hθ

theorem continuousOn_deriv1 {u : ℝ → ℝ} (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2))) :
    ContinuousOn (deriv u) (Set.Ioo 0 (Real.pi / 2)) :=
  (hu.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)).continuousOn

theorem continuousOn_deriv2 {u : ℝ → ℝ} (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2))) :
    ContinuousOn (fun θ => deriv (deriv u) θ) (Set.Ioo 0 (Real.pi / 2)) :=
  ((hu.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)).deriv_of_isOpen isOpen_Ioo
    (m := 0) (by norm_num)).continuousOn

theorem continuousOn_tan_mul {u : ℝ → ℝ} (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2))) :
    ContinuousOn (fun θ => deriv (fun t => Real.tan t * u t) θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
  have hc0 : ContinuousOn u (Set.Ioo 0 (Real.pi / 2)) := hu.continuousOn
  have hc1 : ContinuousOn (deriv u) (Set.Ioo 0 (Real.pi / 2)) := continuousOn_deriv1 hu
  have hg : ContinuousOn
      (fun θ : ℝ => (1 / Real.cos θ ^ 2) * u θ + Real.tan θ * deriv u θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
    have h1 : ContinuousOn (fun θ : ℝ => 1 / Real.cos θ ^ 2) (Set.Ioo 0 (Real.pi / 2)) := by
      refine ContinuousOn.div continuousOn_const (Real.continuous_cos.continuousOn.pow 2) ?_
      intro θ hθ
      exact pow_ne_zero 2 (cos_ne_zero hθ)
    have h2 : ContinuousOn (fun θ : ℝ => Real.tan θ * deriv u θ)
        (Set.Ioo 0 (Real.pi / 2)) := by
      have ht : ContinuousOn Real.tan (Set.Ioo 0 (Real.pi / 2)) :=
        Real.continuousOn_tan.mono (fun x hx => cos_ne_zero hx)
      rw [show (fun θ : ℝ => Real.tan θ * deriv u θ) = Real.tan * deriv u from rfl]
      exact ht.mul hc1
    exact (h1.mul hc0).add h2
  refine ContinuousOn.congr hg ?_
  intro θ hθ
  show deriv (fun t => Real.tan t * u t) θ
    = (1 / Real.cos θ ^ 2) * u θ + Real.tan θ * deriv u θ
  have hm' : HasDerivAt (fun t => Real.tan t * u t)
      ((1 / Real.cos θ ^ 2) * u θ + Real.tan θ * deriv u θ) θ :=
    (Real.hasDerivAt_tan (cos_ne_zero hθ)).mul (hasDerivAt_u hu hθ)
  rw [hm'.deriv]

/-- `Lzero1 u` is continuous on the open interval (only `C²` is needed). -/
theorem continuousOn_Lzero1 {u : ℝ → ℝ} (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2))) :
    ContinuousOn (Work.FTS.EllipticEst.Lzero1 u) (Set.Ioo 0 (Real.pi / 2)) := by
  have hc0 : ContinuousOn u (Set.Ioo 0 (Real.pi / 2)) := hu.continuousOn
  have hc2 : ContinuousOn (fun θ => deriv (deriv u) θ) (Set.Ioo 0 (Real.pi / 2)) :=
    continuousOn_deriv2 hu
  have hm : ContinuousOn (fun θ => deriv (fun t => Real.tan t * u t) θ)
      (Set.Ioo 0 (Real.pi / 2)) := continuousOn_tan_mul hu
  refine ContinuousOn.congr (f := fun θ =>
    -(deriv (deriv u) θ) + deriv (fun t => Real.tan t * u t) θ - 6 * u θ) ?_ ?_
  · exact ((hc2.neg).add hm).sub (hc0.const_mul 6)
  · intro θ hθ
    simp only [Work.FTS.EllipticEst.Lzero1]

theorem intervalIntegrable_two_mul {u : ℝ → ℝ} (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    {a b : ℝ} (hsub : Set.uIcc a b ⊆ Set.Ioo 0 (Real.pi / 2)) :
    IntervalIntegrable
      (fun s : ℝ => 2 * Work.FTS.EllipticEst.Lzero1 u s * Work.Elliptic.sinCos2 s)
      volume a b := by
  have h1 : ContinuousOn
      (fun s : ℝ => 2 * Work.FTS.EllipticEst.Lzero1 u s * Work.Elliptic.sinCos2 s)
      (Set.Ioo 0 (Real.pi / 2)) :=
    ((continuousOn_Lzero1 hu).const_mul 2).mul continuous_sinCos2.continuousOn
  exact (h1.mono hsub).intervalIntegrable

/-! ## The two exact identities -/

/-- The normal form of the equation `Lzero1 u = g` on the open interval. -/
theorem u_ode {u : ℝ → ℝ} (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2))) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    deriv (deriv u) θ = Real.tan θ * deriv u θ + (1 / Real.cos θ ^ 2 - 6) * u θ
      - Work.FTS.EllipticEst.Lzero1 u θ := by
  have hc := cos_ne_zero hθ
  have hdu : HasDerivAt u (deriv u θ) θ := hasDerivAt_u hu hθ
  have htan : HasDerivAt (fun t => Real.tan t * u t)
      ((1 / Real.cos θ ^ 2) * u θ + Real.tan θ * deriv u θ) θ :=
    (Real.hasDerivAt_tan hc).mul hdu
  simp only [Work.FTS.EllipticEst.Lzero1]
  rw [htan.deriv]
  ring

/-- **The derivative of `Dfun`**: `D u` has derivative `2 · Lzero1 u θ · sinθcos²θ`. -/
theorem Dfun_hasDerivAt {u : ℝ → ℝ} (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2))) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    HasDerivAt (Dfun u) (2 * Work.FTS.EllipticEst.Lzero1 u θ * Work.Elliptic.sinCos2 θ) θ := by
  have hc := cos_ne_zero hθ
  have hdu : HasDerivAt u (deriv u θ) θ := hasDerivAt_u hu hθ
  have hd2u : HasDerivAt (deriv u) (deriv (deriv u) θ) θ := hasDerivAt_deriv_u hu hθ
  have hsin := hasDerivAt_sin_two θ
  have hcos := hasDerivAt_cos_two θ
  have h2c : HasDerivAt (fun t : ℝ => 2 * Real.cos (2 * t)) (-4 * Real.sin (2 * θ)) θ :=
    (hcos.const_mul 2).congr_deriv (by ring)
  have hA : HasDerivAt (fun t : ℝ => u t * (2 * Real.cos (2 * t)))
      (deriv u θ * (2 * Real.cos (2 * θ)) + u θ * (-4 * Real.sin (2 * θ))) θ := hdu.mul h2c
  have hB : HasDerivAt (fun t : ℝ => deriv u t * Real.sin (2 * t))
      (deriv (deriv u) θ * Real.sin (2 * θ) + deriv u θ * (2 * Real.cos (2 * θ))) θ :=
    hd2u.mul hsin
  have hmain : HasDerivAt
      (fun t : ℝ => (u t * (2 * Real.cos (2 * t)) - deriv u t * Real.sin (2 * t)))
      ((deriv u θ * (2 * Real.cos (2 * θ)) + u θ * (-4 * Real.sin (2 * θ)))
        - (deriv (deriv u) θ * Real.sin (2 * θ)
            + deriv u θ * (2 * Real.cos (2 * θ)))) θ :=
    hA.sub hB
  have hcosθ : HasDerivAt (fun t : ℝ => Real.cos t) (-Real.sin θ) θ := Real.hasDerivAt_cos θ
  have hD : HasDerivAt (Dfun u)
      ((-Real.sin θ) * (u θ * (2 * Real.cos (2 * θ)) - deriv u θ * Real.sin (2 * θ))
        + Real.cos θ * ((deriv u θ * (2 * Real.cos (2 * θ)) + u θ * (-4 * Real.sin (2 * θ)))
            - (deriv (deriv u) θ * Real.sin (2 * θ)
                + deriv u θ * (2 * Real.cos (2 * θ))))) θ :=
    hcosθ.mul hmain
  refine hD.congr_deriv ?_
  rw [u_ode hu hθ]
  rw [Real.sin_two_mul, Real.cos_two_mul, Real.tan_eq_sin_div_cos, Work.Elliptic.sinCos2]
  field_simp
  ring

/-- The derivative identity `(u / sin 2θ)' = - D u /(cos θ · sin²2θ)`. -/
theorem Rfun_hasDerivAt {u : ℝ → ℝ} (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2))) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    HasDerivAt (Rfun u)
      (-(Dfun u θ) / (Real.cos θ * (Real.sin (2 * θ)) ^ 2)) θ := by
  have hc := cos_ne_zero hθ
  have hs := sin_two_pos hθ
  have hdu : HasDerivAt u (deriv u θ) θ := hasDerivAt_u hu hθ
  have hdiv := hdu.div (hasDerivAt_sin_two θ) (ne_of_gt hs)
  refine hdiv.congr_deriv ?_
  rw [Dfun]
  field_simp
  ring

/-! ## The bound on `Dfun` and the two growth bounds for `Rfun` -/

/-- **`D` has bounded oscillation.**  `|D u θ| ≤ B u = |D u (π/4)| + 2 M u`. -/
theorem Dfun_bound {u : ℝ → ℝ} (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (hg : IntegrableOn
      (fun θ : ℝ => Work.Elliptic.sinCos2 θ * |Work.FTS.EllipticEst.Lzero1 u θ|)
      Work.Spaces.Iθ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    |Dfun u θ| ≤ Bfun u := by
  have hstep : ∀ a b : ℝ, a ≤ b → Set.uIcc a b ⊆ Set.Ioo 0 (Real.pi / 2) →
      |Dfun u b - Dfun u a| ≤ 2 * Mfun u := by
    intro a b hab hsub
    have hineq : Set.Ioc a b ⊆ Work.Spaces.Iθ := by
      intro s hs
      refine mem_Iθ_of_mem_Ioo (hsub ?_)
      simp only [Set.uIcc_of_le hab, Set.mem_Icc]
      exact ⟨le_of_lt hs.1, hs.2⟩
    have hsubI : Set.uIcc a b ⊆ Work.Spaces.Iθ := by
      intro s hs
      exact mem_Iθ_of_mem_Ioo (hsub hs)
    have hftc : ∫ s in a..b,
        2 * Work.FTS.EllipticEst.Lzero1 u s * Work.Elliptic.sinCos2 s
          = Dfun u b - Dfun u a :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun s hs => Dfun_hasDerivAt hu (hsub hs)) (intervalIntegrable_two_mul hu hsub)
    rw [← hftc]
    calc |∫ s in a..b, 2 * Work.FTS.EllipticEst.Lzero1 u s * Work.Elliptic.sinCos2 s|
        ≤ ∫ s in a..b, |2 * Work.FTS.EllipticEst.Lzero1 u s * Work.Elliptic.sinCos2 s| :=
          intervalIntegral.abs_integral_le_integral_abs hab
      _ = ∫ s in a..b, 2 * (Work.Elliptic.sinCos2 s * |Work.FTS.EllipticEst.Lzero1 u s|) := by
          refine intervalIntegral.integral_congr (fun s hs => ?_)
          have hs' : s ∈ Work.Spaces.Iθ := hsubI hs
          rw [abs_mul, abs_mul, abs_of_nonneg (sinCos2_nonneg hs'),
            abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
          ring
      _ = ∫ s in Set.Ioc a b,
            2 * (Work.Elliptic.sinCos2 s * |Work.FTS.EllipticEst.Lzero1 u s|) :=
          intervalIntegral.integral_of_le hab
      _ ≤ ∫ s in Work.Spaces.Iθ,
            2 * (Work.Elliptic.sinCos2 s * |Work.FTS.EllipticEst.Lzero1 u s|) := by
          refine setIntegral_mono_set (hg.const_mul 2) ?_ ?_
          · filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
            exact mul_nonneg (by norm_num)
              (mul_nonneg (sinCos2_nonneg hs) (abs_nonneg _))
          · filter_upwards with s hs using hineq hs
      _ = 2 * Mfun u := by rw [Mfun, integral_const_mul]
  rcases le_or_gt (Real.pi / 4) θ with hle | hlt
  · have hsub : Set.uIcc (Real.pi / 4) θ ⊆ Set.Ioo 0 (Real.pi / 2) := by
      intro s hs
      simp only [Set.uIcc_of_le hle, Set.mem_Icc] at hs
      exact ⟨by linarith [hs.1, Real.pi_pos], by linarith [hs.2, hθ.2]⟩
    have hb := hstep (Real.pi / 4) θ hle hsub
    calc |Dfun u θ| = |(Dfun u θ - Dfun u (Real.pi / 4)) + Dfun u (Real.pi / 4)| := by ring_nf
      _ ≤ |Dfun u θ - Dfun u (Real.pi / 4)| + |Dfun u (Real.pi / 4)| := abs_add_le _ _
      _ ≤ 2 * Mfun u + |Dfun u (Real.pi / 4)| := by linarith
      _ = Bfun u := by rw [Bfun]; ring
  · have hsub : Set.uIcc θ (Real.pi / 4) ⊆ Set.Ioo 0 (Real.pi / 2) := by
      intro s hs
      simp only [Set.uIcc_of_le (le_of_lt hlt), Set.mem_Icc] at hs
      exact ⟨by linarith [hs.1, hθ.1], by linarith [hs.2, Real.pi_pos]⟩
    have hb := hstep θ (Real.pi / 4) (le_of_lt hlt) hsub
    have hb' : |Dfun u θ - Dfun u (Real.pi / 4)| ≤ 2 * Mfun u := by
      rwa [abs_sub_comm] at hb
    calc |Dfun u θ| = |(Dfun u θ - Dfun u (Real.pi / 4)) + Dfun u (Real.pi / 4)| := by ring_nf
      _ ≤ |Dfun u θ - Dfun u (Real.pi / 4)| + |Dfun u (Real.pi / 4)| := abs_add_le _ _
      _ ≤ 2 * Mfun u + |Dfun u (Real.pi / 4)| := by linarith
      _ = Bfun u := by rw [Bfun]; ring

theorem continuousOn_Dfun {u : ℝ → ℝ} (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2))) :
    ContinuousOn (Dfun u) (Set.Ioo 0 (Real.pi / 2)) := by
  have hc0 : ContinuousOn u (Set.Ioo 0 (Real.pi / 2)) := hu.continuousOn
  have hc1 : ContinuousOn (deriv u) (Set.Ioo 0 (Real.pi / 2)) := continuousOn_deriv1 hu
  have h2 : ContinuousOn (fun θ : ℝ => 2 * Real.cos (2 * θ)) (Set.Ioo 0 (Real.pi / 2)) :=
    (by fun_prop : Continuous fun θ : ℝ => 2 * Real.cos (2 * θ)).continuousOn
  have h3 : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo 0 (Real.pi / 2)) :=
    (by fun_prop : Continuous fun θ : ℝ => Real.sin (2 * θ)).continuousOn
  have h4 : ContinuousOn (Real.cos) (Set.Ioo 0 (Real.pi / 2)) :=
    Real.continuous_cos.continuousOn
  exact (h4.mul ((hc0.mul h2).sub (hc1.mul h3)))

theorem continuousOn_Rderiv {u : ℝ → ℝ} (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2))) :
    ContinuousOn (fun s : ℝ => -(Dfun u s) / (Real.cos s * (Real.sin (2 * s)) ^ 2))
      (Set.Ioo 0 (Real.pi / 2)) := by
  have hc : ContinuousOn (fun s : ℝ => Real.cos s * (Real.sin (2 * s)) ^ 2)
      (Set.Ioo 0 (Real.pi / 2)) :=
    (Real.continuous_cos.continuousOn).mul
      ((by fun_prop : Continuous fun s : ℝ => Real.sin (2 * s)).continuousOn.pow 2)
  refine ((continuousOn_Dfun hu).neg).div hc ?_
  intro s hs
  exact mul_ne_zero (cos_ne_zero hs) (pow_ne_zero 2 (ne_of_gt (sin_two_pos hs)))

theorem continuousOn_invker :
    ContinuousOn (fun s : ℝ => 1 / (Real.cos s * (Real.sin (2 * s)) ^ 2))
      (Set.Ioo 0 (Real.pi / 2)) := by
  have hc : ContinuousOn (fun s : ℝ => Real.cos s * (Real.sin (2 * s)) ^ 2)
      (Set.Ioo 0 (Real.pi / 2)) :=
    (Real.continuous_cos.continuousOn).mul
      ((by fun_prop : Continuous fun s : ℝ => Real.sin (2 * s)).continuousOn.pow 2)
  refine ContinuousOn.div continuousOn_const hc ?_
  intro s hs
  exact mul_ne_zero (cos_ne_zero hs) (pow_ne_zero 2 (ne_of_gt (sin_two_pos hs)))

/-- **Growth bound near `π/2`.**  For `θ ∈ [π/4, π/2)`,
`|u θ / sin 2θ| ≤ |u(π/4)| + B u · ∫_{π/4}^{θ} ds/(cos s · sin²2s)`. -/
theorem Rfun_bound_right {u : ℝ → ℝ} (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (hg : IntegrableOn
      (fun θ : ℝ => Work.Elliptic.sinCos2 θ * |Work.FTS.EllipticEst.Lzero1 u θ|)
      Work.Spaces.Iθ) {θ : ℝ} (hθ : θ ∈ Set.Ico (Real.pi / 4) (Real.pi / 2)) :
    |Rfun u θ| ≤ |Rfun u (Real.pi / 4)|
      + Bfun u * ∫ s in (Real.pi / 4)..θ,
          1 / (Real.cos s * (Real.sin (2 * s)) ^ 2) := by
  have hle : Real.pi / 4 ≤ θ := hθ.1
  have hsub : Set.uIcc (Real.pi / 4) θ ⊆ Set.Ioo 0 (Real.pi / 2) := by
    intro s hs
    simp only [Set.uIcc_of_le hle, Set.mem_Icc] at hs
    exact ⟨by linarith [hs.1, Real.pi_pos], by linarith [hs.2, hθ.2]⟩
  have hftc : ∫ s in (Real.pi / 4)..θ,
      -(Dfun u s) / (Real.cos s * (Real.sin (2 * s)) ^ 2) = Rfun u θ - Rfun u (Real.pi / 4) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s hs => Rfun_hasDerivAt hu (hsub hs))
      (((continuousOn_Rderiv hu).mono hsub).intervalIntegrable)
  have h1 : |Rfun u θ - Rfun u (Real.pi / 4)|
      ≤ ∫ s in (Real.pi / 4)..θ,
          |-(Dfun u s) / (Real.cos s * (Real.sin (2 * s)) ^ 2)| := by
    rw [← hftc]
    exact intervalIntegral.abs_integral_le_integral_abs hle
  have h2 : ∫ s in (Real.pi / 4)..θ,
        |-(Dfun u s) / (Real.cos s * (Real.sin (2 * s)) ^ 2)|
      ≤ Bfun u * ∫ s in (Real.pi / 4)..θ,
          1 / (Real.cos s * (Real.sin (2 * s)) ^ 2) := by
    have hpt : ∀ s ∈ Set.Icc (Real.pi / 4) θ,
        |-(Dfun u s) / (Real.cos s * (Real.sin (2 * s)) ^ 2)|
          ≤ Bfun u * (1 / (Real.cos s * (Real.sin (2 * s)) ^ 2)) := by
      intro s hs
      have hs' : s ∈ Set.Ioo 0 (Real.pi / 2) := hsub (by simpa only [Set.uIcc_of_le hle] using hs)
      have hden : 0 < Real.cos s * (Real.sin (2 * s)) ^ 2 :=
        mul_pos (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hs'.1], hs'.2⟩)
          (pow_pos (sin_two_pos hs') 2)
      rw [abs_div, abs_neg, abs_of_pos hden]
      rw [div_le_iff₀ hden]
      rw [show Bfun u * (1 / (Real.cos s * (Real.sin (2 * s)) ^ 2))
            * (Real.cos s * (Real.sin (2 * s)) ^ 2) = Bfun u by
          rw [mul_assoc, one_div, inv_mul_cancel₀ (ne_of_gt hden), mul_one]]
      exact Dfun_bound hu hg hs'
    have hia : IntervalIntegrable
        (fun s : ℝ => |-(Dfun u s) / (Real.cos s * (Real.sin (2 * s)) ^ 2)|) volume
        (Real.pi / 4) θ :=
      (((continuousOn_Rderiv hu).abs).mono hsub).intervalIntegrable
    have hib : IntervalIntegrable
        (fun s : ℝ => Bfun u * (1 / (Real.cos s * (Real.sin (2 * s)) ^ 2))) volume
        (Real.pi / 4) θ :=
      (((continuousOn_invker.const_mul (Bfun u)).mono hsub)).intervalIntegrable
    calc ∫ s in (Real.pi / 4)..θ,
          |-(Dfun u s) / (Real.cos s * (Real.sin (2 * s)) ^ 2)|
        ≤ ∫ s in (Real.pi / 4)..θ,
            Bfun u * (1 / (Real.cos s * (Real.sin (2 * s)) ^ 2)) :=
          intervalIntegral.integral_mono_on hle hia hib hpt
      _ = Bfun u * ∫ s in (Real.pi / 4)..θ,
            1 / (Real.cos s * (Real.sin (2 * s)) ^ 2) :=
          intervalIntegral.integral_const_mul _ _
  calc |Rfun u θ| = |Rfun u (Real.pi / 4) + (Rfun u θ - Rfun u (Real.pi / 4))| := by ring_nf
    _ ≤ |Rfun u (Real.pi / 4)| + |Rfun u θ - Rfun u (Real.pi / 4)| := abs_add_le _ _
    _ ≤ |Rfun u (Real.pi / 4)|
          + (∫ s in (Real.pi / 4)..θ,
              |-(Dfun u s) / (Real.cos s * (Real.sin (2 * s)) ^ 2)|) :=
        add_le_add (le_refl _) h1
    _ ≤ |Rfun u (Real.pi / 4)|
          + Bfun u * (∫ s in (Real.pi / 4)..θ,
              1 / (Real.cos s * (Real.sin (2 * s)) ^ 2)) :=
        add_le_add (le_refl _) h2

/-- **Growth bound near `0`.**  For `θ ∈ (0, π/4]`,
`|u θ / sin 2θ| ≤ |u(π/4)| + B u · ∫_{θ}^{π/4} ds/(cos s · sin²2s)`. -/
theorem Rfun_bound_left {u : ℝ → ℝ} (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (hg : IntegrableOn
      (fun θ : ℝ => Work.Elliptic.sinCos2 θ * |Work.FTS.EllipticEst.Lzero1 u θ|)
      Work.Spaces.Iθ) {θ : ℝ} (hθ : θ ∈ Set.Ioc 0 (Real.pi / 4)) :
    |Rfun u θ| ≤ |Rfun u (Real.pi / 4)|
      + Bfun u * ∫ s in θ..(Real.pi / 4),
          1 / (Real.cos s * (Real.sin (2 * s)) ^ 2) := by
  have hle : θ ≤ Real.pi / 4 := hθ.2
  have hsub : Set.uIcc θ (Real.pi / 4) ⊆ Set.Ioo 0 (Real.pi / 2) := by
    intro s hs
    simp only [Set.uIcc_of_le hle, Set.mem_Icc] at hs
    exact ⟨by linarith [hs.1, hθ.1], by linarith [hs.2, Real.pi_pos]⟩
  have hftc : ∫ s in θ..(Real.pi / 4),
      -(Dfun u s) / (Real.cos s * (Real.sin (2 * s)) ^ 2) = Rfun u (Real.pi / 4) - Rfun u θ :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s hs => Rfun_hasDerivAt hu (hsub hs))
      (((continuousOn_Rderiv hu).mono hsub).intervalIntegrable)
  have h1 : |Rfun u (Real.pi / 4) - Rfun u θ|
      ≤ ∫ s in θ..(Real.pi / 4),
          |-(Dfun u s) / (Real.cos s * (Real.sin (2 * s)) ^ 2)| := by
    rw [← hftc]
    exact intervalIntegral.abs_integral_le_integral_abs hle
  have h2 : ∫ s in θ..(Real.pi / 4),
        |-(Dfun u s) / (Real.cos s * (Real.sin (2 * s)) ^ 2)|
      ≤ Bfun u * ∫ s in θ..(Real.pi / 4),
          1 / (Real.cos s * (Real.sin (2 * s)) ^ 2) := by
    have hpt : ∀ s ∈ Set.Icc θ (Real.pi / 4),
        |-(Dfun u s) / (Real.cos s * (Real.sin (2 * s)) ^ 2)|
          ≤ Bfun u * (1 / (Real.cos s * (Real.sin (2 * s)) ^ 2)) := by
      intro s hs
      have hs' : s ∈ Set.Ioo 0 (Real.pi / 2) := hsub (by simpa only [Set.uIcc_of_le hle] using hs)
      have hden : 0 < Real.cos s * (Real.sin (2 * s)) ^ 2 :=
        mul_pos (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hs'.1], hs'.2⟩)
          (pow_pos (sin_two_pos hs') 2)
      rw [abs_div, abs_neg, abs_of_pos hden]
      rw [div_le_iff₀ hden]
      rw [show Bfun u * (1 / (Real.cos s * (Real.sin (2 * s)) ^ 2))
            * (Real.cos s * (Real.sin (2 * s)) ^ 2) = Bfun u by
          rw [mul_assoc, one_div, inv_mul_cancel₀ (ne_of_gt hden), mul_one]]
      exact Dfun_bound hu hg hs'
    have hia : IntervalIntegrable
        (fun s : ℝ => |-(Dfun u s) / (Real.cos s * (Real.sin (2 * s)) ^ 2)|) volume
        θ (Real.pi / 4) :=
      (((continuousOn_Rderiv hu).abs).mono hsub).intervalIntegrable
    have hib : IntervalIntegrable
        (fun s : ℝ => Bfun u * (1 / (Real.cos s * (Real.sin (2 * s)) ^ 2))) volume
        θ (Real.pi / 4) :=
      (((continuousOn_invker.const_mul (Bfun u)).mono hsub)).intervalIntegrable
    calc ∫ s in θ..(Real.pi / 4),
          |-(Dfun u s) / (Real.cos s * (Real.sin (2 * s)) ^ 2)|
        ≤ ∫ s in θ..(Real.pi / 4),
            Bfun u * (1 / (Real.cos s * (Real.sin (2 * s)) ^ 2)) :=
          intervalIntegral.integral_mono_on hle hia hib hpt
      _ = Bfun u * ∫ s in θ..(Real.pi / 4),
            1 / (Real.cos s * (Real.sin (2 * s)) ^ 2) :=
          intervalIntegral.integral_const_mul _ _
  calc |Rfun u θ| = |Rfun u (Real.pi / 4) + (Rfun u θ - Rfun u (Real.pi / 4))| := by ring_nf
    _ ≤ |Rfun u (Real.pi / 4)| + |Rfun u θ - Rfun u (Real.pi / 4)| := abs_add_le _ _
    _ = |Rfun u (Real.pi / 4)| + |Rfun u (Real.pi / 4) - Rfun u θ| := by rw [abs_sub_comm]
    _ ≤ |Rfun u (Real.pi / 4)|
          + (∫ s in θ..(Real.pi / 4),
              |-(Dfun u s) / (Real.cos s * (Real.sin (2 * s)) ^ 2)|) :=
        add_le_add (le_refl _) h1
    _ ≤ |Rfun u (Real.pi / 4)|
          + Bfun u * (∫ s in θ..(Real.pi / 4),
              1 / (Real.cos s * (Real.sin (2 * s)) ^ 2)) :=
        add_le_add (le_refl _) h2

theorem Rfun_bound_two {u : ℝ → ℝ} (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (hg : IntegrableOn
      (fun θ : ℝ => Work.Elliptic.sinCos2 θ * |Work.FTS.EllipticEst.Lzero1 u θ|)
      Work.Spaces.Iθ) :
    (∀ θ ∈ Set.Ioc (0 : ℝ) (Real.pi / 4),
        |Rfun u θ| ≤ |Rfun u (Real.pi / 4)|
          + Bfun u * ∫ s in θ..(Real.pi / 4),
              1 / (Real.cos s * (Real.sin (2 * s)) ^ 2))
    ∧ (∀ θ ∈ Set.Ico (Real.pi / 4) (Real.pi / 2),
        |Rfun u θ| ≤ |Rfun u (Real.pi / 4)|
          + Bfun u * ∫ s in (Real.pi / 4)..θ,
              1 / (Real.cos s * (Real.sin (2 * s)) ^ 2)) :=
  ⟨fun θ hθ => Rfun_bound_left hu hg hθ, fun θ hθ => Rfun_bound_right hu hg hθ⟩

/-! ## From the two `Rfun` bounds to the pointwise growth of `u` -/

/-- The exact factorisation `u θ = Rfun u θ · sin 2θ`, valid because `sin 2θ ≠ 0`. -/
theorem Rfun_mul_sin {u : ℝ → ℝ} {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Rfun u θ * Real.sin (2 * θ) = u θ := by
  rw [Rfun]
  exact div_mul_cancel₀ _ (ne_of_gt (sin_two_pos hθ))

/-- **The pointwise growth bound.**  The two `Rfun` bounds of `Rfun_bound_two`, together with
the two explicit kernel estimates `lzeroGrowthKernelLeft`/`Right`, give
`|u θ| ≤ C (θ⁻¹ + (π/2-θ)⁻¹)`; the constant constructed is
`|u(π/4)| π²/8 + B u π³/16 + B u π³/32 + 1`. -/
theorem growthOfRfunBounds {u : ℝ → ℝ}
    (hleft : ∀ θ ∈ Set.Ioc (0 : ℝ) (Real.pi / 4),
        |Rfun u θ| ≤ |Rfun u (Real.pi / 4)|
          + Bfun u * ∫ s in θ..(Real.pi / 4),
              1 / (Real.cos s * (Real.sin (2 * s)) ^ 2))
    (hright : ∀ θ ∈ Set.Ico (Real.pi / 4) (Real.pi / 2),
        |Rfun u θ| ≤ |Rfun u (Real.pi / 4)|
          + Bfun u * ∫ s in (Real.pi / 4)..θ,
              1 / (Real.cos s * (Real.sin (2 * s)) ^ 2)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |u θ| ≤ C * (θ⁻¹ + (Real.pi / 2 - θ)⁻¹) := by
  set A : ℝ := |Rfun u (Real.pi / 4)| with hAdef
  set B : ℝ := Bfun u with hBdef
  have hA : 0 ≤ A := abs_nonneg _
  have hB : 0 ≤ B := Bfun_nonneg u
  set C : ℝ := A * (Real.pi ^ 2 / 8) + B * (Real.pi ^ 3 / 16) + B * (Real.pi ^ 3 / 32) + 1
    with hCdef
  have hC : 0 ≤ C := by
    have h1 : 0 ≤ A * (Real.pi ^ 2 / 8) := mul_nonneg hA (by positivity)
    have h2 : 0 ≤ B * (Real.pi ^ 3 / 16) := mul_nonneg hB (by positivity)
    have h3 : 0 ≤ B * (Real.pi ^ 3 / 32) := mul_nonneg hB (by positivity)
    rw [hCdef]; linarith
  refine ⟨C, hC, fun θ hθ => ?_⟩
  have hs2 : 0 < Real.sin (2 * θ) := sin_two_pos hθ
  have habs : |u θ| = |Rfun u θ| * Real.sin (2 * θ) := by
    rw [← Rfun_mul_sin (u := u) hθ, abs_mul, abs_of_pos hs2]
  have htpos : 0 < Real.pi / 2 - θ := by linarith [hθ.2]
  have hinvθ : 0 ≤ θ⁻¹ := inv_nonneg.mpr hθ.1.le
  have hinvt : 0 ≤ (Real.pi / 2 - θ)⁻¹ := inv_nonneg.mpr htpos.le
  have hfin : C * θ⁻¹ ≤ C * (θ⁻¹ + (Real.pi / 2 - θ)⁻¹) :=
    mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hinvt) hC
  rcases le_or_gt θ (Real.pi / 4) with hle | hgt
  · -- the left half `θ ∈ (0, π/4]`
    have hθl : θ ∈ Set.Ioc (0 : ℝ) (Real.pi / 4) := ⟨hθ.1, hle⟩
    have hR := hleft θ hθl
    have hK : ∫ s in θ..(Real.pi / 4), 1 / (Real.cos s * (Real.sin (2 * s)) ^ 2)
        ≤ (Real.pi ^ 2 / 8) / θ := lzeroGrowthKernelLeft hθl
    have hcoef : |Rfun u θ| ≤ A + B * ((Real.pi ^ 2 / 8) / θ) := by
      have h1 : B * (∫ s in θ..(Real.pi / 4), 1 / (Real.cos s * (Real.sin (2 * s)) ^ 2))
          ≤ B * ((Real.pi ^ 2 / 8) / θ) := mul_le_mul_of_nonneg_left hK hB
      rw [hAdef, hBdef] at hR
      linarith
    have hcoef0 : 0 ≤ A + B * ((Real.pi ^ 2 / 8) / θ) := by
      have : 0 ≤ B * ((Real.pi ^ 2 / 8) / θ) :=
        mul_nonneg hB (div_nonneg (by positivity) hθ.1.le)
      linarith
    have hsinle : Real.sin (2 * θ) ≤ 2 * θ := Real.sin_le (by linarith [hθ.1])
    have hstep : |u θ| ≤ (A + B * ((Real.pi ^ 2 / 8) / θ)) * (2 * θ) := by
      rw [habs]
      exact le_trans (mul_le_mul_of_nonneg_right hcoef hs2.le)
        (mul_le_mul_of_nonneg_left hsinle hcoef0)
    have h1 : 2 * A * θ ^ 2 ≤ A * (Real.pi ^ 2 / 8) := by
      have hθ2 : θ ^ 2 ≤ (Real.pi / 4) ^ 2 := pow_le_pow_left₀ hθ.1.le hle 2
      have := mul_le_mul_of_nonneg_left hθ2 (by linarith : (0 : ℝ) ≤ 2 * A)
      nlinarith [this, Real.pi_pos]
    have h2 : B * (Real.pi ^ 2 / 4) * θ ≤ B * (Real.pi ^ 3 / 16) := by
      have hπ : (Real.pi ^ 2 / 4) * θ ≤ (Real.pi ^ 2 / 4) * (Real.pi / 4) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
      have h3 := mul_le_mul_of_nonneg_left hπ hB
      calc B * (Real.pi ^ 2 / 4) * θ = B * ((Real.pi ^ 2 / 4) * θ) := by ring
        _ ≤ B * ((Real.pi ^ 2 / 4) * (Real.pi / 4)) := h3
        _ = B * (Real.pi ^ 3 / 16) := by ring
    have h3 : A * (Real.pi ^ 2 / 8) + B * (Real.pi ^ 3 / 16) ≤ C := by
      have h4 : 0 ≤ B * (Real.pi ^ 3 / 32) := mul_nonneg hB (by positivity)
      rw [hCdef]; linarith
    have hθne : θ ≠ 0 := ne_of_gt hθ.1
    have hval : (A + B * ((Real.pi ^ 2 / 8) / θ)) * (2 * θ)
        = 2 * A * θ + B * (Real.pi ^ 2 / 4) := by
      field_simp [hθne]
      ring
    have hmain : 2 * A * θ + B * (Real.pi ^ 2 / 4) ≤ C * θ⁻¹ := by
      rw [show C * θ⁻¹ = C / θ from (div_eq_mul_inv C θ).symm, le_div_iff₀ hθ.1]
      nlinarith [h1, h2, h3]
    calc |u θ| ≤ (A + B * ((Real.pi ^ 2 / 8) / θ)) * (2 * θ) := hstep
      _ = 2 * A * θ + B * (Real.pi ^ 2 / 4) := hval
      _ ≤ C * θ⁻¹ := hmain
      _ ≤ C * (θ⁻¹ + (Real.pi / 2 - θ)⁻¹) := hfin
  · -- the right half `θ ∈ [π/4, π/2)`
    have hθr : θ ∈ Set.Ico (Real.pi / 4) (Real.pi / 2) := ⟨hgt.le, hθ.2⟩
    have hR := hright θ hθr
    set t : ℝ := Real.pi / 2 - θ with htdef
    have ht0 : 0 < t := by rw [htdef]; exact htpos
    have htle : t ≤ Real.pi / 4 := by rw [htdef]; linarith [hgt]
    have hK : ∫ s in (Real.pi / 4)..θ, 1 / (Real.cos s * (Real.sin (2 * s)) ^ 2)
        ≤ (Real.pi ^ 3 / 64) / t ^ 2 := by
      simpa only [← htdef] using lzeroGrowthKernelRight hθr
    have hcoef : |Rfun u θ| ≤ A + B * ((Real.pi ^ 3 / 64) / t ^ 2) := by
      have h1 : B * (∫ s in (Real.pi / 4)..θ, 1 / (Real.cos s * (Real.sin (2 * s)) ^ 2))
          ≤ B * ((Real.pi ^ 3 / 64) / t ^ 2) := mul_le_mul_of_nonneg_left hK hB
      rw [hAdef, hBdef] at hR
      linarith
    have hcoef0 : 0 ≤ A + B * ((Real.pi ^ 3 / 64) / t ^ 2) := by
      have : 0 ≤ B * ((Real.pi ^ 3 / 64) / t ^ 2) :=
        mul_nonneg hB (div_nonneg (by positivity) (sq_nonneg t))
      linarith
    have hsinle : Real.sin (2 * θ) ≤ 2 * t := by
      have h2θ : 2 * θ = Real.pi - 2 * t := by rw [htdef]; ring
      rw [h2θ, Real.sin_pi_sub]
      exact Real.sin_le (by linarith)
    have hstep : |u θ| ≤ (A + B * ((Real.pi ^ 3 / 64) / t ^ 2)) * (2 * t) := by
      rw [habs]
      exact le_trans (mul_le_mul_of_nonneg_right hcoef hs2.le)
        (mul_le_mul_of_nonneg_left hsinle hcoef0)
    have h1 : 2 * A * t ^ 2 ≤ A * (Real.pi ^ 2 / 8) := by
      have ht2 : t ^ 2 ≤ (Real.pi / 4) ^ 2 := pow_le_pow_left₀ ht0.le htle 2
      have := mul_le_mul_of_nonneg_left ht2 (by linarith : (0 : ℝ) ≤ 2 * A)
      nlinarith [this, Real.pi_pos]
    have h2 : A * (Real.pi ^ 2 / 8) + B * (Real.pi ^ 3 / 32) ≤ C := by
      have h3 : 0 ≤ B * (Real.pi ^ 3 / 16) := mul_nonneg hB (by positivity)
      rw [hCdef]; linarith
    have htne : t ≠ 0 := ne_of_gt ht0
    have hval : (A + B * ((Real.pi ^ 3 / 64) / t ^ 2)) * (2 * t)
        = 2 * A * t + B * (Real.pi ^ 3 / 32) / t := by
      field_simp [htne]
      ring
    have hmain : 2 * A * t + B * (Real.pi ^ 3 / 32) / t ≤ C * t⁻¹ := by
      rw [show C * t⁻¹ = C / t from (div_eq_mul_inv C t).symm, le_div_iff₀ ht0]
      have hmul : (2 * A * t + B * (Real.pi ^ 3 / 32) / t) * t
          = 2 * A * t ^ 2 + B * (Real.pi ^ 3 / 32) := by
        rw [add_mul, div_mul_cancel₀ _ (ne_of_gt ht0)]
        ring
      rw [hmul]
      linarith
    calc |u θ| ≤ (A + B * ((Real.pi ^ 3 / 64) / t ^ 2)) * (2 * t) := hstep
      _ = 2 * A * t + B * (Real.pi ^ 3 / 32) / t := hval
      _ ≤ C * t⁻¹ := hmain
      _ = C * (Real.pi / 2 - θ)⁻¹ := by rw [htdef]
      _ ≤ C * (θ⁻¹ + (Real.pi / 2 - θ)⁻¹) := by
          refine mul_le_mul_of_nonneg_left ?_ hC
          linarith [hinvθ]

end Lzero1Growth

theorem lzero1SliceGrowth : ∀ (u : ℝ → ℝ),
    (∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo (0 : ℝ) (Real.pi / 2))) →
    MeasureTheory.IntegrableOn
      (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2 * |Work.FTS.EllipticEst.Lzero1 u θ|)
      Work.Spaces.Iθ →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |u θ| ≤ C * (θ⁻¹ + (Real.pi / 2 - θ)⁻¹) := by
  intro u hu hint
  have hu2 : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)) := hu 2
  have hg : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Elliptic.sinCos2 θ * |Work.FTS.EllipticEst.Lzero1 u θ|)
      Work.Spaces.Iθ := by
    simpa only [Work.Elliptic.sinCos2] using hint
  exact Lzero1Growth.growthOfRfunBounds (Lzero1Growth.Rfun_bound_two hu2 hg).1
    (Lzero1Growth.Rfun_bound_two hu2 hg).2

end Work.FTS.EllipticEst.H2W
