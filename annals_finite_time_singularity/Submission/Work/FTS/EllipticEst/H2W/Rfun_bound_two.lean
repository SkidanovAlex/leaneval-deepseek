/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Rfun_bound_two`: the two growth bounds for `R u = u / sin 2θ` at regularity `C²`

`Submission/Work/FTS/EllipticEst/H2W/lzeroGrowthSlice.lean` proves the two growth bounds
for `LzeroGrowth.Rfun u` under the *analytic* hypothesis `ContDiffOn ℝ ⊤ u (Ioo 0 (π/2))`.
The present file records the same two bounds under the honest hypothesis
`ContDiffOn ℝ 2 u (Ioo 0 (π/2))` that the consumer needs.

The whole chain used in `lzeroGrowthSlice.lean` only ever asks for

* `u` continuous,
* `deriv u` continuous (and `HasDerivAt u (deriv u θ) θ`),
* `deriv (deriv u)` continuous (and `HasDerivAt (deriv u) (deriv (deriv u) θ) θ`),

all on the open interval, i.e. exactly the content of `ContDiffOn ℝ 2 u`.  So we re-run the
chain in the namespace `LzeroGrowthC2` with `⊤` replaced by `2`; the bodies of the proofs are
those of `lzeroGrowthSlice.lean`, with the differentiability facts replaced by their
`C²` versions (`ContDiffOn.contDiffAt.differentiableAt` and applications of
`ContDiffAt.derivWithin`).

The conclusion is
`|R u θ| ≤ |R u (π/4)| + B u · ∫_θ^{π/4} ds/(cos s · sin²2s)` for `θ ∈ (0, π/4]` and the
mirror statement for `θ ∈ [π/4, π/2)`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.CompletePartialOrder
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

/-! The `C²` version of the chain of `lzeroGrowthSlice.lean`. -/
namespace LzeroGrowthC2

open LzeroGrowth

/-! ## Differentiability and continuity of the data on the open interval, at regularity `C²` -/

theorem hasDerivAt_u {u : ℝ → ℝ} (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2))) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : HasDerivAt u (deriv u θ) θ :=
  ((hu.contDiffAt (isOpen_Ioo.mem_nhds hθ)).differentiableAt (by norm_num)).hasDerivAt

theorem contDiffAt_deriv_of_contDiffOn {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : ContDiffAt ℝ 1 (deriv u) θ :=
  (hu.contDiffAt (isOpen_Ioo.mem_nhds hθ)).derivWithin (m := 1) (by norm_num)

theorem hasDerivAt_deriv_u {u : ℝ → ℝ} (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    HasDerivAt (deriv u) (deriv (deriv u) θ) θ :=
  ((contDiffAt_deriv_of_contDiffOn hu hθ).differentiableAt (by norm_num)).hasDerivAt

theorem continuousOn_deriv1 {u : ℝ → ℝ} (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2))) :
    ContinuousOn (deriv u) (Set.Ioo 0 (Real.pi / 2)) :=
  fun θ hθ => (contDiffAt_deriv_of_contDiffOn hu hθ).continuousAt.continuousWithinAt

theorem continuousOn_deriv2 {u : ℝ → ℝ} (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2))) :
    ContinuousOn (fun θ => deriv (deriv u) θ) (Set.Ioo 0 (Real.pi / 2)) :=
  fun θ hθ =>
    ((contDiffAt_deriv_of_contDiffOn hu hθ).derivWithin (m := 0) (by norm_num)).continuousAt.continuousWithinAt

/-- `Lzero1 u` is continuous on the open interval. -/
theorem continuousOn_Lzero1 {u : ℝ → ℝ} (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2))) :
    ContinuousOn (Work.FTS.EllipticEst.Lzero1 u) (Set.Ioo 0 (Real.pi / 2)) := by
  have hc0 : ContinuousOn u (Set.Ioo 0 (Real.pi / 2)) := hu.continuousOn
  have hc1 : ContinuousOn (deriv u) (Set.Ioo 0 (Real.pi / 2)) := continuousOn_deriv1 hu
  have hc2 : ContinuousOn (fun θ => deriv (deriv u) θ) (Set.Ioo 0 (Real.pi / 2)) :=
    continuousOn_deriv2 hu
  have hm : ContinuousOn (fun θ => deriv (fun t => Real.tan t * u t) θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
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
  refine ContinuousOn.congr (f := fun θ =>
    -(deriv (deriv u) θ) + deriv (fun t => Real.tan t * u t) θ - 6 * u θ) ?_ ?_
  · exact ((hc2.neg).add hm).sub (hc0.const_mul 6)
  · intro θ hθ
    simp only [Work.FTS.EllipticEst.Lzero1]

/-- `Dfun u` is continuous on the open interval. -/
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

/-! ## Interval integrability of the source term `2 g sinθcos²θ` -/

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

/-! ## The two exact derivative identities -/

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

/-- **`D` has bounded oscillation.**  `|D u θ| ≤ B u = |D u (π/4)| + 2 M u` on the open
interval. -/
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
      _ = ∫ s in Set.Ioc a b, 2 * (Work.Elliptic.sinCos2 s * |Work.FTS.EllipticEst.Lzero1 u s|) :=
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

end LzeroGrowthC2

/-- **The two growth bounds for `R u = u / sin 2θ`, at regularity `C²`.**  If
`sinθcos²θ · |Lzero1 u|` is integrable on `Iθ` and `u` is `C²` on `(0, π/2)`, then
`|R u|` is bounded by its value at `θ = π/4` plus `B u` times the explicit kernel
`1/(cos s · sin²2s)` integrated from `θ` to `π/4` (for `θ ≤ π/4`) respectively from `π/4`
to `θ` (for `θ ≥ π/4`). -/
theorem Rfun_bound_two {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (hg : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Elliptic.sinCos2 θ * |Work.FTS.EllipticEst.Lzero1 u θ|)
      Work.Spaces.Iθ) :
    (∀ θ ∈ Set.Ioc (0 : ℝ) (Real.pi / 4),
        |Work.FTS.EllipticEst.H2W.LzeroGrowth.Rfun u θ|
          ≤ |Work.FTS.EllipticEst.H2W.LzeroGrowth.Rfun u (Real.pi / 4)|
            + Work.FTS.EllipticEst.H2W.LzeroGrowth.Bfun u
              * ∫ s in θ..(Real.pi / 4), 1 / (Real.cos s * (Real.sin (2 * s)) ^ 2))
    ∧ (∀ θ ∈ Set.Ico (Real.pi / 4) (Real.pi / 2),
        |Work.FTS.EllipticEst.H2W.LzeroGrowth.Rfun u θ|
          ≤ |Work.FTS.EllipticEst.H2W.LzeroGrowth.Rfun u (Real.pi / 4)|
            + Work.FTS.EllipticEst.H2W.LzeroGrowth.Bfun u
              * ∫ s in (Real.pi / 4)..θ, 1 / (Real.cos s * (Real.sin (2 * s)) ^ 2)) :=
  ⟨fun θ hθ => LzeroGrowthC2.Rfun_bound_left hu hg hθ,
   fun θ hθ => LzeroGrowthC2.Rfun_bound_right hu hg hθ⟩

end Work.FTS.EllipticEst.H2W
