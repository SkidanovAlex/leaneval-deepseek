/-
Copyright: work module for the Elgindi finite-time singularity project.

# `lzeroGrowthSlice`: the weighted `L¹` growth of a slice from the growth of `Lzero1 u`

The angular operator `Lzero1 u = -u'' + ∂_θ(tan θ · u) - 6u` is a second-order ODE on
`(0, π/2)` whose coefficients are smooth on the open interval; the endpoint `θ = π/2` is a
regular singular point with indicial exponents `±1` and the endpoint `θ = 0` is an ordinary
point.  The result proved here is the *weighted `L¹`* version of the standard growth bound:
if `sin θ cos²θ · |Lzero1 u|` is integrable on `[0, π/2]` (the angular weight of the `i = 0`
slot of the paper's `H^k` norm) then so is the slice `θ ↦ u θ · sin θ cos²θ`.

Note that `sin θ cos²θ` is *not* the natural weight for a solution of the homogeneous equation
(those grow like `1/t`, `t = π/2 - θ`, and `t · t^{-1} = O(1)`); the point of the statement is
that the very weak hypothesis on `Lzero1 u` already forbids growth worse than `O(1/t)`, so that
`u · sinθcos²θ = O(t) → 0` at the singular endpoint.  Concretely we prove the pointwise bound

  `|u θ| · sinθcos²θ ≤ 2A θ² + 2BK₂ θ`  for `θ ∈ (0, π/4]`,
  `|u θ| · sinθcos²θ ≤ 2A t³ + 2BK₁ t`  for `t = π/2 - θ ∈ (0, π/4]`,

with `A = |u(π/4)|` and `B = |D(π/4)| + 2M`, `M = ∫_0^{π/2} sinθcos²θ |Lzero1 u θ| dθ`, and
`K₁, K₂` the explicit constants of the two kernel estimates below.  Both bounds are integrable,
which gives the claim.

## The proof

Write `y θ = sin 2θ` (the regular solution of the homogeneous equation, `Lzero1 y = 0`), let
`g = Lzero1 u` and put

  `D θ = cos θ · (u θ · y' θ − u' θ · y θ)`  (a Wronskian-type functional).

Two exact identities drive everything:

* `D' θ = cos θ · y θ · g θ = 2 · g θ · sinθcos²θ`, and
* `(u / y)' θ = − D θ / (cos θ · y θ ^ 2)`.

The first says `D` has bounded oscillation: `|D θ| ≤ |D(π/4)| + 2M =: B`.  The second can then
be integrated, because `cos s · sin²(2s)` is an *explicit* function whose reciprocal has the
explicit behaviour `≈ 1/(4(π/2-s)³)` near `π/2` and `≈ 1/(4s²)` near `0`, giving

  `|u θ / y θ| ≤ |u(π/4)| + B ∫_{π/4}^{θ} ds/(cos s sin²2s) ≤ A + B K₁ / t²` (`t = π/2-θ`),
  `|u θ / y θ| ≤ |u(π/4)| + B ∫_{θ}^{π/4} ds/(cos s sin²2s) ≤ A + B K₂ / θ`.

Multiplying by `y θ · sinθcos²θ = 2 sin²θ cos³θ ≤ 2θ²` (resp. `≤ 2t³`) gives the pointwise
bounds above.  No information about the singular solution `LzeroSing` is needed: it is the
*quotient* `u/sin 2θ` that carries the exponent `-1`.

The reference point `θ = π/4` is chosen because `sin(2·π/4) = 1` there.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.H2W.LzeroSolSpan
import Submission.Work.FTS.EllipticEst.H2W.lzeroGrowthKernelLeft
import Submission.Work.FTS.EllipticEst.H2W.lzeroGrowthKernelRight

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

namespace LzeroGrowth

/-! ## The two auxiliary functionals -/

/-- The Wronskian-type functional `D u θ = cos θ · (u θ · (sin 2θ)' - u' θ · sin 2θ)`; its
derivative is `2 · Lzero1 u θ · sinθcos²θ`. -/
def Dfun (u : ℝ → ℝ) : ℝ → ℝ :=
  fun θ => Real.cos θ * (u θ * (2 * Real.cos (2 * θ)) - deriv u θ * Real.sin (2 * θ))

/-- The quotient `R u θ = u θ / sin(2θ)`, whose derivative is `- D u θ /(cos θ · sin²2θ)`. -/
def Rfun (u : ℝ → ℝ) : ℝ → ℝ := fun θ => u θ / Real.sin (2 * θ)

/-- The weighted `L¹`-size `M u = ∫_0^{π/2} sinθcos²θ · |Lzero1 u θ| dθ` of the source. -/
def Mfun (u : ℝ → ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, Work.Elliptic.sinCos2 θ * |Work.FTS.EllipticEst.Lzero1 u θ|

/-- The constant `B u = |D u (π/4)| + 2 M u` bounding the oscillation of `D u`. -/
def Bfun (u : ℝ → ℝ) : ℝ := |Dfun u (Real.pi / 4)| + 2 * Mfun u

/-! ## Elementary facts about the weight and the interval -/

theorem cos_ne_zero {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : Real.cos θ ≠ 0 :=
  ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩)

theorem sin_two_pos {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

theorem continuous_sinCos2 : Continuous Work.Elliptic.sinCos2 := by
  unfold Work.Elliptic.sinCos2; fun_prop

theorem sinCos2_nonneg {s : ℝ} (hs : s ∈ Work.Spaces.Iθ) : 0 ≤ Work.Elliptic.sinCos2 s := by
  rw [Work.Elliptic.sinCos2]
  have h1 : 0 ≤ Real.sin s :=
    Real.sin_nonneg_of_nonneg_of_le_pi hs.1 (by linarith [hs.2, Real.pi_pos])
  positivity

theorem sinCos2_nonneg_of_mem {s : ℝ} (hs : s ∈ Set.Ioo 0 (Real.pi / 2)) :
    0 ≤ Work.Elliptic.sinCos2 s :=
  sinCos2_nonneg ⟨le_of_lt hs.1, le_of_lt hs.2⟩

theorem mem_Iθ_of_mem_Ioo {s : ℝ} (hs : s ∈ Set.Ioo 0 (Real.pi / 2)) : s ∈ Work.Spaces.Iθ :=
  ⟨le_of_lt hs.1, le_of_lt hs.2⟩

theorem Mfun_nonneg (u : ℝ → ℝ) : 0 ≤ Mfun u := by
  rw [Mfun]
  exact setIntegral_nonneg measurableSet_Icc fun s hs =>
    mul_nonneg (sinCos2_nonneg hs) (abs_nonneg _)

theorem Bfun_nonneg (u : ℝ → ℝ) : 0 ≤ Bfun u := by
  rw [Bfun]
  have h1 : 0 ≤ |Dfun u (Real.pi / 4)| := abs_nonneg _
  have h2 : 0 ≤ Mfun u := Mfun_nonneg u
  linarith

/-! ## Differentiability and continuity of the data on the open interval -/

theorem hasDerivAt_u {u : ℝ → ℝ} (hu : ContDiffOn ℝ ⊤ u (Set.Ioo 0 (Real.pi / 2))) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : HasDerivAt u (deriv u θ) θ :=
  ((hu.contDiffAt (isOpen_Ioo.mem_nhds hθ)).differentiableAt (by simp)).hasDerivAt

theorem contDiffAt_deriv_of_contDiffOn {u : ℝ → ℝ} (hu : ContDiffOn ℝ ⊤ u (Set.Ioo 0 (Real.pi / 2)))
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : ContDiffAt ℝ ⊤ (deriv u) θ :=
  (hu.contDiffAt (isOpen_Ioo.mem_nhds hθ)).derivWithin (m := ⊤) (by simp)

theorem continuousOn_deriv1 {u : ℝ → ℝ} (hu : ContDiffOn ℝ ⊤ u (Set.Ioo 0 (Real.pi / 2))) :
    ContinuousOn (deriv u) (Set.Ioo 0 (Real.pi / 2)) :=
  fun θ hθ => (contDiffAt_deriv_of_contDiffOn hu hθ).continuousAt.continuousWithinAt

theorem continuousOn_deriv2 {u : ℝ → ℝ} (hu : ContDiffOn ℝ ⊤ u (Set.Ioo 0 (Real.pi / 2))) :
    ContinuousOn (fun θ => deriv (deriv u) θ) (Set.Ioo 0 (Real.pi / 2)) :=
  fun θ hθ =>
    ((contDiffAt_deriv_of_contDiffOn hu hθ).derivWithin (m := ⊤) (by simp)).continuousAt.continuousWithinAt

/-- `Lzero1 u` is continuous on the open interval. -/
theorem continuousOn_Lzero1 {u : ℝ → ℝ} (hu : ContDiffOn ℝ ⊤ u (Set.Ioo 0 (Real.pi / 2))) :
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
theorem continuousOn_Dfun {u : ℝ → ℝ} (hu : ContDiffOn ℝ ⊤ u (Set.Ioo 0 (Real.pi / 2))) :
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

theorem aestronglyMeasurable_Lzero1 {u : ℝ → ℝ} (hu : ContDiffOn ℝ ⊤ u (Set.Ioo 0 (Real.pi / 2))) :
    AEStronglyMeasurable (Work.FTS.EllipticEst.Lzero1 u)
      (volume.restrict Work.Spaces.Iθ) := by
  have h1 : AEStronglyMeasurable (Work.FTS.EllipticEst.Lzero1 u)
      (volume.restrict (Set.Ioo 0 (Real.pi / 2))) :=
    (continuousOn_Lzero1 hu).aestronglyMeasurable measurableSet_Ioo
  rw [Measure.restrict_congr_set (Ioo_ae_eq_Icc (a := (0 : ℝ)) (b := Real.pi / 2))] at h1
  exact h1

/-! ## Interval integrability of the source term `2 g sinθcos²θ` -/

theorem intervalIntegrable_two_mul {u : ℝ → ℝ} (hu : ContDiffOn ℝ ⊤ u (Set.Ioo 0 (Real.pi / 2)))
    {a b : ℝ} (hsub : Set.uIcc a b ⊆ Set.Ioo 0 (Real.pi / 2)) :
    IntervalIntegrable
      (fun s : ℝ => 2 * Work.FTS.EllipticEst.Lzero1 u s * Work.Elliptic.sinCos2 s)
      volume a b := by
  have h1 : ContinuousOn
      (fun s : ℝ => 2 * Work.FTS.EllipticEst.Lzero1 u s * Work.Elliptic.sinCos2 s)
      (Set.Ioo 0 (Real.pi / 2)) :=
    ((continuousOn_Lzero1 hu).const_mul 2).mul continuous_sinCos2.continuousOn
  exact (h1.mono hsub).intervalIntegrable

theorem integrableOn_two_mul {u : ℝ → ℝ} (hu : ContDiffOn ℝ ⊤ u (Set.Ioo 0 (Real.pi / 2)))
    (hg : IntegrableOn
      (fun θ : ℝ => Work.Elliptic.sinCos2 θ * |Work.FTS.EllipticEst.Lzero1 u θ|)
      Work.Spaces.Iθ) :
    IntegrableOn
      (fun s : ℝ => 2 * Work.FTS.EllipticEst.Lzero1 u s * Work.Elliptic.sinCos2 s)
      Work.Spaces.Iθ := by
  have hmeas : AEStronglyMeasurable
      (fun s : ℝ => 2 * Work.FTS.EllipticEst.Lzero1 u s * Work.Elliptic.sinCos2 s)
      (volume.restrict Work.Spaces.Iθ) := by
    have h2 : AEStronglyMeasurable (fun s : ℝ => 2 * Work.FTS.EllipticEst.Lzero1 u s)
        (volume.restrict Work.Spaces.Iθ) := (aestronglyMeasurable_Lzero1 hu).const_mul 2
    have h3 : AEStronglyMeasurable (Work.Elliptic.sinCos2) (volume.restrict Work.Spaces.Iθ) :=
      continuous_sinCos2.measurable.aestronglyMeasurable
    rw [show (fun s : ℝ => 2 * Work.FTS.EllipticEst.Lzero1 u s * Work.Elliptic.sinCos2 s)
        = (fun s : ℝ => 2 * Work.FTS.EllipticEst.Lzero1 u s) * Work.Elliptic.sinCos2 from rfl]
    exact h2.mul h3
  refine Integrable.mono'
    (g := fun s : ℝ => 2 * (Work.Elliptic.sinCos2 s * |Work.FTS.EllipticEst.Lzero1 u s|))
    (hg.const_mul 2) hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
  refine le_of_eq ?_
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (sinCos2_nonneg hs),
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  ring

/-! ## Trigonometry and the two exact derivative identities -/

theorem hasDerivAt_sin_two (θ : ℝ) :
    HasDerivAt (fun x : ℝ => Real.sin (2 * x)) (2 * Real.cos (2 * θ)) θ := by
  have h2 : HasDerivAt (fun x : ℝ => (2 : ℝ) * x) 2 θ := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id θ).const_mul 2
  exact ((Real.hasDerivAt_sin (2 * θ)).comp θ h2).congr_deriv (by ring)

theorem hasDerivAt_cos_two (θ : ℝ) :
    HasDerivAt (fun x : ℝ => Real.cos (2 * x)) (-2 * Real.sin (2 * θ)) θ := by
  have h2 : HasDerivAt (fun x : ℝ => (2 : ℝ) * x) 2 θ := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id θ).const_mul 2
  exact ((Real.hasDerivAt_cos (2 * θ)).comp θ h2).congr_deriv (by ring)

theorem hasDerivAt_deriv_sin_two (θ : ℝ) :
    HasDerivAt (deriv (fun x : ℝ => Real.sin (2 * x))) (-4 * Real.sin (2 * θ)) θ := by
  have hfun : deriv (fun x : ℝ => Real.sin (2 * x)) = fun x : ℝ => 2 * Real.cos (2 * x) := by
    funext x; exact (hasDerivAt_sin_two x).deriv
  rw [hfun]
  exact ((hasDerivAt_cos_two θ).const_mul 2).congr_deriv (by ring)

/-- `sin 2θ` solves the homogeneous equation. -/
theorem Lzero1_sin_two {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.FTS.EllipticEst.Lzero1 (fun θ => Real.sin (2 * θ)) θ = 0 := by
  have hc := cos_ne_zero hθ
  have hdy : deriv (fun x : ℝ => Real.sin (2 * x)) θ = 2 * Real.cos (2 * θ) :=
    (hasDerivAt_sin_two θ).deriv
  have htan : HasDerivAt (fun t => Real.tan t * Real.sin (2 * t))
      ((1 / Real.cos θ ^ 2) * Real.sin (2 * θ) + Real.tan θ * (2 * Real.cos (2 * θ))) θ :=
    (Real.hasDerivAt_tan hc).mul (hasDerivAt_sin_two θ)
  have hd2 : deriv (deriv (fun x : ℝ => Real.sin (2 * x))) θ = -4 * Real.sin (2 * θ) :=
    (hasDerivAt_deriv_sin_two θ).deriv
  simp only [Work.FTS.EllipticEst.Lzero1]
  rw [hd2, htan.deriv]
  rw [Real.sin_two_mul, Real.cos_two_mul, Real.tan_eq_sin_div_cos]
  field_simp
  ring

/-- The normal form of the equation `Lzero1 u = g` on the open interval. -/
theorem u_ode {u : ℝ → ℝ} (hu : ContDiffOn ℝ ⊤ u (Set.Ioo 0 (Real.pi / 2))) {θ : ℝ}
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
theorem Dfun_hasDerivAt {u : ℝ → ℝ} (hu : ContDiffOn ℝ ⊤ u (Set.Ioo 0 (Real.pi / 2))) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    HasDerivAt (Dfun u) (2 * Work.FTS.EllipticEst.Lzero1 u θ * Work.Elliptic.sinCos2 θ) θ := by
  have hc := cos_ne_zero hθ
  have hdu : HasDerivAt u (deriv u θ) θ := hasDerivAt_u hu hθ
  have hd2u : HasDerivAt (deriv u) (deriv (deriv u) θ) θ :=
    (contDiffAt_deriv_of_contDiffOn hu hθ).differentiableAt (by simp) |>.hasDerivAt
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
theorem Rfun_hasDerivAt {u : ℝ → ℝ} (hu : ContDiffOn ℝ ⊤ u (Set.Ioo 0 (Real.pi / 2))) {θ : ℝ}
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
theorem Dfun_bound {u : ℝ → ℝ} (hu : ContDiffOn ℝ ⊤ u (Set.Ioo 0 (Real.pi / 2)))
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

theorem continuousOn_Rderiv {u : ℝ → ℝ} (hu : ContDiffOn ℝ ⊤ u (Set.Ioo 0 (Real.pi / 2))) :
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
theorem Rfun_bound_right {u : ℝ → ℝ} (hu : ContDiffOn ℝ ⊤ u (Set.Ioo 0 (Real.pi / 2)))
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
theorem Rfun_bound_left {u : ℝ → ℝ} (hu : ContDiffOn ℝ ⊤ u (Set.Ioo 0 (Real.pi / 2)))
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

/-! ## The pointwise bounds on the weight -/

theorem sin_two_mul_sinCos2_le_left {θ : ℝ} (hθ : θ ∈ Set.Icc 0 (Real.pi / 4)) :
    Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ ≤ 2 * θ ^ 2 := by
  have h0 : 0 ≤ θ := hθ.1
  have hsin : Real.sin (2 * θ) ≤ 2 * θ := Real.sin_le (by linarith)
  have hsinθ : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_nonneg_of_le_pi h0 (by linarith [hθ.2, Real.pi_pos])
  have hcos2 : Real.cos θ ^ 2 ≤ 1 := by
    have := Real.cos_sq_le_one θ
    linarith
  have hφ : Work.Elliptic.sinCos2 θ ≤ θ := by
    rw [Work.Elliptic.sinCos2]
    calc Real.sin θ * Real.cos θ ^ 2 ≤ Real.sin θ * 1 :=
          mul_le_mul_of_nonneg_left hcos2 hsinθ
      _ = Real.sin θ := mul_one _
      _ ≤ θ := Real.sin_le h0
  have hφ0 : 0 ≤ Work.Elliptic.sinCos2 θ := by
    rw [Work.Elliptic.sinCos2]
    exact mul_nonneg hsinθ (sq_nonneg _)
  calc Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ
      ≤ (2 * θ) * Work.Elliptic.sinCos2 θ := mul_le_mul_of_nonneg_right hsin hφ0
    _ ≤ (2 * θ) * θ := mul_le_mul_of_nonneg_left hφ (by linarith)
    _ = 2 * θ ^ 2 := by ring

theorem sin_two_mul_sinCos2_le_right {θ : ℝ} (hθ : θ ∈ Set.Ico (Real.pi / 4) (Real.pi / 2)) :
    Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ ≤ 2 * (Real.pi / 2 - θ) ^ 3 := by
  set t := Real.pi / 2 - θ with ht
  have ht0 : 0 < t := by rw [ht]; linarith [hθ.2]
  have hsinθ : Real.sin θ ≤ 1 := Real.sin_le_one θ
  have hsinθ0 : 0 ≤ Real.sin θ := by
    refine Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1, Real.pi_pos]) ?_
    linarith [hθ.2, Real.pi_pos]
  have hcos : Real.cos θ = Real.sin t := by rw [ht, Real.sin_pi_div_two_sub]
  have hcos0 : 0 ≤ Real.cos θ := le_of_lt (Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩)
  have hcost : Real.cos θ ≤ t := by
    rw [hcos]
    exact Real.sin_le ht0.le
  have hsin2 : Real.sin (2 * θ) = Real.sin (2 * t) := by
    rw [show θ = Real.pi / 2 - t by rw [ht]; ring,
      show 2 * (Real.pi / 2 - t) = Real.pi - 2 * t by ring, Real.sin_pi_sub]
  have hsin2le : Real.sin (2 * t) ≤ 2 * t := Real.sin_le (by linarith)
  have hφ : Work.Elliptic.sinCos2 θ ≤ t ^ 2 := by
    rw [Work.Elliptic.sinCos2]
    calc Real.sin θ * Real.cos θ ^ 2 ≤ 1 * Real.cos θ ^ 2 :=
          mul_le_mul_of_nonneg_right hsinθ (pow_nonneg hcos0 2)
      _ = Real.cos θ ^ 2 := one_mul _
      _ ≤ t ^ 2 := by
          have h := mul_self_le_mul_self hcos0 hcost
          simpa only [sq] using h
  have hφ0 : 0 ≤ Work.Elliptic.sinCos2 θ := by
    rw [Work.Elliptic.sinCos2]
    exact mul_nonneg hsinθ0 (pow_nonneg hcos0 2)
  calc Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ
      ≤ (2 * t) * t ^ 2 := by
        refine mul_le_mul ?_ hφ hφ0 (by positivity)
        rw [hsin2]; exact hsin2le
    _ = 2 * t ^ 3 := by ring

/-- The exact factorisation `u θ · sinθcos²θ = (u θ / sin 2θ) · (sin 2θ · sinθcos²θ)`. -/
theorem abs_mul_sinCos2_eq (u : ℝ → ℝ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    |u θ * Work.Elliptic.sinCos2 θ|
      = |Rfun u θ| * (Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ) := by
  have hs := sin_two_pos hθ
  have hφ := sinCos2_nonneg_of_mem hθ
  have h1 : |Rfun u θ| * Real.sin (2 * θ) = |u θ| := by
    rw [Rfun, abs_div, abs_of_pos hs, div_mul_cancel₀]
    exact ne_of_gt hs
  rw [abs_mul, abs_of_nonneg hφ, ← h1]
  ring

/-! ## The two integrability statements on the half-intervals -/

theorem integrableOn_left {u : ℝ → ℝ} (hu : ContDiffOn ℝ ⊤ u (Set.Ioo 0 (Real.pi / 2)))
    (hg : IntegrableOn
      (fun θ : ℝ => Work.Elliptic.sinCos2 θ * |Work.FTS.EllipticEst.Lzero1 u θ|)
      Work.Spaces.Iθ) :
    IntegrableOn (fun θ : ℝ => u θ * Work.Elliptic.sinCos2 θ)
      (Set.Icc 0 (Real.pi / 4)) := by
  have hB0 : 0 ≤ Bfun u := Bfun_nonneg u
  have hK : 0 ≤ Real.pi ^ 2 / 8 := by positivity
  have hdom : IntegrableOn
      (fun θ : ℝ => 2 * |Rfun u (Real.pi / 4)| * θ ^ 2 + 2 * Bfun u * (Real.pi ^ 2 / 8) * θ)
      (Set.Icc 0 (Real.pi / 4)) := by
    have hc : Continuous fun θ : ℝ =>
        2 * |Rfun u (Real.pi / 4)| * θ ^ 2 + 2 * Bfun u * (Real.pi ^ 2 / 8) * θ := by fun_prop
    exact hc.continuousOn.integrableOn_compact isCompact_Icc
  refine Integrable.mono' hdom ?_ ?_
  · have hcont : ContinuousOn (fun θ : ℝ => u θ * Work.Elliptic.sinCos2 θ)
        (Set.Ioc 0 (Real.pi / 4)) :=
      (hu.continuousOn.mono (fun x hx => ⟨hx.1, by linarith [hx.2, Real.pi_pos]⟩)).mul
        continuous_sinCos2.continuousOn
    have h1 : AEStronglyMeasurable (fun θ : ℝ => u θ * Work.Elliptic.sinCos2 θ)
        (volume.restrict (Set.Ioc 0 (Real.pi / 4))) :=
      hcont.aestronglyMeasurable measurableSet_Ioc
    rwa [Measure.restrict_congr_set (Ioc_ae_eq_Icc (a := (0 : ℝ)) (b := Real.pi / 4)).symm]
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    rcases hθ.1.lt_or_eq with hlt | heq
    · have hθi : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hlt, by linarith [hθ.2, Real.pi_pos]⟩
      have hθl : θ ∈ Set.Ioc 0 (Real.pi / 4) := ⟨hlt, hθ.2⟩
      have hR := Rfun_bound_left hu hg hθl
      have hI := lzeroGrowthKernelLeft (θ := θ) hθl
      have hI' : θ * (∫ s in θ..(Real.pi / 4),
            1 / (Real.cos s * (Real.sin (2 * s)) ^ 2)) ≤ Real.pi ^ 2 / 8 := by
        have h := mul_le_mul_of_nonneg_left hI hlt.le
        rwa [show θ * ((Real.pi ^ 2 / 8) / θ) = Real.pi ^ 2 / 8 by
          rw [mul_comm, div_mul_cancel₀ _ (ne_of_gt hlt)]] at h
      have hR2 : θ * |Rfun u θ|
          ≤ θ * |Rfun u (Real.pi / 4)| + Bfun u * (Real.pi ^ 2 / 8) := by
        have h := mul_le_mul_of_nonneg_left hR hlt.le
        have hsplit : θ * (|Rfun u (Real.pi / 4)| + Bfun u * ∫ s in θ..(Real.pi / 4),
              1 / (Real.cos s * (Real.sin (2 * s)) ^ 2))
            = θ * |Rfun u (Real.pi / 4)|
              + Bfun u * (θ * (∫ s in θ..(Real.pi / 4),
                  1 / (Real.cos s * (Real.sin (2 * s)) ^ 2))) := by ring
        rw [hsplit] at h
        have h2 : Bfun u * (θ * (∫ s in θ..(Real.pi / 4),
              1 / (Real.cos s * (Real.sin (2 * s)) ^ 2))) ≤ Bfun u * (Real.pi ^ 2 / 8) :=
          mul_le_mul_of_nonneg_left hI' hB0
        linarith
      have hφb := sin_two_mul_sinCos2_le_left ⟨hθ.1, hθ.2⟩
      have hφ0 : 0 ≤ Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ :=
        mul_nonneg (le_of_lt (sin_two_pos hθi)) (sinCos2_nonneg_of_mem hθi)
      rw [Real.norm_eq_abs, abs_mul_sinCos2_eq u hθi]
      have hkey : θ * (|Rfun u θ| * (Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ))
          ≤ θ * (2 * |Rfun u (Real.pi / 4)| * θ ^ 2
              + 2 * Bfun u * (Real.pi ^ 2 / 8) * θ) := by
        calc θ * (|Rfun u θ| * (Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ))
            = θ * |Rfun u θ| * (Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ) := by ring
          _ ≤ (θ * |Rfun u (Real.pi / 4)| + Bfun u * (Real.pi ^ 2 / 8)) * (2 * θ ^ 2) :=
              mul_le_mul hR2 hφb hφ0 (by positivity)
          _ = θ * (2 * |Rfun u (Real.pi / 4)| * θ ^ 2
                + 2 * Bfun u * (Real.pi ^ 2 / 8) * θ) := by ring
      exact le_of_mul_le_mul_left hkey hlt
    · subst heq
      simp [Work.Elliptic.sinCos2]

theorem integrableOn_right {u : ℝ → ℝ} (hu : ContDiffOn ℝ ⊤ u (Set.Ioo 0 (Real.pi / 2)))
    (hg : IntegrableOn
      (fun θ : ℝ => Work.Elliptic.sinCos2 θ * |Work.FTS.EllipticEst.Lzero1 u θ|)
      Work.Spaces.Iθ) :
    IntegrableOn (fun θ : ℝ => u θ * Work.Elliptic.sinCos2 θ)
      (Set.Icc (Real.pi / 4) (Real.pi / 2)) := by
  have hB0 : 0 ≤ Bfun u := Bfun_nonneg u
  have hK : 0 ≤ Real.pi ^ 3 / 64 := by positivity
  have hdom : IntegrableOn
      (fun θ : ℝ => 2 * |Rfun u (Real.pi / 4)| * (Real.pi / 2 - θ) ^ 3
        + 2 * Bfun u * (Real.pi ^ 3 / 64) * (Real.pi / 2 - θ))
      (Set.Icc (Real.pi / 4) (Real.pi / 2)) := by
    have hc : Continuous fun θ : ℝ =>
        2 * |Rfun u (Real.pi / 4)| * (Real.pi / 2 - θ) ^ 3
          + 2 * Bfun u * (Real.pi ^ 3 / 64) * (Real.pi / 2 - θ) := by fun_prop
    exact hc.continuousOn.integrableOn_compact isCompact_Icc
  refine Integrable.mono' hdom ?_ ?_
  · have hcont : ContinuousOn (fun θ : ℝ => u θ * Work.Elliptic.sinCos2 θ)
        (Set.Ico (Real.pi / 4) (Real.pi / 2)) :=
      (hu.continuousOn.mono (fun x hx => ⟨by linarith [hx.1, Real.pi_pos], hx.2⟩)).mul
        continuous_sinCos2.continuousOn
    have h1 : AEStronglyMeasurable (fun θ : ℝ => u θ * Work.Elliptic.sinCos2 θ)
        (volume.restrict (Set.Ico (Real.pi / 4) (Real.pi / 2))) :=
      hcont.aestronglyMeasurable measurableSet_Ico
    rwa [Measure.restrict_congr_set (Ico_ae_eq_Icc (a := Real.pi / 4) (b := Real.pi / 2)).symm]
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    rcases hθ.2.lt_or_eq with hlt | heq
    · have hθi : θ ∈ Set.Ioo 0 (Real.pi / 2) :=
        ⟨by linarith [hθ.1, Real.pi_pos], hlt⟩
      have hθr : θ ∈ Set.Ico (Real.pi / 4) (Real.pi / 2) := ⟨hθ.1, hlt⟩
      have ht0 : 0 < Real.pi / 2 - θ := by linarith
      have hR := Rfun_bound_right hu hg hθr
      have hI := lzeroGrowthKernelRight (θ := θ) hθr
      have hI' : (Real.pi / 2 - θ) ^ 2 * (∫ s in (Real.pi / 4)..θ,
            1 / (Real.cos s * (Real.sin (2 * s)) ^ 2)) ≤ Real.pi ^ 3 / 64 := by
        have h := mul_le_mul_of_nonneg_left hI (sq_nonneg (Real.pi / 2 - θ))
        rwa [show (Real.pi / 2 - θ) ^ 2 * ((Real.pi ^ 3 / 64) / (Real.pi / 2 - θ) ^ 2)
              = Real.pi ^ 3 / 64 by
          rw [mul_comm, div_mul_cancel₀ _ (pow_ne_zero 2 (ne_of_gt ht0))]] at h
      have hR2 : (Real.pi / 2 - θ) ^ 2 * |Rfun u θ|
          ≤ (Real.pi / 2 - θ) ^ 2 * |Rfun u (Real.pi / 4)| + Bfun u * (Real.pi ^ 3 / 64) := by
        have h := mul_le_mul_of_nonneg_left hR (sq_nonneg (Real.pi / 2 - θ))
        have hsplit : (Real.pi / 2 - θ) ^ 2 *
              (|Rfun u (Real.pi / 4)| + Bfun u * ∫ s in (Real.pi / 4)..θ,
                1 / (Real.cos s * (Real.sin (2 * s)) ^ 2))
            = (Real.pi / 2 - θ) ^ 2 * |Rfun u (Real.pi / 4)|
              + Bfun u * ((Real.pi / 2 - θ) ^ 2 * (∫ s in (Real.pi / 4)..θ,
                  1 / (Real.cos s * (Real.sin (2 * s)) ^ 2))) := by ring
        rw [hsplit] at h
        have h2 : Bfun u * ((Real.pi / 2 - θ) ^ 2 * (∫ s in (Real.pi / 4)..θ,
              1 / (Real.cos s * (Real.sin (2 * s)) ^ 2))) ≤ Bfun u * (Real.pi ^ 3 / 64) :=
          mul_le_mul_of_nonneg_left hI' hB0
        linarith
      have hφb := sin_two_mul_sinCos2_le_right hθr
      have hφ0 : 0 ≤ Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ :=
        mul_nonneg (le_of_lt (sin_two_pos hθi)) (sinCos2_nonneg_of_mem hθi)
      rw [Real.norm_eq_abs, abs_mul_sinCos2_eq u hθi]
      have hkey : (Real.pi / 2 - θ) ^ 2
            * (|Rfun u θ| * (Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ))
          ≤ (Real.pi / 2 - θ) ^ 2
            * (2 * |Rfun u (Real.pi / 4)| * (Real.pi / 2 - θ) ^ 3
                + 2 * Bfun u * (Real.pi ^ 3 / 64) * (Real.pi / 2 - θ)) := by
        calc (Real.pi / 2 - θ) ^ 2
              * (|Rfun u θ| * (Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ))
            = (Real.pi / 2 - θ) ^ 2 * |Rfun u θ|
                * (Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ) := by ring
          _ ≤ ((Real.pi / 2 - θ) ^ 2 * |Rfun u (Real.pi / 4)| + Bfun u * (Real.pi ^ 3 / 64))
                * (2 * (Real.pi / 2 - θ) ^ 3) :=
              mul_le_mul hR2 hφb hφ0 (by positivity)
          _ = (Real.pi / 2 - θ) ^ 2
                * (2 * |Rfun u (Real.pi / 4)| * (Real.pi / 2 - θ) ^ 3
                    + 2 * Bfun u * (Real.pi ^ 3 / 64) * (Real.pi / 2 - θ)) := by ring
      exact le_of_mul_le_mul_left hkey (pow_pos ht0 2)
    · subst heq
      simp [Work.Elliptic.sinCos2]

end LzeroGrowth

open LzeroGrowth in
/-- **The weighted `L¹` growth of a slice.**  If `sinθcos²θ · |Lzero1 u|` is integrable on
`[0, π/2]`, then so is `u · sinθcos²θ`. -/
theorem lzeroGrowthSlice (u : ℝ → ℝ) (hu : ContDiffOn ℝ ⊤ u (Set.Ioo 0 (Real.pi / 2)))
    (hint : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2 * |Work.FTS.EllipticEst.Lzero1 u θ|)
      Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => u θ * Work.Elliptic.sinCos2 θ)
      Work.Spaces.Iθ := by
  have hg : IntegrableOn
      (fun θ : ℝ => Work.Elliptic.sinCos2 θ * |Work.FTS.EllipticEst.Lzero1 u θ|)
      Work.Spaces.Iθ := by
    simpa only [Work.Elliptic.sinCos2] using hint
  have h3 := (integrableOn_left hu hg).union (integrableOn_right hu hg)
  rw [Set.Icc_union_Icc_eq_Icc (by positivity : (0 : ℝ) ≤ Real.pi / 4)
    (by linarith [Real.pi_pos])] at h3
  exact h3

end Work.FTS.EllipticEst.H2W
