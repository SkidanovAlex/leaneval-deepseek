/-
Copyright: work module for the Elgindi finite-time singularity project.

`htPP` is the antiderivative of the pointwise deficit `htEE` of the integration by parts in
`Work.Elliptic.hardy_two`:

  `deriv (htPP f) θ = htEE f θ`  for `θ ∈ (0, π/2)`, `f` of class `C²` on `[0, π/2]`.

Writing `u = f / sin 2θ`, `s = sin 2θ`, `c = cos 2θ`, one has
`f'' = s u'' + 4 c u' - 4 s u` (relation `deriv_deriv_f_eq`), whence the pointwise identity

  `10 (f'')² - (u')² - htNN = (40 s c u'² - 80 s² u u')'`

whose right hand side is `deriv (htPP f)`.  The derivative of the right hand side is computed
generically in `htPP_hasDerivAt_gen`, and the identification with `htEE` is the finite algebra of
`htPP_deriv_algebra`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.GDelta.MetrizableSpace
import Submission.Work.Elliptic.HardyTwoDefs
import Submission.Work.Elliptic.htU_contDiffAt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Elliptic

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- Change the function of a `HasDerivAt` statement by a pointwise equality. -/
lemma ht_hasDerivAt_congr {f g : ℝ → ℝ} {f' x : ℝ} (h : HasDerivAt f f' x)
    (hfg : ∀ y, g y = f y) : HasDerivAt g f' x :=
  h.congr_of_eventuallyEq (Filter.Eventually.of_forall hfg)

/-- `θ ↦ sin (2θ)` has derivative `2 cos (2θ)`. -/
lemma ht_sin_two_hasDerivAt (θ : ℝ) :
    HasDerivAt (fun x : ℝ => Real.sin (2 * x)) (2 * Real.cos (2 * θ)) θ := by
  have h : HasDerivAt (fun x : ℝ => Real.sin (2 * x)) (Real.cos (2 * θ) * 2) θ := by
    simpa [Function.comp_def, mul_one] using
      (Real.hasDerivAt_sin (2 * θ)).comp θ ((hasDerivAt_id θ).const_mul 2)
  exact h.congr_deriv (by ring)

/-- `θ ↦ cos (2θ)` has derivative `-2 sin (2θ)`. -/
lemma ht_cos_two_hasDerivAt (θ : ℝ) :
    HasDerivAt (fun x : ℝ => Real.cos (2 * x)) (-2 * Real.sin (2 * θ)) θ := by
  have h : HasDerivAt (fun x : ℝ => Real.cos (2 * x)) ((-Real.sin (2 * θ)) * 2) θ := by
    simpa [Function.comp_def, mul_one] using
      (Real.hasDerivAt_cos (2 * θ)).comp θ ((hasDerivAt_id θ).const_mul 2)
  exact h.congr_deriv (by ring)

/-- Derivative of `x ↦ 40 sin(2x) cos(2x) (u' x)² - 80 sin²(2x) u x u' x`, i.e. of `htPP u`,
in terms of `u`, `u' = deriv u` and the data `u θ`, `u' θ = a`, `u'' θ = b`. -/
lemma htPP_hasDerivAt_gen (u : ℝ → ℝ) (θ a b : ℝ)
    (hu : HasDerivAt u a θ) (hd : HasDerivAt (deriv u) b θ) :
    HasDerivAt (fun x : ℝ => 40 * Real.sin (2 * x) * Real.cos (2 * x) * (deriv u x) ^ 2
        - 80 * (Real.sin (2 * x)) ^ 2 * u x * deriv u x)
      (80 * ((Real.cos (2 * θ)) ^ 2 - 2 * (Real.sin (2 * θ)) ^ 2) * a ^ 2
        + 80 * Real.sin (2 * θ) * Real.cos (2 * θ) * a * b
        - 320 * Real.sin (2 * θ) * Real.cos (2 * θ) * u θ * a
        - 80 * (Real.sin (2 * θ)) ^ 2 * u θ * b) θ := by
  have hda : deriv u θ = a := hu.deriv
  have hA : HasDerivAt (fun x : ℝ => 40 * Real.sin (2 * x) * Real.cos (2 * x))
      (80 * ((Real.cos (2 * θ)) ^ 2 - (Real.sin (2 * θ)) ^ 2)) θ := by
    have h0 := ((ht_sin_two_hasDerivAt θ).mul (ht_cos_two_hasDerivAt θ)).const_mul 40
    refine ht_hasDerivAt_congr (h0.congr_deriv ?_) (fun y => ?_)
    · ring
    · simp only [Pi.mul_apply]; try ring
  have hB : HasDerivAt (fun x : ℝ => (deriv u x) ^ 2) (2 * a * b) θ := by
    have h0 := hd.pow 2
    refine ht_hasDerivAt_congr (h0.congr_deriv ?_) (fun y => ?_)
    · rw [hda]; ring_nf
    · simp only [Pi.pow_apply]
  have hP1 : HasDerivAt
      (fun x : ℝ => 40 * Real.sin (2 * x) * Real.cos (2 * x) * (deriv u x) ^ 2)
      (80 * ((Real.cos (2 * θ)) ^ 2 - (Real.sin (2 * θ)) ^ 2) * a ^ 2
        + 40 * Real.sin (2 * θ) * Real.cos (2 * θ) * (2 * a * b)) θ := by
    have h0 := hA.mul hB
    refine ht_hasDerivAt_congr (h0.congr_deriv ?_) (fun y => ?_)
    · rw [hda]; try ring
    · simp only [Pi.mul_apply]; try ring
  have hC : HasDerivAt (fun x : ℝ => 80 * (Real.sin (2 * x)) ^ 2)
      (320 * Real.sin (2 * θ) * Real.cos (2 * θ)) θ := by
    have h0 := ((ht_sin_two_hasDerivAt θ).pow 2).const_mul 80
    refine ht_hasDerivAt_congr (h0.congr_deriv ?_) (fun y => ?_)
    · ring_nf
    · simp only [Pi.pow_apply]
  have hD : HasDerivAt (fun x : ℝ => u x * deriv u x) (a * a + u θ * b) θ := by
    have h0 := hu.mul hd
    refine ht_hasDerivAt_congr (h0.congr_deriv ?_) (fun y => ?_)
    · rw [hda]; try ring
    · simp only [Pi.mul_apply]
  have hP2 : HasDerivAt (fun x : ℝ => 80 * (Real.sin (2 * x)) ^ 2 * u x * deriv u x)
      (320 * Real.sin (2 * θ) * Real.cos (2 * θ) * (u θ * a)
        + 80 * (Real.sin (2 * θ)) ^ 2 * (a * a + u θ * b)) θ := by
    have h0 := hC.mul hD
    refine ht_hasDerivAt_congr (h0.congr_deriv ?_) (fun y => ?_)
    · rw [hda]; try ring
    · simp only [Pi.mul_apply]; try ring
  have h := hP1.sub hP2
  refine ht_hasDerivAt_congr (h.congr_deriv ?_) (fun y => ?_)
  · ring
  · simp only [Pi.sub_apply, Pi.mul_apply, Pi.pow_apply]; try ring

/-- The finite algebraic identity behind the integration by parts: with `s² + c² = 1` and
`g = -4 s u + 4 c a + s b`, the quantity `10 g² - a² - htNN` equals the derivative of
`40 s c a² - 80 s² u a` computed in `htPP_hasDerivAt_gen`. -/
lemma htPP_deriv_algebra (s c u a b g : ℝ) (hsc : s ^ 2 + c ^ 2 = 1)
    (hg : g = -4 * s * u + 4 * c * a + s * b) :
    10 * g ^ 2 - a ^ 2 - (10 * s ^ 2 * b ^ 2 + (79 + 80 * s ^ 2) * a ^ 2 + 160 * s ^ 2 * u ^ 2)
      = 80 * (c ^ 2 - 2 * s ^ 2) * a ^ 2 + 80 * s * c * a * b
        - 320 * s * c * u * a - 80 * s ^ 2 * u * b := by
  rw [hg]
  nlinarith [hsc]

/-- `f'' = s u'' + 4 c u' - 4 s u` for `f = s u`, `u = f / sin 2θ`. -/
lemma deriv_deriv_f_eq (f : ℝ → ℝ) (hf : ContDiffOn ℝ 2 f (Set.Icc 0 (π / 2)))
    (θ : ℝ) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    deriv (deriv f) θ
      = -4 * Real.sin (2 * θ) * htU f θ
        + 4 * Real.cos (2 * θ) * deriv (htU f) θ
        + Real.sin (2 * θ) * deriv (deriv (htU f)) θ := by
  have hC2 : ContDiffAt ℝ 2 (htU f) θ := htU_contDiffAt f hf θ hθ
  have hu1 : HasDerivAt (htU f) (deriv (htU f) θ) θ :=
    ((hC2.of_le (by norm_num)).differentiableAt one_ne_zero).hasDerivAt
  have hu2 : HasDerivAt (deriv (htU f)) (deriv (deriv (htU f)) θ) θ :=
    ((hC2.derivWithin (m := 1) (by norm_num)).differentiableAt one_ne_zero).hasDerivAt
  have hsin_ne : Real.sin (2 * θ) ≠ 0 := by
    have h1 : 0 < 2 * θ := by linarith [hθ.1]
    have h2 : 2 * θ < π := by linarith [hθ.2]
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi h1 h2)
  have hev_ne : ∀ᶠ x in 𝓝 θ, Real.sin (2 * x) ≠ 0 := by
    have hcont : ContinuousAt (fun x : ℝ => Real.sin (2 * x)) θ := by fun_prop
    exact hcont.eventually_ne hsin_ne
  have heq : f =ᶠ[𝓝 θ] (fun x => Real.sin (2 * x) * htU f x) := by
    filter_upwards [hev_ne] with x hx
    simp only [htU]
    field_simp
  have hderiv_eq : deriv f =ᶠ[𝓝 θ] deriv (fun x => Real.sin (2 * x) * htU f x) :=
    heq.deriv
  have step1 : deriv (deriv f) θ
      = deriv (deriv (fun x => Real.sin (2 * x) * htU f x)) θ := hderiv_eq.deriv_eq
  have hev_diff : ∀ᶠ x in 𝓝 θ, DifferentiableAt ℝ (htU f) x :=
    (hC2.eventually (by norm_num)).mono fun x hx => hx.differentiableAt (by norm_num)
  have dg_eq : deriv (fun x => Real.sin (2 * x) * htU f x) =ᶠ[𝓝 θ]
      (fun x => 2 * Real.cos (2 * x) * htU f x + Real.sin (2 * x) * deriv (htU f) x) := by
    filter_upwards [hev_diff] with x hx
    have hgd : HasDerivAt (fun y : ℝ => Real.sin (2 * y) * htU f y)
        (2 * Real.cos (2 * x) * htU f x + Real.sin (2 * x) * deriv (htU f) x) x := by
      have h0 := (ht_sin_two_hasDerivAt x).mul hx.hasDerivAt
      refine ht_hasDerivAt_congr (h0.congr_deriv ?_) (fun y => ?_)
      · ring
      · simp only [Pi.mul_apply]
    exact hgd.deriv
  have step2 : deriv (deriv (fun x => Real.sin (2 * x) * htU f x)) θ
      = deriv (fun x => 2 * Real.cos (2 * x) * htU f x + Real.sin (2 * x) * deriv (htU f) x) θ :=
    dg_eq.deriv_eq
  have hΦ : HasDerivAt
      (fun x => 2 * Real.cos (2 * x) * htU f x + Real.sin (2 * x) * deriv (htU f) x)
      (-4 * Real.sin (2 * θ) * htU f θ + 4 * Real.cos (2 * θ) * deriv (htU f) θ
        + Real.sin (2 * θ) * deriv (deriv (htU f)) θ) θ := by
    have h1 : HasDerivAt (fun x : ℝ => 2 * Real.cos (2 * x)) (-4 * Real.sin (2 * θ)) θ := by
      have h0 := (ht_cos_two_hasDerivAt θ).const_mul 2
      refine ht_hasDerivAt_congr (h0.congr_deriv ?_) (fun y => ?_)
      · ring
      · ring
    have h2 := (h1.mul hu1).add ((ht_sin_two_hasDerivAt θ).mul hu2)
    refine ht_hasDerivAt_congr (h2.congr_deriv ?_) (fun y => ?_)
    · ring
    · simp only [Pi.add_apply, Pi.mul_apply]; try ring
  rw [step1, step2, hΦ.deriv]

/-- `htPP` is an antiderivative of `htEE` on `(0, π/2)`. -/
theorem hardy_two_hasDerivAt (f : ℝ → ℝ) (hf : ContDiffOn ℝ 2 f (Set.Icc 0 (π / 2)))
    (θ : ℝ) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    HasDerivAt (Work.Elliptic.htPP f) (Work.Elliptic.htEE f θ) θ := by
  have hC2 : ContDiffAt ℝ 2 (htU f) θ := htU_contDiffAt f hf θ hθ
  have hu : HasDerivAt (htU f) (deriv (htU f) θ) θ :=
    ((hC2.of_le (by norm_num)).differentiableAt one_ne_zero).hasDerivAt
  have hd : HasDerivAt (deriv (htU f)) (deriv (deriv (htU f)) θ) θ :=
    ((hC2.derivWithin (m := 1) (by norm_num)).differentiableAt one_ne_zero).hasDerivAt
  have hgen := htPP_hasDerivAt_gen (htU f) θ (deriv (htU f) θ) (deriv (deriv (htU f)) θ) hu hd
  have hrel := deriv_deriv_f_eq f hf θ hθ
  have hsc : (Real.sin (2 * θ)) ^ 2 + (Real.cos (2 * θ)) ^ 2 = 1 := Real.sin_sq_add_cos_sq (2 * θ)
  have halg := htPP_deriv_algebra (Real.sin (2 * θ)) (Real.cos (2 * θ)) (htU f θ)
    (deriv (htU f) θ) (deriv (deriv (htU f)) θ) (deriv (deriv f) θ) hsc hrel
  have hEE : htEE f θ
      = 80 * ((Real.cos (2 * θ)) ^ 2 - 2 * (Real.sin (2 * θ)) ^ 2) * (deriv (htU f) θ) ^ 2
        + 80 * Real.sin (2 * θ) * Real.cos (2 * θ) * deriv (htU f) θ * deriv (deriv (htU f)) θ
        - 320 * Real.sin (2 * θ) * Real.cos (2 * θ) * htU f θ * deriv (htU f) θ
        - 80 * (Real.sin (2 * θ)) ^ 2 * htU f θ * deriv (deriv (htU f)) θ := by
    simp only [htEE, htNN]
    exact halg
  exact hgen.congr_deriv hEE.symm

end Work.Elliptic
