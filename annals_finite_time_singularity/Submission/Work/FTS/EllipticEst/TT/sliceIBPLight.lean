/-
Copyright: work module for the Elgindi finite-time singularity project.

# The light-weight (`σ_a = sin(2θ)^a`) one-dimensional angular integration by parts

This module builds the 1-D brick of the route recorded in `NOTES_interpGamma.md` for the target
`Work.FTS.EllipticEst.TT.interpGamma`: the **double angular integration by parts for the light
weight** `σ(θ) = sin(2θ)^a`, `0 < a < 1`.

The template is `Work.FTS.EllipticEst.AngSecond.slice_ibp_sigma`, which does the same for the
heavy weight `sin(2θ)^{-η}` (`0 ≤ η < 1`).  The two differences are

* the *sign structure*: for the light weight `σ'' = -4a σ - 4a(1-a) cos²(2θ) sin(2θ)^{a-2}`, so
  the identity reads
  `∫ (f')²σ = -∫ f f'' σ - 2a ∫ f² σ - 2a(1-a) ∫ f² cos²(2θ) sin(2θ)^{a-2}`
  (the two extra terms are `≤ 0` — this is why no Hardy inequality is needed for `σ_a`,
  cf. the notes);
* the *boundary behaviour*: for `f` of class `C²` on the closed interval with `f 0 = f (π/2) = 0`
  one has `f = O(θ)`, hence `f f' σ → 0` and `f²σ' → 0` at both endpoints (for the heavy weight
  this needs the sharp `η < 1` argument of `slice_boundary_tendsto`).

The proof of the identity is assembled from the generic antiderivative lemma
`Work.FTS.EllipticEst.AngSecond.slice_ftc_zero` (which is about *any* differentiable `g` with
vanishing endpoint limits) applied to the two antiderivatives `A = f·f'·σ` and `B = f²·σ'`.
-/
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.AngSecond.SliceIBPDefs
import Submission.Work.FTS.EllipticEst.AngSecond.slice_ftc_zero

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.TT

set_option autoImplicit false

/-! ## The weight `σ_a` and its two derivatives -/

/-- The light angular weight `σ(θ) = sin(2θ)^a`. -/
def sigR (a θ : ℝ) : ℝ := (Real.sin (2 * θ)) ^ a

/-- The first derivative of `sigR`: `σ' = 2a cos(2θ) sin(2θ)^{a-1}`. -/
def sigDR (a θ : ℝ) : ℝ := 2 * a * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (a - 1)

/-- The second derivative of `sigR`:
`σ'' = -4a σ - 4a(1-a) cos²(2θ) sin(2θ)^{a-2}`. -/
def sigDDR (a θ : ℝ) : ℝ :=
  -4 * a * (Real.sin (2 * θ)) ^ a
    - 4 * a * (1 - a) * Real.cos (2 * θ) ^ 2 * (Real.sin (2 * θ)) ^ (a - 2)

@[simp] theorem sigR_apply (a θ : ℝ) : sigR a θ = (Real.sin (2 * θ)) ^ a := rfl
@[simp] theorem sigDR_apply (a θ : ℝ) : sigDR a θ = 2 * a * Real.cos (2 * θ)
    * (Real.sin (2 * θ)) ^ (a - 1) := rfl
@[simp] theorem sigDDR_apply (a θ : ℝ) : sigDDR a θ =
    -4 * a * (Real.sin (2 * θ)) ^ a
      - 4 * a * (1 - a) * Real.cos (2 * θ) ^ 2 * (Real.sin (2 * θ)) ^ (a - 2) := rfl

/-- On the open interval the base `sin(2θ)` is positive, so `sigR` is differentiable there with
derivative `sigDR`. -/
theorem sigR_hasDerivAt (a : ℝ) {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    HasDerivAt (sigR a) (sigDR a θ) θ := by
  have hsin_pos : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hlin : HasDerivAt (fun t : ℝ => 2 * t) 2 θ := by
    simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
  have hsin : HasDerivAt (fun t : ℝ => Real.sin (2 * t)) (Real.cos (2 * θ) * 2) θ := hlin.sin
  have hpow := hsin.rpow_const (p := a) (Or.inl (ne_of_gt hsin_pos))
  refine hpow.congr_deriv ?_
  rw [sigDR_apply]
  ring

/-- The second derivative of the weight on the open interval. -/
theorem sigDR_hasDerivAt (a : ℝ) {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    HasDerivAt (sigDR a) (sigDDR a θ) θ := by
  have hsin_pos : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hlin : HasDerivAt (fun t : ℝ => 2 * t) 2 θ := by
    simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
  have hcos : HasDerivAt (fun t : ℝ => Real.cos (2 * t)) (-(Real.sin (2 * θ) * 2)) θ :=
    (hlin.cos).congr_deriv (by ring)
  have hsin : HasDerivAt (fun t : ℝ => Real.sin (2 * t)) (Real.cos (2 * θ) * 2) θ := hlin.sin
  -- the second factor `sin(2θ)^{a-1}`
  have hpow : HasDerivAt (fun t : ℝ => (Real.sin (2 * t)) ^ (a - 1))
      ((Real.cos (2 * θ) * 2) * (a - 1) * (Real.sin (2 * θ)) ^ (a - 1 - 1)) θ :=
    hsin.rpow_const (p := a - 1) (Or.inl (ne_of_gt hsin_pos))
  have hprod : HasDerivAt
      (fun t : ℝ => (2 * a * Real.cos (2 * t)) * (Real.sin (2 * t)) ^ (a - 1))
      ((2 * a * (-(Real.sin (2 * θ) * 2))) * (Real.sin (2 * θ)) ^ (a - 1)
        + (2 * a * Real.cos (2 * θ))
          * ((Real.cos (2 * θ) * 2) * (a - 1) * (Real.sin (2 * θ)) ^ (a - 1 - 1))) θ :=
    (hcos.const_mul (2 * a)).mul hpow
  refine hprod.congr_deriv ?_
  -- identify with `sigDDR`
  rw [sigDDR_apply]
  have hs : Real.sin (2 * θ) ≠ 0 := ne_of_gt hsin_pos
  have hsplit : (Real.sin (2 * θ)) ^ (a - 1)
      = (Real.sin (2 * θ)) ^ a * (Real.sin (2 * θ)) ^ (-1 : ℝ) := by
    rw [← Real.rpow_add hsin_pos]
    ring_nf
  have hsplit2 : (Real.sin (2 * θ)) ^ (a - 1 - 1)
      = (Real.sin (2 * θ)) ^ (a - 2) := by ring_nf
  rw [hsplit2]
  -- express everything through `s^a` and `s^{a-2}`
  have hinv : (Real.sin (2 * θ)) ^ (-1 : ℝ) = (Real.sin (2 * θ))⁻¹ :=
    Real.rpow_neg_one _
  have h1 : (2 * a * (-(Real.sin (2 * θ) * 2))) * (Real.sin (2 * θ)) ^ a * (Real.sin (2 * θ))⁻¹
      = -4 * a * (Real.sin (2 * θ)) ^ a := by
    field_simp
    ring
  have h2 : (2 * a * Real.cos (2 * θ)) * ((Real.cos (2 * θ) * 2) * (a - 1)
      * (Real.sin (2 * θ)) ^ (a - 2))
      = 4 * a * (a - 1) * Real.cos (2 * θ) ^ 2 * (Real.sin (2 * θ)) ^ (a - 2) := by ring
  rw [← hinv] at h1
  rw [hsplit] at *
  linarith [h1, h2]

/-! ## The double angular integration by parts for the light weight

The identity is assembled exactly as in `AngSecond.slice_ibp_sigma`: the two antiderivatives
`A = f·f'·σ` and `B = f²·σ'` are integrated with the generic `AngSecond.slice_ftc_zero`, and the
two resulting identities
`∫ ((f')²σ + f f''σ + f f'σ') = 0`, `∫ (2 f f'σ' + f²σ'') = 0`
are combined after expanding `σ''`.  The analytic side conditions (integrability of the five
pieces and the vanishing of the two endpoint limits) are *explicit hypotheses* here, so that this
lemma is independent of how they are discharged for a given slice. -/

/-- **The light-weight angular integration by parts.**

For `0 < a < 1` and `f : ℝ → ℝ` which is `C²` on the open interval `(0,π/2)` and for which the
five weighted integrals below are honest and the two boundary products vanish at the endpoints,

  `∫_θ (f')² σ = -∫_θ f f'' σ - 2a ∫_θ f² σ - 2a(1-a) ∫_θ f² cos²(2θ) sin(2θ)^{a-2}`,

with `σ θ = sin(2θ)^a` (`sigR a`). -/
theorem slice_ibp_light (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 2 f (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (hI1 : MeasureTheory.IntegrableOn (fun θ : ℝ => deriv f θ ^ 2 * sigR a θ)
      Work.Spaces.Iθ)
    (hI2 : MeasureTheory.IntegrableOn
      (fun θ : ℝ => f θ * deriv (deriv f) θ * sigR a θ) Work.Spaces.Iθ)
    (hI3 : MeasureTheory.IntegrableOn (fun θ : ℝ => f θ * deriv f θ * sigDR a θ)
      Work.Spaces.Iθ)
    (hI4 : MeasureTheory.IntegrableOn (fun θ : ℝ => f θ ^ 2 * sigR a θ) Work.Spaces.Iθ)
    (hI5 : MeasureTheory.IntegrableOn (fun θ : ℝ => f θ ^ 2 * Real.cos (2 * θ) ^ 2
      * (Real.sin (2 * θ)) ^ (a - 2)) Work.Spaces.Iθ)
    (hb1 : Filter.Tendsto (fun t : ℝ => f t * deriv f t * sigR a t)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hb2 : Filter.Tendsto (fun t : ℝ => f t * deriv f t * sigR a t)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0))
    (hb3 : Filter.Tendsto (fun t : ℝ => f t ^ 2 * sigDR a t)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hb4 : Filter.Tendsto (fun t : ℝ => f t ^ 2 * sigDR a t)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) :
    (∫ θ in Work.Spaces.Iθ, deriv f θ ^ 2 * sigR a θ)
      = - (∫ θ in Work.Spaces.Iθ, f θ * deriv (deriv f) θ * sigR a θ)
        - 2 * a * (∫ θ in Work.Spaces.Iθ, f θ ^ 2 * sigR a θ)
        - 2 * a * (1 - a) * (∫ θ in Work.Spaces.Iθ, f θ ^ 2 * Real.cos (2 * θ) ^ 2
            * (Real.sin (2 * θ)) ^ (a - 2)) := by
  have hpi2 : (0 : ℝ) < Real.pi / 2 := by positivity
  -- `f` is `C²` at interior points
  have hcd : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), ContDiffAt ℝ 2 f θ := fun θ hθ =>
    (hf θ hθ).contDiffAt (isOpen_Ioo.mem_nhds hθ)
  have hdf : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), HasDerivAt f (deriv f θ) θ := fun θ hθ =>
    ((hcd θ hθ).differentiableAt (by norm_num)).hasDerivAt
  have hddf : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (deriv f) (deriv (deriv f) θ) θ := fun θ hθ =>
    (((hcd θ hθ).derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasDerivAt
  -- integrability of `f² σ''`
  have hI6 : MeasureTheory.IntegrableOn (fun θ : ℝ => f θ ^ 2 * sigDDR a θ)
      Work.Spaces.Iθ := by
    have h : MeasureTheory.IntegrableOn (fun θ : ℝ => -4 * a * (f θ ^ 2 * sigR a θ)
        + (-4 * a * (1 - a)) * (f θ ^ 2 * Real.cos (2 * θ) ^ 2
            * (Real.sin (2 * θ)) ^ (a - 2))) Work.Spaces.Iθ :=
      (hI4.const_mul (-4 * a)).add (hI5.const_mul (-4 * a * (1 - a)))
    refine h.congr_fun_ae ?_
    filter_upwards with θ
    simp only [sigDDR_apply, sigR_apply]
    ring_nf
  -- first integration by parts
  have hA_deriv : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (fun t : ℝ => f t * deriv f t * sigR a t)
        (deriv f θ ^ 2 * sigR a θ + f θ * deriv (deriv f) θ * sigR a θ
          + f θ * deriv f θ * sigDR a θ) θ := by
    intro θ hθ
    have h := ((hdf θ hθ).mul (hddf θ hθ)).mul (sigR_hasDerivAt a hθ)
    refine h.congr_deriv ?_
    simp only [Pi.mul_apply]
    ring
  have hA_int : IntervalIntegrable (fun θ : ℝ => deriv f θ ^ 2 * sigR a θ
      + f θ * deriv (deriv f) θ * sigR a θ + f θ * deriv f θ * sigDR a θ)
      MeasureTheory.volume 0 (Real.pi / 2) := by
    have h : MeasureTheory.IntegrableOn (fun θ : ℝ => deriv f θ ^ 2 * sigR a θ
        + f θ * deriv (deriv f) θ * sigR a θ + f θ * deriv f θ * sigDR a θ)
        Work.Spaces.Iθ := (hI1.add hI2).add hI3
    rw [Work.Spaces.Iθ] at h
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le hpi2.le).mpr h
  have hA_zero : (∫ θ in Work.Spaces.Iθ, deriv f θ ^ 2 * sigR a θ
      + f θ * deriv (deriv f) θ * sigR a θ + f θ * deriv f θ * sigDR a θ) = 0 :=
    Work.FTS.EllipticEst.AngSecond.slice_ftc_zero
      (fun t : ℝ => f t * deriv f t * sigR a t)
      (fun θ : ℝ => deriv f θ ^ 2 * sigR a θ + f θ * deriv (deriv f) θ * sigR a θ
        + f θ * deriv f θ * sigDR a θ) hA_deriv hA_int hb1 hb2
  have hA_split : (∫ θ in Work.Spaces.Iθ, deriv f θ ^ 2 * sigR a θ
        + f θ * deriv (deriv f) θ * sigR a θ + f θ * deriv f θ * sigDR a θ)
      = (∫ θ in Work.Spaces.Iθ, deriv f θ ^ 2 * sigR a θ)
        + (∫ θ in Work.Spaces.Iθ, f θ * deriv (deriv f) θ * sigR a θ)
        + (∫ θ in Work.Spaces.Iθ, f θ * deriv f θ * sigDR a θ) := by
    have h12 : MeasureTheory.IntegrableOn (fun θ : ℝ => deriv f θ ^ 2 * sigR a θ
        + f θ * deriv (deriv f) θ * sigR a θ) Work.Spaces.Iθ := hI1.add hI2
    rw [MeasureTheory.integral_add h12 hI3, MeasureTheory.integral_add hI1 hI2]
  -- second integration by parts
  have hB_deriv : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (fun t : ℝ => f t ^ 2 * sigDR a t)
        (2 * (f θ * deriv f θ * sigDR a θ) + f θ ^ 2 * sigDDR a θ) θ := by
    intro θ hθ
    have h := ((hdf θ hθ).mul (hdf θ hθ)).mul (sigDR_hasDerivAt a hθ)
    have hfun : (f * f) * (fun t : ℝ => sigDR a t) = fun t : ℝ => f t ^ 2 * sigDR a t := by
      funext t
      simp only [Pi.mul_apply]
      ring
    rw [hfun] at h
    refine h.congr_deriv ?_
    simp only [Pi.mul_apply]
    ring
  have hB_int : IntervalIntegrable (fun θ : ℝ => 2 * (f θ * deriv f θ * sigDR a θ)
      + f θ ^ 2 * sigDDR a θ) MeasureTheory.volume 0 (Real.pi / 2) := by
    have h : MeasureTheory.IntegrableOn (fun θ : ℝ => 2 * (f θ * deriv f θ * sigDR a θ)
        + f θ ^ 2 * sigDDR a θ) Work.Spaces.Iθ := (hI3.const_mul 2).add hI6
    rw [Work.Spaces.Iθ] at h
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le hpi2.le).mpr h
  have hB_zero : (∫ θ in Work.Spaces.Iθ, 2 * (f θ * deriv f θ * sigDR a θ)
      + f θ ^ 2 * sigDDR a θ) = 0 :=
    Work.FTS.EllipticEst.AngSecond.slice_ftc_zero (fun t : ℝ => f t ^ 2 * sigDR a t)
      (fun θ : ℝ => 2 * (f θ * deriv f θ * sigDR a θ) + f θ ^ 2 * sigDDR a θ)
      hB_deriv hB_int hb3 hb4
  -- expand `σ''`
  have hI6_eq : (∫ θ in Work.Spaces.Iθ, f θ ^ 2 * sigDDR a θ)
      = -4 * a * (∫ θ in Work.Spaces.Iθ, f θ ^ 2 * sigR a θ)
        + (-4 * a * (1 - a)) * (∫ θ in Work.Spaces.Iθ, f θ ^ 2 * Real.cos (2 * θ) ^ 2
            * (Real.sin (2 * θ)) ^ (a - 2)) := by
    have hfun : (fun θ => f θ ^ 2 * sigDDR a θ)
        = (fun θ => -4 * a * (f θ ^ 2 * sigR a θ)
            + (-4 * a * (1 - a)) * (f θ ^ 2 * Real.cos (2 * θ) ^ 2
                * (Real.sin (2 * θ)) ^ (a - 2))) := by
      funext θ
      simp only [sigDDR_apply, sigR_apply]
      ring_nf
    rw [hfun, MeasureTheory.integral_add (hI4.const_mul (-4 * a))
        (hI5.const_mul (-4 * a * (1 - a))),
      MeasureTheory.integral_const_mul (-4 * a) (fun θ => f θ ^ 2 * sigR a θ),
      MeasureTheory.integral_const_mul (-4 * a * (1 - a))
        (fun θ => f θ ^ 2 * Real.cos (2 * θ) ^ 2 * (Real.sin (2 * θ)) ^ (a - 2))]
  have hB_split : (∫ θ in Work.Spaces.Iθ, 2 * (f θ * deriv f θ * sigDR a θ)
        + f θ ^ 2 * sigDDR a θ)
      = 2 * (∫ θ in Work.Spaces.Iθ, f θ * deriv f θ * sigDR a θ)
        + (∫ θ in Work.Spaces.Iθ, f θ ^ 2 * sigDDR a θ) := by
    rw [MeasureTheory.integral_add (hI3.const_mul 2) hI6,
      MeasureTheory.integral_const_mul 2 (fun θ => f θ * deriv f θ * sigDR a θ)]
  -- assemble
  set P := ∫ θ in Work.Spaces.Iθ, deriv f θ ^ 2 * sigR a θ with hP
  set Q := ∫ θ in Work.Spaces.Iθ, f θ * deriv (deriv f) θ * sigR a θ with hQ
  set R := ∫ θ in Work.Spaces.Iθ, f θ * deriv f θ * sigDR a θ with hR
  set D := ∫ θ in Work.Spaces.Iθ, f θ ^ 2 * sigR a θ with hD
  set E := ∫ θ in Work.Spaces.Iθ, f θ ^ 2 * Real.cos (2 * θ) ^ 2
    * (Real.sin (2 * θ)) ^ (a - 2) with hE
  have h1' : P + Q + R = 0 := by
    rw [← hA_split]; exact hA_zero
  have h2' : 2 * R + (-4 * a * D + (-4 * a * (1 - a)) * E) = 0 := by
    rw [← hI6_eq, ← hB_split]; exact hB_zero
  have hmain : P = -Q - 2 * a * D - 2 * a * (1 - a) * E := by linarith
  rw [hP, hQ, hD, hE] at hmain
  linarith [hmain]

end Work.FTS.EllipticEst.TT
