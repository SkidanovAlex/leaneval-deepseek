/-
# The `z`-integration by parts of the weighted Hardy identity (`Lemma HardyWeight`)

This file proves the identity

  `∫_0^∞ w(z)/z · L₁₂(f)(z) · (∫_0^{π/2} K(θ) f(z,θ) dθ) dz = - ∫_0^∞ (1+z)/z³ · L₁₂(f)(z)² dz`

which is the integration by parts in the radial variable underlying Lemma `HardyWeight`
of T. M. Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the
incompressible Euler equations on `ℝ³`*, Annals of Math. **194** (2021)
(see the proof of Lemma `HardyWeight`, where the term `(∂_z(L₁₂(f)²), w)_{L²_z}` is
produced from `-2(K f/z w, L₁₂(f))_{L²}`).

The argument is the classical one for `w(z) = (1+z)²/z² = 1 + 2/z + 1/z²`:

* `∂_z L₁₂(f)(z) = -L12dens(f)(z) = -(1/z)∫_0^{π/2} K(θ)f(z,θ)dθ`, so
  `∫_θ K f dθ = -z ∂_z L₁₂(f)`, i.e. the angular integral in the LHS is `z · L12dens`;
* hence the LHS integrand is `w · L₁₂(f) · (∂_z L₁₂(f)) = (1/2) ∂_z(w L₁₂(f)²) - (w'/2) L₁₂(f)²
  = (1/2) ∂_z(w L₁₂(f)²) + (1+z)/z³ · L₁₂(f)²`;
* the boundary terms `z ↦ w(z) L₁₂(f)(z)²` vanish at `0⁺` and at `∞` (`HardyHyp.bd0`,
  `HardyHyp.bdTop`), so `∫_0^∞ ∂_z(w L₁₂(f)²) = 0`, giving the claim.

Everything is honest `Ln`-integrability: the joint integrability hypothesis `hint` makes the
LHS an absolutely convergent integral (Fubini), and `HardyHyp.intA` makes the RHS one.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Submission.Work.Coercivity.Defs
import Submission.Work.Coercivity.Basic
import Submission.Work.FM.Core
import Submission.Work.FM.Core2
import Submission.Work.Coercivity.pz_mul_w

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-- Under the Hardy hypotheses on `f`, the radial weight `(1+z)/z³` times the square of
`L₁₂(f)` is integrable on `(0,∞)`: `(1+z)/z³ = 1/z³ + 1/z²`, and on `(0,∞)` one has
`1/z³ ≤ 1/z⁴ + 1/z²` (for `z ≤ 1` use the first summand, for `z ≥ 1` the second), so
`HardyHyp.intA` for `j = 2` and `j = 1` provides an integrable dominating function. -/
theorem L12_z_byparts_rhs_integrable (f : ℝ → ℝ → ℝ) (hf : HardyHyp f) :
    IntegrableOn (fun z : ℝ => (1 + z) / z ^ 3 * (L12f f z) ^ 2) (Set.Ioi (0:ℝ)) := by
  -- `L₁₂(f)` is differentiable, hence continuous, on `(0,∞)`.
  have hdL : ∀ z ∈ Set.Ioi (0:ℝ), HasDerivAt (fun x => L12f f x)
      (-(FM.L12dens Spaces.K f z)) z := by
    intro z hz
    exact Work.FM.hasDerivAt_L12 (K := Spaces.K) (f := f) (a := 0) (ρ := z)
      hf.hint (hf.hcont z hz) hz
  have hLcont : ContinuousOn (fun z => L12f f z) (Set.Ioi (0:ℝ)) := by
    have hd : DifferentiableOn ℝ (fun z => L12f f z) (Set.Ioi (0:ℝ)) := by
      intro z hz
      exact (hdL z hz).differentiableAt.differentiableWithinAt
    exact hd.continuousOn
  -- measurability of the integrand
  have hmeas : AEStronglyMeasurable (fun z => (1 + z) / z ^ 3 * (L12f f z) ^ 2)
      (volume.restrict (Set.Ioi (0:ℝ))) := by
    have hc : ContinuousOn (fun z : ℝ => (1 + z) / z ^ 3) (Set.Ioi (0:ℝ)) := by
      have hnum : ContinuousOn (fun z : ℝ => 1 + z) (Set.Ioi (0:ℝ)) :=
        (continuous_const.add continuous_id).continuousOn
      have hden : ContinuousOn (fun z : ℝ => z ^ 3) (Set.Ioi (0:ℝ)) :=
        (continuous_id.pow 3).continuousOn
      exact hnum.div hden (fun z hz => pow_ne_zero 3 (ne_of_gt hz))
    have hsq : ContinuousOn (fun z : ℝ => (L12f f z) ^ 2) (Set.Ioi (0:ℝ)) := hLcont.pow 2
    exact (hc.mul hsq).aestronglyMeasurable measurableSet_Ioi
  -- the two integrable comparison functions supplied by `HardyHyp.intA`
  have h1 : IntegrableOn (fun z => (L12f f z) ^ 2 / z ^ 2) (Set.Ioi (0:ℝ)) := by
    refine IntegrableOn.congr_fun (hf.intA 1 (by norm_num)) (fun z _ => ?_) measurableSet_Ioi
    norm_num
  have h2 : IntegrableOn (fun z => (L12f f z) ^ 2 / z ^ 4) (Set.Ioi (0:ℝ)) := by
    refine IntegrableOn.congr_fun (hf.intA 2 (by norm_num)) (fun z _ => ?_) measurableSet_Ioi
    norm_num
  have hdom : Integrable
      (fun z => 2 * ((L12f f z) ^ 2 / z ^ 2) + 2 * ((L12f f z) ^ 2 / z ^ 4))
      (volume.restrict (Set.Ioi (0:ℝ))) := (h1.const_mul 2).add (h2.const_mul 2)
  refine hdom.mono hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
  have hz0 : 0 < z := hz
  have hLnn : 0 ≤ (L12f f z) ^ 2 := sq_nonneg _
  -- the pointwise bound on the coefficient `(1+z)/z³`
  have hcoef : (1 + z) / z ^ 3 ≤ 2 / z ^ 2 + 2 / z ^ 4 := by
    rw [← sub_nonneg]
    have key : 2 / z ^ 2 + 2 / z ^ 4 - (1 + z) / z ^ 3 = (z ^ 2 - z + 2) / z ^ 4 := by
      field_simp
      ring
    rw [key]
    exact div_nonneg (by nlinarith [sq_nonneg (z - 1 / 2)]) (by positivity)
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ (1 + z) / z ^ 3 * (L12f f z) ^ 2),
    abs_of_nonneg (by positivity :
      (0:ℝ) ≤ 2 * ((L12f f z) ^ 2 / z ^ 2) + 2 * ((L12f f z) ^ 2 / z ^ 4))]
  calc (1 + z) / z ^ 3 * (L12f f z) ^ 2 ≤ (2 / z ^ 2 + 2 / z ^ 4) * (L12f f z) ^ 2 :=
        mul_le_mul_of_nonneg_right hcoef hLnn
    _ = 2 * ((L12f f z) ^ 2 / z ^ 2) + 2 * ((L12f f z) ^ 2 / z ^ 4) := by ring

/-- **The `z`-integration by parts of the weighted Hardy identity.**  With
`w(z) = (1+z)²/z²`, `L₁₂(f)(z) = ∫_z^∞ ∫_0^{π/2} K(θ)f(s,θ)/s dθ ds` and `K(θ) = 3 sinθ cos²θ`:
`∫_0^∞ w/z · L₁₂(f) · (∫_θ K f) = - ∫_0^∞ (1+z)/z³ · L₁₂(f)²`. -/
theorem L12_z_byparts (f : ℝ → ℝ → ℝ) (hf : HardyHyp f)
    (hint : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Spaces.w z / z * L12f f z * (Spaces.K θ * f z θ)))
      (Spaces.Iz ×ˢ Spaces.Iθ)) :
    (∫ z in Set.Ioi (0:ℝ),
        Spaces.w z / z * L12f f z * (∫ θ in Spaces.Iθ, Spaces.K θ * f z θ))
      = - ∫ z in Set.Ioi (0:ℝ), (1 + z) / z ^ 3 * (L12f f z) ^ 2 := by
  -- ### Step 1: the angular integral is `z · L12dens(f)(z)`
  have hmoment : ∀ z ∈ Set.Ioi (0:ℝ),
      (∫ θ in Spaces.Iθ, Spaces.K θ * f z θ) = z * FM.L12dens Spaces.K f z := by
    intro z hz
    rw [FM.L12dens_eq (K := Spaces.K) (f := f) (ne_of_gt hz)]
    simp only [Spaces.Iθ]
    rw [mul_comm, div_mul_cancel₀ _ (ne_of_gt hz)]
  -- ### Step 2: pointwise identification of the integrand of the left-hand side
  have hcongr_on : Set.EqOn
      (fun z => Spaces.w z / z * L12f f z * (∫ θ in Spaces.Iθ, Spaces.K θ * f z θ))
      (fun z => Spaces.w z * L12f f z * FM.L12dens Spaces.K f z) (Set.Ioi (0:ℝ)) := by
    intro z hz
    show Spaces.w z / z * L12f f z * (∫ θ in Spaces.Iθ, Spaces.K θ * f z θ)
      = Spaces.w z * L12f f z * FM.L12dens Spaces.K f z
    rw [hmoment z hz]
    have hz0 : z ≠ 0 := ne_of_gt hz
    field_simp
  -- ### Step 3: integrability of the left-hand side, from Fubini applied to `hint`
  have hΨ : IntegrableOn
      (fun z => Spaces.w z / z * L12f f z * (∫ θ in Spaces.Iθ, Spaces.K θ * f z θ))
      (Set.Ioi (0:ℝ)) := by
    have hprod : Integrable
        (Function.uncurry (fun z θ => Spaces.w z / z * L12f f z * (Spaces.K θ * f z θ)))
        ((volume.restrict Spaces.Iz).prod (volume.restrict Spaces.Iθ)) := by
      have h := hint
      rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at h
      exact h
    have hslice := hprod.integral_prod_left
    have hslice' : IntegrableOn
        (fun z => ∫ θ in Spaces.Iθ, Spaces.w z / z * L12f f z * (Spaces.K θ * f z θ))
        Spaces.Iz := hslice
    have hpull : Set.EqOn
        (fun z => ∫ θ in Spaces.Iθ, Spaces.w z / z * L12f f z * (Spaces.K θ * f z θ))
        (fun z => Spaces.w z / z * L12f f z * (∫ θ in Spaces.Iθ, Spaces.K θ * f z θ))
        Spaces.Iz := by
      intro z hz
      show (∫ θ in Spaces.Iθ, Spaces.w z / z * L12f f z * (Spaces.K θ * f z θ))
        = Spaces.w z / z * L12f f z * (∫ θ in Spaces.Iθ, Spaces.K θ * f z θ)
      rw [integral_const_mul]
    exact (hslice'.congr_fun hpull measurableSet_Ici).mono_set Set.Ioi_subset_Ici_self
  have hWLD : IntegrableOn (fun z => Spaces.w z * L12f f z * FM.L12dens Spaces.K f z)
      (Set.Ioi (0:ℝ)) := hΨ.congr_fun hcongr_on measurableSet_Ioi
  -- ### Step 4: the derivative data
  have hdL : ∀ z ∈ Set.Ioi (0:ℝ), HasDerivAt (fun x => L12f f x)
      (-(FM.L12dens Spaces.K f z)) z := by
    intro z hz
    exact Work.FM.hasDerivAt_L12 (K := Spaces.K) (f := f) (a := 0) (ρ := z)
      hf.hint (hf.hcont z hz) hz
  have hdW : ∀ z ∈ Set.Ioi (0:ℝ), HasDerivAt Spaces.w (-2 * (1 + z) / z ^ 3) z :=
    fun z hz => hasDerivAt_w (ne_of_gt hz)
  have hdV : ∀ z ∈ Set.Ioi (0:ℝ), HasDerivAt (fun x => (L12f f x) ^ 2)
      (2 * L12f f z * (-(FM.L12dens Spaces.K f z))) z := by
    intro z hz
    have h := (hdL z hz).pow 2
    have hd : (↑2 * L12f f z ^ (2 - 1) * (-(FM.L12dens Spaces.K f z)))
        = 2 * L12f f z * (-(FM.L12dens Spaces.K f z)) := by norm_num
    exact h.congr_deriv hd
  -- ### Step 5: integrability of the two pieces of the derivative of `w · L₁₂(f)²`
  have hG : IntegrableOn (fun z => (1 + z) / z ^ 3 * (L12f f z) ^ 2) (Set.Ioi (0:ℝ)) :=
    L12_z_byparts_rhs_integrable f hf
  have hG' : IntegrableOn (fun z => (-2 * (1 + z) / z ^ 3) * (L12f f z) ^ 2)
      (Set.Ioi (0:ℝ)) := by
    refine IntegrableOn.congr_fun (hG.const_mul (-2)) (fun z _ => ?_) measurableSet_Ioi
    show -2 * ((1 + z) / z ^ 3 * (L12f f z) ^ 2) = (-2 * (1 + z) / z ^ 3) * (L12f f z) ^ 2
    ring
  have hWLD' : IntegrableOn
      (fun z => Spaces.w z * (2 * L12f f z * (-(FM.L12dens Spaces.K f z))))
      (Set.Ioi (0:ℝ)) := by
    refine IntegrableOn.congr_fun (hWLD.const_mul (-2)) (fun z _ => ?_) measurableSet_Ioi
    show -2 * (Spaces.w z * L12f f z * FM.L12dens Spaces.K f z)
      = Spaces.w z * (2 * L12f f z * (-(FM.L12dens Spaces.K f z)))
    ring
  -- ### Step 6: integration by parts, with vanishing boundary terms from `HardyHyp`
  have hIBP := MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul
    (a := (0:ℝ)) (a' := (0:ℝ)) (b' := (0:ℝ))
    (u := Spaces.w) (u' := fun z => -2 * (1 + z) / z ^ 3)
    (v := fun z => (L12f f z) ^ 2)
    (v' := fun z => 2 * L12f f z * (-(FM.L12dens Spaces.K f z)))
    hdW hdV hWLD' hG'
    (by
      show Tendsto (fun z => Spaces.w z * (L12f f z) ^ 2) (𝓝[>] (0:ℝ)) (𝓝 0)
      exact (hf.bd0 0 (by norm_num)).2)
    (by
      show Tendsto (fun z => Spaces.w z * (L12f f z) ^ 2) atTop (𝓝 0)
      exact (hf.bdTop 0 (by norm_num)).2)
  -- ### Step 7: rewrite both integrals of the identity in the required form
  have h1 : (∫ x in Set.Ioi (0:ℝ), Spaces.w x * (2 * L12f f x * (-(FM.L12dens Spaces.K f x))))
      = -2 * ∫ x in Set.Ioi (0:ℝ), Spaces.w x * L12f f x * FM.L12dens Spaces.K f x := by
    rw [show (fun x => Spaces.w x * (2 * L12f f x * (-(FM.L12dens Spaces.K f x))))
        = fun x => -2 * (Spaces.w x * L12f f x * FM.L12dens Spaces.K f x) from by
      funext x; ring]
    rw [integral_const_mul]
  have h2 : (∫ x in Set.Ioi (0:ℝ), (-2 * (1 + x) / x ^ 3) * (L12f f x) ^ 2)
      = -2 * ∫ x in Set.Ioi (0:ℝ), (1 + x) / x ^ 3 * (L12f f x) ^ 2 := by
    rw [show (fun x => (-2 * (1 + x) / x ^ 3) * (L12f f x) ^ 2)
        = fun x => -2 * ((1 + x) / x ^ 3 * (L12f f x) ^ 2) from by
      funext x; ring]
    rw [integral_const_mul]
  have hkey : (∫ x in Set.Ioi (0:ℝ), Spaces.w x * L12f f x * FM.L12dens Spaces.K f x)
      = - ∫ x in Set.Ioi (0:ℝ), (1 + x) / x ^ 3 * (L12f f x) ^ 2 := by
    rw [h1, h2] at hIBP
    linarith
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr_on]
  exact hkey

end Work.Coercivity
