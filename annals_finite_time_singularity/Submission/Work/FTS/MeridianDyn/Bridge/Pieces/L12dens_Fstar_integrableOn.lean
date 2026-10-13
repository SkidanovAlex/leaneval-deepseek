import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Submission.Work.Construction.L12_Fstar_eq
import Submission.Work.FM.Core
import Submission.Work.FM.Defs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The `L₁₂`-density of the profile `F_*` is integrable on `(z,∞)`

`Work.Construction.L12dens (F_*) s` is the angular density `∫_0^{π/2} K(θ) F_*(s,θ)/s dθ` of
the integral operator `L₁₂` at the paper's profile.  By
`Work.Construction.L12dens_Fstar` it equals `α · (F_*(s)/s)` with `F_*(s) = 2s/(1+s)²`
(`Work.FM.Fstar`), so on `/ s ≠ 0` it is the elementary function `2α/(1+s)²`, whose
`z`-integral converges on `(z,∞)` for every `z ≥ 0` (the pole of `1/(1+s)²` sits at
`s = -1 < z`).  The integrability is `L₂`-integrability, not just convergence of the
improper integral, and is obtained from the FTC lemma
`MeasureTheory.integrableOn_Ioi_deriv_of_nonneg'` applied to the primitive
`s ↦ -2/(1+s)` — exactly the computation of `Work.FM.integral_Ioi_Fstar_div`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.MeridianDyn.Bridge.Pieces

/-- The elementary integrand `s ↦ 2/(1+s)²` is integrable on `(z,∞)` for `z ≥ 0`: it has the
antiderivative `s ↦ -2/(1+s)`, which is nonnegative-derivative there and tends to `0` at
`+∞`. -/
theorem integrableOn_two_div_one_add_sq (z : ℝ) (hz : 0 ≤ z) :
    IntegrableOn (fun s : ℝ => 2 / (1 + s) ^ 2) (Ioi z) := by
  refine integrableOn_Ioi_deriv_of_nonneg'
    (g := fun t : ℝ => -2 / (1 + t)) (g' := fun t : ℝ => 2 / (1 + t) ^ 2)
    (a := z) (l := 0) ?_ ?_ ?_
  · intro x hx
    have hxz : z ≤ x := hx.out
    have hx1 : (1 : ℝ) + x ≠ 0 := by linarith
    simpa using Work.FM.hasDerivAt_div_add_const (-2) 1 x hx1
  · intro x hx
    have hx0 : (0 : ℝ) < 1 + x := by have := hx.out; linarith
    positivity
  · have h1 : Tendsto (fun t : ℝ => (1 : ℝ) + t) atTop atTop :=
      tendsto_atTop_add_const_left atTop (1 : ℝ) tendsto_id
    have h2 : Tendsto (fun t : ℝ => ((1 : ℝ) + t)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp h1
    have h3 := h2.const_mul (-2 : ℝ)
    simpa [div_eq_mul_inv] using h3

/-- The `L₁₂`-density of the profile `F_*` is integrable on `(z,∞)` for every `z ≥ 0`: it is
`α · 2/(1+s)²` off the null set `{0}`, and `2/(1+s)²` is integrable on `(z,∞)` by
`integrableOn_two_div_one_add_sq`. -/
theorem L12dens_Fstar_integrableOn {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∀ z : ℝ, 0 ≤ z → MeasureTheory.IntegrableOn
      (Work.Construction.L12dens (Work.Construction.Fstar α)) (Set.Ioi z) := by
  intro z hz
  -- the elementary integrand, and its `α`-multiple
  have hbase : IntegrableOn (fun s : ℝ => 2 / (1 + s) ^ 2) (Ioi z) :=
    integrableOn_two_div_one_add_sq z hz
  have hmul : IntegrableOn (fun s : ℝ => α * (2 / (1 + s) ^ 2)) (Ioi z) :=
    hbase.integrable.const_mul α
  -- `2/(1+s)² = F_*(s)/s` on `(z,∞)` (`z ≥ 0`, so `s ≠ 0` there)
  have hcongr : EqOn (fun s : ℝ => α * (2 / (1 + s) ^ 2))
      (fun s : ℝ => α * (Work.FM.Fstar s / s)) (Ioi z) := by
    intro s hs
    have hs0 : s ≠ 0 := by have := hs.out; linarith
    have hs1 : (1 : ℝ) + s ≠ 0 := by have := hs.out; linarith
    have hkey : Work.FM.Fstar s / s = 2 / (1 + s) ^ 2 := by
      unfold Work.FM.Fstar
      field_simp
    show α * (2 / (1 + s) ^ 2) = α * (Work.FM.Fstar s / s)
    rw [hkey]
  have h1 : IntegrableOn (fun s : ℝ => α * (Work.FM.Fstar s / s)) (Ioi z) :=
    hmul.congr_fun hcongr measurableSet_Ioi
  -- identify the density of `L₁₂` with `α · (F_*/s)`
  refine h1.congr_fun (fun s _ => ?_) measurableSet_Ioi
  exact (Work.Construction.L12dens_Fstar hα hα1 s).symm

end Work.FTS.MeridianDyn.Bridge.Pieces
