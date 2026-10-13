/-
Copyright: work module for the Elgindi finite-time singularity project.

# The moment identity `L₁₂(F)(z) = 15α F_*(Ψ)(z) + 3α² (D_zΨ)_*(z)`

T. M. Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the
incompressible Euler equations on `ℝ³`*, Annals of Math. **194** (3) 2021,
§'Elliptic Regularity Estimates'.

Let `(F,Ψ)` be data of `Work.FTS.EllipticEst.EllHyp α k F Ψ`, i.e. `Ψ` is a smooth solution of
the elliptic problem (PolarBSL) with source `F` in the self-similar variables.  Write

  `m(z) = Ψ_⋆(z) = F_*(Ψ)(z) = ∫_0^{π/2} Ψ(z,θ) sinθcos²θ dθ`

for the angular moment of the solution.  Integrating the equation against `sinθcos²θ` (the
weight of the solvability condition, which lies in the kernel of the adjoint of the `α = 0` part
of the operator, `Work.Elliptic.Lzero_orthogonal`) gives the ODE

  `α²z² m'' + α(5+α) z m' = -F_*(F)`

(`Work.Elliptic.PsiStar_ode`).  Since `L₁₂(F)(z) = 3 ∫_z^∞ F_*(F)(r)/r dr`
(`Work.Elliptic.L12_eq_radial`), and since the integrand is an exact derivative,

  `F_*(F)(r)/r = -(α² r m''(r) + α(5+α)m'(r)) = -d/dr(α² r m'(r) + 5α m(r))`,

we get

  `L₁₂(F)(z) = 3 (α² z m'(z) + 5α m(z))`

**provided the boundary term at infinity vanishes**, i.e. `α²z m'(z) + 5αm(z) → 0` along a
sequence.  This is the mathematical content of the target identity, since

  `3(α² z m'(z) + 5α m(z)) = 15α F_*(Ψ)(z) + 3α² F_*(D_zΨ)(z)`

(the factor `z` of `D_z` is pulled out of the angular integral, `Fstar_DzIter_one_eq`).
Equivalently, the difference

  `K(z) = L₁₂(F)(z) - (15α F_*(Ψ)(z) + 3α² F_*(D_zΨ)(z))`

has vanishing derivative on `(0,∞)` — both sides have derivative `-3F_*(F)(z)/z`, the
left one by the fundamental theorem of calculus for `∫_z^∞`
(`hasDerivAt_L12_of_cont`), the right one by the moment ODE
(`hasDerivAt_moment_rhs`) — hence is constant there.  The constant is computed by evaluating
`K` along a sequence at infinity:

* `L₁₂(F)(z) → 0` as `z → ∞` because `r ↦ F_*(F)(r)/r ∈ L¹(0,∞)`
  (`integrableOn_Fstar_div_self`, proved below);
* the right-hand side tends to `0` along some sequence `u k → ∞`, because it is the square
  integrable function `15α F_*(Ψ) + 3α² F_*(D_zΨ)`, whose two summands are `L²`
  (`Cert.L12Aux.Fstar_L2_of_EllHyp` resp. `Cert.L12Aux.Fstar_DzIter_one_L2_of_EllHyp`); an
  integrable function vanishes along a sequence tending to infinity
  (`Work.FTS.EllipticEst.seq_tendsto_zero_of_integrableOn`).

Hence `K ≡ 0` on `(0,∞)`, which is the claim.

## Why `L₁₂(F)` is differentiable

`EllHyp` does not assume `F` smooth: it only says that `F = bslOp α Ψ` on the open quadrant.
The proof of the sibling `Work.FTS.EllipticEst.HasDerivAt_L12_of_Fstar_facts` uses only the
*continuity* of `F_*(F)` on `(0,∞)` (not its `C^∞`-regularity), and continuity is available
from the moment ODE: `F_*(F)(z) = -(α²z²m''(z) + α(5+α)zm'(z))` with `m` of class `C²` there
(`Work.Elliptic.contDiffOn_two_Fstar`).  This is recorded as `continuousOn_Fstar_of_EllHyp`
and used in `hasDerivAt_L12_of_cont`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.Elliptic.L12_eq_radial
import Submission.Work.Elliptic.Lzero_orthogonal
import Submission.Work.Elliptic.PsiStar_ode
import Submission.Work.Elliptic.PsiStar_zero
import Submission.Work.Elliptic.Fstar_sq_le
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.SmoothCompact_Aux
import Submission.Work.FTS.EllipticEst.Cert.Fstar_div_integrable_of_EllHyp
import Submission.Work.FTS.EllipticEst.seq_tendsto_zero_of_integrableOn
import Submission.Work.FTS.EllipticEst.Cert.L12Aux.Fstar_L2_of_EllHyp

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cert.L12Aux

set_option linter.unusedSimpArgs false

/-! ## Elementary angular facts -/

/-- The angular weight `sinθcos²θ` is continuous on the closed angular interval. -/
theorem continuousOn_sinCos2 :
    ContinuousOn Work.Elliptic.sinCos2 (Set.Icc 0 (π / 2)) := by
  unfold Work.Elliptic.sinCos2
  fun_prop

/-- The angular moment `F_*(F)` is continuous in `z > 0` for `F` smooth on a neighbourhood of
the closed quadrant (its slice is smooth on the compact `Iθ`, so differentiating under the
integral sign applies). -/
theorem continuousAt_Fstar (G : ℝ → ℝ → ℝ) (hG : Work.Spaces.SmoothNbhd G) {z : ℝ}
    (hz : 0 < z) :
    ContinuousAt (fun z' => Work.Elliptic.Fstar G z') z :=
  (Work.Elliptic.hasDerivAt_integral_Iθ G Work.Elliptic.sinCos2 hG continuousOn_sinCos2
    (by linarith : (-1 : ℝ) < z)).continuousAt

/-! ## Continuity of `F_*(F)` for the data of `EllHyp` -/

/-- `z ↦ F_*(F)(z)` is continuous on `(0,∞)` for the data of `EllHyp`: the moment ODE
(`Work.Elliptic.PsiStar_ode`) writes it as `-(α²z²m'' + α(5+α)zm')` with `m = F_*(Ψ)` of class
`C²` there. -/
theorem continuousOn_Fstar_of_EllHyp (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ) (hα : 0 < α)
    (h : Work.FTS.EllipticEst.EllHyp α k F Ψ) :
    ContinuousOn (fun z : ℝ => Work.Elliptic.Fstar F z) (Set.Ioi 0) := by
  have h2 : ContDiffOn ℝ 2 (fun z => Work.Elliptic.Fstar Ψ z) (Set.Ioi 0) :=
    Work.Elliptic.contDiffOn_two_Fstar Ψ h.smoothNbhd
  have h1 : ContDiffOn ℝ 1 (deriv (fun z => Work.Elliptic.Fstar Ψ z)) (Set.Ioi 0) :=
    h2.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have h0 : ContDiffOn ℝ 0 (deriv (deriv (fun z => Work.Elliptic.Fstar Ψ z))) (Set.Ioi 0) :=
    h1.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hd1 : ContinuousOn (fun z => deriv (fun z' => Work.Elliptic.Fstar Ψ z') z)
      (Set.Ioi 0) := h1.continuousOn
  have hd2 : ContinuousOn (fun z => deriv (fun z' => deriv (fun z'' =>
      Work.Elliptic.Fstar Ψ z'') z') z) (Set.Ioi 0) := h0.continuousOn
  have hcont : ContinuousOn (fun z => -(α ^ 2 * z ^ 2 * deriv (fun z' =>
      deriv (fun z'' => Work.Elliptic.Fstar Ψ z'') z') z
      + α * (5 + α) * z * deriv (fun z' => Work.Elliptic.Fstar Ψ z') z)) (Set.Ioi 0) := by
    refine ContinuousOn.neg (ContinuousOn.add ?_ ?_)
    · exact (continuousOn_const.mul (continuousOn_id.pow 2)).mul hd2
    · exact (continuousOn_const.mul continuousOn_id).mul hd1
  refine hcont.congr fun z hz => ?_
  have hODE := Work.Elliptic.PsiStar_ode α F Ψ z hα hz h.smoothNbhd h.sol
  linarith [hODE]

/-! ## The derivative of `L₁₂(F)` -/

/-- **The derivative of the singular term `L₁₂`.**  If the angular moment `F_*(r) = F_*(F)(r)`
is continuous on `(0,∞)` and `r ↦ F_*(F)(r)/r` is integrable there, then
`L₁₂(F)(z) = 3 ∫_z^∞ F_*(F)(r)/r dr` is differentiable at every `z > 0`, with derivative
`-3 F_*(F)(z)/z` (the fundamental theorem of calculus for the improper integral `∫_z^∞`).

This is the sibling `Work.FTS.EllipticEst.HasDerivAt_L12_of_Fstar_facts` with its smoothness
hypothesis weakened to continuity: only the continuity of `F_*(F)` is used in its proof. -/
theorem hasDerivAt_L12_of_cont (F : ℝ → ℝ → ℝ)
    (hFcont : ContinuousOn (fun r : ℝ => Work.Elliptic.Fstar F r) (Set.Ioi 0))
    (hFint : MeasureTheory.IntegrableOn (fun r : ℝ => Work.Elliptic.Fstar F r / r)
      (Set.Ioi 0)) :
    ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (Work.Elliptic.L12 F) (-(3 * Work.Elliptic.Fstar F z / z)) z := by
  intro z hz
  have hzpos : (0 : ℝ) < z := hz
  set g : ℝ → ℝ := fun r => Work.Elliptic.Fstar F r / r with hg
  have hgcontOn : ContinuousOn g (Set.Ioi (0 : ℝ)) := by
    rw [hg]
    exact hFcont.div continuousOn_id (fun x hx => ne_of_gt hx)
  have hgcont : ContinuousAt g z := hgcontOn.continuousAt (isOpen_Ioi.mem_nhds hz)
  have hgmeas : StronglyMeasurableAtFilter g (𝓝 z) MeasureTheory.volume :=
    hgcontOn.stronglyMeasurableAtFilter isOpen_Ioi z hz
  have hInt0 : MeasureTheory.IntegrableOn g (Set.Ioi 0) := hFint
  have hInt : IntervalIntegrable g MeasureTheory.volume 0 z := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hzpos.le]
    exact hInt0.mono_set (fun x hx => hx.1)
  have hFTC : HasDerivAt (fun u => ∫ r in (0 : ℝ)..u, g r) (g z) z :=
    intervalIntegral.integral_hasDerivAt_right hInt hgmeas hgcont
  have hC : HasDerivAt (fun u => (∫ r in Set.Ioi (0 : ℝ), g r) - ∫ r in (0 : ℝ)..u, g r)
      (-(g z)) z := by
    have h := hFTC.const_sub (∫ r in Set.Ioi (0 : ℝ), g r)
    simpa using h
  have heq : (fun u => ∫ r in Set.Ioi u, g r)
      =ᶠ[𝓝 z] (fun u => (∫ r in Set.Ioi (0 : ℝ), g r) - ∫ r in (0 : ℝ)..u, g r) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with u hu
    have hIntu : MeasureTheory.IntegrableOn g (Set.Ioi u) :=
      hInt0.mono_set (Set.Ioi_subset_Ioi hu.le)
    have h := intervalIntegral.integral_Ioi_sub_Ioi' (f := g) (a := (0 : ℝ)) (b := u) hInt0 hIntu
    linarith [h]
  have hcore : HasDerivAt (fun u => ∫ r in Set.Ioi u, g r) (-(g z)) z :=
    hC.congr_of_eventuallyEq heq
  have hrad : HasDerivAt (Work.Elliptic.L12rad F) (-(Work.Elliptic.Fstar F z / z)) z := by
    rw [hg] at hcore
    exact hcore
  have h3 : HasDerivAt (fun u => 3 * Work.Elliptic.L12rad F u)
      (3 * (-(Work.Elliptic.Fstar F z / z))) z :=
    hrad.const_mul 3
  have hL12eq : Work.Elliptic.L12 F = fun u => 3 * Work.Elliptic.L12rad F u :=
    funext (Work.Elliptic.L12_eq_radial F)
  rw [hL12eq]
  exact h3.congr_deriv (by ring)

/-! ## The moment of `D_zΨ` and the derivatives of the moment -/

/-- The derivative of the angular moment, evaluated by differentiating under the integral. -/
theorem hasDerivAt_Fstar (Ψ : ℝ → ℝ → ℝ) (hsm : Work.Spaces.SmoothNbhd Ψ) {z : ℝ}
    (hz : 0 < z) :
    HasDerivAt (fun z' => Work.Elliptic.Fstar Ψ z')
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ) z :=
  Work.Elliptic.hasDerivAt_integral_Iθ Ψ Work.Elliptic.sinCos2 hsm continuousOn_sinCos2
    (by linarith : (-1 : ℝ) < z)

/-- `D_z = z ∂_z` pulls out of the angular integral: `F_*(D_zΨ)(z) = z·F_*(Ψ)'(z)`. -/
theorem Fstar_DzIter_one_eq (Ψ : ℝ → ℝ → ℝ) (hsm : Work.Spaces.SmoothNbhd Ψ) {z : ℝ}
    (hz : 0 < z) :
    Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) z
      = z * deriv (fun z' => Work.Elliptic.Fstar Ψ z') z := by
  have hd : deriv (fun z' => Work.Elliptic.Fstar Ψ z') z
      = ∫ θ in Work.Spaces.Iθ, Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ :=
    (hasDerivAt_Fstar Ψ hsm hz).deriv
  have key : Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) z
      = ∫ θ in Work.Spaces.Iθ, z * (Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ) := by
    rw [Work.Elliptic.Fstar]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
    show (Work.Spaces.DzIter 1 Ψ z θ) * Work.Elliptic.sinCos2 θ
      = z * (Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ)
    simp only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.Dz, Work.Spaces.pz]
    ring
  rw [key, MeasureTheory.integral_const_mul, hd]

/-- The derivative of `z ↦ F_*(Ψ)'(z)`, again by differentiating under the integral. -/
theorem hasDerivAt_deriv_Fstar (Ψ : ℝ → ℝ → ℝ) (hsm : Work.Spaces.SmoothNbhd Ψ) {z : ℝ}
    (hz : 0 < z) :
    HasDerivAt (deriv (fun z' => Work.Elliptic.Fstar Ψ z'))
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.pzIter 2 Ψ z θ * Work.Elliptic.sinCos2 θ) z := by
  have hsm1 : Work.Spaces.SmoothNbhd (Work.Spaces.pz Ψ) := hsm.pz
  have h := Work.Elliptic.hasDerivAt_integral_Iθ (Work.Spaces.pz Ψ) Work.Elliptic.sinCos2 hsm1
    continuousOn_sinCos2 (by linarith : (-1 : ℝ) < z)
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioi.mem_nhds hz] with w hw
  have hw' : (-1 : ℝ) < w := by
    simp only [Set.mem_Ioi] at hw; linarith
  exact (Work.Elliptic.hasDerivAt_integral_Iθ Ψ Work.Elliptic.sinCos2 hsm continuousOn_sinCos2
    hw').deriv

/-! ## The derivative of the right-hand side -/

/-- **The right-hand side of the moment identity has derivative `-3F_*(F)(z)/z`.**

This is the ODE `Work.Elliptic.PsiStar_ode` rewritten: the derivative of
`z ↦ 15α F_*(Ψ)(z) + 3α² F_*(D_zΨ)(z)` at `z > 0` is
`15α m'(z) + 3α²(m'(z) + z m''(z)) = 3α² z m''(z) + (15α+3α²)m'(z)`, and the ODE
`α²z²m'' + α(5+α)zm' = -F_*(F)` turns this into `-3F_*(F)(z)/z`. -/
theorem hasDerivAt_moment_rhs (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ) (hα : 0 < α)
    (h : Work.FTS.EllipticEst.EllHyp α k F Ψ) :
    ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun w => 15 * α * Work.Elliptic.Fstar Ψ w
          + 3 * α ^ 2 * Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) w)
        (-(3 * Work.Elliptic.Fstar F z / z)) z := by
  intro z hz
  have hzpos : (0 : ℝ) < z := hz
  have hsm : Work.Spaces.SmoothNbhd Ψ := h.smoothNbhd
  set D1 : ℝ := ∫ θ in Work.Spaces.Iθ, Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ
    with hD1
  set D2 : ℝ := ∫ θ in Work.Spaces.Iθ, Work.Spaces.pzIter 2 Ψ z θ * Work.Elliptic.sinCos2 θ
    with hD2
  -- the ODE for the angular moment, with its two derivatives as angular integrals
  have hODE := Work.Elliptic.PsiStar_ode α F Ψ z hα hzpos hsm h.sol
  have e1 : deriv (fun z' => Work.Elliptic.Fstar Ψ z') z = D1 :=
    (hasDerivAt_Fstar Ψ hsm hzpos).deriv
  have e2 : deriv (fun z' => deriv (fun z'' => Work.Elliptic.Fstar Ψ z'') z') z = D2 := by
    have h' := (hasDerivAt_deriv_Fstar Ψ hsm hzpos).deriv
    simpa only [hD2] using h'
  rw [e1, e2] at hODE
  -- the product rule for `z ↦ z · F_*(Ψ)'(z)`
  have hmul := (hasDerivAt_id z).mul (hasDerivAt_deriv_Fstar Ψ hsm hzpos)
  have hprod : HasDerivAt (fun w => w * deriv (fun z' => Work.Elliptic.Fstar Ψ z') w)
      (D1 + z * D2) z :=
    hmul.congr_deriv (by simp only [one_mul, id_eq, e1, ← hD2])
  -- collect the two derivative claims
  have hcomb : HasDerivAt (fun w => 15 * α * Work.Elliptic.Fstar Ψ w
      + 3 * α ^ 2 * (w * deriv (fun z' => Work.Elliptic.Fstar Ψ z') w))
      (15 * α * D1 + 3 * α ^ 2 * (D1 + z * D2)) z :=
    ((hasDerivAt_Fstar Ψ hsm hzpos).const_mul (15 * α)).add (hprod.const_mul (3 * α ^ 2))
  -- the value, using the ODE
  have hval' : 15 * α * D1 + 3 * α ^ 2 * (D1 + z * D2)
      = -(3 * Work.Elliptic.Fstar F z) / z := by
    rw [eq_div_iff (ne_of_gt hzpos)]
    have h1 : α ^ 2 * z ^ 2 * D2 + α * (5 + α) * z * D1 = -Work.Elliptic.Fstar F z := hODE
    linear_combination 3 * h1
  -- rewrite the function (the two agree on `(0,∞)`, a neighbourhood of `z`)
  have hfun_eq : (fun w => 15 * α * Work.Elliptic.Fstar Ψ w
      + 3 * α ^ 2 * (w * deriv (fun z' => Work.Elliptic.Fstar Ψ z') w))
      =ᶠ[𝓝 z] (fun w => 15 * α * Work.Elliptic.Fstar Ψ w
        + 3 * α ^ 2 * Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) w) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with w hw
    have hwpos : (0 : ℝ) < w := hw
    rw [Fstar_DzIter_one_eq Ψ hsm hwpos]
  refine (hcomb.congr_of_eventuallyEq hfun_eq.symm).congr_deriv ?_
  rw [hval']
  ring

/-! ## `L₁₂(F) → 0` at infinity -/

/-- `L₁₂(F)(z) → 0` as `z → ∞` when `r ↦ F_*(F)(r)/r` is integrable on `(0,∞)`. -/
theorem tendsto_L12_atTop (F : ℝ → ℝ → ℝ)
    (hint : MeasureTheory.IntegrableOn (fun r : ℝ => Work.Elliptic.Fstar F r / r)
      (Set.Ioi 0)) :
    Filter.Tendsto (Work.Elliptic.L12 F) Filter.atTop (nhds 0) := by
  have hg : Filter.Tendsto (fun z : ℝ => ∫ r in Set.Ioi z, Work.Elliptic.Fstar F r / r)
      Filter.atTop (nhds 0) := by
    have hanti := MeasureTheory.tendsto_setIntegral_of_antitone (μ := volume)
      (f := fun r : ℝ => Work.Elliptic.Fstar F r / r) (s := fun z : ℝ => Set.Ioi z)
      (fun z => measurableSet_Ioi) (fun a b hab => Set.Ioi_subset_Ioi hab) ⟨0, hint⟩
    have hempty : (⋂ z : ℝ, Set.Ioi z) = (∅ : Set ℝ) := by
      ext x
      simp only [Set.mem_iInter, Set.mem_empty_iff_false, iff_false, not_forall]
      exact ⟨x, lt_irrefl x⟩
    rw [hempty, MeasureTheory.setIntegral_empty] at hanti
    simpa only [Work.Elliptic.L12rad] using hanti
  have h3 : Filter.Tendsto (fun z : ℝ => 3 * Work.Elliptic.L12rad F z) Filter.atTop (nhds 0) := by
    have h' := hg.const_mul 3
    simpa only [Work.Elliptic.L12rad, mul_zero] using h'
  have heq : Work.Elliptic.L12 F = fun z => 3 * Work.Elliptic.L12rad F z :=
    funext (Work.Elliptic.L12_eq_radial F)
  rw [heq]
  exact h3

/-! ## The squared `L²`-mass of the right-hand side -/

/-- The square of the angular moment of an `L²`-function is integrable on `(0,∞)`:
Cauchy–Schwarz in `θ` (`Work.Elliptic.Fstar_sq_le`) bounds the moment by the angular `L²`-mass,
whose `z`-integral is finite by the `L2Mem` hypothesis (which also supplies the slice
integrability that `Fstar_sq_le` needs), and whose a.e. strong measurability is assumed. -/
theorem Fstar_sq_integrableOn_of_L2Mem (g : ℝ → ℝ → ℝ) (hl2 : Work.Spaces.L2Mem g)
    (haesm : AEStronglyMeasurable (fun z : ℝ => Work.Elliptic.Fstar g z)
      (volume.restrict (Set.Ioi 0))) :
    MeasureTheory.IntegrableOn (fun z : ℝ => (Work.Elliptic.Fstar g z) ^ 2) (Set.Ioi 0) := by
  have hD : MeasureTheory.IntegrableOn (fun z : ℝ =>
      (π / 2) * ∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2) (Set.Ioi 0) :=
    (hl2.2.mono_set Set.Ioi_subset_Ici_self).const_mul (π / 2)
  show MeasureTheory.Integrable _ (volume.restrict (Set.Ioi 0))
  refine MeasureTheory.Integrable.mono hD (haesm.pow 2) ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
  have h1 : (Work.Elliptic.Fstar g z) ^ 2 ≤ (π / 2) * ∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2 :=
    Work.Elliptic.Fstar_sq_le g z (hl2.1 z (Set.mem_Ici.mpr (le_of_lt hz)))
  have h2 : 0 ≤ ∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2 := integral_nonneg fun θ => sq_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (by positivity) h2)]
  linarith

/-- Multiplication by `z²` pulls out of the angular integral:
`F_*(z²∂_zzΨ)(z) = z² F_*(∂_zzΨ)(z)`. -/
theorem Fstar_zsq_pzIter2_eq' (Ψ : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.Elliptic.Fstar (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z
      = z ^ 2 * Work.Elliptic.Fstar (Work.Spaces.pzIter 2 Ψ) z := by
  have key : Work.Elliptic.Fstar (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z
      = ∫ θ in Work.Spaces.Iθ,
          z ^ 2 * (Work.Spaces.pzIter 2 Ψ z θ * Work.Elliptic.sinCos2 θ) := by
    rw [Work.Elliptic.Fstar]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
    ring
  rw [key, MeasureTheory.integral_const_mul, Work.Elliptic.Fstar]

/-- Multiplication by `z²` and its `θ`-derivatives pull out of the angular integral:
`F_*(z²∂_zzΨ)(z) = z² F_*(Ψ)''(z)`. -/
theorem Fstar_zsq_pzIter2_eq (Ψ : ℝ → ℝ → ℝ) (hsm : Work.Spaces.SmoothNbhd Ψ) {z : ℝ}
    (hz : 0 < z) :
    Work.Elliptic.Fstar (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z
      = z ^ 2 * deriv (fun z' => deriv (fun z'' => Work.Elliptic.Fstar Ψ z'') z') z := by
  have hd : deriv (fun z' => deriv (fun z'' => Work.Elliptic.Fstar Ψ z'') z') z
      = ∫ θ in Work.Spaces.Iθ, Work.Spaces.pzIter 2 Ψ z θ * Work.Elliptic.sinCos2 θ :=
    (hasDerivAt_deriv_Fstar Ψ hsm hz).deriv
  rw [Fstar_zsq_pzIter2_eq' Ψ z, hd]
  rw [Work.Elliptic.Fstar]

/-- `F_*(D_zΨ)(z)` in terms of the source: the moment ODE `α²z²m'' + α(5+α)zm' = -F_*(F)(z)`
with `zm' = F_*(D_zΨ)(z)` and `z²m'' = F_*(z²∂_zzΨ)(z)`. -/
theorem Fstar_DzIter_one_eq_source (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ) (hα : 0 < α)
    (h : Work.FTS.EllipticEst.EllHyp α k F Ψ) :
    ∀ z ∈ Set.Ioi (0 : ℝ),
      Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) z
        = (-Work.Elliptic.Fstar F z
            - α ^ 2 * Work.Elliptic.Fstar
                (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z) / (α * (5 + α)) := by
  intro z hz
  have hzpos : (0 : ℝ) < z := hz
  have hODE := Work.Elliptic.PsiStar_ode α F Ψ z hα hzpos h.smoothNbhd h.sol
  have hm1 : z * deriv (fun z' => Work.Elliptic.Fstar Ψ z') z
      = Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) z :=
    (Fstar_DzIter_one_eq Ψ h.smoothNbhd hzpos).symm
  have hm2 : z ^ 2 * deriv (fun z' => deriv (fun z'' => Work.Elliptic.Fstar Ψ z'') z') z
      = Work.Elliptic.Fstar (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z :=
    (Fstar_zsq_pzIter2_eq Ψ h.smoothNbhd hzpos).symm
  have key : α ^ 2 * Work.Elliptic.Fstar (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z
      + α * (5 + α) * Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) z
      = -Work.Elliptic.Fstar F z := by
    rw [← hm1, ← hm2]
    linear_combination hODE
  have hα5 : α * (5 + α) ≠ 0 := ne_of_gt (by positivity)
  rw [eq_div_iff hα5]
  linarith [key]

/-- `z ↦ (F_*(D_zΨ)(z))²` is integrable on `(0,∞)` for the data of `EllHyp`: the moment ODE
writes `F_*(D_zΨ)` as a constant multiple of the sum of the two moments `F_*(F)` and
`F_*(z²∂_zzΨ)`, which are `L²` because `F` and `z²∂_zzΨ` are `L²` (`EllHyp.l2F`, `EllHyp.l2Z2`). -/
theorem Fstar_DzIter_one_L2_self (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ) (hα : 0 < α)
    (h : Work.FTS.EllipticEst.EllHyp α k F Ψ) :
    MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) z) ^ 2) (Set.Ioi 0) := by
  have hF2 : MeasureTheory.IntegrableOn (fun z : ℝ => (Work.Elliptic.Fstar F z) ^ 2)
      (Set.Ioi 0) :=
    Fstar_sq_integrableOn_of_L2Mem F h.l2F
      (Work.FTS.EllipticEst.Cert.aesm_Fstar α F Ψ h.smoothNbhd h.sol)
  have hZmeas : AEStronglyMeasurable
      (fun z : ℝ => Work.Elliptic.Fstar
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z)
      (volume.restrict (Set.Ioi 0)) := by
    have hcont : ContinuousOn
        (fun z : ℝ => Work.Elliptic.Fstar (Work.Spaces.pzIter 2 Ψ) z) (Set.Ioi 0) :=
      fun z hz => (continuousAt_Fstar (Work.Spaces.pzIter 2 Ψ)
        (Work.Spaces.smoothNbhd_pzIter h.smoothNbhd 2) hz).continuousWithinAt
    have hfun : (fun z : ℝ => Work.Elliptic.Fstar
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z)
        = fun z : ℝ => z ^ 2 * Work.Elliptic.Fstar (Work.Spaces.pzIter 2 Ψ) z :=
      funext fun z => Fstar_zsq_pzIter2_eq' Ψ z
    rw [hfun]
    exact ((continuousOn_id.pow 2).mul hcont).aestronglyMeasurable measurableSet_Ioi
  have hZ2 : MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.Elliptic.Fstar
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z) ^ 2) (Set.Ioi 0) :=
    Fstar_sq_integrableOn_of_L2Mem (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) h.l2Z2
      hZmeas
  have hdom : MeasureTheory.IntegrableOn (fun z : ℝ =>
      (2 / (α * (5 + α)) ^ 2) * ((Work.Elliptic.Fstar F z) ^ 2
        + α ^ 4 * (Work.Elliptic.Fstar (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z) ^ 2))
      (Set.Ioi 0) :=
    (hF2.add (hZ2.const_mul (α ^ 4))).const_mul (2 / (α * (5 + α)) ^ 2)
  show MeasureTheory.Integrable _ (volume.restrict (Set.Ioi 0))
  refine MeasureTheory.Integrable.mono hdom ?_ ?_
  · have hcont : ContinuousOn (fun z : ℝ =>
        Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) z) (Set.Ioi 0) :=
      fun z hz => (continuousAt_Fstar (Work.Spaces.DzIter 1 Ψ)
        (Work.Spaces.smoothNbhd_DzIter h.smoothNbhd 1) hz).continuousWithinAt
    exact (hcont.pow 2).aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
    have hzpos : (0 : ℝ) < z := hz
    have hc : (0 : ℝ) < α * (5 + α) := by positivity
    set A : ℝ := -Work.Elliptic.Fstar F z with hA
    set B : ℝ := -α ^ 2 * Work.Elliptic.Fstar
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z with hB
    have hkey : Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) z = (A + B) / (α * (5 + α)) := by
      rw [Fstar_DzIter_one_eq_source α k F Ψ hα h z hz]
      rw [hA, hB]; ring
    have hsc : (2 / (α * (5 + α)) ^ 2) * ((Work.Elliptic.Fstar F z) ^ 2
        + α ^ 4 * (Work.Elliptic.Fstar (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z) ^ 2)
        = (2 * (A ^ 2 + B ^ 2)) / (α * (5 + α)) ^ 2 := by
      rw [hA, hB]; ring
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), Real.norm_eq_abs, abs_of_nonneg (by
      positivity), hkey, hsc, div_pow]
    have hc2 : 0 < (α * (5 + α)) ^ 2 := by positivity
    rw [div_eq_mul_inv, div_eq_mul_inv]
    have hamgm : (A + B) ^ 2 ≤ 2 * (A ^ 2 + B ^ 2) := by
      nlinarith [sq_nonneg (A - B)]
    calc (A + B) ^ 2 * ((α * (5 + α)) ^ 2)⁻¹
        ≤ (2 * (A ^ 2 + B ^ 2)) * ((α * (5 + α)) ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_right hamgm (by positivity)
      _ = 2 * (A ^ 2 + B ^ 2) / (α * (5 + α)) ^ 2 := by rw [div_eq_mul_inv]

/-- The squared `L²`-mass of `15α F_*(Ψ) + 3α² F_*(D_zΨ)` is finite: both summands are `L²`, and
`(a+b)² ≤ 2a² + 2b²`. -/
theorem integrableOn_moment_rhs_sq (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ) (hα : 0 < α)
    (h : Work.FTS.EllipticEst.EllHyp α k F Ψ) :
    MeasureTheory.IntegrableOn
      (fun z : ℝ => (15 * α * Work.Elliptic.Fstar Ψ z
        + 3 * α ^ 2 * Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) z) ^ 2) (Set.Ioi 0) := by
  have h1 : MeasureTheory.IntegrableOn (fun z : ℝ => (Work.Elliptic.Fstar Ψ z) ^ 2)
      (Set.Ioi 0) := Fstar_L2_of_EllHyp α k F Ψ h
  have h2 : MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) z) ^ 2) (Set.Ioi 0) :=
    Fstar_DzIter_one_L2_self α k F Ψ hα h
  have hdom : MeasureTheory.IntegrableOn (fun z : ℝ =>
      2 * ((15 * α) ^ 2 * (Work.Elliptic.Fstar Ψ z) ^ 2)
        + 2 * ((3 * α ^ 2) ^ 2 * (Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) z) ^ 2))
      (Set.Ioi 0) :=
    ((h1.const_mul ((15 * α) ^ 2)).const_mul 2).add
      ((h2.const_mul ((3 * α ^ 2) ^ 2)).const_mul 2)
  show MeasureTheory.Integrable _ (volume.restrict (Set.Ioi 0))
  refine MeasureTheory.Integrable.mono hdom ?_ ?_
  · have hm1 : ContinuousOn (fun z : ℝ => Work.Elliptic.Fstar Ψ z) (Set.Ioi 0) :=
      fun z hz => (continuousAt_Fstar Ψ h.smoothNbhd hz).continuousWithinAt
    have hm2 : ContinuousOn (fun z : ℝ => Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) z)
        (Set.Ioi 0) :=
      fun z hz => (continuousAt_Fstar (Work.Spaces.DzIter 1 Ψ)
        (Work.Spaces.smoothNbhd_DzIter h.smoothNbhd 1) hz).continuousWithinAt
    exact (((continuousOn_const.mul hm1).add (continuousOn_const.mul hm2)).pow 2)
      |>.aestronglyMeasurable measurableSet_Ioi
  · filter_upwards with z
    have hrw : 2 * ((15 * α) ^ 2 * (Work.Elliptic.Fstar Ψ z) ^ 2)
        + 2 * ((3 * α ^ 2) ^ 2 * (Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) z) ^ 2)
        = 2 * (15 * α * Work.Elliptic.Fstar Ψ z) ^ 2
          + 2 * (3 * α ^ 2 * Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) z) ^ 2 := by ring
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), Real.norm_eq_abs, hrw,
      abs_of_nonneg (by positivity)]
    nlinarith [sq_nonneg (15 * α * Work.Elliptic.Fstar Ψ z
      - 3 * α ^ 2 * Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) z)]

/-! ## Integrability of `r ↦ F_*(F)(r)/r`

The improper integral `L₁₂(F)(z) = 3 ∫_z^∞ F_*(F)(r)/r dr` converges because
`r ↦ F_*(F)(r)/r ∈ L¹(0,∞)`.  This is proved exactly as in the sibling
`Work.FTS.EllipticEst.Cert.Fstar_div_integrable_of_EllHyp`, but with a *self-contained* proof of
the radial `L²`-bound `(r·w(r))⁻¹² ∈ L¹` that the sibling borrows from
`Work.FTS.EllipticEst.Cert.HasFiniteIntegralWInvSq`, still unproved there); the argument is
repeated here so that this module rests only on `[propext, Classical.choice, Quot.sound]`. -/

/-- `r ↦ ((r·w(r))⁻¹)² = (r/(1+r)²)²` is integrable on `(0,∞)`: it is bounded by `1` on the
unit interval and by `r^{-2}` on `(1,∞)`. -/
theorem hasFiniteIntegralWInvSq_self :
    MeasureTheory.HasFiniteIntegral (fun r : ℝ => ((r * Work.Spaces.w r)⁻¹) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
  have hsmall : MeasureTheory.IntegrableOn (fun r : ℝ => (r / (1 + r) ^ 2) ^ 2)
      (Set.Ioc 0 1) := by
    have hc : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioc 0 1) :=
      integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
    have hmeas : AEStronglyMeasurable (fun r : ℝ => (r / (1 + r) ^ 2) ^ 2)
        (volume.restrict (Set.Ioc 0 1)) := by
      have hcont : ContinuousOn (fun r : ℝ => (r / (1 + r) ^ 2) ^ 2) (Set.Ioc 0 1) := by
        refine (ContinuousOn.div continuousOn_id (by fun_prop) ?_).pow 2
        intro r hr
        have h : (1 + r) ^ 2 ≠ 0 := by
          have hr1 : (0 : ℝ) < 1 + r := by linarith [(Set.mem_Ioc.mp hr).1]
          positivity
        exact h
      exact hcont.aestronglyMeasurable measurableSet_Ioc
    refine MeasureTheory.Integrable.mono hc hmeas ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with r hr
    have hr0 : (0 : ℝ) < r := (Set.mem_Ioc.mp hr).1
    have hle : r / (1 + r) ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]
      nlinarith
    have hnn : 0 ≤ r / (1 + r) ^ 2 := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), Real.norm_eq_abs,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)]
    nlinarith [sq_nonneg (r / (1 + r) ^ 2)]
  have hbig : MeasureTheory.IntegrableOn (fun r : ℝ => (r / (1 + r) ^ 2) ^ 2)
      (Set.Ioi 1) := by
    have hc : MeasureTheory.IntegrableOn (fun r : ℝ => r ^ (-2 : ℝ)) (Set.Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) (by norm_num : (0 : ℝ) < 1)
    have hmeas : AEStronglyMeasurable (fun r : ℝ => (r / (1 + r) ^ 2) ^ 2)
        (volume.restrict (Set.Ioi 1)) := by
      have hcont : ContinuousOn (fun r : ℝ => (r / (1 + r) ^ 2) ^ 2) (Set.Ioi 1) := by
        refine (ContinuousOn.div continuousOn_id (by fun_prop) ?_).pow 2
        intro r hr
        have h : (1 + r) ^ 2 ≠ 0 := by
          have hr1 : (0 : ℝ) < 1 + r := by have := Set.mem_Ioi.mp hr; linarith
          positivity
        exact h
      exact hcont.aestronglyMeasurable measurableSet_Ioi
    refine MeasureTheory.Integrable.mono hc hmeas ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
    have hr0 : (0 : ℝ) < r := lt_trans one_pos (Set.mem_Ioi.mp hr)
    have hbound : (r / (1 + r) ^ 2) ^ 2 ≤ r ^ (-2 : ℝ) := by
      rw [Real.rpow_neg hr0.le, Real.rpow_two]
      field_simp
      nlinarith [pow_pos hr0 2, pow_pos hr0 3, pow_pos hr0 4]
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hr0.le _)]
    exact hbound
  have hunion : Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi 1 = Set.Ioi 0 := by
    ext r
    constructor
    · rintro (h | h)
      · exact lt_of_lt_of_le (Set.mem_Ioc.mp h).1 (by norm_num)
      · exact lt_trans one_pos (Set.mem_Ioi.mp h)
    · intro h
      by_cases h1 : r ≤ 1
      · exact Or.inl ⟨h, h1⟩
      · exact Or.inr (lt_of_not_ge h1)
  have hf : MeasureTheory.IntegrableOn (fun r : ℝ => (r / (1 + r) ^ 2) ^ 2) (Set.Ioi 0) := by
    rw [← hunion]
    exact hsmall.union hbig
  have hint : MeasureTheory.Integrable (fun r : ℝ => ((r * Work.Spaces.w r)⁻¹) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    hf.congr (by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
      exact (Work.FTS.EllipticEst.Cert.w_inv_sq_eq r hr).symm)
  exact hint.2

/-- **`r ↦ F_*(F)(r)/r` is integrable on `(0,∞)`** for the data of `EllHyp`.  This is the
sibling `Work.FTS.EllipticEst.Cert.Fstar_div_integrable_of_EllHyp` with its `L¹`-ingredient
`∫ ((r·w(r))⁻¹)² < ∞` proved locally (`hasFiniteIntegralWInvSq_self`). -/
theorem integrableOn_Fstar_div_self (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ) (hα : 0 < α)
    (hHyp : Work.FTS.EllipticEst.EllHyp α k F Ψ) :
    MeasureTheory.IntegrableOn (fun r : ℝ => Work.Elliptic.Fstar F r / r) (Set.Ioi 0) := by
  have hsm : Work.Spaces.SmoothNbhd Ψ := hHyp.smoothNbhd
  have hsol : Work.Elliptic.IsBslSol α F Ψ := hHyp.sol
  have hmem : Work.Spaces.HkMem α k F := hHyp.memF
  have hIθ_meas : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hVne : (volume Work.Spaces.Iθ : ℝ≥0∞) ≠ ⊤ := by
    rw [show Work.Spaces.Iθ = Set.Icc 0 (π / 2) from rfl, Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  have hVlt : (volume Work.Spaces.Iθ : ℝ≥0∞) < ⊤ := lt_top_iff_ne_top.mpr hVne
  have hAESM : AEStronglyMeasurable (fun r : ℝ => Work.Elliptic.Fstar F r / r)
      (volume.restrict (Set.Ioi 0)) :=
    aestronglyMeasurable_iff_aemeasurable.mpr
      ((Work.FTS.EllipticEst.Cert.aesm_Fstar α F Ψ hsm hsol).aemeasurable.div
        measurable_id.aemeasurable)
  refine ⟨hAESM, ?_⟩
  show (∫⁻ r in Set.Ioi 0, ‖Work.Elliptic.Fstar F r / r‖ₑ) < ∞
  set XX : ℝ → ℝ≥0∞ := fun r => ∫⁻ θ in Work.Spaces.Iθ,
      ‖F r θ * Work.Elliptic.sinCos2 θ‖ₑ * (‖r‖ₑ)⁻¹ with hXX
  set AA : ℝ → ℝ≥0∞ := fun r => ∫⁻ θ in Work.Spaces.Iθ,
      ENNReal.ofReal ((F r θ * (Work.Spaces.w r / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
    with hAA
  set BB : ℝ → ℝ≥0∞ := fun r => ENNReal.ofReal (((r * Work.Spaces.w r)⁻¹) ^ 2)
    * volume Work.Spaces.Iθ with hBB
  have hstep1 : (∫⁻ r in Set.Ioi 0, ‖Work.Elliptic.Fstar F r / r‖ₑ)
      ≤ ∫⁻ r in Set.Ioi 0, XX r := by
    refine lintegral_mono_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
    have hdiv : ‖Work.Elliptic.Fstar F r / r‖ₑ = ‖Work.Elliptic.Fstar F r‖ₑ * (‖r‖ₑ)⁻¹ := by
      have hrn : |r| = r := abs_of_pos hr
      have h1 : ‖Work.Elliptic.Fstar F r / r‖ₑ
          = ENNReal.ofReal (|Work.Elliptic.Fstar F r| / r) := by
        rw [Real.enorm_eq_ofReal_abs, abs_div, hrn]
      have h2 : ENNReal.ofReal (|Work.Elliptic.Fstar F r| / r)
          = ‖Work.Elliptic.Fstar F r‖ₑ * (‖r‖ₑ)⁻¹ := by
        have hnormr : (‖r‖ₑ : ℝ≥0∞) = ENNReal.ofReal r := by
          rw [Real.enorm_eq_ofReal_abs, abs_of_pos hr]
        rw [ENNReal.ofReal_div_of_pos hr, div_eq_mul_inv, hnormr, Real.enorm_eq_ofReal_abs]
      rw [h1, h2]
    calc ‖Work.Elliptic.Fstar F r / r‖ₑ
        = ‖Work.Elliptic.Fstar F r‖ₑ * (‖r‖ₑ)⁻¹ := hdiv
      _ ≤ (∫⁻ θ in Work.Spaces.Iθ, ‖F r θ * Work.Elliptic.sinCos2 θ‖ₑ) * (‖r‖ₑ)⁻¹ :=
          mul_le_mul_of_nonneg_right
            (MeasureTheory.enorm_integral_le_lintegral_enorm _) zero_le
      _ ≤ ∫⁻ θ in Work.Spaces.Iθ, ‖F r θ * Work.Elliptic.sinCos2 θ‖ₑ * (‖r‖ₑ)⁻¹ :=
          MeasureTheory.lintegral_mul_const_le _ _
      _ = XX r := by rw [hXX]
  have hstep2 : ∫⁻ r in Set.Ioi 0, XX r ≤ ∫⁻ r in Set.Ioi 0, (AA r + BB r) := by
    refine lintegral_mono_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
    have hsplit : (∫⁻ θ in Work.Spaces.Iθ,
          (ENNReal.ofReal ((F r θ * (Work.Spaces.w r /
              (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
            + ENNReal.ofReal (((r * Work.Spaces.w r)⁻¹) ^ 2)))
        = AA r + BB r := by
      rw [hAA, hBB]
      rw [MeasureTheory.lintegral_add_right' _
        (aemeasurable_const :
          AEMeasurable (fun _ : ℝ => ENNReal.ofReal (((r * Work.Spaces.w r)⁻¹) ^ 2))
            (volume.restrict Work.Spaces.Iθ))]
      rw [MeasureTheory.lintegral_const, Measure.restrict_apply_univ]
    rw [hXX, ← hsplit]
    refine lintegral_mono_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem hIθ_meas] with θ hθ
    exact Work.FTS.EllipticEst.Cert.enorm_step (F r θ) r hr hθ
  have hBB_aem : AEMeasurable BB (volume.restrict (Set.Ioi 0)) := by
    have hcont : ContinuousOn (fun r : ℝ => ENNReal.ofReal ((r / (1 + r) ^ 2) ^ 2))
        (Set.Ioi 0) :=
      ENNReal.continuous_ofReal.comp_continuousOn (by
        refine (ContinuousOn.div ?_ ?_ ?_).pow 2
        · exact continuousOn_id
        · fun_prop
        · intro r hr
          have hr' : (0 : ℝ) < r := Set.mem_Ioi.mp hr
          positivity)
    have h1 : AEMeasurable (fun r : ℝ => ENNReal.ofReal ((r / (1 + r) ^ 2) ^ 2))
        (volume.restrict (Set.Ioi 0)) := hcont.aemeasurable measurableSet_Ioi
    have h2 : AEMeasurable (fun r : ℝ => ENNReal.ofReal ((r / (1 + r) ^ 2) ^ 2)
        * volume Work.Spaces.Iθ) (volume.restrict (Set.Ioi 0)) := h1.mul_const _
    have h2' : AEStronglyMeasurable (fun r : ℝ => ENNReal.ofReal ((r / (1 + r) ^ 2) ^ 2)
        * volume Work.Spaces.Iθ) (volume.restrict (Set.Ioi 0)) :=
      aestronglyMeasurable_iff_aemeasurable.mpr h2
    have h3 : AEStronglyMeasurable BB (volume.restrict (Set.Ioi 0)) := by
      refine h2'.congr ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
      show ENNReal.ofReal ((r / (1 + r) ^ 2) ^ 2) * volume Work.Spaces.Iθ
        = ENNReal.ofReal (((r * Work.Spaces.w r)⁻¹) ^ 2) * volume Work.Spaces.Iθ
      rw [Work.FTS.EllipticEst.Cert.w_inv_sq_eq r hr]
    exact h3.aemeasurable
  have hstep3 : ∫⁻ r in Set.Ioi 0, (AA r + BB r)
      = (∫⁻ r in Set.Ioi 0, AA r) + (∫⁻ r in Set.Ioi 0, BB r) :=
    MeasureTheory.lintegral_add_right' _ hBB_aem
  have hAfin : (∫⁻ r in Set.Ioi 0, AA r) < ⊤ := by
    have h1 : ∫⁻ r in Set.Ioi 0, AA r
        ≤ ∫⁻ r in Set.Ioi 0, ∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal (Work.Spaces.HkIntegrand α k F r θ) := by
      rw [hAA]
      refine lintegral_mono fun r => lintegral_mono fun θ => ?_
      exact ENNReal.ofReal_le_ofReal
        (Work.Spaces.sq_le_HkIntegrand_z α k F r θ 0 (Nat.zero_le k))
    have h2 : ∫⁻ r in Set.Ioi 0, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α k F r θ)
        = ∫⁻ r in Set.Ioi 0,
            ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F r θ) := by
      refine lintegral_congr_ae ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
      refine (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
        (hmem.1 r (show r ∈ Work.Spaces.Iz from le_of_lt (Set.mem_Ioi.mp hr)))
        (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k F r θ)).symm
    have h3 : ∫⁻ r in Set.Ioi 0,
          ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F r θ)
        ≤ ∫⁻ r in Work.Spaces.Iz,
            ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F r θ) :=
      lintegral_mono_set
        (by intro x hx; exact show x ∈ Work.Spaces.Iz from le_of_lt (Set.mem_Ioi.mp hx))
    have h4 : (∫⁻ r in Work.Spaces.Iz,
          ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F r θ)) < ⊤ := by
      have heq : (fun r : ℝ => ENNReal.ofReal
            (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F r θ))
          = fun r : ℝ => ‖(∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F r θ)‖ₑ := by
        funext r
        rw [Real.enorm_eq_ofReal_abs,
          abs_of_nonneg (integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k F r θ)]
      rw [heq]
      exact hmem.2.2
    have h23 : (∫⁻ r in Set.Ioi 0, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α k F r θ))
        ≤ ∫⁻ r in Work.Spaces.Iz,
            ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F r θ) :=
      h2.le.trans h3
    exact lt_of_le_of_lt (h1.trans h23) h4
  have hBfin : (∫⁻ r in Set.Ioi 0, BB r) < ⊤ := by
    have h1 : ∫⁻ r in Set.Ioi 0, BB r
        = (∫⁻ r in Set.Ioi 0, ENNReal.ofReal (((r * Work.Spaces.w r)⁻¹) ^ 2))
          * volume Work.Spaces.Iθ := by
      show (∫⁻ r in Set.Ioi 0, ENNReal.ofReal (((r * Work.Spaces.w r)⁻¹) ^ 2)
            * volume Work.Spaces.Iθ)
          = (∫⁻ r in Set.Ioi 0, ENNReal.ofReal (((r * Work.Spaces.w r)⁻¹) ^ 2))
            * volume Work.Spaces.Iθ
      exact MeasureTheory.lintegral_mul_const' _ _ hVne
    have h2 : (∫⁻ r in Set.Ioi 0, ENNReal.ofReal (((r * Work.Spaces.w r)⁻¹) ^ 2)) < ⊤ := by
      have heq : (fun r : ℝ => ENNReal.ofReal (((r * Work.Spaces.w r)⁻¹) ^ 2))
          = fun r : ℝ => ‖((r * Work.Spaces.w r)⁻¹) ^ 2‖ₑ := by
        funext r
        rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (sq_nonneg _)]
      rw [heq]
      exact hasFiniteIntegralWInvSq_self
    rw [h1]
    exact ENNReal.mul_lt_top h2 hVlt
  calc (∫⁻ r in Set.Ioi 0, ‖Work.Elliptic.Fstar F r / r‖ₑ)
      ≤ ∫⁻ r in Set.Ioi 0, XX r := hstep1
    _ ≤ ∫⁻ r in Set.Ioi 0, (AA r + BB r) := hstep2
    _ = (∫⁻ r in Set.Ioi 0, AA r) + (∫⁻ r in Set.Ioi 0, BB r) := hstep3
    _ < ⊤ := ENNReal.add_lt_top.mpr ⟨hAfin, hBfin⟩

/-! ## The moment identity -/

theorem L12_moment_eq (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ) (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (h : Work.FTS.EllipticEst.EllHyp α k F Ψ) :
    ∀ z : ℝ, 0 < z →
      Work.Elliptic.L12 F z
        = 15 * α * Work.Elliptic.Fstar Ψ z
          + 3 * α ^ 2 * Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) z := by
  set K : ℝ → ℝ := Work.Elliptic.L12 F
    - (fun z => 15 * α * Work.Elliptic.Fstar Ψ z
      + 3 * α ^ 2 * Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) z) with hK
  -- the derivative of `L₁₂(F)`
  have hL12 : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (Work.Elliptic.L12 F) (-(3 * Work.Elliptic.Fstar F z / z)) z :=
    hasDerivAt_L12_of_cont F (continuousOn_Fstar_of_EllHyp α k F Ψ hα h)
      (integrableOn_Fstar_div_self α k F Ψ hα h)
  -- the derivative of the right-hand side, which is the same
  have hR : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun w => 15 * α * Work.Elliptic.Fstar Ψ w
          + 3 * α ^ 2 * Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) w)
        (-(3 * Work.Elliptic.Fstar F z / z)) z :=
    hasDerivAt_moment_rhs α k F Ψ hα h
  -- hence `K` has vanishing derivative on `(0,∞)`
  have hKd : ∀ z ∈ Set.Ioi (0 : ℝ), deriv K z = 0 := by
    intro z hz
    rw [hK]
    simpa only [sub_self] using ((hL12 z hz).sub (hR z hz)).deriv
  -- so `K` is constant on `(0,∞)`
  have hKconst : ∀ a ∈ Set.Ioi (0 : ℝ), ∀ b ∈ Set.Ioi (0 : ℝ), K a = K b := by
    intro a ha b hb
    refine IsOpen.is_const_of_deriv_eq_zero (𝕜 := ℝ) isOpen_Ioi isPreconnected_Ioi ?_ ?_ ha hb
    · intro w hw
      exact ((hL12 w hw).sub (hR w hw)).differentiableAt.differentiableWithinAt
    · intro w hw
      exact hKd w hw
  -- `L₁₂(F) → 0` at infinity
  have hL12tend : Filter.Tendsto (Work.Elliptic.L12 F) Filter.atTop (nhds 0) :=
    tendsto_L12_atTop F (integrableOn_Fstar_div_self α k F Ψ hα h)
  -- the right-hand side is square integrable, hence vanishes along a sequence to infinity
  have hH2 : MeasureTheory.IntegrableOn
      (fun z : ℝ => (15 * α * Work.Elliptic.Fstar Ψ z
        + 3 * α ^ 2 * Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) z) ^ 2) (Set.Ioi 0) :=
    integrableOn_moment_rhs_sq α k F Ψ hα h
  obtain ⟨u, hu, hu2⟩ := seq_tendsto_zero_of_integrableOn hH2
  have hHtend : Filter.Tendsto (fun j : ℕ => 15 * α * Work.Elliptic.Fstar Ψ (u j)
      + 3 * α ^ 2 * Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) (u j)) Filter.atTop
      (nhds 0) := by
    have hsqrt : Filter.Tendsto
        (fun j : ℕ => Real.sqrt ((15 * α * Work.Elliptic.Fstar Ψ (u j)
          + 3 * α ^ 2 * Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) (u j)) ^ 2))
        Filter.atTop (nhds 0) := by
      have h' := Real.continuous_sqrt.continuousAt.tendsto.comp hu2
      simpa only [Function.comp_def, Real.sqrt_zero] using h'
    refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
    have hfun : (fun j : ℕ => ‖(15 * α * Work.Elliptic.Fstar Ψ (u j)
          + 3 * α ^ 2 * Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) (u j)) - 0‖)
        = fun j : ℕ => Real.sqrt ((15 * α * Work.Elliptic.Fstar Ψ (u j)
          + 3 * α ^ 2 * Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) (u j)) ^ 2) := by
      funext j
      rw [sub_zero, Real.norm_eq_abs, Real.sqrt_sq_eq_abs]
    rw [hfun]
    exact hsqrt
  -- evaluate `K` along the sequence and let `j → ∞`
  have hKlim : Filter.Tendsto (fun j : ℕ => K (u j)) Filter.atTop (nhds 0) := by
    have hsub : Filter.Tendsto (fun j : ℕ => Work.Elliptic.L12 F (u j)
        - (15 * α * Work.Elliptic.Fstar Ψ (u j)
          + 3 * α ^ 2 * Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) (u j))) Filter.atTop
        (nhds 0) := by
      have h' := (hL12tend.comp hu).sub hHtend
      simpa only [Function.comp_def, sub_zero] using h'
    rw [hK]
    exact hsub
  intro z hz
  have hzeq : K z = 0 := by
    have hu_pos : ∀ᶠ j : ℕ in Filter.atTop, 0 < u j := hu.eventually (eventually_gt_atTop 0)
    have hconst : ∀ᶠ j : ℕ in Filter.atTop, K (u j) = K z := by
      filter_upwards [hu_pos] with j hj
      exact hKconst (u j) hj z hz
    exact tendsto_nhds_unique (tendsto_nhds_of_eventually_eq hconst) hKlim
  rw [hK] at hzeq
  have hz' : Work.Elliptic.L12 F z
      - (15 * α * Work.Elliptic.Fstar Ψ z
        + 3 * α ^ 2 * Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) z) = 0 := by
    simpa only [Pi.sub_apply] using hzeq
  linarith

end Work.FTS.EllipticEst.Cert.L12Aux
