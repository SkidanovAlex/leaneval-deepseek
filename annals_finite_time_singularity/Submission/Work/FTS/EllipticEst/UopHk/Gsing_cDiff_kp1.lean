import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Interval.Basic
import Mathlib.Tactic.Have
import Submission.Work.FTS.EllipticEst.UopHk.GsingFactsInterior

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.UopHk

open scoped Real Topology ContDiff Interval
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-!
# `Gsing` is `C^{k+1}` and `Gbar` is `C^k` for a source in the interior class `RegQ α k`

This module proves `Work.FTS.EllipticEst.UopHk.Gsing_cDiff_kp1`: for `0 < α ≤ 1`, `k ≥ 2` and
a source `F` in the interior class `RegQ α k F` (`C^∞` on the open quadrant, honest
weighted `ℋ^k`-membership, boundary traces),

* `Work.Elliptic.Gsing α F` is `C^{k+1}` on `(0,∞)`, and
* `Work.Elliptic.Gbar α F` is `C^k` on `(0,∞)`.

## The route

The two functions are

`Gsing = Gstar + Gbar`, `Gstar = -(1/(4α)) L₁₂(F)`, `Gbar z = -(3/(4α)) z^{-5/α} J(z)`,

with `L₁₂(F)(z) = 3∫_z^∞ F_*(r)/r dr` and `J(z) = ∫_0^z s^{(5-α)/α} F_*(s) ds`.

The single analytic input is the sharp interior regularity of the angular moment
`F_* = ∫_θ F sinθcos²θ dθ` supplied by `GsingFactsInterior`: `F_*` is `C^{k-1}` on `(0,∞)`, with
`deriv F_* = F_*(D_z F)/z`.  From it:

* the integrand `s ↦ s^{(5-α)/α} F_*(s)` of `J` is `C^{k-1}`, so `J ∈ C^k`
  (`contDiffOn_Jfun_k`; this is the sharp order — the monomial factor costs only the `1/s` of
  the exponent);
* `Gbar = Abar · J` with `Abar = -(3/(4α)) z^{-5/α}` smooth, hence `Gbar ∈ C^k`;
* the first integral of the ODE for `Gsing` is `α z ∂_z Gsing = -5 Gbar` (`Gsing_deriv_rel`),
  i.e. `∂_z Gsing = -5 Gbar/(α z)`, a `C^k` function on `(0,∞)`.  Since `Gsing` is
  differentiable at every `z > 0` with that derivative, the one-order-gain lemma
  `contDiffOn_succ_of_hasDerivAt` upgrades `Gsing` to `C^{k+1}`.

This is exactly one order more than `Gbar`: the extra order comes from the first-order relation
`α z ∂_z Gsing = -5 Gbar`, i.e. from the cancellation of the `F_*`-terms between `Gstar` and
`Gbar` (`Gsing` solves `α²z²y'' + α(5+α)zy' = (15/4)F_*`).
-/

/-- **The primitive `J(z) = ∫_0^z s^{(5-α)/α} F_*(s) ds` is `C^k`.**

`GsingFactsInterior` provides the cruder statement `ContDiffOn ℝ (k-1) (Jfun α F)`; here the
right order is recorded: the integrand `s^{(5-α)/α} F_*(s)` is `C^{k-1}`, so the primitive gains
exactly one order over it. -/
theorem contDiffOn_Jfun_k (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (hmem : Work.Spaces.HkMem α k F) (hk : 2 ≤ k) :
    ContDiffOn ℝ k (Work.Elliptic.Jfun α F) (Set.Ioi 0) := by
  have hk1 : 1 ≤ k := by omega
  have hFstar : ContDiffOn ℝ (k - 1) (Work.Elliptic.Fstar F) (Set.Ioi 0) :=
    contDiffOn_Fstar_of_smoothOpen_Hk α k F hF hmem hk1
  -- the integrand is `C^{k-1}`
  have hsm : ContDiffOn ℝ (k - 1)
      (fun s : ℝ => s ^ ((5 - α) / α) * Work.Elliptic.Fstar F s) (Set.Ioi 0) :=
    (ContDiffOn.rpow_const_of_ne contDiffOn_id (fun x hx => ne_of_gt hx)).mul hFstar
  -- interval integrability on `(0,z]` at every `z > 0`
  have hI : ∀ z ∈ Set.Ioi (0 : ℝ),
      IntervalIntegrable (fun s : ℝ => s ^ ((5 - α) / α) * Work.Elliptic.Fstar F s)
        volume 0 z := by
    intro z hz
    have hloc := (Work.FTS.EllipticEst.GbarSin.Fstar_local_integrableOn α k F hα hα1 hF hmem
      0 (Nat.zero_le k)).2 z hz
    refine hloc.congr ?_
    intro s hs
    have hpexp : s ^ ((5 - α) / α) = s ^ (5 / α - 1) := by
      rw [show (5 - α) / α = 5 / α - 1 by field_simp]
    show s ^ (5 / α - 1) * Work.Elliptic.Fstar F s
        = s ^ ((5 - α) / α) * Work.Elliptic.Fstar F s
    rw [hpexp]
  -- the derivative of the primitive is the integrand
  have hprim : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (Work.Elliptic.Jfun α F)
        (z ^ ((5 - α) / α) * Work.Elliptic.Fstar F z) z := by
    intro z hz
    exact intervalIntegral.integral_hasDerivAt_right (hI z hz)
      (hsm.continuousOn.stronglyMeasurableAtFilter isOpen_Ioi z hz)
      (hsm.continuousOn.continuousAt (isOpen_Ioi.mem_nhds hz))
  have h := contDiffOn_succ_of_hasDerivAt (m := k - 1) hprim hsm
  have hcast : ((k - 1 : ℕ) : ℕ∞ω) + 1 = ((k : ℕ) : ℕ∞ω) := by
    calc ((k - 1 : ℕ) : ℕ∞ω) + 1 = ((k - 1 + 1 : ℕ) : ℕ∞ω) := by
          rw [Nat.cast_add, Nat.cast_one]
      _ = ((k : ℕ) : ℕ∞ω) := by rw [Nat.sub_add_cancel hk1]
  simpa only [hcast] using h

/-- `Abar α` has derivative `DAbar α` at every `z > 0`. -/
theorem hasDerivAt_Abar_fts (α : ℝ) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (Work.Elliptic.Abar α) (Work.Elliptic.DAbar α z) z := by
  have hzne : z ≠ 0 := ne_of_gt hz
  have hp : HasDerivAt (fun y : ℝ => y ^ (-(5 / α)))
      ((-(5 / α)) * z ^ (-(5 / α) - 1)) z :=
    Real.hasDerivAt_rpow_const (Or.inl hzne)
  have h := hp.const_mul (-(3 / (4 * α)))
  convert h using 1
  · ext y; rfl
  · show (-(3 / (4 * α)) * (-(5 / α))) * z ^ (-(5 / α) - 1)
        = -(3 / (4 * α)) * (-(5 / α) * z ^ (-(5 / α) - 1))
    ring

theorem Gsing_cDiff_kp1 (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hk : 2 ≤ k) (hF : Work.FTS.Nonlin.RegQ α k F) :
    (∀ m : ℕ, m ≤ k + 1 → ContDiffOn ℝ m (Work.Elliptic.Gsing α F) (Set.Ioi 0)) ∧
    (∀ m : ℕ, m ≤ k → ContDiffOn ℝ m (Work.Elliptic.Gbar α F) (Set.Ioi 0)) := by
  have hk1 : 1 ≤ k := by omega
  have hFopen : Work.FTS.EllipticEst.SmoothOpen F := smoothOpen_of_smoothQuad hF.1
  have hmem : Work.Spaces.HkMem α k F := hF.2.1
  -- ## 1. the regularity input: `F_*` is `C^{k-1}` and its derivative data
  have hFstar : ContDiffOn ℝ (k - 1) (Work.Elliptic.Fstar F) (Set.Ioi 0) :=
    contDiffOn_Fstar_of_smoothOpen_Hk α k F hFopen hmem hk1
  have hFc : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (Work.Elliptic.Fstar F) (deriv (Work.Elliptic.Fstar F) z) z := by
    intro z hz
    have h1 : ContDiffOn ℝ 1 (Work.Elliptic.Fstar F) (Set.Ioi 0) := by
      have hle : ((1 : ℕ) : ℕ∞ω) ≤ ((k - 1 : ℕ) : ℕ∞ω) := by
        exact_mod_cast (by omega : 1 ≤ k - 1)
      exact hFstar.of_le hle
    exact ((h1.differentiableOn (by simp)).differentiableAt
      (isOpen_Ioi.mem_nhds hz)).hasDerivAt
  have hL12diff : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (Work.Elliptic.L12 F) (-(3 * Work.Elliptic.Fstar F z / z)) z :=
    (contDiffOn_L12_of_smoothOpen_Hk α k F hFopen hmem hk).2
  have hJdata := contDiffOn_Jfun_of_smoothOpen_Hk α k F hα hα1 hFopen hmem hk
  have hJ : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (Work.Elliptic.Jfun α F)
        (z ^ ((5 - α) / α) * Work.Elliptic.Fstar F z) z := by
    intro z hz
    have h := hJdata.2 z hz
    have hfun : (fun z' : ℝ => ∫ s in (0 : ℝ)..z',
        s ^ ((5 - α) / α) * Work.Elliptic.Fstar F s) = Work.Elliptic.Jfun α F := rfl
    rwa [hfun] at h
  -- ## 2. `Jfun` and `Gbar` are `C^k`
  have hJsm : ContDiffOn ℝ k (Work.Elliptic.Jfun α F) (Set.Ioi 0) :=
    contDiffOn_Jfun_k α k F hα hα1 hFopen hmem hk
  have hGbar : ContDiffOn ℝ k (Work.Elliptic.Gbar α F) (Set.Ioi 0) := by
    have hA : ContDiffOn ℝ k (Work.Elliptic.Abar α) (Set.Ioi 0) := by
      change ContDiffOn ℝ k (fun z : ℝ => -(3 / (4 * α)) * z ^ (-(5 / α))) (Set.Ioi 0)
      exact contDiffOn_const.mul
        (ContDiffOn.rpow_const_of_ne contDiffOn_id fun x hx => ne_of_gt hx)
    have hfun : (Work.Elliptic.Gbar α F)
        = fun z => Work.Elliptic.Abar α z * Work.Elliptic.Jfun α F z := rfl
    rw [hfun]
    exact hA.mul hJsm
  -- ## 3. the derivative of `Gsing` is the explicit `DGstar + DGbar`
  have hGsing_deriv : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (Work.Elliptic.Gsing α F)
        (Work.Elliptic.DGstar α F z + Work.Elliptic.DGbar α F z) z := by
    intro z hz
    have h1 : HasDerivAt (Work.Elliptic.Gstar α F) (Work.Elliptic.DGstar α F z) z := by
      have h := (hL12diff z hz).const_mul (-(1 / (4 * α)))
      have hfun : (fun y : ℝ => -(1 / (4 * α)) * Work.Elliptic.L12 F y)
          = Work.Elliptic.Gstar α F := rfl
      rw [hfun] at h
      simpa only [Work.Elliptic.DGstar] using h
    have h2 : HasDerivAt (Work.Elliptic.Gbar α F) (Work.Elliptic.DGbar α F z) z := by
      have h := (hasDerivAt_Abar_fts α hz).mul (hJ z hz)
      have hfun : (Work.Elliptic.Abar α * Work.Elliptic.Jfun α F)
          = Work.Elliptic.Gbar α F := rfl
      rw [hfun] at h
      simpa only [Work.Elliptic.DGbar] using h
    have h := h1.add h2
    have hfun : ((Work.Elliptic.Gstar α F) + (Work.Elliptic.Gbar α F))
        = Work.Elliptic.Gsing α F := rfl
    rw [hfun] at h
    exact h
  -- ## 4. the first integral of the ODE: `α z ∂_z Gsing = -5 Gbar`
  have hderiv_value : ∀ z ∈ Set.Ioi (0 : ℝ),
      Work.Elliptic.DGstar α F z + Work.Elliptic.DGbar α F z
        = -(5 * Work.Elliptic.Gbar α F z) / (α * z) := by
    intro z hz
    have h1 := (hGsing_deriv z hz).deriv
    have h2 := Work.FTS.EllipticEst.Gsing_deriv_rel α F hα hL12diff hFc hJ z hz
    have hαz : α * z ≠ 0 := mul_ne_zero (ne_of_gt hα) (ne_of_gt hz)
    rw [h1] at h2
    rw [eq_div_iff hαz]
    linarith [h2]
  -- ## 5. `∂_z Gsing = -5 Gbar/(α z)` is `C^k`, so `Gsing` is `C^{k+1}`
  have hg : ContDiffOn ℝ k (fun z : ℝ => -(5 * Work.Elliptic.Gbar α F z) / (α * z))
      (Set.Ioi 0) :=
    (contDiffOn_const.mul hGbar).neg.div (contDiffOn_const.mul contDiffOn_id)
      (fun z hz => mul_ne_zero (ne_of_gt hα) (ne_of_gt hz))
  have hGsing_succ : ContDiffOn ℝ (k + 1) (Work.Elliptic.Gsing α F) (Set.Ioi 0) :=
    contDiffOn_succ_of_hasDerivAt (m := k)
      (fun z hz => (hGsing_deriv z hz).congr_deriv (hderiv_value z hz)) hg
  exact ⟨fun m hm => hGsing_succ.of_le (by exact_mod_cast hm),
    fun m hm => hGbar.of_le (by exact_mod_cast hm)⟩

end Work.FTS.EllipticEst.UopHk
