/-
# `Work.FTS.H2.ModalSolR.RGWeak` — auxiliary definitions for `radGreenWeakOdeMeas`

This file collects the notation shared by the pieces of the proof of

```
∫_{z>0} radGreen α m c z · (L ψ)(z) · z^((5-α)/α)
  + λ_m · ∫_{z>0} radGreen α m c z · ψ z · z^((5-α)/α) = ∫_{z>0} c z · ψ z · z^((5-α)/α)
```

where `L ψ = -(α²z²ψ'' + α(5+α)zψ')` and `λ_m = 2m(2m+5)`.  The weight `z^((5-α)/α)` is
exactly the one making `L` formally self-adjoint, and `radGreen` is the explicit Green
function

```
radGreen α m c z = 1/(α(4m+5)) · ( z^{s⁻} ∫₀^z srcM + z^{s⁺} ∫_z^∞ srcP )
```

with `srcM α m c t = c t · t^{(2m+5)/α - 1}`, `srcP α m c t = c t · t^{-2m/α - 1}`,
`s⁻ = -(2m+5)/α`, `s⁺ = 2m/α` (see `Radial/Defs.lean` and `RGW/Defs.lean`).

The key object here is the antiderivative of the Lagrange integrand with `v = z^s`:

`Fgen α s ψ z = pwt α z · (z^s ψ'(z) − s z^{s−1} ψ(z))`, whose derivative is
`−(z^s · (wgt · L ψ) + λ_m · z^s wgt ψ)` whenever `s` solves the indicial equation
`α²s² + 5αs = λ_m` (this is `Fgen_hasDerivAt`, an immediate consequence of
`RGW.hasDerivAt_lagrange` and `RGW.Lneg_rpow`).
-/
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.PhiStar.Radial.Defs
import Submission.Work.EllipticEst.ModalSolution.RGW.Defs
import Submission.Work.EllipticEst.ModalSolution.RGW.lagrange_ibp
import Submission.Work.EllipticEst.ModalSolution.RGW.Lneg_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.ModalSolR.RGWeak

open Work.EllipticEst.ModalSolution.RadGreenWeak

/-- `Fgen α s ψ z = pwt α z · (z^s ψ'(z) − s z^{s−1} ψ(z))` — the (negated) antiderivative
produced by the Lagrange identity with `v = z^s`. -/
def Fgen (α : ℝ) (s : ℝ) (ψ : ℝ → ℝ) (z : ℝ) : ℝ :=
  pwt α z * (z ^ s * deriv ψ z - s * z ^ (s - 1) * ψ z)

/-- `Fgen` vanishes where `ψ` and `ψ'` do. -/
theorem Fgen_eq_zero {α s : ℝ} {ψ : ℝ → ℝ} {z : ℝ} (h0 : ψ z = 0) (h1 : deriv ψ z = 0) :
    Fgen α s ψ z = 0 := by
  simp only [Fgen, h0, h1, mul_zero, sub_zero, mul_zero]

/-- The decaying indicial exponent `s⁻ = -(2m+5)/α` solves `α²s² + 5αs = λ_m`. -/
theorem indicial_sM {α : ℝ} (hα : α ≠ 0) (m : ℕ) :
    α ^ 2 * sM α m ^ 2 + 5 * α * sM α m = Work.FTS.PhiStar.Radial.lamR m := by
  simp only [sM, Work.FTS.PhiStar.Radial.lamR]
  field_simp <;> ring

/-- The growing indicial exponent `s⁺ = 2m/α` solves `α²s² + 5αs = λ_m`. -/
theorem indicial_sP {α : ℝ} (hα : α ≠ 0) (m : ℕ) :
    α ^ 2 * sP α m ^ 2 + 5 * α * sP α m = Work.FTS.PhiStar.Radial.lamR m := by
  simp only [sP, Work.FTS.PhiStar.Radial.lamR]
  field_simp <;> ring

/-- **The derivative of `Fgen`.**  If `s` solves the indicial equation `α²s² + 5αs = λ_m`, then
`(Fgen α s ψ)' = -(z^s (wgt · L ψ) + λ_m z^s wgt ψ)`, i.e. the Lagrange identity for `v = z^s`
reads `z^s · wgt · L ψ = - λ_m z^s wgt ψ - (Fgen α s ψ)'`. -/
theorem Fgen_hasDerivAt {α : ℝ} (hα : 0 < α) {m : ℕ} {s : ℝ}
    (hs : α ^ 2 * s ^ 2 + 5 * α * s = Work.FTS.PhiStar.Radial.lamR m)
    {ψ : ℝ → ℝ} (hψ : ContDiffOn ℝ 2 ψ (Set.Ioi 0)) :
    ∀ z : ℝ, 0 < z →
      HasDerivAt (Fgen α s ψ)
        (-(z ^ s * (wgt α z * Lneg α ψ z)
            + Work.FTS.PhiStar.Radial.lamR m * (z ^ s * wgt α z * ψ z))) z := by
  intro z hz
  have hv : ContDiffOn ℝ 2 (fun t : ℝ => t ^ s) (Set.Ioi 0) := fun t ht =>
    (Real.contDiffAt_rpow_const (p := s) (n := 2) (Or.inl (ne_of_gt ht))).contDiffWithinAt
  have h := Work.EllipticEst.ModalSolution.RGW.hasDerivAt_lagrange α hv hψ z hz
  have hfun : (fun y => pwt α y * (deriv (fun t : ℝ => t ^ s) y * ψ y - y ^ s * deriv ψ y))
      = fun y => - Fgen α s ψ y := by
    funext y
    simp only [Fgen, Real.deriv_rpow_const]
    ring
  rw [hfun] at h
  have hL : Lneg α (fun t : ℝ => t ^ s) z = - Work.FTS.PhiStar.Radial.lamR m * z ^ s :=
    Work.EllipticEst.ModalSolution.RGW.Lneg_rpow α m hz hs
  rw [hL] at h
  have h2 : HasDerivAt (Fgen α s ψ)
      (-(((z ^ s * Lneg α ψ z - (-(Work.FTS.PhiStar.Radial.lamR m) * z ^ s) * ψ z)
        * wgt α z))) z :=
    h.neg.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun y => by simp))
  exact h2.congr_deriv (by ring)

/-- A set integral over `Ioi 0` of a function vanishing off `(a,b)` (with `0 < a`) is the
interval integral over `[a,b]`. -/
theorem integral_Ioi_eq_intervalIntegral {f : ℝ → ℝ} {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hf : ∀ z : ℝ, z ∉ Set.Ioo a b → f z = 0) :
    ∫ z in Set.Ioi 0, f z = ∫ z in a..b, f z := by
  have h1 : ∫ z in Set.Ioi (0 : ℝ), f z = ∫ z in Set.Ioo a b, f z :=
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (fun z hz => by simp only [mem_Ioo] at hz ⊢; exact lt_trans ha hz.1)
      (fun z hz => hf z hz.2)
  rw [h1, intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo]

end Work.FTS.H2.ModalSolR.RGWeak
