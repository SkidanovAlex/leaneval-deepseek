/-
# `Transfer/hasDerivAt_radA.lean` — the derivative of the radial transfer profile

The transfer defect of `𝓛_Γ^T` is `Corr α f = Γ(θ)·radA α f (z)` (`Corr_eq_radA`), where

  `radA α f z = −a(z)·L₁₂(f)(z) + (b(z)/c)·L₁₂(Transport f)(0)`,  `a(z) = 2z/(c(1+z)²)`,
  `b(z) = 2z²/(1+z)³`,

so its `z`-derivative is again an angular factor times a *radial* factor.  The point of the
lemma below is that this radial factor is **exactly** the profile `radS` of
`Transfer/Profiles.lean`:

  `deriv (radA α f) z = radS α f z / z`  for `0 < z`,

i.e. `D_z (Corr α f) = Γ(θ)·radS α f z`.  This is the second of the two identities that drive
the transfer; the middle term of `radS` is `−a(z)·z·(L₁₂ f)'(z)`, and it is *this* term that
`Transfer.L12_deriv_eq` rewrites as an angular moment `−⟨K, f(z,·)⟩` (rather than as an `L₁₂`
of a differentiated datum — the whole point of design `N45_DESIGN_LEAD.md` §5 T2).

## Proof

Both `z`-factors are elementary rational functions: `ampA` is differentiable at `z > 0`
(the only way its denominator `c·(1+z)²` can vanish at `z > 0` is `c = 0`, and then the
function is identically `0`), `ampB` likewise, and `L₁₂ f` is differentiable at `z > 0` by
`FM.hasDerivAt_L12` applied to the `hint`/`hcont` fields of `HardyHyp`.  Differentiating the
two-summand expression for `radA` gives

  `−a'(z)·L₁₂ f z − a(z)·(L₁₂ f)'(z) + (b'(z)/c)·L₁₂(Transport f)(0)`,

and multiplying `radS α f z` by `z` (legitimate since `z ≠ 0`) turns
`−dAmpA·L − ampA·(z·L') + (dAmpB/c)·C₀` into `z` times the same expression, because
`dAmpA α z = z·a'(z)` and `dAmpB α z = z·b'(z)` by definition.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.CoercivityFix.Transfer.Profiles

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.CoercivityFix.Transfer

open Work.FTS.Galerkin (Fn)

/-- `ampA α` is differentiable at every `z > 0`.  If `c α = 0` the function is identically
`0` (division by the vanishing denominator); otherwise the denominator `c·(1+z)²` is nonzero
at `z > 0`. -/
lemma differentiableAt_ampA (α : ℝ) {z : ℝ} (hz : 0 < z) :
    DifferentiableAt ℝ (ampA α) z := by
  by_cases hc : Work.Spaces.c α = 0
  · have h0 : ampA α = fun _ : ℝ => 0 := by funext w; simp [ampA, hc]
    rw [h0]; exact differentiableAt_const 0
  · have hnum : DifferentiableAt ℝ (fun w : ℝ => 2 * w) z :=
      (differentiableAt_const (2 : ℝ)).mul differentiableAt_id
    have hden : DifferentiableAt ℝ (fun w : ℝ => Work.Spaces.c α * (1 + w) ^ 2) z :=
      (((differentiableAt_const (1 : ℝ)).add differentiableAt_id).pow 2).const_mul
        (Work.Spaces.c α)
    have hne : Work.Spaces.c α * (1 + z) ^ 2 ≠ 0 := by
      refine mul_ne_zero hc (pow_ne_zero 2 ?_)
      linarith
    exact hnum.div hden hne

/-- The derivative form of `differentiableAt_ampA`. -/
lemma hasDerivAt_ampA (α : ℝ) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (ampA α) (deriv (ampA α) z) z :=
  (differentiableAt_ampA α hz).hasDerivAt

/-- `ampB α` is differentiable at every `z > 0`. -/
lemma differentiableAt_ampB (α : ℝ) {z : ℝ} (hz : 0 < z) :
    DifferentiableAt ℝ (ampB α) z := by
  have hden : DifferentiableAt ℝ (fun w : ℝ => (1 + w) ^ 3) z :=
    ((differentiableAt_const (1 : ℝ)).add differentiableAt_id).pow 3
  have hnum : DifferentiableAt ℝ (fun w : ℝ => 2 * w ^ 2) z :=
    (differentiableAt_const (2 : ℝ)).mul (differentiableAt_id.pow 2)
  have hne : (1 + z) ^ 3 ≠ 0 := by
    refine pow_ne_zero 3 ?_
    linarith
  exact hnum.div hden hne

/-- The derivative form of `differentiableAt_ampB`. -/
lemma hasDerivAt_ampB (α : ℝ) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (ampB α) (deriv (ampB α) z) z :=
  (differentiableAt_ampB α hz).hasDerivAt

/-- The composite `z ↦ radA α f z` is differentiable at `z > 0`, with derivative the explicit
expression appearing in `hasDerivAt_radA`.  This is just the product/negation calculus on
`ampA`, `ampB` and `L₁₂ f`. -/
lemma hasDerivAt_radA_aux (α : ℝ) (f : Fn) (hfH : Work.Coercivity.HardyHyp f) {z : ℝ}
    (hz : 0 < z) :
    HasDerivAt (radA α f)
      (-(deriv (ampA α) z) * Work.Coercivity.L12f f z
        + (-ampA α z) * deriv (Work.Coercivity.L12f f) z
        + (deriv (ampB α) z / Work.Spaces.c α)
            * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0) z := by
  have hA : HasDerivAt (ampA α) (deriv (ampA α) z) z := hasDerivAt_ampA α hz
  have hB : HasDerivAt (ampB α) (deriv (ampB α) z) z := hasDerivAt_ampB α hz
  have hL : HasDerivAt (Work.Coercivity.L12f f)
      (-(Work.FM.L12dens Work.Spaces.K f z)) z :=
    Work.FM.hasDerivAt_L12 (K := Work.Spaces.K) (f := f) (a := 0) hfH.hint (hfH.hcont z hz) hz
  have hLd : HasDerivAt (Work.Coercivity.L12f f)
      (deriv (Work.Coercivity.L12f f) z) z := hL.differentiableAt.hasDerivAt
  have h1 : HasDerivAt (fun w => -ampA α w * Work.Coercivity.L12f f w)
      (-(deriv (ampA α) z) * Work.Coercivity.L12f f z
        + (-ampA α z) * deriv (Work.Coercivity.L12f f) z) z := hA.neg.mul hLd
  have h2 : HasDerivAt
      (fun w => (ampB α w / Work.Spaces.c α)
        * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0)
      ((deriv (ampB α) z / Work.Spaces.c α)
        * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0) z :=
    (hB.div_const (Work.Spaces.c α)).mul_const
      (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0)
  have h : HasDerivAt
      (fun w => -ampA α w * Work.Coercivity.L12f f w
        + (ampB α w / Work.Spaces.c α) * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0)
      (-(deriv (ampA α) z) * Work.Coercivity.L12f f z
        + (-ampA α z) * deriv (Work.Coercivity.L12f f) z
        + (deriv (ampB α) z / Work.Spaces.c α)
            * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0) z := h1.add h2
  exact h

/-- **The derivative of the radial profile `radA` is `radS` divided by `z`.**
For `f` with the Hardy hypotheses and `z > 0`,
`deriv (radA α f) z = radS α f z / z`.

Consequently `D_z (Corr α f) = Γ(θ)·radS α f z`, the `D_z`-defect of the transfer. -/
theorem hasDerivAt_radA (α : ℝ) (f : ℝ → ℝ → ℝ) (hfH : Work.Coercivity.HardyHyp f) {z : ℝ}
    (hz : 0 < z) :
    HasDerivAt (Work.FTS.CoercivityFix.Transfer.radA α f)
      (Work.FTS.CoercivityFix.Transfer.radS α f z / z) z := by
  have h := hasDerivAt_radA_aux α f hfH hz
  have hd : DifferentiableAt ℝ (radA α f) z := h.differentiableAt
  have hderiv : deriv (radA α f) z
      = -(deriv (ampA α) z) * Work.Coercivity.L12f f z
        + (-ampA α z) * deriv (Work.Coercivity.L12f f) z
        + (deriv (ampB α) z / Work.Spaces.c α)
            * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 := h.deriv
  have hval : radS α f z / z
      = -(deriv (ampA α) z) * Work.Coercivity.L12f f z
        + (-ampA α z) * deriv (Work.Coercivity.L12f f) z
        + (deriv (ampB α) z / Work.Spaces.c α)
            * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 := by
    rw [div_eq_iff (ne_of_gt hz)]
    simp only [radS, dAmpA, dAmpB]
    ring
  have hd' : HasDerivAt (radA α f) (deriv (radA α f) z) z := hd.hasDerivAt
  rw [hderiv] at hd'
  rwa [← hval] at hd'

end Work.FTS.CoercivityFix.Transfer
