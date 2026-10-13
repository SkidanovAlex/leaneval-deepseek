/-
# `∂_τ g = 0` in the far field: the perturbation does not move above the support radius

The perturbation `g = F - F_*` of the self-similar profile is only defined through the *full*
profile `F = F_* + g`, which `RegPkg'.hsupp` makes **compactly supported in `z`**: there is `L > 0`
with `F(z,θ,τ) = 0` for `z ≥ L` and `τ ∈ [0,S]`.

Above the support threshold the leading profile `F_*(z,θ) = Work.Construction.Fstar (3α) z θ` does
not depend on the fake time `τ`, so the perturbation is frozen:

  `g z θ τ = - F_*(z,θ)`  for all `τ ∈ [0,S]`, `z > L`.

Consequently `τ ↦ g z θ τ` is *constant on the strip `[0,S]`* for every `z > L`, and its derivative
vanishes at every point of the strip.  That is `Work.FTS.Regularity.dtgZero`:

  `∃ L > 0, ∀ z θ τ, L < z → θ ∈ Iθ → τ ∈ Icc 0 S → deriv (fun s => g z θ s) τ = 0`.

Note the difference with the `z`-analogue `Work.FTS.Regularity.dzProfFullZero`: there, `z > L`
places `z` in an *open* neighbourhood of the support threshold, so the function `z' ↦ F(z',θ,τ)` is
*eventually constant* and `Filter.EventuallyEq.deriv_eq` applies.  In fake time the point `τ` may be
an *endpoint* of the strip `[0,S]`, where the constancy controls the difference quotient only from
one side.  The correct statement at an endpoint is the general

  `deriv_eq_zero_of_const_on_Icc`: a function constant on `Icc a b` (`a < b`) has vanishing
  derivative at every point of `Icc a b`

— true because a differentiable function which is constant on a one-sided neighbourhood has
one-sided difference quotient `0`, while a function *not* differentiable at the point has
`deriv = 0` by the convention for `fderiv` of a non-differentiable function (Mathlib:
`deriv_zero_of_frequently_const`).  That general lemma — isolated for reuse, since the `τ`-variable
enters every transfer statement of this chapter and the endpoint case recurs there — is proved in
the sibling module `Submission.Work.FTS.Regularity.deriv_eq_zero_of_const_on_Icc`, which this file
imports; what remains is the reduction to constancy, and that is this file's content.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Submission.Work.FTS.Regularity.Defs
import Submission.Work.FTS.Regularity.deriv_eq_zero_of_const_on_Icc
import Submission.Work.FTS.RegPkgGal.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.FireFix.Prime

open Work.FTS.Regularity Work.FTS.RegPkgGal

theorem dtgZero {α S : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (h : RegPkg' α S A B g) :
    ∃ L : ℝ, 0 < L ∧ ∀ z θ τ : ℝ, L < z → θ ∈ Work.Spaces.Iθ → τ ∈ Set.Icc 0 S →
      deriv (fun s => g z θ s) τ = 0 := by
  obtain ⟨L, hLpos, hL⟩ := h.hsupp
  refine ⟨L, hLpos, fun z θ τ hz _ hτ => ?_⟩
  -- The full profile vanishes at every time of the strip above the support radius `L`, and the
  -- leading profile `F_*` is time-independent, so `s ↦ g z θ s` is constant on `[0,S]`.
  refine deriv_eq_zero_of_const_on_Icc h.hS ?_ τ hτ
  intro s hs t ht
  have h1 : Work.Construction.Fstar (pExp α) z θ + g z θ s = 0 := hL s hs z θ hz.le
  have h2 : Work.Construction.Fstar (pExp α) z θ + g z θ t = 0 := hL t ht z θ hz.le
  linarith

end Work.FTS.FireFix.Prime
