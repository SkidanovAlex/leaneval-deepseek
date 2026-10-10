/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.Genus
-/
import Mathlib
import Submission.Work.Genus.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The Frobenius descent of the genus chapter

In characteristic `p` a non-constant `𝔽(t)`-point of a Weierstrass curve may be *inseparable*: the
coordinates can be `p`-th powers.  The Riemann–Hurwitz argument of `Work.Genus.Analysis` only gives
`deriv x = 0`, so in characteristic `p` one has to descend along the Frobenius: if `x = X ^ p` and
`y = Y ^ p` then `(X, Y)` is a `𝔽(t)`-point of the **`p`-th root twist**

  `E^{(1/p)} : v² + a₁^{1/p} u v + a₃^{1/p} v = u³ + a₂^{1/p} u² + a₄^{1/p} u + a₆^{1/p}`

(over a perfect field, where the `p`-th roots of the coefficients exist), which is again
non-singular (`rootTwist_Δ`), and the "size" of the point (the degree of the numerator and
denominator of `x`) strictly decreases.  Iterating kills the inseparability.

This file defines the twist (`Work.Genus.rootTwist`) and its basic API.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open Polynomial

namespace Work.Genus

noncomputable section

variable {F : Type*} [Field F] {p : ℕ} [ExpChar F p] [PerfectRing F p]

/-- **The `p`-th root twist `E^{(1/p)}`** of a Weierstrass curve over a perfect field of
characteristic `p`: the curve whose `aᵢ` are `p`-th roots of the `aᵢ` of `E` (chosen with
`Classical.choose` from the surjectivity of the Frobenius). -/
noncomputable def rootTwist (E : WeierstrassCurve F) : WeierstrassCurve F :=
  ⟨Classical.choose ((PerfectRing.bijective_frobenius (R := F) (p := p)).2 E.a₁),
    Classical.choose ((PerfectRing.bijective_frobenius (R := F) (p := p)).2 E.a₂),
    Classical.choose ((PerfectRing.bijective_frobenius (R := F) (p := p)).2 E.a₃),
    Classical.choose ((PerfectRing.bijective_frobenius (R := F) (p := p)).2 E.a₄),
    Classical.choose ((PerfectRing.bijective_frobenius (R := F) (p := p)).2 E.a₆)⟩

@[simp]
theorem rootTwist_a₁ (E : WeierstrassCurve F) : (rootTwist (p := p) E).a₁ ^ p = E.a₁ :=
  Classical.choose_spec ((PerfectRing.bijective_frobenius (R := F) (p := p)).2 E.a₁)

@[simp]
theorem rootTwist_a₂ (E : WeierstrassCurve F) : (rootTwist (p := p) E).a₂ ^ p = E.a₂ :=
  Classical.choose_spec ((PerfectRing.bijective_frobenius (R := F) (p := p)).2 E.a₂)

@[simp]
theorem rootTwist_a₃ (E : WeierstrassCurve F) : (rootTwist (p := p) E).a₃ ^ p = E.a₃ :=
  Classical.choose_spec ((PerfectRing.bijective_frobenius (R := F) (p := p)).2 E.a₃)

@[simp]
theorem rootTwist_a₄ (E : WeierstrassCurve F) : (rootTwist (p := p) E).a₄ ^ p = E.a₄ :=
  Classical.choose_spec ((PerfectRing.bijective_frobenius (R := F) (p := p)).2 E.a₄)

@[simp]
theorem rootTwist_a₆ (E : WeierstrassCurve F) : (rootTwist (p := p) E).a₆ ^ p = E.a₆ :=
  Classical.choose_spec ((PerfectRing.bijective_frobenius (R := F) (p := p)).2 E.a₆)

end

end Work.Genus
