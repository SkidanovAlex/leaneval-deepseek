/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.Genus
-/
import Mathlib
import Submission.Work.Genus.Main.exists_algebraMap_of_weierstrass
import Submission.Work.PointlessTwist.FunctionField

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `ConstantsOnly` for the concrete constant curve: `E(𝔽(t)) = E(𝔽)`

This file contains the *glue* that turns the algebraic theorem
`Work.Genus.Main.exists_algebraMap_of_weierstrass` (a solution of a Weierstrass equation over `𝔽(t)`
has constant coordinates) into the named statement

  `Work.PointlessTwist.ConstantsOnly 𝔽 E (RatFunc 𝔽)`   (`E(𝔽(t)) = E(𝔽)`),

the classical input of classes (b), (c), (d) of Lin–Shinder Theorem 1.2 (1) and the exact datum the
`PointlessTwist` chain consumes: *there is no non-constant morphism `ℙ¹ → E`*.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open WeierstrassCurve WeierstrassCurve.Affine

namespace Work.Genus

noncomputable section

variable {F : Type} [Field F]

/-- **`E(𝔽(t)) = E(𝔽)`.**  Every point of the base change of a non-singular Weierstrass curve `E/𝔽`
to the rational function field `𝔽(t)` is the base change of a point of `E`. -/
theorem constantsOnly_ratFunc [CharZero F] [DecidableEq F] (E : WeierstrassCurve F) (hΔ : E.Δ ≠ 0) :
    @Work.PointlessTwist.ConstantsOnly F _ ‹DecidableEq F› E (RatFunc F) _
      (Classical.decEq (RatFunc F)) _ := by
  classical
  intro R
  rcases R with _ | ⟨x, y, hns⟩
  · exact ⟨0, WeierstrassCurve.Affine.Point.map_zero (W' := E) (f := Algebra.ofId F (RatFunc F))⟩
  · have heq : y ^ 2 + algebraMap F (RatFunc F) E.a₁ * x * y + algebraMap F (RatFunc F) E.a₃ * y
        = x ^ 3 + algebraMap F (RatFunc F) E.a₂ * x ^ 2 + algebraMap F (RatFunc F) E.a₄ * x
          + algebraMap F (RatFunc F) E.a₆ := by
      have h1 := (WeierstrassCurve.Affine.equation_iff (W := E.baseChange (RatFunc F)) x y).mp
        hns.1
      simpa only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
        WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆,
        Algebra.ofId_apply] using h1
    obtain ⟨⟨x₀, hx₀⟩, ⟨y₀, hy₀⟩⟩ := Work.Genus.Main.exists_algebraMap_of_weierstrass E hΔ heq
    have hns' : WeierstrassCurve.Affine.Nonsingular (E.baseChange (RatFunc F))
        (algebraMap F (RatFunc F) x₀) (algebraMap F (RatFunc F) y₀) := by
      rw [← hx₀, ← hy₀]; exact hns
    have hq : WeierstrassCurve.Affine.Nonsingular (E.baseChange F) x₀ y₀ :=
      (WeierstrassCurve.Affine.baseChange_nonsingular E (f := Algebra.ofId F (RatFunc F))
        (Algebra.ofId F (RatFunc F)).injective x₀ y₀).mp hns'
    refine ⟨WeierstrassCurve.Affine.Point.some x₀ y₀ hq, ?_⟩
    refine (WeierstrassCurve.Affine.Point.map_some (W' := E) (f := Algebra.ofId F (RatFunc F))
      (x := x₀) (y := y₀) hq).trans ?_
    rw [WeierstrassCurve.Affine.Point.some.injEq]
    exact ⟨by rw [Algebra.ofId_apply, hx₀], by rw [Algebra.ofId_apply, hy₀]⟩

end

end Work.Genus
