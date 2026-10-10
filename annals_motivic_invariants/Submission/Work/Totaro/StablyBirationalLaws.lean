import Submission.Work.Totaro.StablyBirational_of_isoOver
import Submission.Work.Totaro.stablyBirational_congr

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.Totaro.StablyBirationalLaws` — the equivalence-relation laws of stable birationality

`Work.Totaro.StablyBirational` (the relation of `Work.CY3.TotaroInput` / `Work.K3.TotaroInput`,
i.e. `∃ n m, X × 𝔸ⁿ ∼ Y × 𝔸ᵐ`) is an equivalence relation on `𝕜`-varieties:

* `Work.Totaro.stablyBirational_refl` — reflexivity (`n = m = 0`, from `IsoOver.refl`);
* `Work.Totaro.stablyBirational_symm` — symmetry (swap the exponents and invert the birational map);
* `Work.Totaro.stablyBirational_trans` — transitivity, in
  `Submission/Work/Totaro/stablyBirational_trans.lean` (the exponents are shifted upward with the
  associativity isomorphisms `(X × 𝔸ⁿ) × 𝔸ᵏ ≅ X × 𝔸^{n+k}` so that the two relations can be
  composed).

These laws are what makes "the stable birational class of a variety" a well-defined invariant — the
invariant with which the cohomological certificate of `Submission/Work/Totaro/Cohomology.lean` is
compared — and they are not in Mathlib or in the two L-link chapters.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
attribute [instance] MotivicInvariants.Variety.over MotivicInvariants.Variety.isIntegral

namespace Work.Totaro

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
  MotivicInvariants Order

noncomputable section

variable {𝕜 : Type} [Field 𝕜]

/-- Stable birationality is reflexive: `X × 𝔸⁰ ≅ X`. -/
theorem stablyBirational_refl (X : Scheme.{0}) [Variety 𝕜 X] : StablyBirational 𝕜 X X :=
  StablyBirational_of_isoOver (Work.K3.IsoOver.refl 𝕜 X)

/-- Stable birationality is symmetric: swap the two exponents and invert the birational map. -/
theorem stablyBirational_symm {X Y : Scheme.{0}} [Variety 𝕜 X] [Variety 𝕜 Y]
    (h : StablyBirational 𝕜 X Y) : StablyBirational 𝕜 Y X := by
  obtain ⟨n, m, hXn, hYm, φ⟩ := h
  exact ⟨m, n, hYm, hXn, φ.map fun ψ => ψ.symm⟩

end

end Work.Totaro
