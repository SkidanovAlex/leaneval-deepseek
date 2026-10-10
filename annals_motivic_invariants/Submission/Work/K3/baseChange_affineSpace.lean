import Mathlib
import Submission.Work.K3.BaseChange
import Submission.Work.K3.baseChange_comp

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.K3.baseChange_affineSpace` — affine space commutes with base change

Affine `n`-space over `S` is by definition the fibred product of `S` with the integral model
`Spec ℤ[X_1,…,X_n]` over the terminal scheme:

`𝔸(n; S) = S ×_{Spec ℤ} Spec ℤ[X_1,…,X_n]`.

Base changing `𝔸(n; Spec K)` along a field extension `K → L` therefore computes the pullback of
the cospan

`Spec L ⟶ Spec K ⟶ Spec ℤ ⟵ Spec ℤ[X_1,…,X_n]`,

which — by pasting of pullbacks (`Work.K3.pullback_pullback_iso`) — is the pullback of the cospan
`Spec L ⟶ Spec ℤ ⟵ Spec ℤ[X_1,…,X_n]`, i.e. `𝔸(n; Spec L)`.  The isomorphism is obtained over
`Spec L` because both sides are the first projection of the corresponding fibred product.

This is what lets one transport the affine models of an `L`-link along a field extension
(e.g. the transports `ε : 𝔸⁴ ⤏ P` of `Work.K3.K3Data`).
-/

namespace Work.K3

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

/-- **Base change of affine space**: `𝔸ⁿ_K ×_{Spec K} Spec L ≅ 𝔸ⁿ_L`, by an isomorphism over
`Spec L`.  This is what lets one transport the affine models of an L-link along a field extension
(e.g. the transports `ε : 𝔸⁴ ⤏ P` of `Work.K3.K3Data`). -/
theorem baseChange_affineSpace (K L : Type) [Field K] [Field L] [Algebra K L] (n : ℕ) :
    ∃ e : Work.K3.baseChange K L (𝔸(Fin n; Spec (.of K))) ≅ 𝔸(Fin n; Spec (.of L)),
      e.hom.IsOver (Spec (.of L)) := by
  -- `𝔸(n; S) = S ×_{Spec ℤ} Spec ℤ[X_1,…,X_n]`; paste the two pullback squares of the cospan
  -- `Spec L ⟶ Spec K ⟶ Spec ℤ ⟵ Spec ℤ[X_1,…,X_n]`.
  obtain ⟨e, he⟩ := Work.K3.pullback_pullback_iso
    (f := terminal.from (Spec (.of K)))
    (g := Work.K3.specMap K L)
    (w := terminal.from (Spec (.of (MvPolynomial (Fin n) (ULift ℤ)))))
    (h := terminal.from (Spec (.of L)))
    (Subsingleton.elim _ _)
  -- `he` is precisely the assertion that `e` is a morphism over `Spec L`, since the structure
  -- morphisms of both sides are the first projections of the corresponding pullbacks.
  exact ⟨e, by rw [Hom.isOver_iff]; exact he⟩

end Work.K3
