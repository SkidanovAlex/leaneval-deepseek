import Mathlib
import Submission.Work.K3.Defs
import Submission.Work.K3Inputs.exists_variety_prodOver_affineSpace

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.CY3Stab.Cylinder` — the cylinder `𝔸ᵏ ×_{Spec 𝕜} X` and its `Triplet`

The vocabulary underlying the stabilisation: `AffineK k = 𝔸ᵏ`, the cylinder
`WProd X k = 𝔸ᵏ ×_{Spec 𝕜} X` (the base change of `X` along `𝔸ᵏ ⟶ Spec 𝕜`, in the order of
`Work.K3.baseChangeAlong` so that the K3 chapter's analysed base-change lemmas apply verbatim),
and the `Triplet` `cylTriplet X x k` from which the cylinder point over `x` is built
(`Work.CY3Stab.prodPt`, `Submission/Work/CY3Stab/Defs.lean`).

This module exists (separately from `Defs.lean`) so that
`Submission/Work/CY3Stab/Prod/isDomain_cylTriplet_tensor.lean` — the proof that the tensor of the
`Triplet` is a domain, which is what makes the *generic* point of the cylinder fibre available —
can import it without a cycle.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
attribute [instance] MotivicInvariants.Variety.over MotivicInvariants.Variety.isIntegral

namespace Work.CY3Stab

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
  MotivicInvariants Order

noncomputable section

variable {𝕜 : Type} [Field 𝕜]

/-- Affine `k`-space `𝔸ᵏ_𝕜`, the stabilising factor `W` of Lin–Shinder. -/
abbrev AffineK (k : ℕ) : Scheme.{0} := 𝔸(Fin k; Spec (.of 𝕜))

/-- **The cylinder** `𝔸ᵏ ×_{Spec 𝕜} X` of a `𝕜`-scheme `X`.

The order of the factors is the one of `Work.K3.baseChangeAlong` (the `𝔸ᵏ`-leg is the first
projection), so that `WProd X k` is *definitionally* `Work.K3.baseChangeAlong (𝔸ᵏ ↘ Spec 𝕜) X` and
the analysed base-change lemmas of the K3 chapter (`Work.K3.PartialMap.baseChangeAlong`,
`Work.K3.isIsoAt_baseChangeAlong`, `Work.K3.coheight_le_of_flat`,
`Work.K3Inputs.exDiv_affineProd_subset`) apply without transport. -/
abbrev WProd (X : Scheme.{0}) [X.Over (Spec (.of 𝕜))] (k : ℕ) : Scheme.{0} :=
  Work.K3.baseChangeAlong (AffineK (𝕜 := 𝕜) k ↘ Spec (.of 𝕜)) X

/-- The cylinder is the base change of `X` along `𝔸ᵏ ⟶ Spec 𝕜`. -/
theorem wProd_eq_baseChangeAlong (X : Scheme.{0}) [X.Over (Spec (.of 𝕜))] (k : ℕ) :
    WProd (𝕜 := 𝕜) X k =
      Work.K3.baseChangeAlong (AffineK (𝕜 := 𝕜) k ↘ Spec (.of 𝕜)) X := rfl

/-- The cylinder of a `𝕜`-scheme is a `𝕜`-scheme (via the projection onto `X`).  This is
`Work.K3.baseChangeAlongOver` for the morphism `𝔸ᵏ ⟶ Spec 𝕜`. -/
instance (priority := 100) wProdOver (X : Scheme.{0}) [X.Over (Spec (.of 𝕜))] (k : ℕ) :
    (WProd (𝕜 := 𝕜) X k).Over (Spec (.of 𝕜)) :=
  ⟨pullback.fst (AffineK (𝕜 := 𝕜) k ↘ Spec (.of 𝕜)) (X ↘ Spec (.of 𝕜)) ≫
    (AffineK (𝕜 := 𝕜) k ↘ Spec (.of 𝕜))⟩

/-- **The cylinder triplet over `x`**: the pair `(genericPoint 𝔸ᵏ, x)` of points lying over the
(unique) point of `Spec 𝕜`. -/
noncomputable def cylTriplet (X : Scheme.{0}) [X.Over (Spec (.of 𝕜))] (x : X) (k : ℕ) :
    Pullback.Triplet (AffineK (𝕜 := 𝕜) k ↘ Spec (.of 𝕜)) (X ↘ Spec (.of 𝕜)) :=
  Pullback.Triplet.mk' (genericPoint (AffineK (𝕜 := 𝕜) k)) x (Subsingleton.elim _ _)


end

end Work.CY3Stab
