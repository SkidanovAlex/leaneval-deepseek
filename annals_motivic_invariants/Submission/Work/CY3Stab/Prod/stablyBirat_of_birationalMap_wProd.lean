import Mathlib
import Submission.Work.CY3Stab.Defs
import Submission.Work.K3Inputs.Defs
import Submission.Work.K3Inputs.StablyBiratK3
import Submission.Work.K3Inputs.exists_variety_prodOver_affineSpace
import Submission.Work.Motivic.exists_partialIso_toBirationalMap

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.CY3Stab.Prod.stablyBirat_of_birationalMap_wProd`

The cylinder `Work.CY3Stab.WProd X n = 𝔸ⁿ ×_{Spec 𝕜} X` of `Submission/Work/CY3Stab/Defs.lean`
is the fibred product over `Spec 𝕜` of `𝔸ⁿ` and `X`, with the `𝔸ⁿ`-leg first (the order of
`Work.K3.baseChangeAlong`).  The stable-birationality relation `Work.K3Inputs.StablyBirat 𝕜 X Y`
of the K3 chapter is stated with the *other* order, `Work.K3.prodOver 𝕜 X (AffineN 𝕜 n) =
X ×_{Spec 𝕜} 𝔸ⁿ`.  The two fibre products differ only by the exchange of the two legs, so they are
canonically isomorphic (`wProd_iso_prodOver` below, `CategoryTheory.Limits.pullbackSymmetry`), and
an isomorphism of schemes induces a partial isomorphism, i.e. a birationality.

Consequently, a birational map `𝔸ⁿ × X ⤏ 𝔸ⁿ × Y` *is* a stable birationality of `X` and `Y` with
equal exponents `n`, `n` — no cancellation theorem is needed: the relation `StablyBirat` is
defined by the existence of the exponents, and conjugating by the two canonical isomorphisms
(`Scheme.PartialIso.ofIso`/`PartialIso.trans`) transports the given birationality
(`Work.Motivic.exists_partialIso_toBirationalMap`, which is where the irreducibility hypotheses of
the statement are used) to `(X × 𝔸ⁿ) ⤏ (Y × 𝔸ⁿ)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
attribute [instance] MotivicInvariants.Variety.over MotivicInvariants.Variety.isIntegral

namespace Work.CY3Stab.Prod

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
  MotivicInvariants Order

noncomputable section

variable {𝕜 : Type} [Field 𝕜]

/-- **The cylinder is the product of `Work.K3.prodOver`.**

`Work.CY3Stab.WProd X n = pullback (𝔸ⁿ ⟶ Spec 𝕜) (X ⟶ Spec 𝕜)` and
`Work.K3.prodOver 𝕜 X (AffineN 𝕜 n) = pullback (X ⟶ Spec 𝕜) (𝔸ⁿ ⟶ Spec 𝕜)` are the same fibre
product with the two legs exchanged, hence canonically isomorphic by the symmetry of the pullback.
(`AffineK 𝕜 n` and `Work.K3Inputs.AffineN 𝕜 n` are the same scheme
`𝔸(Fin n; Spec (.of 𝕜))`.) -/
noncomputable def wProd_iso_prodOver (X : Scheme.{0}) [X.Over (Spec (.of 𝕜))] (n : ℕ) :
    WProd (𝕜 := 𝕜) X n ≅ Work.K3.prodOver 𝕜 X (Work.K3Inputs.AffineN 𝕜 n) :=
  pullbackSymmetry (AffineK (𝕜 := 𝕜) n ↘ Spec (.of 𝕜)) (X ↘ Spec (.of 𝕜))

theorem stablyBirat_of_birationalMap_wProd (𝕜 : Type) [Field 𝕜]
    {X Y : AlgebraicGeometry.Scheme.{0}} [MotivicInvariants.Variety 𝕜 X]
    [MotivicInvariants.Variety 𝕜 Y] (n : ℕ)
    [IrreducibleSpace (Work.CY3Stab.WProd (𝕜 := 𝕜) X n)]
    [IrreducibleSpace (Work.CY3Stab.WProd (𝕜 := 𝕜) Y n)]
    (h : Nonempty (AlgebraicGeometry.Scheme.BirationalMap (Work.CY3Stab.WProd (𝕜 := 𝕜) X n)
      (Work.CY3Stab.WProd (𝕜 := 𝕜) Y n))) :
    Work.K3Inputs.StablyBirat 𝕜 X Y := by
  -- A birational map of the two cylinders is represented by a partial isomorphism.
  obtain ⟨φ⟩ := h
  obtain ⟨i, -⟩ := Work.Motivic.exists_partialIso_toBirationalMap φ
  -- Conjugate it by the canonical identifications of the cylinders with the products of
  -- `Work.K3.prodOver`; the exponents are both `n`, so this is a stable birationality.
  exact ⟨n, n, ⟨(PartialIso.ofIso (wProd_iso_prodOver (𝕜 := 𝕜) X n).symm).trans
    (i.trans (PartialIso.ofIso (wProd_iso_prodOver (𝕜 := 𝕜) Y n)))⟩⟩

end

end Work.CY3Stab.Prod
