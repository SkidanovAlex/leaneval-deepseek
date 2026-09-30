import Mathlib
import Submission.Work.Cohomology.Crux33.ShuffleIndex

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The Eilenberg–Zilber shuffle chain of a pair of simplices

For a `(p,q)`-shuffle `S` (an element of `PShuffle p q`, i.e. the positions of the `q` `N`-steps),
`aHom S` and `bHom S` are the two monotone maps `⦋p+q⦌ ⟶ ⦋p⦌`, `⦋p+q⦌ ⟶ ⦋q⦌` which are the two
coordinates of the corresponding maximal simplex of the prism `Δ[p] × Δ[q]`
(`Submission/Work/Cohomology/Crux33/ShuffleIndex.lean`).

`ezGen p q X Y σ τ` is the corresponding sum over the shuffles, in the tensor product `X ⊗ Y` of
simplicial sets, of `shufSign S • (σ ∘ a_S, τ ∘ b_S)` — the Eilenberg–Zilber shuffle chain of the
pair of simplices `σ`, `τ`.  For `p = q = 3` this is the chain whose boundary is studied by
`ezGen_isCycle`, and which is the `6`-cycle of the cup-product witness.

The definition is written on generators only: the statements needed for the witness
(`ezGen_isCycle` and the evaluation against normalized cocycles) are for *simplices* `σ`, `τ`, so no
linear extension is required here.
-/

open CategoryTheory AlgebraicTopology Simplicial Limits MonoidalCategory
open scoped Simplicial

namespace Work.Cohomology.Crux33

noncomputable section

/-- **The Eilenberg–Zilber shuffle chain** of a `p`-simplex `σ` of `X` and a `q`-simplex `τ` of
`Y`, as an element of the `(p+q)`-chains of the tensor product `X ⊗ Y` of simplicial sets. -/
def ezGen (p q : ℕ) (X Y : SSet) (σ : X _⦋p⦌) (τ : Y _⦋q⦌) :
    ((X ⊗ Y).chainComplex (ModuleCat.of ℤ ℤ)).X (p + q) :=
  ∑ S : PShuffle p q, shufSign S.1 • ((X ⊗ Y).ιChainComplex (R := ModuleCat.of ℤ ℤ)
    (X.map (aHom S.1 S.2).op σ, Y.map (bHom S.1 S.2).op τ)).hom 1

/-! ## Canonical spellings used in statements

These pinned abbreviations let statements mention the relevant objects without the scoped simplex
notation (which is not available when a statement is elaborated standalone). -/

/-- The `3`-simplices of a simplicial set. -/
abbrev S3 (X : SSet) : Type := X.obj (Opposite.op (SimplexCategory.mk 3))

/-- The `n`-chains of a simplicial set. -/
abbrev Cn (X : SSet) (n : ℕ) : Type := ((X.chainComplex (ModuleCat.of ℤ ℤ)).X n)

/-- The differential `C₃ ⟶ C₂`. -/
abbrev d32 (X : SSet) : Cn X 3 →ₗ[ℤ] Cn X 2 :=
  (((X.chainComplex (ModuleCat.of ℤ ℤ)).d 3 2)).hom

/-- The differential `C₆ ⟶ C₅`. -/
abbrev d65 (X : SSet) : Cn X 6 →ₗ[ℤ] Cn X 5 :=
  (((X.chainComplex (ModuleCat.of ℤ ℤ)).d 6 5)).hom

/-- The generator of the chains associated with a `3`-simplex. -/
abbrev gen3 (X : SSet) (σ : S3 X) : Cn X 3 :=
  ((X.ιChainComplex (R := ModuleCat.of ℤ ℤ) σ)).hom 1

/-- The chains of the tensor product of two simplicial sets (pinned spelling: hides `⊗`). -/
abbrev Tn (X Y : SSet) (n : ℕ) : Type := ((X ⊗ Y).chainComplex (ModuleCat.of ℤ ℤ)).X n

/-- The Eilenberg–Zilber shuffle chain, at the pinned spelling for `p = q = 3`. -/
abbrev ezC (X Y : SSet) (σ : S3 X) (τ : S3 Y) : Tn X Y 6 := ezGen 3 3 X Y σ τ

/-- The differential `C₆ ⟶ C₅` of the tensor product (pinned spelling: hides `⊗`). -/
abbrev Td65 (X Y : SSet) : Tn X Y 6 →ₗ[ℤ] Tn X Y 5 :=
  (((X ⊗ Y).chainComplex (ModuleCat.of ℤ ℤ)).d 6 5).hom

end

end Work.Cohomology.Crux33
