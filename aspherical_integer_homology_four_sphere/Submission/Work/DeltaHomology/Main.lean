import Mathlib
import ChallengeDeps
import Submission.Work.DeltaHomology.Basic
import Submission.Work.DeltaHomology.ChainDefs
import Submission.Work.DeltaHomology.Chain
import Submission.Work.DeltaHomology.RealizationDefs
import Submission.Work.DeltaHomology.Realization
import Submission.Work.DeltaHomology.quasiOso_deltaChainMap
import Submission.Work.DeltaHomology.chain_homology_isZero_of_dim_lt
import Submission.Work.Homology.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The `Δ`-chain complex computes singular homology (Hatcher Theorem 2.27)

For a finite `Δ`-complex `K` realized in a compact Hausdorff space `X`
(`DeltaRealization K X`), the comparison chain map

`deltaChainMap : C_*^Δ(K; ℤ) ⟶ C_*^{sing}(X; ℤ)`,  `σ ↦ χ σ`

is a quasi-isomorphism, and hence induces isomorphisms

`deltaChainHomologyIso : H_k^Δ(K; ℤ) ≅ H_k(X; ℤ)`,
`deltaHomologyIso : H_k(X; ℤ) ≅ H_k^Δ(K; ℤ)`.

Everything in this file except `deltaChainMap_quasiIso` (and the two
`deltaChainHomologyIso`/`deltaHomologyIso` built on it) is proved without
the frontier statement of the area.  The hypothesis-free isomorphism is stated below as
`deltaChainHomologyIsoOfQuasiIso`, which takes the quasi-isomorphism as an
explicit argument, together with the naturality of that isomorphism (proved).

**Status of `deltaChainMap_quasiIso`.**  It is the frontier of this area.  Its
proof is Hatcher's induction on skeleta: compare the long exact sequences of the
pairs `(X^k, X^{k-1})` and the algebraically evident exact sequence of
`C_*^Δ(K^k)/C_*^Δ(K^{k-1}) ≅ ℤ[K_k]`, and apply the five lemma.  What has to be
built is the computation `H_n(X^k, X^{k-1}) ≅ ℤ^{K_k}` (`n = k`, zero otherwise):
see `Submission/Work/DeltaHomology/NOTES.md` for the precise route (collar of
`X^{k-1}` in `X^k` + excision for singular homology).
-/

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open Convexity
open LeanEval.Topology
open Work.Homology

set_option linter.unusedVariables false

namespace Work.DeltaHomology

noncomputable section

open scoped Simplicial

variable {K L : DeltaCx} {X Y : TopCat.{0}}

/-- Given the quasi-isomorphism statement, the induced isomorphism on homology
in degree `k`: the inverse of the map induced by the comparison chain map
`σ ↦ χ σ`. -/
noncomputable def deltaChainHomologyIsoOfQuasiIso (K : DeltaCx) {X : TopCat.{0}}
    (R : DeltaRealization K X) (h : QuasiIso R.toDeltaSimplexMap.deltaChainMap) (k : ℕ) :
    K.chain.homology k ≅ singHomology Work.Homology.ZMod k X := by
  haveI : QuasiIsoAt R.toDeltaSimplexMap.deltaChainMap k := h.quasiIsoAt k
  exact isoOfQuasiIsoAt R.toDeltaSimplexMap.deltaChainMap k

/-- The isomorphism of `deltaChainHomologyIsoOfQuasiIso` is the map induced by
the comparison chain map. -/
theorem deltaChainHomologyIsoOfQuasiIso_hom (K : DeltaCx) {X : TopCat.{0}}
    (R : DeltaRealization K X) (h : QuasiIso R.toDeltaSimplexMap.deltaChainMap) (k : ℕ) :
    (deltaChainHomologyIsoOfQuasiIso K R h k).hom
      = HomologicalComplex.homologyMap R.toDeltaSimplexMap.deltaChainMap k :=
  isoOfQuasiIsoAt_hom _ _

/-- **Naturality of the comparison isomorphism** (hypothesis-free form, taking
the quasi-isomorphism as an argument).  A simplicial map `f : K ⟶ L` of
`Δ`-complexes covered by a continuous map `g : X ⟶ Y`
(`singMap g (χ σ) = χ' (f σ)`) induces a commuting square of isomorphisms. -/
theorem deltaChainHomologyIsoOfQuasiIso_natural (K L : DeltaCx) {X Y : TopCat.{0}}
    (R : DeltaRealization K X) (R' : DeltaRealization L Y)
    (hK : QuasiIso R.toDeltaSimplexMap.deltaChainMap)
    (hL : QuasiIso R'.toDeltaSimplexMap.deltaChainMap)
    (f : K.Hom L) (g : X ⟶ Y)
    (h : ∀ (k : ℕ) (σ : Fin (K.card k)), singMap g (R.χ k σ) = R'.χ k (f.map σ)) (k : ℕ) :
    (deltaChainHomologyIsoOfQuasiIso K R hK k).hom ≫ singHomologyMap Work.Homology.ZMod k g
      = HomologicalComplex.homologyMap (DeltaCx.Hom.chainMap f) k
        ≫ (deltaChainHomologyIsoOfQuasiIso L R' hL k).hom := by
  rw [deltaChainHomologyIsoOfQuasiIso_hom, deltaChainHomologyIsoOfQuasiIso_hom]
  exact (DeltaSimplexMap.deltaHomologyMap_natural R.toDeltaSimplexMap R'.toDeltaSimplexMap
    f g h k).symm

/-- If the comparison map is a quasi-isomorphism (Hatcher 2.27), then the
singular homology of a realization of a bounded `Δ`-complex vanishes above its
dimension: `H_k(X) = 0` for `k > K.dim`. -/
theorem singHomology_isZero_of_dim_lt_of_quasiIso (K : DeltaCx) {X : TopCat.{0}}
    (R : DeltaRealization K X) (h : QuasiIso R.toDeltaSimplexMap.deltaChainMap)
    {k : ℕ} (hk : K.dim < k) : IsZero (intHomology k X) :=
  IsZero.of_iso (chain_homology_isZero_of_dim_lt K hk)
    (deltaChainHomologyIsoOfQuasiIso K R h k).symm

/-! ## The frontier: Hatcher's theorem -/

/-- **Hatcher Theorem 2.27 (quasi-isomorphism form).**  For a `Δ`-complex `K`
realized in a compact Hausdorff space `X`, the comparison chain map from the
`Δ`-chains to the singular chains is a quasi-isomorphism.

Proved in `Submission.Work.DeltaHomology.quasiOso_deltaChainMap`, which assembles it from the
skeleta induction `Submission.Work.DeltaHomology.quasiOso_deltaChainMapSkel`; see
`Submission/Work/DeltaHomology/NOTES.md` for the structure of the proof (collar, excision,
clopen splitting of `H_n(X^k, X^{k-1})` over the cells, the degree-`±1` statement for the
characteristic map of a top cell, and the five lemma in the middle position). -/
theorem deltaChainMap_quasiIso (K : DeltaCx) {X : TopCat.{0}} (R : DeltaRealization K X) :
    QuasiIso R.toDeltaSimplexMap.deltaChainMap :=
  quasiOso_deltaChainMap R

/-- **Hatcher Theorem 2.27.**  The homology of the `Δ`-chain complex of `K`
computes the singular homology of its realization, via the comparison chain map
`σ ↦ χ σ`. -/
abbrev deltaChainHomologyIso (K : DeltaCx) {X : TopCat.{0}}
    (R : DeltaRealization K X) (k : ℕ) :
    K.chain.homology k ≅ singHomology Work.Homology.ZMod k X :=
  deltaChainHomologyIsoOfQuasiIso K R (deltaChainMap_quasiIso K R) k

/-- **Hatcher Theorem 2.27.**  The singular homology of a realization of a
`Δ`-complex is isomorphic to the homology of its `Δ`-chain complex.

This is the direction used to transfer a certificate about the `Δ`-chain complex
(an explicit homology class, or the vanishing of `H_k^Δ`) to singular homology;
its inverse is the map induced by `σ ↦ χ σ`. -/
abbrev deltaHomologyIso (K : DeltaCx) {X : TopCat.{0}}
    (R : DeltaRealization K X) (k : ℕ) : intHomology k X ≅ K.chain.homology k :=
  (deltaChainHomologyIso K R k).symm

/-- **Vanishing above the dimension.**  The singular homology of a realization
of a `Δ`-complex of dimension `dim` vanishes in degrees `> dim`.  (This is the
statement used to deduce `H_k(M̂) = 0` for `k ≥ 5` from a 4-dimensional `Δ`-complex
structure on `M̂`.) -/
theorem singHomology_isZero_of_dim_lt (K : DeltaCx) {X : TopCat.{0}}
    (R : DeltaRealization K X) {k : ℕ} (hk : K.dim < k) : IsZero (intHomology k X) :=
  singHomology_isZero_of_dim_lt_of_quasiIso K R (deltaChainMap_quasiIso K R) hk

/-- The `hom` component of `deltaChainHomologyIso` is the map induced by the
comparison chain map `σ ↦ χ σ`. -/
theorem deltaChainHomologyIso_hom (K : DeltaCx) {X : TopCat.{0}}
    (R : DeltaRealization K X) (k : ℕ) :
    (deltaChainHomologyIso K R k).hom
      = HomologicalComplex.homologyMap R.toDeltaSimplexMap.deltaChainMap k :=
  rfl

/-- The `inv` component of `deltaHomologyIso` is the map induced by the
comparison chain map `σ ↦ χ σ` (so the `hom` of `deltaHomologyIso` is the
inverse of the comparison map on homology). -/
theorem deltaHomologyIso_inv (K : DeltaCx) {X : TopCat.{0}}
    (R : DeltaRealization K X) (k : ℕ) :
    (deltaHomologyIso K R k).inv
      = HomologicalComplex.homologyMap R.toDeltaSimplexMap.deltaChainMap k :=
  rfl

/-- **Naturality of `deltaChainHomologyIso`.**  A simplicial map `f : K ⟶ L`
of `Δ`-complexes covered by `g : X ⟶ Y` gives a commuting square of the
comparison isomorphisms. -/
theorem deltaChainHomologyIso_natural (K L : DeltaCx) {X Y : TopCat.{0}}
    (R : DeltaRealization K X) (R' : DeltaRealization L Y) (f : K.Hom L) (g : X ⟶ Y)
    (h : ∀ (k : ℕ) (σ : Fin (K.card k)), singMap g (R.χ k σ) = R'.χ k (f.map σ)) (k : ℕ) :
    (deltaChainHomologyIso K R k).hom ≫ singHomologyMap Work.Homology.ZMod k g
      = HomologicalComplex.homologyMap (DeltaCx.Hom.chainMap f) k
        ≫ (deltaChainHomologyIso L R' k).hom :=
  deltaChainHomologyIsoOfQuasiIso_natural K L R R'
    (deltaChainMap_quasiIso K R) (deltaChainMap_quasiIso L R') f g h k

/-- **Naturality of `deltaHomologyIso`.**  A simplicial map `f : K ⟶ L` of
`Δ`-complexes covered by `g : X ⟶ Y` gives a commuting square.  The case of an
inclusion of subcomplexes is the case where `f` is the inclusion of a subcomplex
and `g` the corresponding map of realizations. -/
theorem deltaHomologyIso_natural (K L : DeltaCx) {X Y : TopCat.{0}}
    (R : DeltaRealization K X) (R' : DeltaRealization L Y) (f : K.Hom L) (g : X ⟶ Y)
    (h : ∀ (k : ℕ) (σ : Fin (K.card k)), singMap g (R.χ k σ) = R'.χ k (f.map σ)) (k : ℕ) :
    (deltaHomologyIso K R k).hom ≫ HomologicalComplex.homologyMap (DeltaCx.Hom.chainMap f) k
      = singHomologyMap Work.Homology.ZMod k g ≫ (deltaHomologyIso L R' k).hom := by
  show (deltaChainHomologyIso K R k).inv
        ≫ HomologicalComplex.homologyMap (DeltaCx.Hom.chainMap f) k
      = singHomologyMap Work.Homology.ZMod k g ≫ (deltaChainHomologyIso L R' k).inv
  rw [Iso.inv_comp_eq (deltaChainHomologyIso K R k)]
  rw [← Category.assoc]
  rw [Iso.eq_comp_inv (deltaChainHomologyIso L R' k)]
  exact (deltaChainHomologyIso_natural K L R R' f g h k).symm

end

end Work.DeltaHomology
