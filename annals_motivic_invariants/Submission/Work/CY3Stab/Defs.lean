import Mathlib
import Submission.Work.CY3.Main
import Submission.Work.Totaro.Main
import Submission.Work.K3Inputs.affineN_prodOver_iso
import Submission.Work.K3Inputs.exDiv_affineProd_subset
import Submission.Work.CY3Stab.Cylinder
import Submission.Work.K3Inputs.exists_variety_prodOver_affineSpace

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.CY3Stab.Defs` — vocabulary of the CY3 stabilisation `Cr 5 → Cr n`

Lin–Shinder (Annals **199** (1), 2024) prove Theorem 1.2 (3) for `n ≥ 5` by *stabilising* the
`Cr 5`-link of `thm:CY3` (proof of `thm:bir-generation`, case (c)):

> For an arbitrary `W` as in Theorem `thm:bir-generation`, it then follows from Corollary
> `cor-CYnSB` that `c(φ × Id_W) = [Z × ℙ¹ × W] − [Z' × ℙ¹ × W] ≠ 0 ∈ ℤ[Bir/𝕜].`

with `W = 𝔸^{n-5}` (`ℙ¹ × W` is separably rationally connected).  In the per-coefficient
vocabulary of this workspace (`Work.Motivic.cInv`, `Work.Motivic.exDiv`, `Work.Motivic.IsIsoAt`)
the step is the passage from a non-vanishing coefficient in `Cr 𝕜 5` to one in `Cr 𝕜 n` through
the map `φ ↦ φ × id_{𝔸^{n-5}}` and the *coordinate choice* of the base point — the cylinder point
`prodPt z k` of the base point `z`, i.e. the generic point of the cylinder `𝔸ᵏ × \overline{z}`,
whose residue field is `κ(z)(t₁,…,t_k)`.

## Contents

* `AffineK k = 𝔸ᵏ_𝕜` — the stabilising factor `W`;
* `WProd X k = 𝔸ᵏ ×_{Spec 𝕜} X` — the cylinder of `X` (the order of the factors is the one of
  `Work.K3.baseChangeAlong`, so that the K3 chapter's analysed base-change lemmas apply verbatim);
* `cylTriplet X x k`, `prodPt X x k` — the cylinder point over `x`, together with its two
  projections `prodPt_fst` (`pr₁ (prodPt x k) = genericPoint 𝔸ᵏ`) and `prodPt_snd`
  (`pr₂ (prodPt x k) = x`).  It is defined as *any* point of the fibre over the pair
  `(genericPoint 𝔸ᵏ, x)`; that fibre is the spectrum of the domain `κ(𝕜(t₁,…,t_k) ⊗ κ(x))`, so it
  is a single point and the choice is immaterial — this is the first half of the clause (2) below;
* `prodMap k φ` — **the product map** `φ × id_{𝔸ᵏ}`, the base change of a partial-isomorphism
  representative of `φ` along `𝔸ᵏ ⟶ Spec 𝕜` (`Work.K3.birationalMap_baseChangeAlong`), with its
  pinned representative property `prodMap_spec`, which is what makes the K3 chapter's `exDiv`
  analysis applicable;
* `ProdStab 𝕜 k` — **the named residual of the `∀`-form of the stabilisation**: the coefficient
  comparison `cInv 𝕜 (prodPt z k) (φ × id_{𝔸ᵏ}) = cInv 𝕜 z φ` at the canonical cylinder structure
  (the structure hypothesis is part of the field: with an arbitrary `Variety`-structure on the
  cylinder the statement is false).  Its mathematical content is the residue-field comparison
  `ResEquiv 𝕜 (prodPt x k) (prodPt z k) ↔ ResEquiv 𝕜 x z`, whose `⟸` direction is *proved*
  (`Work.CY3Stab.Prod.resEquiv_prodPt_of_resEquiv`), so the residual is exactly the paper's
  `lem-stbirCY`-type `⟹` direction; the `exDiv` analysis of the product map
  (`exDiv (φ × id) = prodPt · k '' exDiv φ`, `Work.CY3Stab.Prod.exDiv_prodMap_eq`) and the counting
  which turns the comparison into the coefficient comparison (`Work.CY3Stab.cInv_prodMap_eq`,
  `Submission/Work/CY3Stab/ProdCoeff.lean`) are *proved* here, and the packaging to `Cr 𝕜 n` is
  `Submission/Work/CY3Stab/Main.lean`.

`ProdStab` is the residual of the `∀`-quantified `Work.CY3.CY3Stabilisation` only.  The `n ≥ 5`
chain of Theorem 1.2 (3) is **closed without it** (`Work.CY3Stab.Final`,
`Work.CY3Stab.not_gen_of_CY3_infiniteField`): at the link the residue-field comparison is *known*
from the `ℙ¹`-bundle structure of the two exceptional divisors (`Work.CY3Stab.CY3P1Bundle`).

The exact status of the residual, with the proof routes, is in
`Submission/Work/CY3Stab/NOTES.md`.
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

/-- **The cylinder point over `x`**: a point of the cylinder `𝔸ᵏ × X` lying over the pair
`(genericPoint 𝔸ᵏ, x)`, i.e. the generic point of the cylinder `𝔸ᵏ × \overline{x}`.

The fibre over the pair `(genericPoint 𝔸ᵏ, x)` is `Spec (𝕜(t₁,…,t_k) ⊗_𝕜 κ(x))`, which is a
*field* (a localisation of `κ(x)[t₁,…,t_k]`), so this fibre is a single point and any choice of a
point over the pair gives the same point of the cylinder; in particular its residue field is the
function field `κ(x)(t₁,…,t_k)` of the cylinder over `x`.  Both facts enter the residual
`ProdStab` below, through the *proved* comparison `Work.CY3Stab.cInv_prodMap_eq` (together with
the residue-field computation `κ(𝔸ᵏ) ⊗ κ(x) = κ(x)(t)`); the point is the *generic* point of the
fibre, not an arbitrary one, which is what makes the statements about it true. -/
noncomputable def prodPt (X : Scheme.{0}) [X.Over (Spec (.of 𝕜))] (x : X) (k : ℕ)
    [IsDomain (cylTriplet (𝕜 := 𝕜) X x k).tensor] : WProd (𝕜 := 𝕜) X k :=
  (cylTriplet (𝕜 := 𝕜) X x k).SpecTensorTo (⊥ : PrimeSpectrum _)

/-- The first projection of the cylinder point is the generic point of `𝔸ᵏ`. -/
theorem prodPt_fst (X : Scheme.{0}) [X.Over (Spec (.of 𝕜))] (x : X) (k : ℕ)
    [IsDomain (cylTriplet (𝕜 := 𝕜) X x k).tensor] :
    pullback.fst (AffineK (𝕜 := 𝕜) k ↘ Spec (.of 𝕜)) (X ↘ Spec (.of 𝕜)) (prodPt X x k) =
      genericPoint (AffineK (𝕜 := 𝕜) k) :=
  Pullback.Triplet.fst_SpecTensorTo_apply (T := cylTriplet (𝕜 := 𝕜) X x k)
    (⊥ : PrimeSpectrum _)

/-- The second projection of the cylinder point is `x`. -/
theorem prodPt_snd (X : Scheme.{0}) [X.Over (Spec (.of 𝕜))] (x : X) (k : ℕ)
    [IsDomain (cylTriplet (𝕜 := 𝕜) X x k).tensor] :
    pullback.snd (AffineK (𝕜 := 𝕜) k ↘ Spec (.of 𝕜)) (X ↘ Spec (.of 𝕜)) (prodPt X x k) = x :=
  Pullback.Triplet.snd_SpecTensorTo_apply (T := cylTriplet (𝕜 := 𝕜) X x k)
    (⊥ : PrimeSpectrum _)

/-- The projection of the cylinder onto `X`, in the vocabulary of `Work.K3`. -/
theorem wProdProj_apply (X : Scheme.{0}) [X.Over (Spec (.of 𝕜))] (x : X) (k : ℕ)
    [IsDomain (cylTriplet (𝕜 := 𝕜) X x k).tensor] :
    Work.K3.baseChangeAlongProj (AffineK (𝕜 := 𝕜) k ↘ Spec (.of 𝕜)) X (prodPt X x k) = x :=
  prodPt_snd X x k

/-- The cylinder point over `x` lies over the generic point of `𝔸ᵏ`. -/
theorem wProdFst_apply (X : Scheme.{0}) [X.Over (Spec (.of 𝕜))] (x : X) (k : ℕ)
    [IsDomain (cylTriplet (𝕜 := 𝕜) X x k).tensor] :
    pullback.fst (AffineK (𝕜 := 𝕜) k ↘ Spec (.of 𝕜)) (X ↘ Spec (.of 𝕜)) (prodPt X x k) =
      pullback.fst (AffineK (𝕜 := 𝕜) k ↘ Spec (.of 𝕜)) (X ↘ Spec (.of 𝕜))
        (prodPt X x k) := rfl

/-- **The product map** `φ × id_{𝔸ᵏ}`, as a birational map `𝔸ᵏ × X ⤏ 𝔸ᵏ × Y` over `𝕜`.

It is the base change of a partial-isomorphism representative of `φ` along the projection
`𝔸ᵏ ⟶ Spec 𝕜` (`Work.K3.birationalMap_baseChangeAlong`); its representative compatibility
properties are recorded in `prodMap_spec`, and they are exactly the hypotheses under which the K3
chapter's `exDiv` analysis (`Work.K3Inputs.exDiv_affineProd_subset`) applies. -/
noncomputable def prodMap (k : ℕ) {X Y : Scheme.{0}} [IrreducibleSpace X] [IrreducibleSpace Y]
    [X.Over (Spec (.of 𝕜))] [Y.Over (Spec (.of 𝕜))] (φ : X.BirationalMap Y)
    [φ.IsOver (Spec (.of 𝕜))]
    [IrreducibleSpace (WProd (𝕜 := 𝕜) X k)] [IrreducibleSpace (WProd (𝕜 := 𝕜) Y k)] :
    (WProd (𝕜 := 𝕜) X k).BirationalMap (WProd (𝕜 := 𝕜) Y k) :=
  (Work.K3.birationalMap_baseChangeAlong (AffineK (𝕜 := 𝕜) k ↘ Spec (.of 𝕜)) φ
    ‹φ.IsOver (Spec (.of 𝕜))›).choose

/-- **The defining property of `prodMap`**: it is over `𝕜`, and the base change of every
`𝕜`-over partial-map representative of `φ` (resp. of `φ⁻¹`) represents `prodMap k φ` (resp. its
inverse).  This is the bookkeeping under which the K3 chapter's `exDiv` analysis applies. -/
theorem prodMap_spec (k : ℕ) {X Y : Scheme.{0}} [IrreducibleSpace X] [IrreducibleSpace Y]
    [X.Over (Spec (.of 𝕜))] [Y.Over (Spec (.of 𝕜))] (φ : X.BirationalMap Y)
    [φ.IsOver (Spec (.of 𝕜))]
    [IrreducibleSpace (WProd (𝕜 := 𝕜) X k)] [IrreducibleSpace (WProd (𝕜 := 𝕜) Y k)] :
    (prodMap (𝕜 := 𝕜) k φ).IsOver (AffineK (𝕜 := 𝕜) k) ∧
    (∀ (g : X.PartialMap Y) [g.IsOver (Spec (.of 𝕜))], g.toRationalMap = φ.hom →
      (Work.K3.PartialMap.baseChangeAlong (AffineK (𝕜 := 𝕜) k ↘ Spec (.of 𝕜)) g).toRationalMap =
        (prodMap (𝕜 := 𝕜) k φ).hom) ∧
    (∀ (g : Y.PartialMap X) [g.IsOver (Spec (.of 𝕜))], g.toRationalMap = φ.inv →
      (Work.K3.PartialMap.baseChangeAlong (AffineK (𝕜 := 𝕜) k ↘ Spec (.of 𝕜)) g).toRationalMap =
        (prodMap (𝕜 := 𝕜) k φ).inv) :=
  (Work.K3.birationalMap_baseChangeAlong (AffineK (𝕜 := 𝕜) k ↘ Spec (.of 𝕜)) φ
    ‹φ.IsOver (Spec (.of 𝕜))›).choose_spec

/-- **The inclusion half of the `exDiv` analysis of the product map** (proved): if a point of the
cylinder is an exceptional divisor of `φ × id_{𝔸ᵏ}`, then its projection to `X` is an exceptional
divisor of `φ`.

This is the delivered `Work.K3Inputs.exDiv_affineProd_subset` in the vocabulary of this file
(the cylinder is *definitionally* the base change `𝔸ᵏ ×_{Spec 𝕜} X` along `𝔸ᵏ ⟶ Spec 𝕜`, and
`prodMap_spec` supplies the representative-compatibility hypothesis). -/
theorem exDiv_prodMap_subset (k : ℕ) {X Y : Scheme.{0}} [Variety 𝕜 X] [Variety 𝕜 Y]
    (φ : X.BirationalMap Y) [φ.IsOver (Spec (.of 𝕜))]
    [IsIntegral (WProd (𝕜 := 𝕜) X k)] [IsIntegral (WProd (𝕜 := 𝕜) Y k)]
    {p : WProd (𝕜 := 𝕜) X k} (hp : p ∈ exDiv (prodMap (𝕜 := 𝕜) k φ)) :
    Work.K3.baseChangeAlongProj (AffineK (𝕜 := 𝕜) k ↘ Spec (.of 𝕜)) X p ∈ exDiv φ :=
  Work.K3Inputs.exDiv_affineProd_subset 𝕜 φ k (prodMap (𝕜 := 𝕜) k φ)
    (prodMap_spec (𝕜 := 𝕜) k φ).2.1 hp

/-- **Named residual of the stabilisation: the coefficient comparison
`cInv 𝕜 (prodPt z k) (φ × id_{𝔸ᵏ}) = cInv 𝕜 z φ`** at the canonical cylinder structure.

This is the paper's

> `c(φ × Id_W) = [Z × ℙ¹ × W] − [Z' × ℙ¹ × W]`

read off at the base point `z` (the coefficient of the class of the closure of `z`); the hypothesis
`hW` records that the `Over`-structure of the cylinder `𝔸ᵏ × X` is the canonical composite
`𝔸ᵏ × X ⟶ 𝔸ᵏ ⟶ Spec 𝕜` (`Work.CY3Stab.wProdOver`), which is *necessary*: with an arbitrary
`Variety`-structure on the cylinder the statement is false (a base-change twist changes `resMap`;
see `Submission/Work/CY3Stab/Prod/cInv_prodMap_eq_zero_of_strong.lean`).  At the call sites in this
directory the hypothesis is discharged by `rfl`, since there the cylinder structure is
`Work.CY3Stab.varietyWProd`, whose `over` field *is* `wProdOver`.

*The mathematics behind it* is (1) the `exDiv` analysis of the product map,
`exDiv (φ × id_{𝔸ᵏ}) = prodPt · k '' exDiv φ` — **proved** in this directory
(`Work.CY3Stab.Prod.exDiv_prodMap_eq`) — and (2) the residue-field comparison at the cylinder
points, `ResEquiv 𝕜 (prodPt x k) (prodPt z k) ↔ ResEquiv 𝕜 x z` — proved in the direction `⟸`
(`Work.CY3Stab.Prod.resEquiv_prodPt_of_resEquiv`, the tensor transport with `𝕜(t₁,…,t_k)`, i.e. the
paper's "coordinate choice `z₀` transported through the product"), the direction `⟹` being the one
mathematical input that this directory does not prove (the paper's Lemma `lem-stbirCY`,
Corollary `cor-CYnSB` applied to the two `ℙ¹`-bundles of the link).  With the two halves, the
comparison is the *theorem* `Work.CY3Stab.cInv_prodMap_eq` (`Submission/Work/CY3Stab/ProdCoeff.lean`).

Consequently this structure is the residual of the **`∀`-form** of the stabilisation step
(`Work.CY3Stab.exists_cInv_ne_zero_add`, `Work.CY3Stab.cy3Stabilisation_of_prodStab`,
`Work.CY3Stab.cy3Stabilisation_of_prodStab'`) only.  The `n ≥ 5` chain of Theorem 1.2 (3) does
**not** need it: at the *link* the residue-field comparison is *known*, because the two exceptional
divisors are `ℙ¹`-bundles over the two centres (`Work.CY3Stab.CY3P1Bundle`), and
`Work.CY3Stab.Prod.stablyBirational_cyl_two` turns an isomorphism of their cylinder residue fields
into `StablyBirational 𝕜 Z Z'`, which Totaro's `cor-CYnSB` forbids.  That is the route of
`Work.CY3Stab.Prod.exists_cInv_ne_zero_of_CY3Data` and of
`Work.CY3Stab.not_gen_of_CY3_infiniteField` (`Submission/Work/CY3Stab/Final.lean`). -/
structure ProdStab (𝕜 : Type) [Field 𝕜] (k : ℕ) : Prop where
  /-- the coefficient comparison at the cylinder point of `z`, for the canonical cylinder structure
  of `𝔸ᵏ × X` -/
  cInv_prodMap : ∀ (X : Scheme.{0}) [Variety 𝕜 X] (φ : X.BirationalMap X)
    [φ.IsOver (Spec (.of 𝕜))] [Variety 𝕜 (WProd (𝕜 := 𝕜) X k)]
    (hW : (WProd (𝕜 := 𝕜) X k ↘ Spec (.of 𝕜)) = (wProdOver (𝕜 := 𝕜) X k).1)
    (Z : Scheme.{0}) [Z.Over (Spec (.of 𝕜))] (z : Z)
    [IsDomain (cylTriplet (𝕜 := 𝕜) Z z k).tensor],
    cInv 𝕜 (prodPt (𝕜 := 𝕜) Z z k) (prodMap (𝕜 := 𝕜) k φ) = cInv 𝕜 z φ

end

end Work.CY3Stab
