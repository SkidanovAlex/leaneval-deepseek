import Mathlib
import Submission.Work.MotA.Defs
import Submission.Work.MotA.excCount_basicOpenBirationalMap
import Submission.Work.Motivic.cInv_add
import Submission.Work.Motivic.cInv_eq_zero_of_pseudoReg
import Submission.Work.LLink.cInv_eq_zero_of_isPseudoIso
import Submission.Work.MotA.TransportAPI
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

noncomputable section

namespace Work.MotA

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme MotivicInvariants Order

/-!
# The basic-open formula: assembly

The mathematical ingredients of the proof of `Work.MotA.exists_awayBirationalMap_cInv` in this file
are

* `Work.MotA.excCount_basicOpenBirationalMap` — `divCount 𝕜 n F z` is the exceptional weight of the
  inverse of the open immersion `D(F) ↪ 𝔸ⁿ`;
* `Work.Motivic.cInv_add` — additivity of the Lin–Shinder invariant coefficient;
* `Work.MotA.cInv_symm_of_partialIso_source_eq_top` and
  `Work.MotA.cInv_of_partialIso_source_eq_top` — the coefficients of the two sides of an open
  immersion;
* the construction of an isomorphism `D(G) ≅ D(F)` over `Spec 𝕜` from the `𝕜`-algebra isomorphism
  `Φ : 𝕜[F⁻¹] ≃ₐ[𝕜] 𝕜[G⁻¹]`, via `AlgebraicGeometry.basicOpenIsoSpecAway` (the identification
  `D(f) ≅ Spec R[1/f]`), followed by `Scheme.Spec.map Φ` and `PartialIso.ofIso`.

Note on instances.  `MotivicInvariants.Variety` has an instance field `over`, registered as an
instance; once a `Variety` instance for an open subscheme `D(F)` is in the local context,
typeclass search for `D(F) ↘ Spec 𝕜` may find `Variety.over` instead of the canonical
`CanonicallyOverClass.instOverClass` instance, and the projection of the `Variety` value does not
reduce, so the two are not definitionally equal.  The local high-priority instance
`instOverBasicOpenLocal` below pins the structure morphism of `D(F)` to its explicit form
`D(F).ι ≫ (𝔸ⁿ ↘ Spec 𝕜)` (which is definitionally the canonical instance), so that all the local
instances used in the proof — including those consumed by `Work.Motivic.cInv_add`, which derives
the `Over` instances of its arguments from the `Variety` instances it is given — agree.
-/

/-- The structure morphism of `D(F) ⊆ 𝔸ⁿ` to `Spec 𝕜`, in the explicit form
`D(F) ↪ 𝔸ⁿ ⟶ Spec 𝕜`.  See the note on instances above for why this is installed as a
high-priority local instance. -/
local instance (priority := 2000) instOverBasicOpenLocal (𝕜 : Type) [Field 𝕜] (n : ℕ)
    (F : MvPolynomial (Fin n) 𝕜) :
    ((basicOpen 𝕜 n F).toScheme).Over (Spec (CommRingCat.of 𝕜)) :=
  ⟨(basicOpen 𝕜 n F).ι ≫ ((polySpec 𝕜 n) ↘ (Spec (CommRingCat.of 𝕜)))⟩

/-- `D(F)` is irreducible for `F ≠ 0` (it is a dense open subscheme of the irreducible `𝔸ⁿ`). -/
private lemma irreducibleSpace_basicOpen (𝕜 : Type) [Field 𝕜] (n : ℕ)
    (F : MvPolynomial (Fin n) 𝕜) (hF : F ≠ 0) :
    IrreducibleSpace ((basicOpen 𝕜 n F).toScheme) :=
  Work.CrauderKatz.BlowUp.irreducibleSpace_opensOfDense (basicOpen_dense 𝕜 n F hF)

private lemma isSeparated_basicOpen (𝕜 : Type) [Field 𝕜] (n : ℕ)
    (F : MvPolynomial (Fin n) 𝕜) :
    IsSeparated (((basicOpen 𝕜 n F).toScheme) ↘ (Spec (CommRingCat.of 𝕜))) := by
  rw [show (((basicOpen 𝕜 n F).toScheme) ↘ (Spec (CommRingCat.of 𝕜)))
      = (basicOpen 𝕜 n F).ι ≫ ((polySpec 𝕜 n) ↘ (Spec (CommRingCat.of 𝕜))) from rfl]
  infer_instance

private lemma locallyOfFiniteType_basicOpen (𝕜 : Type) [Field 𝕜] (n : ℕ)
    (F : MvPolynomial (Fin n) 𝕜) :
    LocallyOfFiniteType (((basicOpen 𝕜 n F).toScheme) ↘ (Spec (CommRingCat.of 𝕜))) := by
  rw [show (((basicOpen 𝕜 n F).toScheme) ↘ (Spec (CommRingCat.of 𝕜)))
      = (basicOpen 𝕜 n F).ι ≫ ((polySpec 𝕜 n) ↘ (Spec (CommRingCat.of 𝕜))) from rfl]
  haveI : LocallyOfFiniteType ((polySpec 𝕜 n) ↘ (Spec (CommRingCat.of 𝕜))) :=
    locallyOfFiniteType_polySpec 𝕜 n
  infer_instance

private lemma quasiCompact_basicOpen (𝕜 : Type) [Field 𝕜] (n : ℕ)
    (F : MvPolynomial (Fin n) 𝕜) :
    QuasiCompact (((basicOpen 𝕜 n F).toScheme) ↘ (Spec (CommRingCat.of 𝕜))) := by
  rw [show (((basicOpen 𝕜 n F).toScheme) ↘ (Spec (CommRingCat.of 𝕜)))
      = (basicOpen 𝕜 n F).ι ≫ ((polySpec 𝕜 n) ↘ (Spec (CommRingCat.of 𝕜))) from rfl]
  infer_instance

/-- The partial isomorphism of the open immersion `D(F) ↪ 𝔸ⁿ` is a morphism over `Spec 𝕜`. -/
private lemma partialIsoOfDense_isOver (𝕜 : Type) [Field 𝕜] (n : ℕ)
    (F : MvPolynomial (Fin n) 𝕜) (hF : F ≠ 0) :
    ((basicOpen 𝕜 n F).partialIsoOfDense (basicOpen_dense 𝕜 n F hF)).IsOver
      (((basicOpen 𝕜 n F).toScheme) ↘ (Spec (CommRingCat.of 𝕜)))
      ((polySpec 𝕜 n) ↘ (Spec (CommRingCat.of 𝕜))) := by
  rw [PartialIso.IsOver]
  simp only [Opens.partialIsoOfDense_iso, Scheme.topIso_hom]
  rfl

/-! ## The isomorphism `D(G) ≅ D(F)` induced by an isomorphism of localisations -/

/-- `D(F)` as `Spec 𝕜[F⁻¹]` (`AlgebraicGeometry.basicOpenIsoSpecAway`). -/
private noncomputable def awayIso (𝕜 : Type) [Field 𝕜] (n : ℕ) (F : MvPolynomial (Fin n) 𝕜) :
    (basicOpen 𝕜 n F).toScheme ≅ Spec (CommRingCat.of (Localization.Away F)) :=
  AlgebraicGeometry.basicOpenIsoSpecAway (R := CommRingCat.of (MvPolynomial (Fin n) 𝕜)) F

private lemma awayIso_hom (𝕜 : Type) [Field 𝕜] (n : ℕ) (F : MvPolynomial (Fin n) 𝕜) :
    (awayIso 𝕜 n F).hom
      = (AlgebraicGeometry.basicOpenIsoSpecAway
          (R := CommRingCat.of (MvPolynomial (Fin n) 𝕜)) F).hom := rfl

/-- `D(F) ≅ Spec 𝕜[F⁻¹]` is a morphism over `Spec 𝕜`. -/
private lemma awayIso_hom_structure (𝕜 : Type) [Field 𝕜] (n : ℕ) (F : MvPolynomial (Fin n) 𝕜) :
    (awayIso 𝕜 n F).hom
        ≫ ((Spec (CommRingCat.of (Localization.Away F))) ↘ (Spec (CommRingCat.of 𝕜)))
      = (((basicOpen 𝕜 n F).toScheme) ↘ (Spec (CommRingCat.of 𝕜))) := by
  have h1 : ((Spec (CommRingCat.of (Localization.Away F))) ↘ (Spec (CommRingCat.of 𝕜)))
      = Spec.map (CommRingCat.ofHom (algebraMap (MvPolynomial (Fin n) 𝕜) (Localization.Away F)))
        ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝕜 (MvPolynomial (Fin n) 𝕜))) := by
    show Spec.map (CommRingCat.ofHom (algebraMap 𝕜 (Localization.Away F))) = _
    rw [IsScalarTower.algebraMap_eq 𝕜 (MvPolynomial (Fin n) 𝕜) (Localization.Away F),
      CommRingCat.ofHom_comp, Spec.map_comp]
  have h2 : (((basicOpen 𝕜 n F).toScheme) ↘ (Spec (CommRingCat.of 𝕜)))
      = (basicOpen 𝕜 n F).ι
        ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝕜 (MvPolynomial (Fin n) 𝕜))) := rfl
  rw [h1, h2, awayIso_hom 𝕜 n F]
  rw [← Category.assoc, AlgebraicGeometry.basicOpenIsoSpecAway_hom_SpecMap
    (R := CommRingCat.of (MvPolynomial (Fin n) 𝕜)) F]

private lemma awayIso_inv_structure (𝕜 : Type) [Field 𝕜] (n : ℕ)
    (F : MvPolynomial (Fin n) 𝕜) :
    (awayIso 𝕜 n F).inv
        ≫ (((basicOpen 𝕜 n F).toScheme) ↘ (Spec (CommRingCat.of 𝕜)))
      = ((Spec (CommRingCat.of (Localization.Away F))) ↘ (Spec (CommRingCat.of 𝕜))) := by
  rw [← awayIso_hom_structure 𝕜 n F, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- `Spec.map Φ` is a morphism over `Spec 𝕜` (the algebra isomorphism `Φ` is `𝕜`-linear). -/
private lemma specMap_away_structure (𝕜 : Type) [Field 𝕜] (n : ℕ)
    (F G : MvPolynomial (Fin n) 𝕜) (Φ : Localization.Away F ≃ₐ[𝕜] Localization.Away G) :
    Spec.map (CommRingCat.ofHom Φ.toRingEquiv.toRingHom)
        ≫ ((Spec (CommRingCat.of (Localization.Away F))) ↘ (Spec (CommRingCat.of 𝕜)))
      = ((Spec (CommRingCat.of (Localization.Away G))) ↘ (Spec (CommRingCat.of 𝕜))) := by
  show _ ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝕜 (Localization.Away F)))
      = Spec.map (CommRingCat.ofHom (algebraMap 𝕜 (Localization.Away G)))
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext a
  exact Φ.commutes a

private lemma specMapIso_hom_eq (𝕜 : Type) [Field 𝕜] (n : ℕ)
    (F G : MvPolynomial (Fin n) 𝕜) (Φ : Localization.Away F ≃ₐ[𝕜] Localization.Away G) :
    (Scheme.Spec.mapIso (Φ.toRingEquiv.toCommRingCatIso.op)).hom
      = Spec.map (CommRingCat.ofHom Φ.toRingEquiv.toRingHom) := by
  rw [Functor.mapIso_hom, Iso.op_hom, RingEquiv.toCommRingCatIso_hom]
  rfl

/-- A scheme isomorphism compatible with the structure morphisms to a base `S` is a partial
isomorphism over `S`, with source and target everything. -/
private lemma partialIso_ofIso_isOver {S : Scheme.{0}} {X Y : Scheme.{0}} [X.Over S]
    [Y.Over S] (e : X ≅ Y) (he : e.hom ≫ (Y ↘ S) = (X ↘ S)) :
    (PartialIso.ofIso e).IsOver (X ↘ S) (Y ↘ S) := by
  rw [PartialIso.IsOver]
  show (X.topIso ≪≫ e ≪≫ Y.topIso.symm).hom ≫ (⊤ : Y.Opens).ι ≫ (Y ↘ S)
      = (⊤ : X.Opens).ι ≫ (X ↘ S)
  rw [Iso.trans_hom, Iso.trans_hom]
  simp only [Category.assoc]
  rw [show Y.topIso.symm.hom ≫ (⊤ : Y.Opens).ι ≫ (Y ↘ S) = (Y ↘ S) from
    Y.topIso.inv_hom_id_assoc (Y ↘ S)]
  rw [he, Scheme.topIso_hom]

/-- **An isomorphism of localisations away from `F` and `G` gives an isomorphism `D(G) ≅ D(F)`
over `Spec 𝕜`**, as a partial isomorphism with source and target everything: the composite
`D(G) ≅ Spec 𝕜[G⁻¹] --Spec.map Φ--> Spec 𝕜[F⁻¹] ≅ D(F)`. -/
private theorem exists_partialIso_away (𝕜 : Type) [Field 𝕜] (n : ℕ)
    (F G : MvPolynomial (Fin n) 𝕜) (hF : F ≠ 0) (hG : G ≠ 0)
    (Φ : Localization.Away F ≃ₐ[𝕜] Localization.Away G) :
    ∃ β : ((basicOpen 𝕜 n G).toScheme).PartialIso ((basicOpen 𝕜 n F).toScheme),
      β.source = ⊤ ∧ β.target = ⊤ ∧
      β.IsOver (((basicOpen 𝕜 n G).toScheme) ↘ (Spec (CommRingCat.of 𝕜)))
        (((basicOpen 𝕜 n F).toScheme) ↘ (Spec (CommRingCat.of 𝕜))) := by
  let iso : ((basicOpen 𝕜 n G).toScheme) ≅ ((basicOpen 𝕜 n F).toScheme) :=
    (awayIso 𝕜 n G) ≪≫ (Scheme.Spec.mapIso (Φ.toRingEquiv.toCommRingCatIso.op))
      ≪≫ (awayIso 𝕜 n F).symm
  have hiso : iso.hom ≫ (((basicOpen 𝕜 n F).toScheme) ↘ (Spec (CommRingCat.of 𝕜)))
      = (((basicOpen 𝕜 n G).toScheme) ↘ (Spec (CommRingCat.of 𝕜))) := by
    rw [show iso.hom = (awayIso 𝕜 n G).hom
        ≫ (Scheme.Spec.mapIso (Φ.toRingEquiv.toCommRingCatIso.op)).hom
        ≫ (awayIso 𝕜 n F).inv from rfl]
    rw [specMapIso_hom_eq 𝕜 n F G Φ]
    simp only [Category.assoc]
    rw [awayIso_inv_structure 𝕜 n F, specMap_away_structure 𝕜 n F G Φ,
      awayIso_hom_structure 𝕜 n G]
  refine ⟨PartialIso.ofIso iso, ?_, ?_, ?_⟩
  · rw [PartialIso.ofIso_source]
  · rw [PartialIso.ofIso_target]
  · exact partialIso_ofIso_isOver iso hiso

/-- Audit node **A1, computational core** (the "basic-open formula").

Notation (from `Submission/Work/MotA/Defs.lean` and `Submission/Work/Motivic/Defs.lean`):
`Work.MotA.polySpec 𝕜 n = AlgebraicGeometry.Spec (CommRingCat.of (MvPolynomial (Fin n) 𝕜))` is
affine `n`-space, `Work.MotA.divCount 𝕜 n F z` counts the codimension-one points of `𝔸ⁿ` lying on
`V(F)` whose residue field is `𝕜`-isomorphic to `κ(z)`, and `cInv 𝕜 z f = excCount 𝕜 z f.symm -
excCount 𝕜 z f` is the `[κ(z)]`-coefficient of the Lin–Shinder invariant (root-level definition).

**Claim.** For any isomorphism `Φ : Localization.Away F ≃ₐ[𝕜] Localization.Away G` (with `F`, `G`
nonzero) there is a birational self-map `f` of `X = Work.MotA.polySpec 𝕜 n` over `Spec 𝕜` whose
invariant coefficient at any base point `z` is the difference of the two divisor counts.

Construction.  Put `U_F = Work.MotA.basicOpen 𝕜 n F = D(F)`, `U_G = D(G)` (dense by
`Work.MotA.basicOpen_dense`; the instances `IrreducibleSpace ↑U_F` and `IrreducibleSpace ↑U_G`
come from `Work.CrauderKatz.BlowUp.irreducibleSpace_opensOfDense`).  Let
* `α : X ⤏ U_G` be `Work.MotA.basicOpenBirationalMap 𝕜 n G hG`, the inverse of the open
  immersion `U_G ↪ X` (definitionally `(U_G.partialIsoOfDense _).symm.toBirationalMap`);
* `γ : U_F ⤏ X` be the birational map of the open immersion, i.e.
  `(U_F.partialIsoOfDense _).toBirationalMap`;
* `β : U_G.PartialIso U_F` with `iso` the composite `U_G.toScheme ≅ Spec (Localization.Away G)
  --Spec.map Φ--> Spec (Localization.Away F) ≅ U_F.toScheme`, where the outer isomorphisms are
  `IsAffineOpen.isoSpec` of `AlgebraicGeometry.Scheme.Spec_basicOpen` composed with the ring
  isomorphism induced by `IsLocalization.algEquiv (Submonoid.powers F) (Localization.Away F)
  Γ(X, U_F)` (an isomorphism because `IsLocalization.Away F Γ(X, U_F)` is an instance in
  `Mathlib/AlgebraicGeometry/AffineScheme.lean`), and put
  `f := α.trans (β.toBirationalMap.trans γ)`.

Then `Work.Motivic.cInv_add` (twice) gives `cInv 𝕜 z f = cInv 𝕜 z α + cInv 𝕜 z β + cInv 𝕜 z γ`:
* `cInv 𝕜 z α = -divCount 𝕜 n G z` (its `excCount` is `divCount` by
  `Work.MotA.excCount_basicOpenBirationalMap`, and `exDiv α.symm = ∅` because `α.symm` is
  represented by a partial isomorphism with source everything);
* `cInv 𝕜 z β = 0` because `β` is an isomorphism, hence a pseudo-isomorphism with source and target
  everything (`Work.Motivic.pseudoReg_cInv_toBirationalMap`) — or prove `exDiv β = exDiv β.symm = ∅`;
* `cInv 𝕜 z γ = divCount 𝕜 n F z` since `exDiv γ = ∅` (source is everything) and
  `γ.symm.toBirationalMap` is definitionally `Work.MotA.basicOpenBirationalMap 𝕜 n F hF`, whose
  `excCount` is `divCount` by the same result applied to `F`.

If your construction produces the opposite sign, replace `f` by `f.symm` (`cInv` of the inverse is
the negative, `Work.LLink.cInv_eq_neg_symm`).

Every leg is a morphism over `Spec 𝕜`: `Opens.birationalOver_of_dense` supplies the `IsOver`
condition for the open-immersion partial isomorphisms, `Spec.map Φ` is over `Spec 𝕜` because `Φ` is
a `𝕜`-algebra isomorphism, and `Work.Motivic.pseudoReg_isOver_trans` /
`Work.Motivic.pseudoReg_isOver_toBirationalMap` assemble the composite (`BirationalMap.trans` and
`PartialIso.toBirationalMap` are plain definitions, so instance search does not unfold them). -/
theorem exists_awayBirationalMap_cInv (𝕜 : Type) [Field 𝕜] (n : ℕ)
    (F G : MvPolynomial (Fin n) 𝕜) (hF : F ≠ 0) (hG : G ≠ 0)
    (Φ : Localization.Away F ≃ₐ[𝕜] Localization.Away G) :
    ∃ f : (Work.MotA.polySpec 𝕜 n).BirationalMap (Work.MotA.polySpec 𝕜 n),
      f.IsOver (AlgebraicGeometry.Spec (CommRingCat.of 𝕜)) ∧
      ∀ {Z : AlgebraicGeometry.Scheme.{0}} [Z.Over (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))]
        (z : Z), cInv 𝕜 z f
          = (Work.MotA.divCount 𝕜 n F z : ℤ) - (Work.MotA.divCount 𝕜 n G z : ℤ) := by
  -- the two basic opens are varieties (dense opens of the irreducible `𝔸ⁿ`)
  letI hIrrG : IrreducibleSpace ((basicOpen 𝕜 n G).toScheme) :=
    irreducibleSpace_basicOpen 𝕜 n G hG
  letI hIrrF : IrreducibleSpace ((basicOpen 𝕜 n F).toScheme) :=
    irreducibleSpace_basicOpen 𝕜 n F hF
  letI hIntG : IsIntegral ((basicOpen 𝕜 n G).toScheme) :=
    isIntegral_of_irreducibleSpace_of_isReduced _
  letI hIntF : IsIntegral ((basicOpen 𝕜 n F).toScheme) :=
    isIntegral_of_irreducibleSpace_of_isReduced _
  letI hSepG : IsSeparated (((basicOpen 𝕜 n G).toScheme) ↘ (Spec (CommRingCat.of 𝕜))) :=
    isSeparated_basicOpen 𝕜 n G
  letI hSepF : IsSeparated (((basicOpen 𝕜 n F).toScheme) ↘ (Spec (CommRingCat.of 𝕜))) :=
    isSeparated_basicOpen 𝕜 n F
  letI hLftG : LocallyOfFiniteType (((basicOpen 𝕜 n G).toScheme) ↘ (Spec (CommRingCat.of 𝕜))) :=
    locallyOfFiniteType_basicOpen 𝕜 n G
  letI hLftF : LocallyOfFiniteType (((basicOpen 𝕜 n F).toScheme) ↘ (Spec (CommRingCat.of 𝕜))) :=
    locallyOfFiniteType_basicOpen 𝕜 n F
  letI hQcG : QuasiCompact (((basicOpen 𝕜 n G).toScheme) ↘ (Spec (CommRingCat.of 𝕜))) :=
    quasiCompact_basicOpen 𝕜 n G
  letI hQcF : QuasiCompact (((basicOpen 𝕜 n F).toScheme) ↘ (Spec (CommRingCat.of 𝕜))) :=
    quasiCompact_basicOpen 𝕜 n F
  letI hVarG : Variety 𝕜 ((basicOpen 𝕜 n G).toScheme) := ⟨⟩
  letI hVarF : Variety 𝕜 ((basicOpen 𝕜 n F).toScheme) := ⟨⟩
  -- the three legs `α : X ⤏ D(G)`, `β : D(G) ≅ D(F)`, `γ : D(F) ⤏ X`
  obtain ⟨β, hβsrc, hβtgt, hβover⟩ := exists_partialIso_away 𝕜 n F G hF hG Φ
  let α : (polySpec 𝕜 n).BirationalMap ((basicOpen 𝕜 n G).toScheme) :=
    basicOpenBirationalMap 𝕜 n G hG
  let γ : ((basicOpen 𝕜 n F).toScheme).BirationalMap (polySpec 𝕜 n) :=
    ((basicOpen 𝕜 n F).partialIsoOfDense (basicOpen_dense 𝕜 n F hF)).toBirationalMap
  let ψ : ((basicOpen 𝕜 n G).toScheme).BirationalMap (polySpec 𝕜 n) :=
    β.toBirationalMap.trans γ
  let f : (polySpec 𝕜 n).BirationalMap (polySpec 𝕜 n) := α.trans ψ
  -- every leg is a morphism over `Spec 𝕜`
  letI hαo : α.IsOver (Spec (CommRingCat.of 𝕜)) :=
    Work.Motivic.pseudoReg_isOver_toBirationalMap
      (((basicOpen 𝕜 n G).partialIsoOfDense (basicOpen_dense 𝕜 n G hG)).symm)
      (PartialIso.IsOver.symm (partialIsoOfDense_isOver 𝕜 n G hG))
  letI hβo : β.toBirationalMap.IsOver (Spec (CommRingCat.of 𝕜)) :=
    Work.Motivic.pseudoReg_isOver_toBirationalMap β hβover
  letI hγo : γ.IsOver (Spec (CommRingCat.of 𝕜)) :=
    Work.Motivic.pseudoReg_isOver_toBirationalMap
      ((basicOpen 𝕜 n F).partialIsoOfDense (basicOpen_dense 𝕜 n F hF))
      (partialIsoOfDense_isOver 𝕜 n F hF)
  letI hψo : ψ.IsOver (Spec (CommRingCat.of 𝕜)) :=
    Work.Motivic.pseudoReg_isOver_trans β.toBirationalMap γ
  have hfo : f.IsOver (Spec (CommRingCat.of 𝕜)) :=
    Work.Motivic.pseudoReg_isOver_trans α ψ
  refine ⟨f, hfo, ?_⟩
  intro Z hZ z
  -- additivity of the invariant coefficient, in two steps
  have h1 : cInv 𝕜 z f = cInv 𝕜 z α + cInv 𝕜 z ψ :=
    @Work.Motivic.cInv_add 𝕜 _ (polySpec 𝕜 n) ((basicOpen 𝕜 n G).toScheme) (polySpec 𝕜 n) Z
      (inferInstance : Variety 𝕜 (polySpec 𝕜 n)) hVarG (inferInstance : Variety 𝕜 (polySpec 𝕜 n))
      hZ z α ψ hαo hψo
  have h2 : cInv 𝕜 z ψ = cInv 𝕜 z β.toBirationalMap + cInv 𝕜 z γ :=
    @Work.Motivic.cInv_add 𝕜 _ ((basicOpen 𝕜 n G).toScheme) ((basicOpen 𝕜 n F).toScheme)
      (polySpec 𝕜 n) Z hVarG hVarF (inferInstance : Variety 𝕜 (polySpec 𝕜 n))
      hZ z β.toBirationalMap γ hβo hγo
  -- the isomorphism `β` contributes nothing (it is a pseudo-isomorphism with source and target ⊤)
  have hβcInv : cInv 𝕜 z β.toBirationalMap = 0 :=
    Work.LLink.cInv_eq_zero_of_isPseudoIso 𝕜 z β
      ⟨(fun x hx => by rw [hβsrc] at hx; exact absurd trivial hx),
       (fun y hy => by rw [hβtgt] at hy; exact absurd trivial hy)⟩
  -- the inverse of the open immersion `D(G) ↪ 𝔸ⁿ`: everything comes from the target side
  have hαcInv : cInv 𝕜 z α = -(divCount 𝕜 n G z : ℤ) := by
    let iG : ((basicOpen 𝕜 n G).toScheme).PartialIso (polySpec 𝕜 n) :=
      (basicOpen 𝕜 n G).partialIsoOfDense (basicOpen_dense 𝕜 n G hG)
    have hEqα : α = iG.toBirationalMap.symm := by
      rw [show α = iG.symm.toBirationalMap from rfl]
      exact (Work.MotA.PartialIso.toBirationalMap_symm iG).symm
    rw [hEqα, Work.MotA.cInv_symm_of_partialIso_source_eq_top iG
      (by rw [Opens.partialIsoOfDense_source]) z]
    have hset : {y : polySpec 𝕜 n | Order.coheight y = 1 ∧
          y ∉ ((iG.target : Set (polySpec 𝕜 n))) ∧ ResEquiv 𝕜 y z}
        = {y : polySpec 𝕜 n | Order.coheight y = 1 ∧ G ∈ y.asIdeal ∧ ResEquiv 𝕜 y z} := by
      ext y
      simp only [Set.mem_ofPred_eq]
      constructor
      · rintro ⟨h1, h2, h3⟩
        refine ⟨h1, ?_, h3⟩
        rw [Opens.partialIsoOfDense_target] at h2
        simpa [mem_basicOpen_iff] using h2
      · rintro ⟨h1, h2, h3⟩
        refine ⟨h1, ?_, h3⟩
        rw [Opens.partialIsoOfDense_target]
        simpa [mem_basicOpen_iff] using h2
    simp only [divCount]
    rw [hset]
  -- the open immersion `D(F) ↪ 𝔸ⁿ`: the missing divisors are those with `F ∈ y.asIdeal`
  have hγcInv : cInv 𝕜 z γ = (divCount 𝕜 n F z : ℤ) := by
    let iF : ((basicOpen 𝕜 n F).toScheme).PartialIso (polySpec 𝕜 n) :=
      (basicOpen 𝕜 n F).partialIsoOfDense (basicOpen_dense 𝕜 n F hF)
    have hEqγ : γ = iF.toBirationalMap := rfl
    rw [hEqγ, Work.MotA.cInv_of_partialIso_source_eq_top iF
      (by rw [Opens.partialIsoOfDense_source]) z]
    have hset : {y : polySpec 𝕜 n | Order.coheight y = 1 ∧
          y ∉ ((iF.target : Set (polySpec 𝕜 n))) ∧ ResEquiv 𝕜 y z}
        = {y : polySpec 𝕜 n | Order.coheight y = 1 ∧ F ∈ y.asIdeal ∧ ResEquiv 𝕜 y z} := by
      ext y
      simp only [Set.mem_ofPred_eq]
      constructor
      · rintro ⟨h1, h2, h3⟩
        refine ⟨h1, ?_, h3⟩
        rw [Opens.partialIsoOfDense_target] at h2
        simpa [mem_basicOpen_iff] using h2
      · rintro ⟨h1, h2, h3⟩
        refine ⟨h1, ?_, h3⟩
        rw [Opens.partialIsoOfDense_target]
        simpa [mem_basicOpen_iff] using h2
    simp only [divCount]
    rw [hset]
  rw [h1, h2, hαcInv, hβcInv, hγcInv]
  first | refl_ring1 | ring

end Work.MotA
