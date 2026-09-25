import Mathlib
import Submission.NK.LocalCFT.Basic
import Submission.NK.LocalCFT.Reduction.Defs

/-!
# The Artin reciprocity datum from the compatible reciprocity law

`NK.LocalCFT.ReciprocityLaw F F'` is the reciprocity law of local class field theory in its
*canonical, compatible* form: at every finite abelian Galois level `L ≤ F^{ab}` it gives an
isomorphism `Fˣ ⧸ N_{L/F} Lˣ ≃* Gal(L/F)`, and these isomorphisms are compatible with the
restriction maps between levels.  `NK.LocalCFT.ExistenceTheorem F F'` is the existence theorem
(cofinality of the norm groups).

The point of this file is that the Artin map `Fˣ →* Gal(F^{ab}/F)` is *not* extra data: it is the
inverse limit of the compatible family of level isomorphisms.  Concretely, a monoid homomorphism
into `Gal(F^{ab}/F) ≅ lim_L Gal(L/F)` (the projective limit over the finite Galois levels `L` of
`F^{ab}/F`) is exactly a compatible family of elements of the `Gal(L/F)`, and the level isomorphisms
supplied by the reciprocity law are such a family.  Taking the corresponding element of the limit
and transporting it back to `Gal(F^{ab}/F)` along Mathlib's
`InfiniteGalois.mulEquivToLimit` produces the Artin map, and the reciprocity isomorphisms at the
levels are recovered by construction.

## Main definition

* `NK.LocalCFT.Reduction.artinMap` — the Artin map `Fˣ →* Gal(F^{ab}/F)` obtained from a
  `ReciprocityLaw`;

## Main result

* `NK.LocalCFT.Reduction.nonempty_artinReciprocity_of_reciprocityLaw` — the reciprocity law
  together with the existence theorem yields the full Artin reciprocity datum.
-/

open scoped Classical
open CategoryTheory Opposite

namespace NK.LocalCFT.Reduction

universe u v

noncomputable section

set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

variable {F : Type u} {F' : Type v} [Field F] [Field F'] [Algebra F F'] [IsGalois F F']

/-- **Every finite normal subextension of `F^{ab}` is abelian over `F`.**  The Galois group of
`F^{ab}/F` is abelian, and restriction to a finite normal level is surjective. -/
theorem commutative_level (L : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'))
    [Normal F L] : ∀ σ τ : ↥L ≃ₐ[F] ↥L, σ * τ = τ * σ := by
  intro σ τ
  obtain ⟨σ', rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := ↥L)
    (E := ↥(NK.LocalReciprocity.maxAbelianSubext F F')) σ
  obtain ⟨τ', rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := ↥L)
    (E := ↥(NK.LocalReciprocity.maxAbelianSubext F F')) τ
  rw [← map_mul, ← map_mul, NK.LocalReciprocity.commutative_gal_maxAbelianSubext σ' τ']

/-- **The compatible family of reciprocity isomorphisms, as an element of the projective limit.**
For a fixed unit `x : Fˣ` and each finite Galois level `L` of `F^{ab}`, the reciprocity law gives
an element of `Gal(L/F)`; compatibility of the level isomorphisms (`ReciprocityLaw.compat`) says
precisely that these elements form an element of the limit `lim_L Gal(L/F)`. -/
noncomputable def artinLimitHom (hlaw : NK.LocalCFT.ReciprocityLaw F F') :
    Fˣ →* ↑(ProfiniteGrp.limit (InfiniteGalois.asProfiniteGaloisGroupFunctor F
      (NK.LocalReciprocity.maxAbelianSubext F F'))).toProfinite.toTop where
  toFun x :=
    ⟨fun L => hlaw.levelEquiv
        (L.unop : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'))
        (commutative_level (L.unop : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F')))
        (QuotientGroup.mk x),
      fun {L₁ L₂} π => by
        show NK.LocalCFT.levelRestrictLe (leOfHom π.unop)
            (hlaw.levelEquiv (L₁.unop : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'))
              _ (QuotientGroup.mk x)) =
          hlaw.levelEquiv (L₂.unop : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'))
            _ (QuotientGroup.mk x)
        rw [NK.LocalCFT.ReciprocityLaw.compat hlaw L₁.unop L₂.unop _ _
          (leOfHom π.unop) x]
        refine congrArg (fun z => hlaw.levelEquiv
          (L₂.unop : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'))
          (commutative_level
            (L₂.unop : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'))) z) ?_
        exact (QuotientGroup.map_mk
          (NK.LocalReciprocity.normGroup F
            ↥(L₁.unop : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F')))
          (NK.LocalReciprocity.normGroup F
            ↥(L₂.unop : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F')))
          (MonoidHom.id Fˣ)
          (NK.LocalCFT.normGroup_le_of_le (leOfHom π.unop)) x).trans rfl⟩
  map_one' := by
    apply ProfiniteGrp.limit_ext
    intro L
    rw [ProfiniteGrp.limit_one_val]
    simp only [Subtype.coe_mk]
    rw [QuotientGroup.mk_one, map_one]
  map_mul' x y := by
    apply ProfiniteGrp.limit_ext
    intro L
    rw [ProfiniteGrp.limit_mul_val]
    simp only [Subtype.coe_mk]
    rw [QuotientGroup.mk_mul, map_mul]

/-- **The Artin map** `Fˣ →* Gal(F^{ab}/F)` attached to a reciprocity law: the element of the
projective limit provided by the compatible level isomorphisms, transported back to
`Gal(F^{ab}/F)`. -/
noncomputable def artinMap (hlaw : NK.LocalCFT.ReciprocityLaw F F') : Fˣ →* AbGal F F' :=
  ((InfiniteGalois.mulEquivToLimit F
      (NK.LocalReciprocity.maxAbelianSubext F F')).symm).toMonoidHom.comp (artinLimitHom hlaw)

/-- The Artin map restricts to the reciprocity isomorphism at every finite abelian Galois level. -/
theorem artinMap_restrict (hlaw : NK.LocalCFT.ReciprocityLaw F F') (x : Fˣ)
    (L : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'))
    [FiniteDimensional F L] [Normal F L]
    (hcomm : ∀ σ τ : ↥L ≃ₐ[F] ↥L, σ * τ = τ * σ) :
    NK.LocalCFT.levelRestrict L (artinMap hlaw x) =
      hlaw.levelEquiv L hcomm (QuotientGroup.mk x) := by
  -- view the level `L` as a `FiniteGaloisIntermediateField` (it is normal, finite and separable)
  let L₀ : FiniteGaloisIntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F') :=
    { toIntermediateField := L
      finiteDimensional := inferInstance
      isGalois := isGalois_iff.mpr ⟨inferInstance, inferInstance⟩ }
  -- the compatible family used to define `artinMap` is the image of `artinMap` under
  -- `algEquivToLimit`
  have h1 : InfiniteGalois.algEquivToLimit F (NK.LocalReciprocity.maxAbelianSubext F F')
      (artinMap hlaw x) = artinLimitHom hlaw x :=
    MulEquiv.apply_symm_apply
      (InfiniteGalois.mulEquivToLimit F (NK.LocalReciprocity.maxAbelianSubext F F'))
      (artinLimitHom hlaw x)
  -- evaluate both sides of `h1` at the level `L₀`
  have h2 := congrArg (fun g => g.val (Opposite.op L₀)) h1
  rw [show NK.LocalCFT.levelRestrict L (artinMap hlaw x) =
      (InfiniteGalois.algEquivToLimit F (NK.LocalReciprocity.maxAbelianSubext F F')
        (artinMap hlaw x)).val (Opposite.op L₀) from rfl]
  rw [h2]
  rw [show (artinLimitHom hlaw x).val (Opposite.op L₀) =
      hlaw.levelEquiv L₀
        (commutative_level (L₀ : IntermediateField F
          (NK.LocalReciprocity.maxAbelianSubext F F'))) (QuotientGroup.mk x) from rfl]

theorem nonempty_artinReciprocity_of_reciprocityLaw {F : Type u} {F' : Type v} [Field F]
    [Field F'] [Algebra F F'] [IsGalois F F'] (hlaw : NK.LocalCFT.ReciprocityLaw F F')
    (hex : NK.LocalCFT.ExistenceTheorem F F') :
    Nonempty (NK.LocalCFT.ArtinReciprocity F F') := by
  refine ⟨{ artin := artinMap hlaw, isLevelIso := ?_, cofinal := hex }⟩
  intro L hfd hnorm hcomm
  have heq : (NK.LocalCFT.levelRestrict L).comp (artinMap hlaw) =
      (hlaw.levelEquiv L hcomm).toMonoidHom.comp
        (QuotientGroup.mk' (NK.LocalReciprocity.normGroup F ↥L)) := by
    refine MonoidHom.ext fun x => ?_
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, QuotientGroup.mk'_apply]
    exact artinMap_restrict hlaw x L hcomm
  constructor
  · rw [heq]
    exact (hlaw.levelEquiv L hcomm).surjective.comp (QuotientGroup.mk'_surjective _)
  · rw [heq, MonoidHom.ker_comp_of_injective _ _ (hlaw.levelEquiv L hcomm).injective,
      QuotientGroup.ker_mk']

end

end NK.LocalCFT.Reduction
