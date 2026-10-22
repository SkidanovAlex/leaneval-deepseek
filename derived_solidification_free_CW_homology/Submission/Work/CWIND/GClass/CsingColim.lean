import Mathlib
import Submission.Work.CWIND.GClass.ExhSetup
import Submission.Work.CWIND.GClass.Prelim

-- The expressions `(CsingExh A hmono ⋙ eval _ _ (-k)).obj n` and
-- `((CsrcFunctor.obj ↧↑(A n)).extend embeddingDownNat).X (-k)` are definitionally equal, but only
-- after unfolding the definition of `CsingExh`; several tactics below (in particular `simp`'s
-- internal type checks and `rw`'s keyed matching) would otherwise refuse to see this.  The same
-- option is used throughout `Mathlib/Algebra/Homology/Embedding/` for exactly this reason.
set_option backward.isDefEq.respectTransparency false

namespace Work.CWIND.GClass

open CategoryTheory CategoryTheory.Limits LightCondensed LightProfinite
open LightCondensed.Solid Submission.Blueprint
open scoped Simplicial
open Work.CWIND Work.CWIND.GClass

noncomputable section

/-! ## Auxiliary lemmas for the singular-chain side of the exhaustion

The degreewise colimit of the exhaustion of singular chains is proved at the level of the
simplices.  The three lemmas below record the facts about the singular simplicial set of a
topological space that are needed: the description of the map induced on `k`-simplices by a map of
spaces (postcomposition), its injectivity for monomorphisms, and the vanishing of the singular
chain complex in positive cohomological degrees (it is the extension of an `ℕ`-chain complex along
`ComplexShape.embeddingDownNat`). -/

/-- The `k`-simplices of `Z` obtained from those of `Y` by a map `f : Y ⟶ Z` are the
postcompositions with `f`. -/
lemma csing_toSSetObjEquiv_map_app {Y Z : TopCat.{0}} (f : Y ⟶ Z) (k : ℕ)
    (τ : (TopCat.toSSet.obj Y).obj (Opposite.op ⦋k⦌)) :
    (TopCat.toSSetObjEquiv Z (Opposite.op ⦋k⦌)) ((TopCat.toSSet.map f).app (Opposite.op ⦋k⦌) τ) =
      f.hom.comp (TopCat.toSSetObjEquiv Y (Opposite.op ⦋k⦌) τ) := rfl

/-- Postcomposition with an injective continuous map is injective on `k`-simplices. -/
lemma csing_toSSet_map_app_injective {Y Z : TopCat.{0}} (f : Y ⟶ Z)
    (hf : Function.Injective f.hom) (k : ℕ) :
    Function.Injective ((TopCat.toSSet.map f).app (Opposite.op ⦋k⦌)) := by
  intro x y hxy
  have hu := congrArg (TopCat.toSSetObjEquiv Z (Opposite.op ⦋k⦌)) hxy
  rw [csing_toSSetObjEquiv_map_app f k x, csing_toSSetObjEquiv_map_app f k y] at hu
  apply (TopCat.toSSetObjEquiv Y (Opposite.op ⦋k⦌)).injective
  apply ContinuousMap.ext
  intro s
  exact hf (congrFun (congrArg DFunLike.coe hu) s)

/-- The legs of the exhaustion cocone of `k`-simplices are injective. -/
lemma csing_types_hinj {X : TopCat.{0}} (A : ℕ → Set X) (k : ℕ) :
    ∀ n, Function.Injective ((TopCat.toSSet.map (inclTop (A n))).app (Opposite.op ⦋k⦌)) :=
  fun n => csing_toSSet_map_app_injective (inclTop (A n)) Subtype.val_injective k

/-- The legs of the exhaustion cocone of `k`-simplices are jointly surjective: a continuous map
`Δᵏ ⟶ X` has compact image, hence lands in some `A n`. -/
lemma csing_types_hsurj {X : TopCat.{0}} (A : ℕ → Set X) (k : ℕ)
    (hcpt : ∀ K : Set X, IsCompact K → ∃ n, K ⊆ A n) :
    ∀ y : (TopCat.toSSet.obj X).obj (Opposite.op ⦋k⦌),
      ∃ n, ∃ x : (TopCat.toSSet.obj (TopCat.of (A n))).obj (Opposite.op ⦋k⦌),
        (TopCat.toSSet.map (inclTop (A n))).app (Opposite.op ⦋k⦌) x = y := by
  intro y
  haveI : CompactSpace ↥(Δ k) := Convexity.StdSimplex.compactSpace ℝ (Fin (k + 1))
  let g : C(Δ k, X) := TopCat.toSSetObjEquiv X (Opposite.op ⦋k⦌) y
  obtain ⟨n, hn⟩ := hcpt (Set.range g) (isCompact_range g.continuous)
  refine ⟨n, (TopCat.toSSetObjEquiv (TopCat.of (A n)) (Opposite.op ⦋k⦌)).symm
    ⟨fun s => ⟨g s, hn ⟨s, rfl⟩⟩, Continuous.subtype_mk g.continuous fun s => hn ⟨s, rfl⟩⟩, ?_⟩
  apply (TopCat.toSSetObjEquiv X (Opposite.op ⦋k⦌)).injective
  rw [csing_toSSetObjEquiv_map_app (inclTop (A n)) k]
  simp only [Equiv.apply_symm_apply]
  rfl

/-- The singular chain complex of `X` vanishes in positive cohomological degrees: it is the
extension along `ComplexShape.embeddingDownNat` of an `ℕ`-chain complex. -/
lemma csing_isZero_X_of_pos (X : TopCat.{0}) {q : ℤ} (hq : 0 < q) :
    IsZero ((singularChainsLightCondAbComplexFunctor.obj X).X q) :=
  HomologicalComplex.isZero_extend_X (CsrcFunctor.obj X) ComplexShape.embeddingDownNat q
    (fun i hi => by
      simp only [ComplexShape.embeddingDownNat_f] at hi
      omega)

/-- **CWIND/T9, the singular-chain side.**  If every compact subset of `X` is contained in some
`A n`, then the cocone of singular chain complexes `C_sing(A n) → C_sing(X)` (with the maps induced
by the inclusions, `CsingExhCocone`) is a colimit cocone.

Route: `HomologicalComplex.isColimitOfEval` reduces to degrees `q : ℤ`; for `q > 0` both sides
vanish (`HomologicalComplex.isZero_extend_X` for the extension along
`ComplexShape.embeddingDownNat`), and for `q = -k` the degree-`(-k)` cocone is obtained from the
degree-`k` cocone of `CsrcExhCocone` (the same cocone before extension, i.e. of singular chains
`ℤ[Sing_k(-)]`) by `IsColimit.equivOfNatIsoOfIso` using the natural isomorphism
`ComplexShape.embeddingDownNat.extendFunctorCompEvalIso` (whose naturality is
`HomologicalComplex.extendMap_f`), with the cocone iso built by `Cocone.ext`.

The degreewise colimit of `CsrcExhCocone` at `k` comes from the diagram of types
`typeExh A hmono k` of `k`-simplices: its cocone `typeCocone A hmono k` is a colimit by
`Work.CWIND.GClass.types_colim` (legs are injective because `A n ⊆ A (n+1)` is an inclusion of
subspaces, and jointly surjective because a continuous map `Δᵏ → X` has compact image, so its image
lies in some `A n` by `hcpt`); transfer along `Work.CWIND.GClass.coprod_union_colimit` (with
`G = ModuleCat.of ℤ ℤ`) and then along `LightCondensed.discrete` (a left adjoint, hence preserves
colimits); the resulting cocone is definitionally `(HomologicalComplex.eval _ _ k).mapCocone
(CsrcExhCocone A hmono)` (see `SSet.chainComplexXCofan`, `SSet.ιChainComplex`,
`SSet.chainComplexMap`). -/
theorem CsingColim {X : TopCat.{0}} (A : ℕ → Set X) (hmono : Monotone A)
    (hcpt : ∀ K : Set X, IsCompact K → ∃ n, K ⊆ A n) :
    Nonempty (IsColimit (CsingExhCocone A hmono)) := by
  -- The degree `k` cocone of the exhaustion of singular chains before extension is a colimit.
  have hCsrc : ∀ k : ℕ,
      IsColimit ((HomologicalComplex.eval LightCondAb (ComplexShape.down ℕ) k).mapCocone
        (CsrcExhCocone A hmono)) := fun k => by
    have hinj : ∀ n, Function.Injective ((typeCocone A hmono k).ι.app n) :=
      fun n => csing_types_hinj A k n
    have hsurj : ∀ y : (typeCocone A hmono k).pt, ∃ n, ∃ x : (typeExh A hmono k).obj n,
        (typeCocone A hmono k).ι.app n x = y := csing_types_hsurj A k hcpt
    have hc := Classical.choice (coprod_union_colimit (typeCocone A hmono k)
      (ModuleCat.of ℤ ℤ) hinj hsurj)
    haveI : (LightCondensed.discrete (ModuleCat.{0} ℤ)).IsLeftAdjoint :=
      (LightCondensed.discreteUnderlyingAdj (ModuleCat.{0} ℤ)).isLeftAdjoint
    exact isColimitOfPreserves (LightCondensed.discrete (ModuleCat.{0} ℤ)) hc
  -- The degree `-k` cocone of the exhaustion of singular chains.
  have hCsing : ∀ k : ℕ,
      IsColimit ((HomologicalComplex.eval LightCondAb (ComplexShape.up ℤ) (-(k : ℤ))).mapCocone
        (CsingExhCocone A hmono)) := fun k => by
    let α : (CsrcExh A hmono ⋙ HomologicalComplex.eval LightCondAb (ComplexShape.down ℕ) k) ≅
        (CsingExh A hmono ⋙ HomologicalComplex.eval LightCondAb (ComplexShape.up ℤ) (-(k : ℤ))) :=
      Functor.isoWhiskerLeft (CsrcExh A hmono)
        (ComplexShape.embeddingDownNat.extendFunctorCompEvalIso LightCondAb
          (ComplexShape.embeddingDownNat_f k)).symm
    let c := (HomologicalComplex.eval LightCondAb (ComplexShape.down ℕ) k).mapCocone
      (CsrcExhCocone A hmono)
    let d := (HomologicalComplex.eval LightCondAb (ComplexShape.up ℤ) (-(k : ℤ))).mapCocone
      (CsingExhCocone A hmono)
    have w : (Cocone.precompose α.inv).obj c ≅ d := by
      refine Cocone.ext ((CsrcFunctor.obj X).extendXIso ComplexShape.embeddingDownNat
        (ComplexShape.embeddingDownNat_f k)).symm ?_
      intro n
      dsimp only [Cocone.precompose]
      simp only [NatTrans.comp_app]
      dsimp only [α]
      simp only [Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app, Iso.symm_hom, Iso.symm_inv]
      rw [show d.ι.app n = (HomologicalComplex.extendMap (CsrcFunctor.map (inclTop (A n)))
            ComplexShape.embeddingDownNat).f (-(k : ℤ)) from rfl,
        HomologicalComplex.extendMap_f (φ := CsrcFunctor.map (inclTop (A n)))
          (e := ComplexShape.embeddingDownNat) (i := k) (i' := -(k : ℤ))
          (h := (ComplexShape.embeddingDownNat_f k))]
      simp only [Category.assoc]
      rfl
    exact IsColimit.equivOfNatIsoOfIso α c d w (hCsrc k)
  refine ⟨HomologicalComplex.isColimitOfEval (CsingExh A hmono) (CsingExhCocone A hmono) ?_⟩
  intro q
  by_cases hq : 0 < q
  · -- in positive degrees both the diagram and the point vanish
    refine (zero_cocone ((HomologicalComplex.eval LightCondAb (ComplexShape.up ℤ) q).mapCocone
      (CsingExhCocone A hmono)) ?_ ?_).some
    · exact csing_isZero_X_of_pos X hq
    · intro j
      exact csing_isZero_X_of_pos (TopCat.of (A j)) hq
  · -- `q = -k` for `k = (-q).toNat`
    rw [show q = -(((-q).toNat : ℕ) : ℤ) from by omega]
    exact hCsing _

end

end Work.CWIND.GClass
