import Mathlib
import Submission.Work.CWIND.GClass.ExhSetup
import Submission.Work.CWIND.GClass.Prelim
import Submission.Work.CONDMV.Main

namespace Work.CWIND.GClass

open CategoryTheory CategoryTheory.Limits LightCondensed LightProfinite
open LightCondensed.Solid Submission.Blueprint
open scoped Simplicial
open Work.CWIND Work.CWIND.GClass

noncomputable section

/-! ## Auxiliary lemmas for the exhaustion of the compact-open mapping space -/

/-- The subset `B n = {f | ∀ s, f s ∈ A n}` of the compact-open mapping space `X^{Δᵏ}`, the
exhausting family of the mapping space induced by the exhaustion `A` of `X`. -/
def Bset {X : TopCat.{0}} (A : Set X) (k : ℕ) : Set (singSpace X k) :=
  {f | ∀ s, f s ∈ A}

lemma monotone_Bset {X : TopCat.{0}} {A : ℕ → Set X} (hmono : Monotone A) (k : ℕ) :
    Monotone (fun n => Bset (A n) k) := by
  intro m n h f hf s
  exact hmono h (hf s)

/-- Naturality of the homeomorphism `Bset A k ≅ singSpace (TopCat.of A) k` of
`Work.CWIND.GClass.singSpace_subtype_iso` with respect to an inclusion of subspaces: both sides
are the identity on continuous maps, so the square commutes.  This is the naturality of the
diagram isomorphism identifying the exhaustion of the mapping space with the exhaustion of `X`. -/
theorem singSpace_subtype_iso_natural {X : TopCat.{0}} {A B : Set X} (h : A ⊆ B) (k : ℕ)
    (eA : TopCat.of (Bset A k) ≅ singSpace (TopCat.of A) k)
    (eB : TopCat.of (Bset B k) ≅ singSpace (TopCat.of B) k)
    (hA : eA.hom ≫ singSpacePostcomp (inclTop A) k = inclTop (Bset A k))
    (hB : eB.hom ≫ singSpacePostcomp (inclTop B) k = inclTop (Bset B k)) :
    eA.hom ≫ singSpacePostcomp (incl h) k =
      incl (A := Bset A k) (B := Bset B k) (fun g hg => fun s => h (hg s)) ≫ eB.hom := by
  have hinj : Function.Injective (singSpacePostcomp (inclTop B) k) := by
    intro g g' hgg
    apply ContinuousMap.ext
    intro s
    exact Subtype.ext (congrFun (congrArg DFunLike.coe hgg) s)
  have hpost : singSpacePostcomp (incl h) k ≫ singSpacePostcomp (inclTop B) k =
      singSpacePostcomp (inclTop A) k := by
    apply TopCat.ext
    intro g
    rfl
  have hsub : incl (A := Bset A k) (B := Bset B k) (fun g hg s => h (hg s)) ≫
      inclTop (Bset B k) = inclTop (Bset A k) := by
    apply TopCat.ext
    intro g
    rfl
  have key : (eA.hom ≫ singSpacePostcomp (incl h) k) ≫ singSpacePostcomp (inclTop B) k =
      (incl (A := Bset A k) (B := Bset B k) (fun g hg s => h (hg s)) ≫ eB.hom) ≫
        singSpacePostcomp (inclTop B) k := by
    calc (eA.hom ≫ singSpacePostcomp (incl h) k) ≫ singSpacePostcomp (inclTop B) k
        = eA.hom ≫ (singSpacePostcomp (incl h) k ≫
            singSpacePostcomp (inclTop B) k) := Category.assoc _ _ _
      _ = eA.hom ≫ singSpacePostcomp (inclTop A) k := by rw [hpost]
      _ = inclTop (Bset A k) := hA
      _ = incl (A := Bset A k) (B := Bset B k) (fun g hg s => h (hg s)) ≫
            inclTop (Bset B k) := hsub.symm
      _ = incl (A := Bset A k) (B := Bset B k) (fun g hg s => h (hg s)) ≫
            (eB.hom ≫ singSpacePostcomp (inclTop B) k) := by rw [hB]
      _ = (incl (A := Bset A k) (B := Bset B k) (fun g hg s => h (hg s)) ≫ eB.hom) ≫
            singSpacePostcomp (inclTop B) k := (Category.assoc _ _ _).symm
  have : Mono (singSpacePostcomp (inclTop B) k) :=
    ConcreteCategory.mono_of_injective _ hinj
  exact (cancel_mono _).mp key

/-- **CWIND/T9, degreewise.**  At each degree `k`, the degree-`k` part of the exhaustion cocone
`A(A n) → A(X)` — equivalently, the free light condensed abelian groups on the exhaustion of the
compact-open mapping space `X^{Δᵏ}` by the subspaces `B n = {f | ∀ s, f s ∈ A n}` — is a colimit
cocone. -/
theorem AchainExhCocone_degree_colim_aux {X : TopCat.{0}} [T2Space X] (A : ℕ → Set X)
    (hmono : Monotone A) (hcpt : ∀ K : Set X, IsCompact K → ∃ n, K ⊆ A n) (k : ℕ) :
    Nonempty (IsColimit ((HomologicalComplex.eval LightCondAb (ComplexShape.down ℕ) k).mapCocone
      (AchainExhCocone A hmono))) := by
  have hspec : ∀ n, ∃ e : TopCat.of (Bset (A n) k) ≅ singSpace (TopCat.of (A n)) k,
      e.hom ≫ singSpacePostcomp (inclTop (A n)) k = inclTop (Bset (A n) k) :=
    fun n => singSpace_subtype_iso (A n) k
  choose e he using hspec
  obtain ⟨hl⟩ := Work.CONDMV.isColimit_exhaustCocone_free (fun n => Bset (A n) k)
    (monotone_Bset hmono k) (fun K hK => by
      obtain ⟨n, hn⟩ := mapping_compact hcpt k hK
      exact ⟨n, fun f hf s => hn f hf s⟩)
  -- the identification of the exhaustion diagram of the mapping space with the degree-`k` diagram
  let Φ : (Work.CONDMV.exhaustFunctor (fun n => Bset (A n) k) (monotone_Bset hmono k) ⋙
        (LightCondensed.free ℤ)) ≅
      (AchainExh A hmono ⋙ HomologicalComplex.eval LightCondAb (ComplexShape.down ℕ) k) :=
    NatIso.ofComponents
      (fun n => (LightCondensed.free ℤ).mapIso (topCatToLightCondSet.mapIso (e n)))
      (fun {m n} f => by
        show (LightCondensed.free ℤ).map
              (topCatToLightCondSet.map (incl (monotone_Bset hmono k (leOfHom f)))) ≫
            (LightCondensed.free ℤ).map (topCatToLightCondSet.map (e n).hom) =
          (LightCondensed.free ℤ).map (topCatToLightCondSet.map (e m).hom) ≫
            (LightCondensed.free ℤ).map (topCatToLightCondSet.map
              (singSpacePostcomp (incl (hmono (leOfHom f))) k))
        simp only [← Functor.map_comp]
        exact congrArg (fun (φ : TopCat.of (Bset (A m) k) ⟶ singSpace (TopCat.of (A n)) k) =>
            (LightCondensed.free ℤ).map (topCatToLightCondSet.map φ))
          (singSpace_subtype_iso_natural (hmono (leOfHom f)) k (e m) (e n) (he m) (he n)).symm)
  -- the corresponding isomorphism of cocones
  have w : (Cocone.precompose Φ.inv).obj ((LightCondensed.free ℤ).mapCocone
        (Work.CONDMV.exhaustCocone (fun n => Bset (A n) k) (monotone_Bset hmono k))) ≅
      (HomologicalComplex.eval LightCondAb (ComplexShape.down ℕ) k).mapCocone
        (AchainExhCocone A hmono) := by
    refine Cocone.ext (Iso.refl _) ?_
    intro n
    show (LightCondensed.free ℤ).map (topCatToLightCondSet.map (e n).inv) ≫
        (LightCondensed.free ℤ).map (topCatToLightCondSet.map (inclTop (Bset (A n) k))) =
      (LightCondensed.free ℤ).map (topCatToLightCondSet.map
        (singSpacePostcomp (inclTop (A n)) k))
    have hleg : singSpacePostcomp (inclTop (A n)) k =
        (e n).inv ≫ inclTop (Bset (A n) k) := by
      rw [← he n, Iso.inv_hom_id_assoc]
    simp only [← Functor.map_comp]
    exact congrArg (fun (φ : singSpace (TopCat.of (A n)) k ⟶ singSpace X k) =>
        (LightCondensed.free ℤ).map (topCatToLightCondSet.map φ)) hleg.symm
  exact ⟨(IsColimit.equivOfNatIsoOfIso Φ _ _ w) hl⟩

/-- **CWIND/T9, degree shift.**  A colimit at degree `k` of the exhaustion cocone of `ℕ`-chain
complexes gives a colimit at degree `-(k : ℤ)` of the exhaustion cocone of `ℤ`-cochain complexes,
because the extension of complexes identifies the two degrees
(`ComplexShape.embeddingDownNat.extendFunctorCompEvalIso`, naturality by
`HomologicalComplex.extendMap_f`). -/
theorem AexhCocone_eval_neg_of_degree_aux {X : TopCat.{0}} (A : ℕ → Set X)
    (hmono : Monotone A) (k : ℕ)
    (h : Nonempty (IsColimit ((HomologicalComplex.eval LightCondAb (ComplexShape.down ℕ) k).mapCocone
      (AchainExhCocone A hmono)))) :
    Nonempty (IsColimit ((HomologicalComplex.eval LightCondAb (ComplexShape.up ℤ) (-(k : ℤ))).mapCocone
      (AexhCocone A hmono))) := by
  obtain ⟨h⟩ := h
  have hk : ComplexShape.embeddingDownNat.f k = -(k : ℤ) := ComplexShape.embeddingDownNat_f k
  let Ψ : (AchainExh A hmono ⋙ HomologicalComplex.eval LightCondAb (ComplexShape.down ℕ) k) ≅
      (AchainExh A hmono ⋙ (ComplexShape.embeddingDownNat.extendFunctor LightCondAb ⋙
        HomologicalComplex.eval LightCondAb (ComplexShape.up ℤ) (-(k : ℤ)))) :=
    (Functor.isoWhiskerLeft (AchainExh A hmono)
      (ComplexShape.embeddingDownNat.extendFunctorCompEvalIso LightCondAb hk)).symm
  have w : (Cocone.precompose Ψ.inv).obj ((HomologicalComplex.eval LightCondAb
        (ComplexShape.down ℕ) k).mapCocone (AchainExhCocone A hmono)) ≅
      (HomologicalComplex.eval LightCondAb (ComplexShape.up ℤ) (-(k : ℤ))).mapCocone
        (AexhCocone A hmono) := by
    refine Cocone.ext ((Achain X).extendXIso ComplexShape.embeddingDownNat hk).symm ?_
    intro j
    dsimp only [Cocone.precompose, Ψ]
    simp only [Iso.symm_hom, Iso.symm_inv, Functor.isoWhiskerLeft_hom, Functor.mapCocone_ι_app,
      HomologicalComplex.eval_map]
    show (((Achain (TopCat.of (A j))).extendXIso ComplexShape.embeddingDownNat hk).hom ≫
          (AchainFunctor.map (inclTop (A j))).f k) ≫
          ((Achain X).extendXIso ComplexShape.embeddingDownNat hk).inv =
      (HomologicalComplex.extendMap (AchainFunctor.map (inclTop (A j)))
        ComplexShape.embeddingDownNat).f (-(k : ℤ))
    rw [HomologicalComplex.extendMap_f (AchainFunctor.map (inclTop (A j)))
      ComplexShape.embeddingDownNat hk]
    exact Category.assoc _ _ _
  exact ⟨(IsColimit.equivOfNatIsoOfIso Ψ _ _ w) h⟩

/-- **CWIND/T9, the mapping-space side.**  If `X` is Hausdorff and every compact subset of `X` is
contained in some `A n`, then the cocone of complexes `A(A n) → A(X)` (with the maps induced by the
inclusions, `AexhCocone`) is a colimit cocone.

Route: `HomologicalComplex.isColimitOfEval` reduces to degrees `q : ℤ`; for `q > 0` both sides
vanish (`Work.CWIND.isZero_A_X_of_pos`), and for `q = -k` the degree-`(-k)` cocone of `AexhCocone`
is obtained from the degree-`k` cocone of `AchainExhCocone` (whose objects are
`ℤ[singSpace (A n) k] = freeLightCondAbOfTop (singSpace (A n) k)`) by
`IsColimit.equivOfNatIsoOfIso` using `ComplexShape.embeddingDownNat.extendFunctorCompEvalIso`
(naturality: `HomologicalComplex.extendMap_f`), with the cocone iso built by `Cocone.ext`.

The degree-`k` colimit of `AchainExhCocone` is obtained from the exhaustion of the compact-open
mapping space `Σ k = singSpace X k` by the subsets `B n = {f | ∀ s, f s ∈ A n}`: the cocone
`Free ℤ`-image of `Work.CONDMV.exhaustCocone B hmonoB` is a colimit by
`Work.CONDMV.isColimit_exhaustCocone_free` (the compactness hypothesis is
`Work.CWIND.GClass.mapping_compact`), and it is carried to `AchainExhCocone`'s degree-`k` cocone by
the canonical homeomorphism `Work.CWIND.GClass.singSpace_subtype_iso` between
`TopCat.of (B n)` and `singSpace (TopCat.of (A n)) k` (again via
`IsColimit.equivOfNatIsoOfIso`, using `freeLightCondAbOfTopFunctor.mapIso`). -/
theorem AexhColim {X : TopCat.{0}} [T2Space X] (A : ℕ → Set X) (hmono : Monotone A)
    (hcpt : ∀ K : Set X, IsCompact K → ∃ n, K ⊆ A n) :
    Nonempty (IsColimit (AexhCocone A hmono)) := by
  have hdeg : ∀ k : ℕ, Nonempty (IsColimit ((HomologicalComplex.eval LightCondAb
      (ComplexShape.down ℕ) k).mapCocone (AchainExhCocone A hmono))) :=
    fun k => AchainExhCocone_degree_colim_aux A hmono hcpt k
  have hneg : ∀ k : ℕ, Nonempty (IsColimit ((HomologicalComplex.eval LightCondAb
      (ComplexShape.up ℤ) (-(k : ℤ))).mapCocone (AexhCocone A hmono))) :=
    fun k => AexhCocone_eval_neg_of_degree_aux A hmono k (hdeg k)
  refine ⟨HomologicalComplex.isColimitOfEval _ _ (fun q => ?_)⟩
  by_cases hq : 0 < q
  · exact (zero_cocone ((HomologicalComplex.eval LightCondAb (ComplexShape.up ℤ) q).mapCocone
      (AexhCocone A hmono)) (isZero_A_X_of_pos X hq)
      (fun n => isZero_A_X_of_pos (TopCat.of (A n)) hq)).some
  · have hk : q = -(((-q).toNat : ℕ) : ℤ) := by omega
    rw [hk]
    exact (hneg (-q).toNat).some

end

end Work.CWIND.GClass
