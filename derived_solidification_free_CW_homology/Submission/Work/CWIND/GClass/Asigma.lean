import Mathlib
import Submission.Work.CWIND.Basic
import Submission.Work.CWIND.GClass.GTrans
import Submission.Work.CWIND.GClass.SigmaFst

noncomputable section

open CategoryTheory CategoryTheory.Limits LightCondensed LightProfinite
open _root_.LightCondensed _root_.LightCondensed.Solid
open scoped Simplicial

namespace Work.CWIND.GClass

open Work.CWIND

variable {J : Type} (X : J → TopCat.{0})

/-- The disjoint union of the pieces, as a topological space. -/
abbrev sigmaSpace (X : J → TopCat.{0}) : TopCat.{0} := TopCat.of (Σ j, (X j : Type))

/-- The pieces of the disjoint union of the mapping spaces. -/
abbrev sigmaPiece (X : J → TopCat.{0}) (n : ℕ) : J → TopCat.{0} := fun j => singSpace (X j) n

/-- The disjoint union of the mapping spaces `C(Δⁿ, X j)`. -/
abbrev sigmaPt (X : J → TopCat.{0}) (n : ℕ) : TopCat.{0} := TopCat.of (Σ j, singSpace (X j) n)

variable {n : ℕ}

/-- **The comparison isomorphism between the two presentations of the mapping space.**  Given that
the coproduct inclusions `C(Δⁿ, X j) ⟶ C(Δⁿ, ⊔_j X j)` exhibit `C(Δⁿ, ⊔_j X j)` as the coproduct,
this gives the homeomorphism `C(Δⁿ, ⊔_j X j) ≅ ⊔_j C(Δⁿ, X j)`, compatible with the inclusions. -/
theorem exists_sigmaCoprodIso
    (hSig : IsIso (Limits.Sigma.desc (fun j => singSpacePostcomp (TopCat.sigmaι X j) n))) :
    ∃ e : singSpace (sigmaSpace X) n ≅ sigmaPt X n,
      ∀ j, singSpacePostcomp (TopCat.sigmaι X j) n ≫ e.hom =
        TopCat.sigmaι (sigmaPiece X n) j := by
  set p : ∀ j, sigmaPiece X n j ⟶ singSpace (sigmaSpace X) n :=
    fun j => singSpacePostcomp (TopCat.sigmaι X j) n
  haveI hp : IsIso (Limits.Sigma.desc (f := sigmaPiece X n)
    (P := singSpace (sigmaSpace X) n) p) := hSig
  have h1 : IsColimit (Cofan.mk (singSpace (sigmaSpace X) n) p) :=
    isColimit_cofan_of_isIso p
  have h2 : IsColimit (Cofan.mk (sigmaPt X n) (fun j => TopCat.sigmaι (sigmaPiece X n) j)) :=
    TopCat.sigmaCofanIsColimit (sigmaPiece X n)
  have hiso : IsIso (h1.desc (Cofan.mk (sigmaPt X n)
      (fun j => TopCat.sigmaι (sigmaPiece X n) j))) := by
    refine ⟨⟨h2.desc (Cofan.mk (singSpace (sigmaSpace X) n) p), ?_, ?_⟩⟩
    · apply IsColimit.hom_ext h1
      intro j
      rcases j with ⟨j⟩
      rw [IsColimit.fac_assoc h1 (Cofan.mk (sigmaPt X n)
          (fun j => TopCat.sigmaι (sigmaPiece X n) j)) (Discrete.mk j) (h2.desc _),
        IsColimit.fac h2 (Cofan.mk (singSpace (sigmaSpace X) n) p) (Discrete.mk j)]
      simp
    · apply IsColimit.hom_ext h2
      intro j
      rcases j with ⟨j⟩
      rw [IsColimit.fac_assoc h2 (Cofan.mk (singSpace (sigmaSpace X) n) p) (Discrete.mk j)
          (h1.desc _),
        IsColimit.fac h1 (Cofan.mk (sigmaPt X n) (fun j => TopCat.sigmaι (sigmaPiece X n) j))
          (Discrete.mk j)]
      simp
  exact ⟨asIso (h1.desc (Cofan.mk (sigmaPt X n)
      (fun j => TopCat.sigmaι (sigmaPiece X n) j))),
    fun j => by
      simpa [asIso_hom, Cofan.mk_ι_app] using IsColimit.fac h1
        (Cofan.mk (sigmaPt X n) (fun j => TopCat.sigmaι (sigmaPiece X n) j)) (Discrete.mk j)⟩

/-- **The degreewise decomposition of the free light condensed abelian group on the mapping space.**
This is the last step on the `A`-side: `ℤ[C(Δⁿ, ⊔_j X j)] ≅ ⊕_j ℤ[C(Δⁿ, X j)]`. -/
theorem isColimit_freeLightCondAbOfTop_singSpace_sigma
    (hSig : IsIso (Limits.Sigma.desc (fun j => singSpacePostcomp (TopCat.sigmaι X j) n)))
    (hDUS : Nonempty (IsColimit (Cofan.mk (topCatToLightCondSet.obj (sigmaPt X n))
      (fun j => topCatToLightCondSet.map (TopCat.sigmaι (sigmaPiece X n) j))))) :
    Nonempty (IsColimit (Cofan.mk (freeLightCondAbOfTop (singSpace (sigmaSpace X) n))
      (fun j => freeLightCondAbOfTopFunctor.map
        (singSpacePostcomp (TopCat.sigmaι X j) n)))) := by
  obtain ⟨e, he⟩ := exists_sigmaCoprodIso X hSig
  set p : ∀ j, sigmaPiece X n j ⟶ singSpace (sigmaSpace X) n :=
    fun j => singSpacePostcomp (TopCat.sigmaι X j) n with hp
  have hleg : ∀ j, p j = TopCat.sigmaι (sigmaPiece X n) j ≫ e.inv := by
    intro j
    calc p j = p j ≫ 𝟙 (singSpace (sigmaSpace X) n) := (Category.comp_id _).symm
      _ = p j ≫ (e.hom ≫ e.inv) := by rw [Iso.hom_inv_id]
      _ = (p j ≫ e.hom) ≫ e.inv := (Category.assoc _ _ _).symm
      _ = TopCat.sigmaι (sigmaPiece X n) j ≫ e.inv := by rw [he j]
  have h1 : IsColimit (Cofan.mk (topCatToLightCondSet.obj (singSpace (sigmaSpace X) n))
      (fun j => topCatToLightCondSet.map (p j))) := by
    have h := isColimit_cofan_postcomp_iso
      (fun j => topCatToLightCondSet.map (TopCat.sigmaι (sigmaPiece X n) j))
      ((topCatToLightCondSet.mapIso e).symm) hDUS.some
    have hfun : (fun j => topCatToLightCondSet.map (TopCat.sigmaι (sigmaPiece X n) j) ≫
        (topCatToLightCondSet.mapIso e).symm.hom) =
        (fun j => topCatToLightCondSet.map (p j)) := by
      funext j
      rw [show (topCatToLightCondSet.mapIso e).symm.hom = topCatToLightCondSet.map e.inv from by
        rw [Iso.symm_hom, Functor.mapIso_inv], ← Functor.map_comp, ← hleg j]
    have hcoc : Cofan.mk (topCatToLightCondSet.obj (singSpace (sigmaSpace X) n))
        (fun j => topCatToLightCondSet.map (p j)) =
        Cofan.mk (topCatToLightCondSet.obj (singSpace (sigmaSpace X) n))
          (fun j => topCatToLightCondSet.map (TopCat.sigmaι (sigmaPiece X n) j) ≫
            (topCatToLightCondSet.mapIso e).symm.hom) :=
      congrArg (Cofan.mk (topCatToLightCondSet.obj (singSpace (sigmaSpace X) n))) hfun.symm
    rw [← hcoc] at h
    exact h
  haveI : PreservesColimitsOfShape (Discrete J) (LightCondensed.free ℤ) := inferInstance
  exact ⟨isColimit_cofan_map (fun j => topCatToLightCondSet.map (p j))
    (LightCondensed.free ℤ) h1⟩

/-- **The chain complex level.**  Taking the degreewise decomposition through the alternating face
map complex, the chain complex `A_chain(⊔_j X j)` is the coproduct of the `A_chain(X j)`.

The only input beyond the degreewise statement `hdeg` is the general principle that a cofan of chain
complexes whose degreewise cofans are colimits is a colimit; it is passed here as the hypothesis
`hcomp` (see `IsColimitCofanOfComponents`). -/
theorem isColimit_Achain_sigma
    (hcomp : ∀ {J' : Type} {K : J' → ChainComplex LightCondAb ℕ}
      {L : ChainComplex LightCondAb ℕ} (f : ∀ j, K j ⟶ L),
      (∀ n : ℕ, Nonempty (IsColimit (Cofan.mk (L.X n) (fun j => (f j).f n)))) →
        Nonempty (IsColimit (Cofan.mk L f)))
    (hdeg : ∀ n, Nonempty (IsColimit (Cofan.mk
      (freeLightCondAbOfTop (singSpace (sigmaSpace X) n))
      (fun j => freeLightCondAbOfTopFunctor.map
        (singSpacePostcomp (TopCat.sigmaι X j) n))))) :
    Nonempty (IsColimit (Cofan.mk (Achain (sigmaSpace X))
      (fun j => AchainFunctor.map (TopCat.sigmaι X j)))) := by
  refine hcomp (fun j => AchainFunctor.map (TopCat.sigmaι X j)) (fun n => ?_)
  obtain ⟨h⟩ := hdeg n
  have hfun : (fun j => (AchainFunctor.map (TopCat.sigmaι X j)).f n) =
      (fun j => freeLightCondAbOfTopFunctor.map
        (singSpacePostcomp (TopCat.sigmaι X j) n)) := by
    funext j
    simp only [AchainFunctor, Functor.comp_map,
      AlgebraicTopology.alternatingFaceMapComplex_map_f, YFunctor]
    rfl
  have hcoc : Cofan.mk (freeLightCondAbOfTop (singSpace (sigmaSpace X) n))
        (fun j => (AchainFunctor.map (TopCat.sigmaι X j)).f n) =
      Cofan.mk (freeLightCondAbOfTop (singSpace (sigmaSpace X) n))
        (fun j => freeLightCondAbOfTopFunctor.map
          (singSpacePostcomp (TopCat.sigmaι X j) n)) :=
    congrArg (Cofan.mk (freeLightCondAbOfTop (singSpace (sigmaSpace X) n))) hfun
  show Nonempty (IsColimit (Cofan.mk (freeLightCondAbOfTop (singSpace (sigmaSpace X) n))
    (fun j => (AchainFunctor.map (TopCat.sigmaι X j)).f n)))
  rw [hcoc]
  exact ⟨h⟩

/-- **The cochain complex level.**  Transporting the chain level decomposition along the extension
functor gives `A(⊔_j X j) ≅ ⊕_j A(X j)`. -/
theorem isColimit_A_sigma
    (hAch : Nonempty (IsColimit (Cofan.mk (Achain (sigmaSpace X))
      (fun j => AchainFunctor.map (TopCat.sigmaι X j))))) :
    Nonempty (IsColimit (Cofan.mk (AFunctor.obj (sigmaSpace X))
      (fun j => AFunctor.map (TopCat.sigmaι X j)))) := by
  haveI : HasColimitsOfShape (Discrete J) LightCondAb :=
    (IsGrothendieckAbelian.hasColimits LightCondAb).has_colimits_of_shape _
  haveI : PreservesColimitsOfShape (Discrete J)
      (ComplexShape.embeddingDownNat.extendFunctor LightCondAb) :=
    preservesColimitsOfShape_extendFunctor _ _
  exact ⟨isColimit_cofan_map (fun j => AchainFunctor.map (TopCat.sigmaι X j))
    (ComplexShape.embeddingDownNat.extendFunctor LightCondAb) hAch.some⟩

/-- The sigma inclusions are open embeddings. -/
theorem sigmaι_isOpenEmbedding {J : Type} (X : J → TopCat.{0}) (j : J) :
    Topology.IsOpenEmbedding ⇑(TopCat.sigmaι X j) := by
  rw [funext (sigmaι_apply (X := X) j)]
  exact Topology.IsOpenEmbedding.sigmaMk

/-- The ranges of the sigma inclusions are pairwise disjoint. -/
theorem sigmaι_disjoint {J : Type} (X : J → TopCat.{0}) :
    Pairwise fun j k =>
      Disjoint (Set.range ⇑(TopCat.sigmaι X j)) (Set.range ⇑(TopCat.sigmaι X k)) := by
  intro j k hjk
  rw [Set.disjoint_left]
  rintro s ⟨a, ha⟩ ⟨b, hb⟩
  rw [sigmaι_apply] at ha hb
  exact hjk (by simpa using congrArg Sigma.fst (ha.trans hb.symm))

/-- The ranges of the sigma inclusions cover the disjoint union. -/
theorem sigmaι_iUnion_range {J : Type} (X : J → TopCat.{0}) :
    (⋃ j, Set.range ⇑(TopCat.sigmaι X j)) = Set.univ := by
  ext s
  simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
  exact ⟨s.1, s.2, rfl⟩

end Work.CWIND.GClass
