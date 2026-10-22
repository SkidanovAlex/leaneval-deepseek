import Mathlib
import Submission.Work.CWIND.Basic
import Submission.Work.CWIND.GClass.SigmaFst
import Submission.Work.CWIND.GClass.GTrans
import Submission.Work.CWIND.GClass.Asigma
import Submission.Work.CWIND.GClass.DUS
import Submission.Work.CWIND.GClass.SigmaCodHomeo
import Submission.Work.CWIND.GClass.KsigmaIso
import Submission.Work.CWIND.GClass.IsColimitCofanOfComponents

noncomputable section

namespace Work.CWIND.GClass

open CategoryTheory CategoryTheory.Limits LightCondensed LightProfinite
open LightCondensed.Solid Submission.Blueprint
open Work.CWIND

/-- **CWIND/T7 (the `sigma` field of the CW induction).**  `GOf b X` is the class of REFS/05
section 2: `X` is Hausdorff and the comparison map `b(X) : C_sing(X) ⟶ A(X)` becomes an
isomorphism after solidification, i.e. `Q (b.app X)` is a solid-equivalence.

A disjoint union of spaces in `GOf` lies in `GOf`: the singular simplices of `⊔_j X_j` are those
of the pieces (a simplex has connected source `Δⁿ`), and `(⊔_j X_j)^{Δⁿ} = ⊔_j X_j^{Δⁿ}` because
`Δⁿ` is connected, so that `C(⊔_j X_j) = ⊕_j C(X_j)` and `A(⊔_j X_j) = ⊕_j A(X_j)`; naturality of
`b` identifies `b(⊔_j X_j)` with the coproduct of the `b(X_j)`, and `ToolkitProp.sigma` gives the
solid-equivalence of the coproduct. -/
theorem G_sigma (hTK : ToolkitProp)
    (b : singularChainsLightCondAbComplexFunctor ⟶ AFunctor) (J : Type) (X : J → TopCat.{0})
    [∀ j, T2Space (X j)] (h : ∀ j, GOf b (X j)) :
    GOf b (TopCat.of (Σ j, X j)) := by
  classical
  refine ⟨inferInstance, ?_⟩
  set S : TopCat.{0} := TopCat.of (Σ j, (X j : Type)) with hS
  set σ : ∀ j, X j ⟶ S := fun j => TopCat.sigmaι X j with hσ
  -- the degreewise decomposition of the mapping space and of the free group on it
  haveI hSig : ∀ n, IsIso (Limits.Sigma.desc
      (fun j => singSpacePostcomp (TopCat.sigmaι X j) n)) := fun n => SigmaCodHomeo X n
  have hDUS : ∀ n, Nonempty (IsColimit (Cofan.mk (topCatToLightCondSet.obj (sigmaPt X n))
      (fun j => topCatToLightCondSet.map (TopCat.sigmaι (sigmaPiece X n) j)))) :=
    fun n => DUS (sigmaPiece X n) (fun j => TopCat.sigmaι (sigmaPiece X n) j)
      (fun j => sigmaι_isOpenEmbedding _ j) (sigmaι_disjoint _) (sigmaι_iUnion_range _)
  have hdeg : ∀ n, Nonempty (IsColimit (Cofan.mk (freeLightCondAbOfTop (singSpace S n))
      (fun j => freeLightCondAbOfTopFunctor.map (singSpacePostcomp (σ j) n)))) :=
    fun n => isColimit_freeLightCondAbOfTop_singSpace_sigma X (hSig n) (hDUS n)
  -- the `A`-side: `A(⊔_j X_j) ≅ ⊕_j A(X_j)`
  have hAch : Nonempty (IsColimit (Cofan.mk (Achain S) (fun j => AchainFunctor.map (σ j)))) :=
    isColimit_Achain_sigma X IsColimitCofanOfComponents hdeg
  have hAc : Nonempty (IsColimit (Cofan.mk (AFunctor.obj S) (fun j => AFunctor.map (σ j)))) :=
    isColimit_A_sigma X hAch
  haveI : HasColimitsOfShape (Discrete J) LightCondAb :=
    (IsGrothendieckAbelian.hasColimits LightCondAb).has_colimits_of_shape _
  haveI : HasColimitsOfShape (Discrete J) (CochainComplex LightCondAb ℤ) :=
    HomologicalComplex.instHasColimitsOfShape (C := LightCondAb) (c := ComplexShape.up ℤ)
  -- the `K`-side: `C_sing(⊔_j X_j) ≅ ⊕_j C_sing(X_j)`
  haveI hKiso : IsIso (Limits.Sigma.desc
      (fun j => singularChainsLightCondAbComplexFunctor.map (σ j))) :=
    isIso_sigmaDesc_of_isColimit _ (KsigmaIso X).some
  haveI hAiso : IsIso (Limits.Sigma.desc (fun j => AFunctor.map (σ j))) :=
    isIso_sigmaDesc_of_isColimit _ hAc.some
  -- naturality of `b` with respect to the coproduct decompositions
  have hnat : Limits.Sigma.desc (fun j => singularChainsLightCondAbComplexFunctor.map (σ j)) ≫
        b.app S =
      Limits.Sigma.map (fun j => b.app (X j)) ≫
        Limits.Sigma.desc (fun j => AFunctor.map (σ j)) := by
    apply Sigma.hom_ext
    intro j
    rw [Limits.Sigma.ι_comp_desc_assoc, Limits.Sigma.ι_map_assoc, Limits.Sigma.ι_comp_desc]
    exact b.naturality (σ j)
  exact hTK.of_comp_left
    ((DerivedCategory.Q).map (Limits.Sigma.desc
      (fun j => singularChainsLightCondAbComplexFunctor.map (σ j))))
    ((DerivedCategory.Q).map (b.app S))
    (hTK.of_iso _ (Functor.map_isIso _ _))
    (by
      rw [← Functor.map_comp, hnat, Functor.map_comp]
      exact hTK.comp _ _
        (hTK.sigma J (fun j => singularChainsLightCondAbComplexFunctor.obj (X j))
          (fun j => AFunctor.obj (X j)) (fun j => b.app (X j)) (fun j => (h j).2))
        (hTK.of_iso _ (Functor.map_isIso _ _)))

end Work.CWIND.GClass
