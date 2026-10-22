import Mathlib
import Submission.Work.CWIND.GClass.GTrans

namespace Work.CWIND.GClass

open CategoryTheory CategoryTheory.Limits

/-- Colimits of a discrete diagram in a category of homological complexes are computed
degreewise (`HomologicalComplex.isColimitOfEval`): a cofan of chain complexes whose `n`-th
component is a colimit cofan for every `n` is itself a colimit cofan.

The only point needing care is that the degreewise colimit cocones supplied by the hypothesis
live over the diagram `Discrete.functor (fun j => (K j).X n)`, whereas the `n`-th component of
the cocone `Cofan.mk L f` lives over `Discrete.functor K ⋙ eval LightCondAb (ComplexShape.down ℕ) n`.
These two diagrams (and the two cocones) are identified by `Discrete.natIsoFunctor`, whose
components are identities, so that `IsColimit.equivOfNatIsoOfIso` transfers the colimit property. -/
theorem IsColimitCofanOfComponents {J : Type} {K : J → ChainComplex LightCondAb ℕ}
    {L : ChainComplex LightCondAb ℕ} (f : ∀ j, K j ⟶ L)
    (h : ∀ n : ℕ, Nonempty (CategoryTheory.Limits.IsColimit (CategoryTheory.Limits.Cofan.mk (L.X n)
      (fun j => (f j).f n)))) :
    Nonempty (CategoryTheory.Limits.IsColimit (CategoryTheory.Limits.Cofan.mk L f)) := by
  classical
  refine ⟨HomologicalComplex.isColimitOfEval (Discrete.functor K) (Cofan.mk L f) (fun n => ?_)⟩
  have hc : IsColimit (Cofan.mk (L.X n) (fun j => (f j).f n)) := (h n).some
  refine (IsColimit.equivOfNatIsoOfIso
    (F := Discrete.functor (fun j => (K j).X n))
    (G := Discrete.functor K ⋙ HomologicalComplex.eval LightCondAb (ComplexShape.down ℕ) n)
    (Discrete.natIsoFunctor (F := Discrete.functor K ⋙
      HomologicalComplex.eval LightCondAb (ComplexShape.down ℕ) n)).symm
    (Cofan.mk (L.X n) (fun j => (f j).f n))
    ((HomologicalComplex.eval LightCondAb (ComplexShape.down ℕ) n).mapCocone (Cofan.mk L f))
    (Cocone.ext (Iso.refl _) (fun j => by simp))).toFun hc

end Work.CWIND.GClass
