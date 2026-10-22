import Mathlib
import Submission.Work.CWIND.GClass.GTrans
import Submission.Work.CWIND.GClass.SingChainSigma
import Submission.Work.CWIND.Basic

/-!
# CWIND/GClass — the singular chains of a disjoint union, in the cochain complex

The `n`-chains of a disjoint union `⊔_j X j` are the coproduct of the `n`-chains of the pieces
(`Work.CWIND.GClass.isColimit_singC_sigma`), so the singular chain complexes form a coproduct as
well.  This file proves that the functor `singularChainsLightCondAbComplexFunctor` takes the
coproduct `Σ j, X j` in `TopCat` to the coproduct of the `C_sing(X j)`, i.e. that the cofan with
point `C_sing(⊔_j X j)` and legs `C_sing(sigmaι X j)` is a colimit cocone.

The proof is degreewise:

* degree `-k` (`k : ℕ`): transport `isColimit_singC_sigma` along the discrete functor and then
  along the extension `ComplexShape.embeddingDownNat.extendFunctor`, using
  `HomologicalComplex.extendFunctorCompEvalIso` and `HomologicalComplex.extendMap_f`;
* degree `q > 0`: both the point and all the pieces vanish (`HomologicalComplex.isZero_extend_X`),
  so the cofan is a colimit by `zero_cocone`;
* the degrees are assembled with `HomologicalComplex.isColimitOfEval`, the passage between the
  cofan form and the `Functor.mapCocone` form being `Cofan.isColimitMapCoconeEquiv`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits LightCondensed LightProfinite
open LightCondensed.Solid Submission.Blueprint

namespace Work.CWIND.GClass

/-- Integral singular chains, pushed forward to light condensed abelian groups, as an `ℕ`-graded
chain complex (the singular chain functor before extension to a cochain complex). -/
abbrev singCsrcC : TopCat.{0} ⥤ ChainComplex LightCondAb ℕ :=
  Submission.Blueprint.singC ⋙
    (LightCondensed.discrete (ModuleCat ℤ)).mapHomologicalComplex (ComplexShape.down ℕ)

/-- Integral singular chains as a cochain complex of light condensed abelian groups, namely the
extension along `ComplexShape.embeddingDownNat`.  This is definitionally
`LightCondensed.Solid.singularChainsLightCondAbComplexFunctor`. -/
abbrev singCochainC : TopCat.{0} ⥤ CochainComplex LightCondAb ℤ :=
  singCsrcC ⋙ ComplexShape.embeddingDownNat.extendFunctor LightCondAb

lemma singCochainC_eq :
    singCochainC = LightCondensed.Solid.singularChainsLightCondAbComplexFunctor := rfl

/-- **The singular chains of a disjoint union form the coproduct of the chains of the pieces.**
The singular chain complex of `⊔_j X j` is the coproduct of the singular chain complexes of the
`X j` (the coproduct being taken in `CochainComplex LightCondAb ℤ`). -/
theorem KsigmaIso {J : Type} (X : J → TopCat.{0}) :
    Nonempty (CategoryTheory.Limits.IsColimit (CategoryTheory.Limits.Cofan.mk
      (LightCondensed.Solid.singularChainsLightCondAbComplexFunctor.obj
        (TopCat.of (Sigma fun j => (X j : Type))))
      (fun j => LightCondensed.Solid.singularChainsLightCondAbComplexFunctor.map
        (TopCat.sigmaι X j)))) := by
  classical
  -- The degreewise colimits, before extension: the `k`-chains of the disjoint union.
  have hdeg : ∀ k : ℕ, IsColimit (Cofan.mk ((singCsrcC.obj (TopCat.of (Σ j, (X j : Type)))).X k)
      (fun j => (singCsrcC.map (TopCat.sigmaι X j)).f k)) := fun k => by
    have h := Classical.choice (isColimit_singC_sigma J X k)
    haveI := (LightCondensed.discreteUnderlyingAdj (ModuleCat.{0} ℤ)).leftAdjoint_preservesColimits
    exact (Cofan.isColimitMapCoconeEquiv (LightCondensed.discrete (ModuleCat ℤ))
      (fun j => (Submission.Blueprint.singC.obj (X j)).X k)
      (Cofan.mk ((Submission.Blueprint.singC.obj (TopCat.of (Σ j, (X j : Type)))).X k)
        (fun j => (Submission.Blueprint.singC.map (TopCat.sigmaι X j)).f k))).1
      (isColimitOfPreserves _ h)
  -- Degree `-k`: transport along the extension functor.
  have hneg : ∀ k : ℕ,
      IsColimit (Cofan.mk ((singCochainC.obj (TopCat.of (Σ j, (X j : Type)))).X (-(k:ℤ)))
        (fun j => (singCochainC.map (TopCat.sigmaι X j)).f (-(k:ℤ)))) := fun k => by
    let e := ComplexShape.embeddingDownNat
    let hk : e.f k = -(k:ℤ) := ComplexShape.embeddingDownNat_f k
    let Srcd : Discrete J ⥤ LightCondAb := Discrete.functor (fun j => (singCsrcC.obj (X j)).X k)
    let Tgt : Discrete J ⥤ LightCondAb :=
      Discrete.functor (fun j => (HomologicalComplex.extend (singCsrcC.obj (X j)) e).X (-(k:ℤ)))
    let α : Srcd ≅ Tgt := Discrete.natIso (fun j =>
      (e.extendFunctorCompEvalIso LightCondAb hk).app (singCsrcC.obj (X j.as)) |>.symm)
    have hcomp : ∀ j : J, α.inv.app (Discrete.mk j) =
        (HomologicalComplex.extendXIso (singCsrcC.obj (X j)) e hk).hom := by
      intro j
      simp only [α]
      rfl
    have hleg : ∀ j : J, (α.inv.app (Discrete.mk j) ≫ (singCsrcC.map (TopCat.sigmaι X j)).f k) ≫
        (HomologicalComplex.extendXIso (singCsrcC.obj (TopCat.of (Σ j, (X j : Type)))) e hk).inv
        = (HomologicalComplex.extendMap (singCsrcC.map (TopCat.sigmaι X j)) e).f (-(k:ℤ)) := by
      intro j
      rw [hcomp j]
      rw [HomologicalComplex.extendMap_f (φ := singCsrcC.map (TopCat.sigmaι X j))
        (e := e) (i := k) (i' := -(k:ℤ)) hk]
      simp only [Category.assoc]
    have w : (Cocone.precompose α.inv).obj
        (Cofan.mk ((singCsrcC.obj (TopCat.of (Σ j, (X j : Type)))).X k)
          (fun j => (singCsrcC.map (TopCat.sigmaι X j)).f k)) ≅
        (Cofan.mk ((HomologicalComplex.extend (singCsrcC.obj (TopCat.of (Σ j, (X j : Type)))) e).X
            (-(k:ℤ)))
          (fun j => (HomologicalComplex.extendMap (singCsrcC.map (TopCat.sigmaι X j)) e).f
            (-(k:ℤ)))) := by
      refine Cocone.ext ((HomologicalComplex.extendXIso
        (singCsrcC.obj (TopCat.of (Σ j, (X j : Type)))) e hk)).symm ?_
      intro j
      simpa only [Cocone.precompose_obj_ι, NatTrans.comp_app, Cofan.mk_ι_app, Iso.symm_hom,
        Discrete.mk_as] using hleg j.as
    exact IsColimit.equivOfNatIsoOfIso α _ _ w (hdeg k)
  -- Degree `q > 0`: everything vanishes.
  have hpos : ∀ q : ℤ, 0 < q →
      IsColimit (Cofan.mk ((singCochainC.obj (TopCat.of (Σ j, (X j : Type)))).X q)
        (fun j => (singCochainC.map (TopCat.sigmaι X j)).f q)) := fun q hq => by
    have hpt : IsZero ((singCochainC.obj (TopCat.of (Σ j, (X j : Type)))).X q) :=
      HomologicalComplex.isZero_extend_X (singCsrcC.obj (TopCat.of (Σ j, (X j : Type))))
        ComplexShape.embeddingDownNat q (fun i hi => by
          simp only [ComplexShape.embeddingDownNat_f] at hi
          omega)
    refine { desc := fun s => hpt.to_ s.pt
             fac := fun s j => ?_
             uniq := fun s m _ => hpt.eq_of_src _ _ }
    exact (HomologicalComplex.isZero_extend_X (singCsrcC.obj (X j.as))
      ComplexShape.embeddingDownNat q (fun i hi => by
        simp only [ComplexShape.embeddingDownNat_f] at hi
        omega)).eq_of_src _ _
  -- Degrees `≤ 0` and `> 0` together.
  have key : ∀ q : ℤ, Nonempty (IsColimit
      (Cofan.mk ((singCochainC.obj (TopCat.of (Σ j, (X j : Type)))).X q)
        (fun j => (singCochainC.map (TopCat.sigmaι X j)).f q))) := by
    intro q
    rcases Int.eq_nat_or_neg q with ⟨n, hn | hn⟩
    · rcases Nat.eq_zero_or_pos n with hn0 | hnpos
      · subst hn0
        rw [hn]
        exact ⟨by simpa using hneg 0⟩
      · rw [hn]
        exact ⟨hpos (n:ℤ) (by exact_mod_cast hnpos)⟩
    · rw [hn]
      exact ⟨hneg n⟩
  -- Assemble the degrees.
  refine ⟨HomologicalComplex.isColimitOfEval (Discrete.functor (fun j => singCochainC.obj (X j)))
    (Cofan.mk (singCochainC.obj (TopCat.of (Σ j, (X j : Type))))
      (fun j => singCochainC.map (TopCat.sigmaι X j)))
    (fun q => ?_)⟩
  exact (Cofan.isColimitMapCoconeEquiv (HomologicalComplex.eval LightCondAb (ComplexShape.up ℤ) q)
    (fun j => singCochainC.obj (X j)) (Cofan.mk (singCochainC.obj (TopCat.of (Σ j, (X j : Type))))
      (fun j => singCochainC.map (TopCat.sigmaι X j)))).symm (Classical.choice (key q))

end Work.CWIND.GClass
