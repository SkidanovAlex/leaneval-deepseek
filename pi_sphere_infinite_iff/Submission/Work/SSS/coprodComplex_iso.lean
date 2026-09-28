import Mathlib
import Submission.Work.SSS.HomologySigmaAux

/-!
# The coproduct of chain complexes is the pointwise coproduct

For a family `F : ι → ChainComplex C ℕ` of chain complexes in a preadditive category `C` which
has coproducts indexed by `ι`, the coproduct `∐ F` in the category of chain complexes is
(degreewise) the pointwise coproduct `coprodComplex F` of `Work.SSS.HomologySigmaAux`.

The proof exhibits `coprodComplex F`, together with the degreewise coproduct inclusions, as a
colimit cocone: the universal property is checked componentwise, where it is the defining
universal property of the coproduct in `C`.  The comparison isomorphism is then supplied by
`IsColimit.coconePointUniqueUpToIso`.
-/

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits

section

variable {C : Type*} [Category C] [Preadditive C]

/-- The degreewise coproduct inclusion `K i ⟶ coprodComplex K`, as a chain map. -/
noncomputable def coprodComplexInj {ι : Type} [HasCoproductsOfShape ι C]
    (K : ι → ChainComplex C ℕ) (i : ι) : K i ⟶ coprodComplex K where
  f n := Sigma.ι (fun i => (K i).X n) i
  comm' n m _ := by
    rw [coprodComplex_d]
    exact Sigma.ι_map (fun i => (K i).d n m) i

/-- The cofan (coproduct cocone) with point `coprodComplex K` and the degreewise coproduct
inclusions. -/
noncomputable def coprodComplexCofan {ι : Type} [HasCoproductsOfShape ι C]
    (K : ι → ChainComplex C ℕ) : Cofan K :=
  Cofan.mk (coprodComplex K) (coprodComplexInj K)

/-- The chain map out of `coprodComplex K` induced by an arbitrary cofan on `K`, defined
degreewise by the universal property of the coproduct in `C`. -/
noncomputable def coprodComplexDesc {ι : Type} [HasCoproductsOfShape ι C]
    (K : ι → ChainComplex C ℕ) (t : Cofan K) : coprodComplex K ⟶ t.pt where
  f n := Sigma.desc (fun i => (t.inj i).f n)
  comm' n m _ := by
    change Sigma.desc (fun i => (t.inj i).f n) ≫ (t.pt).d n m =
      Limits.Sigma.map (fun i => (K i).d n m) ≫ Sigma.desc (fun i => (t.inj i).f m)
    apply Sigma.hom_ext
    intro i
    rw [← Category.assoc, Sigma.ι_desc, ← Category.assoc, Sigma.ι_map, Category.assoc,
        Sigma.ι_desc]
    exact (t.inj i).comm n m

/-- `coprodComplex K` is the coproduct of the family `K`: the cofan `coprodComplexCofan K` is a
colimit cocone. -/
noncomputable def coprodComplex_isColimit {ι : Type} [HasCoproductsOfShape ι C]
    (K : ι → ChainComplex C ℕ) : IsColimit (coprodComplexCofan K) :=
  Cofan.IsColimit.mk (coprodComplexCofan K) (coprodComplexDesc K)
    (fun t j => by
      apply HomologicalComplex.Hom.ext
      funext n
      show Sigma.ι (fun i => (K i).X n) j ≫ Limits.Sigma.desc (fun i => (t.inj i).f n) =
        (t.inj j).f n
      exact Sigma.ι_desc (fun i => (t.inj i).f n) j)
    (fun t m hm => by
      apply HomologicalComplex.Hom.ext
      funext n
      apply Sigma.hom_ext
      intro j
      have h := congrArg (fun (φ : K j ⟶ t.pt) => φ.f n) (hm j)
      have hR : Sigma.ι (fun i => (K i).X n) j ≫ (coprodComplexDesc K t).f n =
          (t.inj j).f n :=
        Sigma.ι_desc (fun i => (t.inj i).f n) j
      rw [hR]
      exact h)

end

open CategoryTheory CategoryTheory.Limits in
theorem coprodComplex_iso {C : Type*} [Category C] [Preadditive C] {ι : Type}
    [HasColimitsOfShape (Discrete ι) C] (F : ι → ChainComplex C ℕ) :
    Nonempty (∐ F ≅ coprodComplex F) := by
  refine ⟨(IsColimit.coconePointUniqueUpToIso (coprodComplex_isColimit F)
    (colimit.isColimit (Discrete.functor F))).symm⟩

end Work.SSS
