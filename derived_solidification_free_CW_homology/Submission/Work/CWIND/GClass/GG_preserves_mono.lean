import Submission.Work.CWIND.GClass.MVDefs
import Submission.Work.HOMOL.Discrete

/-!
# The functor `GG` preserves quasi-isomorphisms and monomorphisms

`GG` (see `Submission/Work/CWIND/GClass/MVDefs.lean`) is the composite of the degreewise
discretisation functor `(LightCondensed.discrete (ModuleCat ℤ)).mapHomologicalComplex (down ℕ)`
and the extension-by-zero functor `ComplexShape.embeddingDownNat.extendFunctor LightCondAb`.

* The discrete functor is exact (`Work.HOMOL.discretePreservesHomology`), hence preserves
  quasi-isomorphisms (`HomologicalComplex.quasiIso_map_of_preservesHomology`) and monomorphisms.
* Extension by zero preserves quasi-isomorphisms (`HomologicalComplex.quasiIso_extendMap_iff`) and
  monomorphisms (it is degreewise either the original map, up to isomorphism, or a map between
  zero objects).
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits LightCondensed LightProfinite
open LightCondensed.Solid Submission.Blueprint

namespace Work.CWIND.GClass

instance instAdditiveDiscreteLightCondAbGClass :
    (LightCondensed.discrete (ModuleCat ℤ)).Additive := by
  unfold LightCondensed.discrete CategoryTheory.constantSheaf
  infer_instance

instance instPreservesMonoDiscreteLightCondAbGClass :
    (LightCondensed.discrete (ModuleCat ℤ)).PreservesMonomorphisms := by
  unfold LightCondensed.discrete CategoryTheory.constantSheaf
  infer_instance

/-- The degreewise discretisation of a quasi-isomorphism of `ℕ`-graded chain complexes of
abelian groups is a quasi-isomorphism of chain complexes of light condensed abelian groups. -/
theorem GG_preserves_quasiIso {K L : ChainComplex (ModuleCat.{0} ℤ) ℕ} (φ : K ⟶ L)
    (hφ : QuasiIso φ) : QuasiIso (GG.map φ) := by
  have h₁ : QuasiIso (((LightCondensed.discrete (ModuleCat ℤ)).mapHomologicalComplex
      (ComplexShape.down ℕ)).map φ) :=
    HomologicalComplex.quasiIso_map_of_preservesHomology φ (LightCondensed.discrete (ModuleCat ℤ))
  rw [show GG.map φ = HomologicalComplex.extendMap
      ((((LightCondensed.discrete (ModuleCat ℤ)).mapHomologicalComplex (ComplexShape.down ℕ)).map φ))
      ComplexShape.embeddingDownNat from rfl]
  exact (HomologicalComplex.quasiIso_extendMap_iff _ _).2 h₁

/-- Extension by zero along `ComplexShape.embeddingDownNat` preserves monomorphisms. -/
theorem mono_extendMap_downNat {K L : ChainComplex LightCondAb ℕ} (φ : K ⟶ L) (h : Mono φ) :
    Mono (HomologicalComplex.extendMap φ ComplexShape.embeddingDownNat) := by
  refine HomologicalComplex.mono_of_mono_f _ (fun q => ?_)
  by_cases hq : ∃ n : ℕ, (ComplexShape.embeddingDownNat.f n : ℤ) = q
  · obtain ⟨n, hn⟩ := hq
    haveI : Mono (φ.f n) := by
      haveI := (inferInstance :
        (HomologicalComplex.eval LightCondAb (ComplexShape.down ℕ) n).PreservesMonomorphisms)
      exact inferInstance
    rw [HomologicalComplex.extendMap_f _ _ hn]
    exact mono_comp _ _
  · have hz : IsZero ((K.extend ComplexShape.embeddingDownNat).X q) :=
      HomologicalComplex.isZero_extend_X K ComplexShape.embeddingDownNat q
        (fun n hn => hq ⟨n, hn⟩)
    exact hz.mono _

/-- `GG` preserves monomorphisms. -/
theorem GG_preserves_mono {K L : ChainComplex (ModuleCat.{0} ℤ) ℕ} (φ : K ⟶ L)
    (h : Mono φ) : Mono (GG.map φ) := by
  have h₁ : Mono (((LightCondensed.discrete (ModuleCat ℤ)).mapHomologicalComplex
      (ComplexShape.down ℕ)).map φ) := by
    refine HomologicalComplex.mono_of_mono_f _ (fun n => ?_)
    rw [Functor.mapHomologicalComplex_map_f]
    haveI : Mono (φ.f n) := by
      haveI := (inferInstance :
        (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) n).PreservesMonomorphisms)
      exact inferInstance
    exact inferInstance
  rw [show GG.map φ = HomologicalComplex.extendMap
      ((((LightCondensed.discrete (ModuleCat ℤ)).mapHomologicalComplex (ComplexShape.down ℕ)).map φ))
      ComplexShape.embeddingDownNat from rfl]
  exact mono_extendMap_downNat _ h₁

end Work.CWIND.GClass
