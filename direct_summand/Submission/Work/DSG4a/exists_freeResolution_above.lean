import Mathlib
import Submission.Work.DSG4a.FreeResDefs
import Submission.Work.DSG4a.quasiIso_qdown
import Submission.Work.DSG4a.F_finite_free

namespace Work.DSG4a

open CategoryTheory AlgebraicGeometry Limits Opposite

universe u

/-- **A finitely generated module over a Noetherian ring has a free resolution by finitely
generated free modules, supported in degrees `≤ 0`.**

This is the iterated syzygy resolution built in `Work.DSG4a.FreeResDefs`: the chain complex
`Kcc` of finitely generated free `A`-modules with `LinearMap.range (phi (k+1)) =
LinearMap.ker (phi k)` is a resolution of `M`, i.e. its comparison map `qdown` to `M`
concentrated in degree `0` is a quasi-isomorphism.  Extending it along the embedding
`n ↦ -n` of `down ℕ` into `up ℤ` produces the required cochain complex supported in
degrees `≤ 0`. -/
theorem exists_freeResolution_above {A : Type u} [CommRing A] [IsNoetherianRing A]
    (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M] :
    ∃ F : CochainComplex (ModuleCat.{u} A) ℤ,
      (∀ i, Module.Finite A (F.X i)) ∧ (∀ i, Module.Free A (F.X i)) ∧ F.IsStrictlyLE 0 ∧
      ∃ q : F ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A M),
        QuasiIso q := by
  obtain ⟨hfin, hfree⟩ := F_finite_free (A:=A) M
  refine ⟨F (A:=A) M, hfin, hfree, F_isStrictlyLE (A:=A) M, ?_⟩
  refine ⟨(HomologicalComplex.extendMap (qdown (A:=A) M) (emb)) ≫
    (HomologicalComplex.extendSingleIso (emb) (ModuleCat.of A M) 0 0 (rfl)).hom, ?_⟩
  have hq : QuasiIso (qdown (A:=A) M) := quasiIso_qdown (A:=A) M
  haveI h1 : QuasiIso (HomologicalComplex.extendMap (qdown (A:=A) M) (emb)) :=
    (HomologicalComplex.quasiIso_extendMap_iff (qdown (A:=A) M) (emb)).2 hq
  haveI h2 : QuasiIso (HomologicalComplex.extendSingleIso (emb) (ModuleCat.of A M) 0 0
      (rfl)).hom := quasiIso_of_isIso _
  exact quasiIso_comp (HomologicalComplex.extendMap (qdown (A:=A) M) (emb))
    (HomologicalComplex.extendSingleIso (emb) (ModuleCat.of A M) 0 0 (rfl)).hom

end Work.DSG4a
