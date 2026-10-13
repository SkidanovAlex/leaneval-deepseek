import Mathlib
import Submission.Work.DSG4a.cechZBaseChangeDefs
import Submission.Work.DSG4a.cechZBaseChangeCoaug
import Submission.Work.DSG4a.cechZBaseChangeComm
import Submission.Work.DSG4a.cechZBaseChangeIsIso

/-!
# DSG4a: the Čech complex base-changes compatibly with the coaugmentation

For an algebra `A ⟶ A'`, a scheme `f : X ⟶ Spec A` with separated `X`, and a finite nonempty
family `U` of affine opens of `X`, there is a comparison morphism

`baseChangeComplex (cechZ A X f U) ⟶ cechZ A' X' f' U'`

of the base change (along `A ⟶ A'`) of the Čech complex of `X` with the Čech complex of the base
change `X' = X ×_{Spec A} Spec A'`; it is a quasi-isomorphism and carries the canonical
coaugmentation of the former to the canonical coaugmentation of the latter.

The proof is assembled from the modules `cechZBaseChangeDefs` (the comparison and its
componentwise descriptions), `cechZBaseChangeComm` (commutation with the Čech differential),
`cechZBaseChangeIsIso` (the termwise comparison is an isomorphism on affine opens) and
`cechZBaseChangeCoaug` (the coaugmentations correspond).
-/

namespace Work.DSG4a

open CategoryTheory AlgebraicGeometry Limits Opposite
open scoped ChangeOfRings TensorProduct

universe u

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

/-- The `ℕ`-indexed comparison as a morphism of complexes. -/
private noncomputable def bcPhiN {A : Type u} [CommRing A] {A' : Type u} [CommRing A']
    [Algebra A A'] (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) {ι : Type u} [Finite ι]
    (U : ι → X.Opens) : bcCN (A := A) (A' := A') X f U ⟶ bcCT (A := A) (A' := A') X f U :=
  HomologicalComplex.Hom.mk (fun n => bcMapT (A := A) (A' := A') X f U n)
    (fun i j hij => by
      rw [← hij]
      exact (bcMapT_comm_aux (A := A) (A' := A') X f U i).symm)

theorem cechZ_baseChange {A : Type u} [CommRing A] {A' : Type u} [CommRing A'] [Algebra A A']
    (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) {ι : Type u} [Finite ι] [Nonempty ι]
    [IsAffineHom (pullback.diagonal (terminal.from X))] (U : ι → X.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) :
    ∃ Φ : Work.DSG4a.baseChangeComplex (A := A) (A' := A') (DSMap.cechZ A X f U) ⟶
        DSMap.cechZ A' (Work.DSG4a.baseChangeScheme (A := A) (A' := A') X f)
          (Work.DSG4a.baseChangeSnd (A := A) (A' := A') X f)
          (fun i => Work.DSG4a.baseChangeOpen (A := A) (A' := A') X f (U i)),
      QuasiIso Φ ∧
      (∀ a' : A', (Φ.f 0) (a' ⊗ₜ[A, algebraMap A A'] Work.DSG4a.coaugZElem A X f U) =
        a' • Work.DSG4a.coaugZElem A' (Work.DSG4a.baseChangeScheme (A := A) (A' := A') X f)
          (Work.DSG4a.baseChangeSnd (A := A) (A' := A') X f)
          (fun i => Work.DSG4a.baseChangeOpen (A := A) (A' := A') X f (U i))) := by
  haveI : ∀ n : ℕ, IsIso ((bcPhiN (A := A) (A' := A') X f U).f n) :=
    fun n => bcMapT_isIso_aux (A := A) (A' := A') X f U hU n
  haveI : IsIso (bcPhiN (A := A) (A' := A') X f U) :=
    HomologicalComplex.Hom.isIso_of_components _
  haveI : IsIso (HomologicalComplex.extendMap (bcPhiN (A := A) (A' := A') X f U)
      ComplexShape.embeddingUpNat) := by
    rw [← ComplexShape.Embedding.extendFunctor_map]
    exact Functor.map_isIso _ _
  refine ⟨(bcChi (A := A) (A' := A') X f U).hom ≫
    HomologicalComplex.extendMap (bcPhiN (A := A) (A' := A') X f U) ComplexShape.embeddingUpNat,
    ?_, ?_⟩
  · infer_instance
  · intro a'
    exact bcChi_extendMap_coaug (A := A) (A' := A') X f U (bcPhiN (A := A) (A' := A') X f U)
      (fun a' => bcMapT_coaug_aux (A := A) (A' := A') X f U a') a'

end Work.DSG4a
