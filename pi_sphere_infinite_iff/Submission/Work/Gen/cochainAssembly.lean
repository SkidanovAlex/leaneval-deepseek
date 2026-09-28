import Mathlib
import Submission.Work.Gen.pathCompDecomp
import Submission.Work.Gen.cochain_homologypi_eq_zero
import Submission.Work.Cohomology.CupRing
import Submission.Work.Cohomology.cupNaturalH
import Submission.Work.Cohomology.relCochain_shortExact
import Submission.Work.Thom.Cohomology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Gen

noncomputable section

/-! ## Prescribing the values of a cochain on the generators -/

/-- The cochain of a simplicial set `Y` with prescribed values on the generators (the `n`-simplices
of `Y`): the linear functional on the free module of `n`-chains determined by a function on the
set of `n`-simplices. -/
def mkCochain (R : Type) [CommRing R] (Y : SSet) (n : ℕ) (g : Y _⦋n⦌ → R) :
    (Y.chainComplex (ModuleCat.of R R)).X n →ₗ[R] R :=
  ModuleCat.Hom.hom (Cofan.IsColimit.desc (Y.isColimitChainComplexXCofan (ModuleCat.of R R) n)
    (fun σ => ModuleCat.ofHom (LinearMap.toSpanSingleton R R (g σ))))

/-- The computation rule for `mkCochain`. -/
@[simp]
theorem genEval_mkCochain (R : Type) [CommRing R] (Y : SSet) (n : ℕ) (g : Y _⦋n⦌ → R)
    (σ : Y _⦋n⦌) :
    Work.Cohomology.genEval R Y (mkCochain R Y n g) σ = g σ := by
  have h := Cofan.IsColimit.fac (Y.isColimitChainComplexXCofan (ModuleCat.of R R) n)
      (fun σ : Y _⦋n⦌ => ModuleCat.ofHom (LinearMap.toSpanSingleton R R (g σ))) σ
  have h2 := congrArg (fun (m : ModuleCat.of R R ⟶ ModuleCat.of R R) => m.hom (1 : R)) h
  rw [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  have h3 : (Y.chainComplexXCofan (ModuleCat.of R R) n).inj σ = Y.ιChainComplex σ := rfl
  rw [h3] at h2
  rw [Work.Cohomology.genEval, mkCochain]
  rw [ModuleCat.hom_ofHom, LinearMap.toSpanSingleton_apply, one_smul] at h2
  exact h2

/-! ## The pullback of a cochain, evaluated on a generator -/

/-- The chain map induced by a continuous map sends the generator of a simplex to the generator of
its image. -/
theorem chainMap_ιChainComplex (R : Type) [CommRing R] {Y Z : TopCat} (f : Y ⟶ Z) {n : ℕ}
    (τ : (TopCat.toSSet.obj Y) _⦋n⦌) :
    ((Work.Cohomology.chainMap R Y Z f).f n).hom
        ((SSet.ιChainComplex (TopCat.toSSet.obj Y) (R := ModuleCat.of R R) τ).hom 1) =
      (SSet.ιChainComplex (TopCat.toSSet.obj Z) (R := ModuleCat.of R R)
        ((TopCat.toSSet.map f).app (Opposite.op ⦋n⦌) τ)).hom 1 := by
  rw [Work.Cohomology.chainMap_f_eq]
  exact congrArg (fun (m : ModuleCat.of R R ⟶
      ((TopCat.toSSet.obj Z).chainComplex (ModuleCat.of R R)).X n) => m.hom (1 : R))
    (SSet.ι_chainComplexMap_f (TopCat.toSSet.obj Y) (TopCat.toSSet.obj Z) (TopCat.toSSet.map f)
      (ModuleCat.of R R) τ)

/-- **The pullback of a cochain, evaluated on a simplex**: `(f^* β)(τ) = β(f τ)`. -/
theorem genEval_cochainPullbackHom (R : Type) [CommRing R] {Y Z : TopCat} (f : Y ⟶ Z) {n : ℕ}
    (β : Work.Cohomology.Cochain R (TopCat.toSSet.obj Z) n)
    (τ : (TopCat.toSSet.obj Y) _⦋n⦌) :
    Work.Cohomology.genEval R (TopCat.toSSet.obj Y)
        ((Work.Cohomology.cochainPullbackHom R Y Z f n).hom β) τ =
      Work.Cohomology.genEval R (TopCat.toSSet.obj Z) β ((TopCat.toSSet.map f).app _ τ) := by
  show ((Work.Cohomology.cochainPullbackHom R Y Z f n).hom β)
      ((SSet.ιChainComplex (TopCat.toSSet.obj Y) (R := ModuleCat.of R R) τ).hom 1) =
    β ((SSet.ιChainComplex (TopCat.toSSet.obj Z) (R := ModuleCat.of R R)
      ((TopCat.toSSet.map f).app (Opposite.op ⦋n⦌) τ)).hom 1)
  rw [Work.Cohomology.cochainPullbackHom_apply]
  exact congrArg (fun x => β x) (chainMap_ιChainComplex R f τ)

/-! ## The class of a coboundary vanishes -/

/-- The coboundary of a coboundary is zero. -/
theorem cochainDiff_cochainDiff (R : Type) [CommRing R] (Y : SSet) {k : ℕ}
    (w : Work.Cohomology.Cochain R Y k) :
    Work.Cohomology.cochainDiff R Y (Work.Cohomology.cochainDiff R Y w) = 0 := by
  have h1 : Work.Cohomology.cochainDiff R Y (Work.Cohomology.cochainDiff R Y w) =
      ((Work.Cohomology.SSetCochainComplex R Y).d (k + 1) (k + 2)).hom
        (((Work.Cohomology.SSetCochainComplex R Y).d k (k + 1)).hom w) := by
    rw [← Work.Cohomology.SSetCochainComplex_d_apply R Y (k + 1)
      (Work.Cohomology.cochainDiff R Y w)]
    congr 1
    rw [Work.Cohomology.SSetCochainComplex_d_apply R Y k w]
  have h2 : ((Work.Cohomology.SSetCochainComplex R Y).d (k + 1) (k + 2)).hom
      (((Work.Cohomology.SSetCochainComplex R Y).d k (k + 1)).hom w) = 0 := by
    have h := congrArg (fun (m : (Work.Cohomology.SSetCochainComplex R Y).X k ⟶
        (Work.Cohomology.SSetCochainComplex R Y).X (k + 2)) => m.hom w)
      (HomologicalComplex.d_comp_d (Work.Cohomology.SSetCochainComplex R Y) k (k + 1) (k + 2))
    rw [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply] at h
    exact h
  rw [h1, h2]

/-- **The cohomology class of a coboundary is zero.** -/
theorem cohomologyClassOf_cochainDiff_eq_zero (Y : SSet) {k : ℕ}
    (w : Work.Cohomology.Cochain ℤ Y k) :
    Work.Cohomology.cohomologyClassOf ℤ Y (Work.Cohomology.cochainDiff ℤ Y w)
      (cochainDiff_cochainDiff ℤ Y w) = 0 := by
  have hcyc : Work.Cohomology.cocycleOf ℤ Y (Work.Cohomology.cochainDiff ℤ Y w)
      (cochainDiff_cochainDiff ℤ Y w) =
      (Work.Cohomology.SSetCochainComplex ℤ Y).toCycles k (k + 1) w := by
    apply Work.Cohomology.iCycles_injective ℤ Y (k + 1)
    have h := congrArg (fun (m : (Work.Cohomology.SSetCochainComplex ℤ Y).X k ⟶
      (Work.Cohomology.SSetCochainComplex ℤ Y).X (k + 1)) => m.hom w)
      (HomologicalComplex.toCycles_i (Work.Cohomology.SSetCochainComplex ℤ Y) k (k + 1))
    rw [ModuleCat.hom_comp, LinearMap.comp_apply,
      Work.Cohomology.SSetCochainComplex_d_apply] at h
    rw [Work.Cohomology.iCycles_cocycleOf]
    exact h.symm
  rw [Work.Cohomology.cohomologyClassOf, hcyc]
  have h := HomologicalComplex.toCycles_comp_homologyπ
    (Work.Cohomology.SSetCochainComplex ℤ Y) k (k + 1)
  have h2 := congrArg (fun (m : (Work.Cohomology.SSetCochainComplex ℤ Y).X k ⟶
      (Work.Cohomology.SSetCochainComplex ℤ Y).homology (k + 1)) => m.hom w) h
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply] using h2

/-- **A cocycle of the singular cochain complex whose class vanishes is a coboundary.** -/
theorem exists_cochainDiff_eq_of_class_zero {Y : SSet} {k : ℕ}
    (β : Work.Cohomology.Cochain ℤ Y (k + 1))
    (hβ : Work.Cohomology.cochainDiff ℤ Y β = 0)
    (h : Work.Cohomology.cohomologyClassOf ℤ Y β hβ = 0) :
    ∃ w : Work.Cohomology.Cochain ℤ Y k, Work.Cohomology.cochainDiff ℤ Y w = β := by
  have hz : (Work.Cohomology.SSetCochainComplex ℤ Y).homologyπ (k + 1)
      (Work.Cohomology.cocycleOf ℤ Y β hβ) = 0 := h
  obtain ⟨y, hy⟩ := cochain_homologypi_eq_zero (Work.Cohomology.SSetCochainComplex ℤ Y) k
    (Work.Cohomology.cocycleOf ℤ Y β hβ) hz
  refine ⟨y, ?_⟩
  rw [← Work.Cohomology.iCycles_cocycleOf ℤ Y β hβ]
  rw [← hy]
  rw [Work.Cohomology.SSetCochainComplex_d_apply]

end

end Work.Gen

namespace Work.Gen

noncomputable section

variable {X : Type} [TopologicalSpace X]

/-! ## Assembling a family of componentwise cochains -/

/-- **The assembly of a family of cochains on the path components**: the cochain on `X` whose
value at a simplex `σ` is the value of the cochain of the component of `σ` at the lift of `σ` to
that component. -/
noncomputable def assemble {k : ℕ}
    (w : ∀ c : SSet.π₀ (TopCat.toSSet.obj (TopCat.of X)),
      Work.Cohomology.Cochain ℤ (TopCat.toSSet.obj (pathComp X c)) k) :
    Work.Cohomology.Cochain ℤ (TopCat.toSSet.obj (TopCat.of X)) k :=
  mkCochain ℤ (TopCat.toSSet.obj (TopCat.of X)) k
    (fun σ => Work.Cohomology.genEval ℤ (TopCat.toSSet.obj (pathComp X (simpComp σ)))
      (w (simpComp σ)) (factorWith σ (simpComp σ)))

/-- The computation rule for the assembly. -/
@[simp]
theorem genEval_assemble {k : ℕ}
    (w : ∀ c : SSet.π₀ (TopCat.toSSet.obj (TopCat.of X)),
      Work.Cohomology.Cochain ℤ (TopCat.toSSet.obj (pathComp X c)) k)
    (σ : (TopCat.toSSet.obj (TopCat.of X)) _⦋k⦌) :
    Work.Cohomology.genEval ℤ (TopCat.toSSet.obj (TopCat.of X)) (assemble w) σ =
      Work.Cohomology.genEval ℤ (TopCat.toSSet.obj (pathComp X (simpComp σ)))
        (w (simpComp σ)) (factorWith σ (simpComp σ)) :=
  genEval_mkCochain ℤ (TopCat.toSSet.obj (TopCat.of X)) k _ σ

/-- **The assembly is compatible with the differential**, componentwise. -/
theorem cochainDiff_assemble {k : ℕ}
    (w : ∀ c : SSet.π₀ (TopCat.toSSet.obj (TopCat.of X)),
      Work.Cohomology.Cochain ℤ (TopCat.toSSet.obj (pathComp X c)) k) :
    Work.Cohomology.cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of X)) (assemble w) =
      assemble (fun c => Work.Cohomology.cochainDiff ℤ
        (TopCat.toSSet.obj (pathComp X c)) (w c)) := by
  apply Work.Cohomology.genEval_ext
  intro σ
  rw [Work.Cohomology.genEval_cochainDiff, genEval_assemble]
  rw [Work.Cohomology.genEval_cochainDiff]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [genEval_assemble, factorWith_δ, simpComp_δ]

/-- **Assembling the pullbacks of a cochain returns the cochain.** -/
theorem assemble_pullback {k : ℕ}
    (β : Work.Cohomology.Cochain ℤ (TopCat.toSSet.obj (TopCat.of X)) (k + 1)) :
    assemble (fun c => (Work.Cohomology.cochainPullbackHom ℤ (pathComp X c) (TopCat.of X)
      (TopCat.ofHom (pathCompIncl X c)) (k + 1)).hom β) = β := by
  apply Work.Cohomology.genEval_ext
  intro σ
  rw [genEval_assemble, genEval_cochainPullbackHom]
  rw [factorWith_spec σ (simpComp σ) rfl]

end

end Work.Gen

namespace Work.Gen

noncomputable section

variable {X : Type} [TopologicalSpace X]

/-- **Assembling the pullbacks of a cochain returns the cochain**, in the form in which the
pullback of a cochain is written as the transpose of the chain map induced on the singular
simplicial set. -/
theorem assemble_pullback_dualMap {k : ℕ}
    (β : Work.Cohomology.Cochain ℤ (TopCat.toSSet.obj (TopCat.of X)) (k + 1)) :
    assemble (fun c => ((SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom (pathCompIncl X c)))
      (ModuleCat.of ℤ ℤ)).f (k + 1)).hom.dualMap β) = β := by
  rw [show (fun c => ((SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom (pathCompIncl X c)))
      (ModuleCat.of ℤ ℤ)).f (k + 1)).hom.dualMap β) =
      (fun c => (Work.Cohomology.cochainPullbackHom ℤ (pathComp X c) (TopCat.of X)
        (TopCat.ofHom (pathCompIncl X c)) (k + 1)).hom β) from funext (fun c => rfl)]
  exact assemble_pullback β

end

end Work.Gen
