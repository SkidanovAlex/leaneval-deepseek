/-
AREA TOOLKIT — the field `sigma` of `Submission.Blueprint.ToolkitProp`.

Solid-equivalences are stable under small coproducts.  The proof reduces the question to the
statement that the localization functor `Q : Cpx ⤒ D(LightCondAb)` preserves coproducts
(`Submission/Work/TOOLKIT/Sigma/hom_coproduct_bijective.lean`): identifying
`Hom(Q (∐ K), iD.obj N)` with `∏ j, Hom(Q (K j), iD.obj N)` turns the precomposition with
`Q (Sigma.map f)` into the product of the precompositions with the `Q (f j)`, and a product of
bijections is a bijection.
-/
import Submission.Work.TOOLKIT.Basic
import Submission.Work.TOOLKIT.Instances
import Submission.Work.TOOLKIT.Sigma.hom_coproduct_bijective

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid
open Submission.Blueprint

noncomputable section

namespace Work.TOOLKIT

/-- **The `sigma` field.**  Solid-equivalences are stable under small coproducts. -/
theorem solidEquiv_sigma (J : Type) (K L : J → Cpx) [HasCoproduct K] [HasCoproduct L]
    (f : ∀ j, K j ⟶ L j) (hf : ∀ j, SolidEquiv (DerivedCategory.Q.map (f j))) :
    SolidEquiv (DerivedCategory.Q.map (CategoryTheory.Limits.Sigma.map f)) := by
  intro N
  have bK : Function.Bijective (fun g : DerivedCategory.Q.obj
      (CategoryTheory.Limits.sigmaObj K) ⟶ iD.obj N =>
      fun j => DerivedCategory.Q.map (CategoryTheory.Limits.Sigma.ι K j) ≫ g) :=
    Sigma.hom_coproduct_bijective J K (iD.obj N)
  have bL : Function.Bijective (fun g : DerivedCategory.Q.obj
      (CategoryTheory.Limits.sigmaObj L) ⟶ iD.obj N =>
      fun j => DerivedCategory.Q.map (CategoryTheory.Limits.Sigma.ι L j) ≫ g) :=
    Sigma.hom_coproduct_bijective J L (iD.obj N)
  set eK := Equiv.ofBijective _ bK with heK
  set eL := Equiv.ofBijective _ bL with heL
  have hKapp : ∀ g, eK g = fun j => DerivedCategory.Q.map (CategoryTheory.Limits.Sigma.ι K j) ≫ g :=
    fun g => rfl
  have hLapp : ∀ g, eL g = fun j => DerivedCategory.Q.map (CategoryTheory.Limits.Sigma.ι L j) ≫ g :=
    fun g => rfl
  have hprod : Function.Bijective (fun (ψ : ∀ j, DerivedCategory.Q.obj (L j) ⟶ iD.obj N) =>
      fun j => DerivedCategory.Q.map (f j) ≫ ψ j) := by
    constructor
    · intro a b hab
      funext j
      exact (hf j N).1 (congrFun hab j)
    · intro b
      choose c hc using fun j => (hf j N).2 (b j)
      exact ⟨c, by funext j; exact hc j⟩
  have hsq : ⇑eK ∘ precompD (DerivedCategory.Q.map (CategoryTheory.Limits.Sigma.map f)) N =
      (fun (ψ : ∀ j, DerivedCategory.Q.obj (L j) ⟶ iD.obj N) =>
        fun j => DerivedCategory.Q.map (f j) ≫ ψ j) ∘ ⇑eL := by
    funext g
    funext j
    simp only [Function.comp_apply, precompD_apply, hKapp, hLapp]
    rw [← Category.assoc, ← Functor.map_comp, CategoryTheory.Limits.Sigma.ι_map,
      Functor.map_comp, Category.assoc]
  have hmain : (fun g : DerivedCategory.Q.obj (CategoryTheory.Limits.sigmaObj L) ⟶ iD.obj N =>
      DerivedCategory.Q.map (CategoryTheory.Limits.Sigma.map f) ≫ g) =
      ⇑eK.symm ∘ ((fun (ψ : ∀ j, DerivedCategory.Q.obj (L j) ⟶ iD.obj N) =>
        fun j => DerivedCategory.Q.map (f j) ≫ ψ j) ∘ ⇑eL) := by
    funext g
    have h := congrFun hsq g
    simp only [Function.comp_apply] at h ⊢
    have h2 := congrArg (fun w => eK.symm w) h
    simpa using h2
  rw [hmain]
  exact (Equiv.bijective eK.symm).comp (hprod.comp (Equiv.bijective eL))

end Work.TOOLKIT
