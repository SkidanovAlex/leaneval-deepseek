import Mathlib
import Submission.Work.DSF1.Scheme.Affine
import Submission.Work.DSF1.Cech.CoaugSheaf
import Submission.Work.DSF1.Derived.rightDerived_finProduct_isZero

/-!
# Acyclicity of the sheaf-level Čech terms (DSF1)

Let `X` be a scheme separated over `Spec A`, and let `U : ι → X.Opens` be a finite covering
family of affine opens.  The sheaf-level Čech complex

`K = (cechComplexFunctor U).obj (cechSheafPresheaf X) : CochainComplex X.Modules ℕ`

has, in degree `n`, the term

`Kⁿ = ∏ᶜ (fun x : Fin (n+1) → ι => secSheaf (∏ᶜ (fun a => U (x a))))`,

the product of the sheaves `secSheaf W = (W.ι)_* 𝒪_W` over the opens `W = U (x 0) ⊓ ⋯ ⊓ U (x n)`
of the Čech nerve of `U`.

This file proves that each of these terms is acyclic for the global sections functor
`Γ = DSMap.GammaA A X f`: for `0 < q` and every `n`, the object `R^q Γ (Kⁿ)` is zero.

The proof is a single reduction.  The interest lies in two facts:

* every `x`-th factor `∏ᶜ (fun a => U (x a))` is affine: it is the infimum `⨅ a, U (x a)` of the
  affine opens `U (x a)` (`pi_opens_eq_iInf`), and finite intersections of affine opens of a scheme
  separated over an affine base are affine (`Work.DSF1.Scheme.affineOpen_iInf_of_isSeparated`);
* the vanishing `R^q Γ (secSheaf W) = 0` for `W` affine open is the hypothesis `hacyc` of the
  statement (Serre's affine vanishing).

Since the index type `Fin (n+1) → ι` is finite, `R^q Γ` of a finite product of acyclic objects is
zero (`Work.DSF1.Derived.rightDerived_finProduct_isZero`, using that `R^q Γ` is additive).
-/

open CategoryTheory AlgebraicGeometry Opposite Limits

namespace Work.DSF1.Cech

universe u v

/-- In the lattice of opens of a topological space, the categorical product of a family of opens
is its infimum. -/
lemma pi_opens_eq_iInf {X : Type u} [TopologicalSpace X] {β : Type v}
    (V : β → TopologicalSpace.Opens X) [HasProduct V] : ∏ᶜ V = ⨅ b, V b := by
  apply le_antisymm
  · exact le_iInf (fun b => leOfHom (Pi.π V b))
  · exact leOfHom (Pi.lift (fun b => homOfLE (iInf_le V b)))

theorem cechTerm_acyclic {A : Type u} [CommRing A] (X : AlgebraicGeometry.Scheme.{u}) (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A)) [AlgebraicGeometry.IsSeparated f] {ι : Type u} [Finite ι] (U : ι → X.Opens) (hU : ∀ i, AlgebraicGeometry.IsAffineOpen (U i)) (hcov : sSup (Set.range U) = ⊤) [HasDerivedCategory (SheafOfModules X.ringCatSheaf)] [HasDerivedCategory (ModuleCat A)] [CategoryTheory.EnoughInjectives (SheafOfModules X.ringCatSheaf)] (hacyc : ∀ (W : X.Opens), AlgebraicGeometry.IsAffineOpen W → AlgebraicGeometry.IsAffineHom (AlgebraicGeometry.Scheme.Opens.ι W) → ∀ q : ℕ, 0 < q → CategoryTheory.Limits.IsZero (((DSMap.GammaA A X f).rightDerived q).obj (Work.DSF1.secSheaf W))) (q : ℕ) (hq : 0 < q) (n : ℕ) : CategoryTheory.Limits.IsZero (((DSMap.GammaA A X f).rightDerived q).obj (((CategoryTheory.cechComplexFunctor U).obj (Work.DSF1.Sheaf.cechSheafPresheaf X) : CochainComplex (AlgebraicGeometry.Scheme.Modules X) ℕ).X n)) := by
  -- The degree-`n` term of the sheaf-level Čech complex is the product of the sheaves
  -- `secSheaf (U (x 0) ⊓ ⋯ ⊓ U (x n))` over the `n`-simplices `x` of the Čech nerve of `U`.
  have hterm : (((CategoryTheory.cechComplexFunctor U).obj
        (Work.DSF1.Sheaf.cechSheafPresheaf X) : CochainComplex
          (AlgebraicGeometry.Scheme.Modules X) ℕ)).X n
      = ∏ᶜ (fun x : Fin (n + 1) → ι =>
          Work.DSF1.secSheaf (∏ᶜ (fun a : Fin (n + 1) => U (x a)))) := rfl
  rw [hterm]
  -- A finite product of `Γ`-acyclic objects is `Γ`-acyclic.  (The statement of
  -- `rightDerived_finProduct_isZero` asks for a derived category of the target; the goal does not
  -- involve derived categories, so the standard one is enough.)
  letI : HasDerivedCategory (ModuleCat.{u} A) := HasDerivedCategory.standard _
  refine Work.DSF1.Derived.rightDerived_finProduct_isZero (DSMap.GammaA A X f)
    (fun x : Fin (n + 1) → ι =>
      Work.DSF1.secSheaf (∏ᶜ (fun a : Fin (n + 1) => U (x a)))) q hq ?_
  intro x
  -- The intersection of the affine opens `U (x a)` is affine (`X` is separated over `Spec A`),
  -- so `hacyc` applies to it.
  have hW : AlgebraicGeometry.IsAffineOpen (∏ᶜ (fun a : Fin (n + 1) => U (x a))) := by
    rw [pi_opens_eq_iInf]
    exact Work.DSF1.Scheme.affineOpen_iInf_of_isSeparated X f U hU x
  exact hacyc _ hW (Work.DSF1.Scheme.affineHom_opens_ι_of_isSeparated X f _ hW) q hq

end Work.DSF1.Cech
