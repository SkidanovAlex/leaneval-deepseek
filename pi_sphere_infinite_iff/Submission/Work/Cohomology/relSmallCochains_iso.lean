import Mathlib
import Submission.Work.Cohomology.RelCupTransfer
import Submission.Work.Cohomology.RelMVDefs
import Submission.Work.Cohomology.relMV_quasiIso
import Submission.Work.Cohomology.relCochainDual
import Submission.Work.Cohomology.dualComplexMap_quasiIso
import Submission.Work.Cohomology.DualComplex
import Submission.Work.Cohomology.relChainsProjective

/-!
# The relative small cochains compute relative cohomology

For a topological space `X`, an open cover `U ∪ V = X` and an arbitrary subset `A ⊆ X`, the
**relative small cochains** are the `ℤ`-dual of the relative small chains
`Work.Cohomology.relSmallTop U V A` (the small chains of the cover modulo the small-in-`A` chains).
The main result of this file is

`Work.Cohomology.relSmallCochains_iso` :
`H^n(X,A;ℤ) ≅ H^n(dualComplex ℤ (relSmallTop U V A))`,

i.e. relative cohomology can be computed from the *small* relative chains.

The proof has three ingredients.

* `relCochainDual X A` — relative cochains are the dual of the relative singular chains,
  `relComplex ℤ X A ≅ dualComplex ℤ (relChains X A)`.
* `relMV_quasiIso X A U V …` — the comparison map `φ : relSmallTop U V A ⟶ relChains X A` from the
  small relative chains to the singular relative chains is a quasi-isomorphism.
* `dualComplexMap_quasiIso` — the `ℤ`-dual of a quasi-isomorphism between chain complexes of
  non-negative degree consisting of projective modules is a quasi-isomorphism; the relevant
  projectivity is `relChainsProjective` and `relSmallTopProjective` below.

The auxiliary `chainCokernelIso` is the general form of `relChains_cokernelIso`: the `n`-th
component of a cokernel of chain complexes is the cokernel of the `n`-th component.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

/-! ## The `n`-th component of a cokernel of chain complexes -/

/-- **The `n`-th component of the cokernel of a morphism of chain complexes is the cokernel of the
`n`-th component.**

This is the general form of `relChains_cokernelIso`.  The evaluation functor
`HomologicalComplex.eval` preserves colimits, so the colimiting cocone defining `(cokernel f).X n`
is a colimiting cocone for the diagram `parallelPair (f.f n) 0`; the two functors
`parallelPair f 0 ⋙ eval` and `parallelPair (f.f n) 0` are equal (they have the same objects and
morphisms), which compares the two colimits. -/
def chainCokernelIso (C D : ChainComplex (ModuleCat ℤ) ℕ) (f : C ⟶ D) (n : ℕ) :
    (cokernel f).X n ≅ cokernel (f.f n) := by
  let F : WalkingParallelPair ⥤ ModuleCat ℤ := (parallelPair f 0) ⋙
    HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) n
  let G : WalkingParallelPair ⥤ ModuleCat ℤ := parallelPair (f.f n) 0
  have hFG : F = G := by
    refine CategoryTheory.Functor.ext (fun j => ?_) ?_
    · cases j <;> rfl
    · rintro X' Y' g
      match g with
      | .left => cat_disch
      | .right => cat_disch
      | .id Z => cat_disch
  exact IsColimit.coconePointUniqueUpToIso
      (isColimitOfPreserves (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) n)
        (colimit.isColimit (parallelPair f 0)))
      (colimit.isColimit F) ≪≫ HasColimit.isoOfNatIso (eqToIso hFG)

/-! ## The small chains in degree `n` are projective -/

/-- The small `n`-chains are the coproduct, over the small `n`-simplices, of copies of `ℤ`; hence
they form a projective `ℤ`-module. -/
theorem projective_smallChains (X : TopCat) (U V : Set X) (n : ℕ) :
    Module.Projective ℤ ↥((smallChains U V).X n) :=
  (inferInstance : Module.Projective ℤ
    ↥(∐ (fun _ : (smallSSet U V).obj (Opposite.op (SimplexCategory.mk n)) =>
          ModuleCat.of ℤ ℤ)))

/-! ## The inclusion of the small-in-`A` chains is a split monomorphism -/

/-- **The projection of the small chains onto the small-in-`A` chains retracts the inclusion**:
`(smallInToSmall U V A).f n ≫ smallInProj U V A n = 𝟙`.  This is the `hcomp` step of
`smallInToSmall_f_injective`, exported for use in the projectivity argument. -/
theorem smallInToSmall_comp_smallInProj (X : TopCat) (U V A : Set X) (n : ℕ) :
    (smallInToSmall U V A).f n ≫ smallInProj U V A n = 𝟙 ((smallInChains U V A).X n) := by
  classical
  have hfac : ∀ σ : (smallSSet U V) _⦋n⦌,
      (smallSSet U V).ιChainComplex (R := ModuleCat.of ℤ ℤ) σ ≫ smallInProj U V A n
        = if h : IsSmallIn U V A σ.1 then
            (smallInSSet U V A).ιChainComplex ⟨σ.1, h⟩ else 0 :=
    fun σ => Cofan.IsColimit.fac _ _ _
  apply SSet.chainComplex_hom_ext (X := smallInSSet U V A) (R := ModuleCat.of ℤ ℤ) (n := n)
  intro x
  have h1 : (smallInSSet U V A).ιChainComplex (R := ModuleCat.of ℤ ℤ) x
      ≫ (smallInToSmall U V A).f n
      = (smallSSet U V).ιChainComplex (R := ModuleCat.of ℤ ℤ) ⟨x.1, x.2.1⟩ := by
    have h := SSet.ι_chainComplexMap_f
      (f := Subfunctor.homOfLe (smallInSubcomplex_le U V A)) (R := ModuleCat.of ℤ ℤ)
      (X := smallInSSet U V A) (Y := smallSSet U V) (n := n) x
    simp [smallInToSmall]
  rw [← Category.assoc, h1, Category.comp_id, hfac,
    dif_pos (show IsSmallIn U V A (⟨x.1, x.2.1⟩ : (smallSSet U V) _⦋n⦌).1 from x.2)]
  congr 1

/-! ## The relative small chains are degreewise projective -/

/-- **The relative small chains `C^{U,V}_n(X,A)` form a projective `ℤ`-module.**

`relSmallTop U V A` is the cokernel of the split monomorphism
`smallInToSmall U V A : C^{U,V}_*(A) ⟶ C^{U,V}_*(X)`, split degreewise by `smallInProj`, and
`C^{U,V}_n(X)` is projective (a coproduct of copies of `ℤ`), so `C^{U,V}_n(X,A)` is a direct
summand of `C^{U,V}_n(X)` and hence projective. -/
theorem relSmallTopProjective (X : TopCat) (U V A : Set X) (n : ℕ) :
    Module.Projective ℤ ↥((relSmallTop U V A).X n) := by
  haveI : Module.Projective ℤ ↥((smallChains U V).X n) := projective_smallChains X U V n
  have hproj : Module.Projective ℤ ↥(cokernel ((smallInToSmall U V A).f n)) :=
    projective_cokernel_of_split_mono ((smallInToSmall U V A).f n) (smallInProj U V A n)
      (smallInToSmall_comp_smallInProj X U V A n)
  haveI := hproj
  exact Module.Projective.of_equiv'
    ((chainCokernelIso (smallInChains U V A) (smallChains U V) (smallInToSmall U V A) n).symm.toLinearEquiv)

/-! ## The main result -/

/-- **The relative small cochains compute relative cohomology.**

For an open cover `U ∪ V = X` of a topological space and an arbitrary subset `A ⊆ X`, the cohomology
of the `ℤ`-dual of the relative small chains `C^{U,V}_*(X,A)` is the relative singular cohomology
`H^n(X,A;ℤ)`. -/
theorem relSmallCochains_iso (X : TopCat) (A U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) (n : ℕ) :
    Nonempty (Work.Cohomology.relCohomology ℤ X A n ≅
      HomologicalComplex.homology
        (Work.Cohomology.dualComplex ℤ (Work.Cohomology.relSmallTop U V A)) n) := by
  obtain ⟨e⟩ := relCochainDual X A
  obtain ⟨phi, hphi, _⟩ := relMV_quasiIso X A U V hU hV hcov
  have h1 : Work.Cohomology.relCohomology ℤ X A n ≅
      HomologicalComplex.homology (Work.Cohomology.dualComplex ℤ
        (Work.Cohomology.relChains X A)) n :=
    Functor.mapIso
      (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.up ℕ) n) e
  haveI : CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.dualComplexMap ℤ (Work.Cohomology.relSmallTop U V A)
        (Work.Cohomology.relChains X A) phi) n) :=
    dualComplexMap_quasiIso phi (fun k => relSmallTopProjective X U V A k)
      (fun k => relChainsProjective X A k) hphi n
  have h2 : HomologicalComplex.homology (Work.Cohomology.dualComplex ℤ
        (Work.Cohomology.relChains X A)) n ≅
      HomologicalComplex.homology (Work.Cohomology.dualComplex ℤ
        (Work.Cohomology.relSmallTop U V A)) n :=
    asIso (HomologicalComplex.homologyMap
      (Work.Cohomology.dualComplexMap ℤ (Work.Cohomology.relSmallTop U V A)
        (Work.Cohomology.relChains X A) phi) n)
  exact ⟨h1 ≪≫ h2⟩

end

end Work.Cohomology
