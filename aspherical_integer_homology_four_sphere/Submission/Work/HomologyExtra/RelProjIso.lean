import Mathlib
import ChallengeDeps
import Submission.Work.HomologyExtra.Basic
import Submission.Work.Homology.Pairs
import Submission.Work.Homology.StdSimplexHomology
import Submission.Work.Cohomology.epsilonNaturality

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The projection `H₁(X) → H₁(X,A)` is an isomorphism when `A` is connected and `H₁(A) = 0`

Two general lemmas about the long exact sequence of a pair `(X, A)`:

* `Work.HomologyExtra.mono_homologyMap_inclChain_zero` — if `A` is path-connected then the map
  `H₀(A;ℤ) ⟶ H₀(X;ℤ)` induced by the inclusion is a monomorphism.  (It is the naturality of the
  augmentation `ε : H₀(-;ℤ) → ℤ` together with the fact that `ε` is an isomorphism for a
  path-connected space: if `i(x) = i(y)` then `ε(x) = ε(i x) = ε(i y) = ε(y)` and `ε` is
  injective.)  Note that no hypothesis on `X` is needed, only on `A`.

* `Work.HomologyExtra.isIso_relProjHom_one` — if moreover `H₁(A;ℤ) = 0`, then
  `relProjHom : H₁(X;ℤ) ⟶ H₁(X,A;ℤ)` is an isomorphism.  Indeed in the exact sequence

  `H₁(A) → H₁(X) --g--> H₁(X,A) --δ--> H₀(A) --i--> H₀(X)`

  the map `g` is injective (exactness at `H₁(X)`, since `H₁(A) = 0`) and `δ = 0` (the composite
  `δ ≫ i` is zero and `i` is a monomorphism), so `g` is surjective by exactness at `H₁(X,A)`.

The case of interest is `A = simplexStar 1 ⊆ ∂Δ²`, which is contractible, hence
`H₁(A) = 0` and path-connected; this is what makes the argument for `simplexGenMap 1` work.
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.HomologyExtra

noncomputable section

/-- **The degree-`0` map induced by the inclusion of a path-connected subspace is injective.** -/
theorem mono_homologyMap_inclChain_zero (X : TopCat) (A : Set X)
    [PathConnectedSpace (TopCat.of A)] :
    Mono (HomologicalComplex.homologyMap (Work.Homology.inclChain Work.Homology.ZMod X A) 0) := by
  -- naturality of the augmentation
  have hnat := Work.Cohomology.epsilonNaturality (TopCat.of A) X (Work.Homology.incl A)
  have hcomp : LinearMap.comp (ModuleCat.Hom.hom (X.singularHomology₀ε (ModuleCat.of ℤ ℤ)))
      (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (Work.Homology.inclChain Work.Homology.ZMod X A) 0))
      = ModuleCat.Hom.hom ((TopCat.of A).singularHomology₀ε (ModuleCat.of ℤ ℤ)) := by
    have h := congrArg (fun (g : Work.Homology.singHomology Work.Homology.ZMod 0 (TopCat.of A) ⟶
      Work.Homology.ZMod) => ModuleCat.Hom.hom g) hnat
    rw [ModuleCat.hom_comp] at h
    exact h
  haveI : IsIso ((TopCat.of A).singularHomology₀ε (ModuleCat.of ℤ ℤ)) := inferInstance
  rw [ModuleCat.mono_iff_injective]
  intro x y hxy
  have hε : ModuleCat.Hom.hom ((TopCat.of A).singularHomology₀ε (ModuleCat.of ℤ ℤ)) x
      = ModuleCat.Hom.hom ((TopCat.of A).singularHomology₀ε (ModuleCat.of ℤ ℤ)) y := by
    have h1 : (ModuleCat.Hom.hom (X.singularHomology₀ε (ModuleCat.of ℤ ℤ))).comp
        (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
          (Work.Homology.inclChain Work.Homology.ZMod X A) 0)) x
        = (ModuleCat.Hom.hom (X.singularHomology₀ε (ModuleCat.of ℤ ℤ))).comp
        (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
          (Work.Homology.inclChain Work.Homology.ZMod X A) 0)) y := by
      simp only [LinearMap.comp_apply]
      exact congrArg (ModuleCat.Hom.hom (X.singularHomology₀ε (ModuleCat.of ℤ ℤ))) hxy
    rwa [hcomp] at h1
  exact (ConcreteCategory.isIso_iff_bijective
    ((TopCat.of A).singularHomology₀ε (ModuleCat.of ℤ ℤ))).mp inferInstance |>.1 hε

/-- **`H₁(X) → H₁(X,A)` is an isomorphism** when `A` is path-connected and `H₁(A) = 0`. -/
theorem isIso_relProjHom_one (X : TopCat) (A : Set X)
    (h1 : IsZero (Work.Homology.singHomology Work.Homology.ZMod 1 (TopCat.of A)))
    (h0 : Mono (HomologicalComplex.homologyMap
      (Work.Homology.inclChain Work.Homology.ZMod X A) 0)) :
    IsIso (Work.Homology.relProjHom Work.Homology.ZMod 1 X A) := by
  haveI hmono : Mono (Work.Homology.relProjHom Work.Homology.ZMod 1 X A) :=
    (ShortComplex.exact_iff_mono _ (h1.eq_of_src _ 0)).1
      (Work.Homology.pairHomHX_exact Work.Homology.ZMod X A 1)
  have hδ : (Work.Homology.pairHomA Work.Homology.ZMod X A 0).f = 0 := by
    rw [← cancel_mono (Work.Homology.pairHomA Work.Homology.ZMod X A 0).g, ShortComplex.zero,
      zero_comp]
  haveI hepi : Epi (Work.Homology.relProjHom Work.Homology.ZMod 1 X A) :=
    (ShortComplex.exact_iff_epi _ hδ).1 (Work.Homology.pairHomRel_exact Work.Homology.ZMod X A 0)
  exact isIso_of_mono_of_epi _

end

end Work.HomologyExtra
