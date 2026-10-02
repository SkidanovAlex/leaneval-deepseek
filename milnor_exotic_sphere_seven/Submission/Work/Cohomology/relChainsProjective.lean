import Mathlib
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.Cohomology.relCochain_shortExact

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The relative singular chains are degreewise projective

For a topological space `X` and a subset `A ⊆ X`, the relative singular chain complex
`C_*(X,A)` is defined (`Work.Cohomology.relChains`) as the cokernel of the inclusion
`C_*(A) ⟶ C_*(X)` of chain complexes.  The main result of this file is

`Module.Projective ℤ ↥((relChains X A).X n)` :

every degree of `C_*(X,A)` is a projective `ℤ`-module.

The argument has three ingredients.

* The `n`-th singular chains of `X` form the coproduct, over the singular `n`-simplices of `X`, of
  copies of `ℤ`; a coproduct of projective modules is projective, so `C_n(X)` is projective
  (`projective_singularChains`).

* The inclusion `C_n(A) ⟶ C_n(X)` is a split monomorphism, by the explicit retraction
  `Work.Cohomology.chainRetract` of singular chains (`chainRetract_spec`): a simplex of `X` that
  comes from `A` is sent back to its (unique) preimage, and all other simplices to `0`.  Whenever
  `f : M ⟶ N` is a split monomorphism with `N` projective, `cokernel f` is a direct summand of `N`
  (an explicit section of `cokernel.π f` is built from the idempotent `𝟙 N - s ≫ f`), hence
  projective (`projective_cokernel_of_split_mono`).

* Finally, the `n`-th component of a cokernel of chain complexes is the cokernel of the `n`-th
  component, because the evaluation functors `HomologicalComplex.eval` preserve colimits
  (`relChains_cokernelIso`).

## Main results

* `projective_singularChains` — the singular chains `C_n(X)` are projective.
* `projective_cokernel_of_split_mono` — the cokernel of a split monomorphism into a projective
  module is projective.
* `relChains_cokernelIso` — `(relChains X A).X n ≅ cokernel ((inclChains X A).f n)`.
* `relChainsProjective` — `(relChains X A).X n` is a projective `ℤ`-module.
-/

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

/-! ## The singular chains in degree `n` are projective -/

/-- The singular `n`-chains of `X` are the coproduct, over the singular `n`-simplices of `X`, of
copies of `ℤ`; hence they form a projective `ℤ`-module. -/
theorem projective_singularChains (X : TopCat) (n : ℕ) :
    Module.Projective ℤ ↥((singularChains ℤ X).X n) :=
  (inferInstance : Module.Projective ℤ
    ↥(∐ (fun _ : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n)) =>
          ModuleCat.of ℤ ℤ)))

/-! ## The cokernel of a split monomorphism into a projective module -/

/-- **The cokernel of a split monomorphism into a projective module is projective.**

If `f : M ⟶ N` admits a retraction `s` (`f ≫ s = 𝟙 M`) and `N` is projective, then `cokernel f` is
a direct summand of `N`: the idempotent `q = 𝟙 N - s ≫ f` on `N` satisfies `f ≫ q = 0`, so it
factors through `σ := cokernel.desc f q _ : cokernel f ⟶ N`; and since `q ≫ cokernel.π f =
cokernel.π f`, the map `σ` is a section of `cokernel.π f`.  A direct summand of a projective
module is projective (`Module.Projective.of_split`). -/
theorem projective_cokernel_of_split_mono {R : Type*} [Ring R] {M N : ModuleCat R}
    (f : M ⟶ N) (s : N ⟶ M) (h : f ≫ s = 𝟙 M) [Module.Projective R ↥N] :
    Module.Projective R ↥(cokernel f) := by
  -- `q = 𝟙 N - s ≫ f` is the idempotent projection onto the complement of `im f`.
  have hq : f ≫ (𝟙 N - s ≫ f) = 0 := by
    rw [Preadditive.comp_sub, Category.comp_id, ← Category.assoc, h, Category.id_comp, sub_self]
  -- `σ` is the section of `cokernel.π f` associated with `q`.
  let σ : cokernel f ⟶ N := cokernel.desc f (𝟙 N - s ≫ f) hq
  have hσ : cokernel.π f ≫ σ = 𝟙 N - s ≫ f := cokernel.π_desc f _ hq
  -- `q` is the identity on `coker f`, i.e. `q ≫ cokernel.π f = cokernel.π f`.
  have hqπ : (𝟙 N - s ≫ f) ≫ cokernel.π f = cokernel.π f := by
    rw [Preadditive.sub_comp, Category.id_comp, Category.assoc, cokernel.condition, comp_zero,
      sub_zero]
  -- hence `σ` is a section of `cokernel.π f`.
  have hsec : σ ≫ cokernel.π f = 𝟙 (cokernel f) := by
    rw [← cancel_epi (cokernel.π f), ← Category.assoc, hσ, hqπ, Category.comp_id]
  have hcomp : (cokernel.π f).hom.comp σ.hom = LinearMap.id := by
    have h2 := congrArg ModuleCat.Hom.hom hsec
    rwa [ModuleCat.hom_comp, ModuleCat.hom_id] at h2
  exact Module.Projective.of_split σ.hom (cokernel.π f).hom hcomp

/-! ## The `n`-th component of a cokernel of chain complexes -/

/-- **The `n`-th component of the cokernel of a morphism of chain complexes is the cokernel of the
`n`-th component.**

The evaluation functor `HomologicalComplex.eval` preserves colimits, so the colimiting cocone
defining `(cokernel f).X n` is a colimiting cocone for the diagram `parallelPair (f.f n) 0`; the
two functors `parallelPair f 0 ⋙ eval` and `parallelPair (f.f n) 0` are equal (they have the same
objects and morphisms), which compares the two colimits. -/
def relChains_cokernelIso (X : TopCat) (A : Set X) (n : ℕ) :
    (relChains X A).X n ≅ cokernel ((inclChains X A).f n) := by
  let F : WalkingParallelPair ⥤ ModuleCat ℤ := (parallelPair (inclChains X A) 0) ⋙
    HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) n
  let G : WalkingParallelPair ⥤ ModuleCat ℤ := parallelPair ((inclChains X A).f n) 0
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
        (colimit.isColimit (parallelPair (inclChains X A) 0)))
      (colimit.isColimit F) ≪≫ HasColimit.isoOfNatIso (eqToIso hFG)

/-! ## The relative chains are degreewise projective -/

/-- **The relative singular chains `C_n(X,A)` form a projective `ℤ`-module.**

`C_*(X,A)` is the cokernel of the split monomorphism `C_*(A) ⟶ C_*(X)` (split degreewise by
`chainRetract`), and `C_n(X)` is projective, so `C_n(X,A)` is a direct summand of `C_n(X)`. -/
theorem relChainsProjective (X : TopCat) (A : Set X) (n : ℕ) :
    Module.Projective ℤ ↥((relChains X A).X n) := by
  haveI : Module.Projective ℤ ↥((singularChains ℤ X).X n) := projective_singularChains X n
  have hproj : Module.Projective ℤ ↥(cokernel ((inclChains X A).f n)) :=
    projective_cokernel_of_split_mono ((inclChains X A).f n) (chainRetract ℤ X A n)
      (chainRetract_spec ℤ X A n)
  haveI := hproj
  exact Module.Projective.of_equiv' ((relChains_cokernelIso X A n).symm.toLinearEquiv)

end

end Work.Cohomology
