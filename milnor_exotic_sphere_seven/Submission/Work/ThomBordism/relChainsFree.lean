import Mathlib
import Submission.Work.Cohomology.singularChains_free
import Submission.Work.Cohomology.relChainsProjective
import Submission.Work.Cohomology.free_submodule_of_free_int

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The relative singular chains are degreewise free

`Work.Cohomology.relChainsProjective` proves that every degree of the relative singular chain
complex `C_*(X,A)` is a *projective* `ℤ`-module.  Here we prove the stronger statement that every
degree is *free*.

`C_n(X,A)` is the cokernel of the split monomorphism `C_n(A) ⟶ C_n(X)` (`chainRetract`), and the
cokernel of a split monomorphism into a free module is free: if `f : M ⟶ N` is split by
`s : N ⟶ M` (`f ≫ s = 𝟙 M`), then `coker f` is the direct summand `ker s ⊆ N` of `N`, and a
submodule of a free `ℤ`-module is free (`Work.Cohomology.free_submodule_of_free_int`).

## Main results

* `free_cokernel_of_split_mono` — the cokernel of a split monomorphism into a free module is free;
* `relChains_X_free` — `C_n(X,A)` is a free `ℤ`-module.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

attribute [local instance 5000] Submodule.module

open CategoryTheory CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

/-- All `Module ℤ M` structures on a fixed `AddCommGroup` are equal, so freeness can be
transported between them. -/
theorem free_instance_congr {M : Type*} [AddCommGroup M] {i₁ i₂ : Module ℤ M}
    (h : @Module.Free ℤ M _ _ i₁) : @Module.Free ℤ M _ _ i₂ :=
  Eq.mp (congrArg (fun i => @Module.Free ℤ M _ _ i) (Subsingleton.elim i₁ i₂)) h

/-- **The cokernel of a split monomorphism into a free `ℤ`-module is free.**

If `f : M ⟶ N` has a retraction `s : N ⟶ M`, then the idempotent `q = 𝟙 N - s ≫ f` factors
through `cokernel f`, and the induced map `σ : cokernel f ⟶ N` is a section of `cokernel.π f`;
hence `cokernel f` is isomorphic to the submodule `range σ ⊆ N`, and `range σ` is free whenever
`N` is. -/
theorem free_cokernel_of_split_mono {M N : ModuleCat ℤ} (f : M ⟶ N) (s : N ⟶ M)
    (h : f ≫ s = 𝟙 M) [Module.Free ℤ ↥N] : Module.Free ℤ ↥(cokernel f) := by
  have hq : f ≫ (𝟙 N - s ≫ f) = 0 := by
    rw [Preadditive.comp_sub, Category.comp_id, ← Category.assoc, h, Category.id_comp, sub_self]
  let σ : cokernel f ⟶ N := cokernel.desc f (𝟙 N - s ≫ f) hq
  have hsec : σ ≫ cokernel.π f = 𝟙 (cokernel f) := by
    rw [← cancel_epi (cokernel.π f), ← Category.assoc, cokernel.π_desc, Preadditive.sub_comp,
      Category.id_comp, Category.assoc, cokernel.condition, comp_zero, sub_zero, Category.comp_id]
  have hπσ : ∀ x : ↥(cokernel f), (cokernel.π f).hom (σ.hom x) = x := by
    intro x
    have h2 := congrArg ModuleCat.Hom.hom hsec
    rw [ModuleCat.hom_comp, ModuleCat.hom_id] at h2
    exact LinearMap.congr_fun h2 x
  have hinj : Function.Injective σ.hom := fun a b hab => by rw [← hπσ a, ← hπσ b, hab]
  have hfr := free_submodule_of_free_int (LinearMap.range σ.hom)
  exact Module.Free.of_equiv' (free_instance_congr hfr)
    (LinearEquiv.ofInjective σ.hom hinj).symm

/-- **The relative singular chains are degreewise free.** -/
theorem relChains_X_free (X : TopCat) (A : Set X) (k : ℕ) :
    Module.Free ℤ ↥((relChains X A).X k) := by
  haveI : Module.Free ℤ ↥((singularChains ℤ X).X k) := singularChains_free X k
  have hfree : Module.Free ℤ ↥(cokernel ((inclChains X A).f k)) :=
    free_cokernel_of_split_mono ((inclChains X A).f k) (chainRetract ℤ X A k)
      (chainRetract_spec ℤ X A k)
  exact Module.Free.of_equiv' hfree (relChains_cokernelIso X A k).symm.toLinearEquiv

end

end Work.Cohomology
