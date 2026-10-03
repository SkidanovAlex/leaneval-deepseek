import Mathlib
import Submission.Work.ORReductions.API
import Submission.Work.ORReductions.Coherent.submodule_fg_ker_of_coherent
import Submission.Work.ORReductions.Coherent.submodule_finitePresentation_of_fg

/-!
# Coherence of a finite free ring extension

Let `R` be a ring and `S` a ring which is a *finite free* left `R`-module via a ring homomorphism
`f : R →+* S` (so `r • s = f r * s`).  If `R` is coherent (every finitely generated left ideal of
`R` is finitely presented), then so is `S`.

This is the standard fact that coherence is inherited by finite free ring extensions.  The proof
follows the pattern of Chase's lemma:

* a finitely generated ideal `I` of `S` is finitely generated as an `R`-module
  (`Submodule.FG.restrictScalars`, using `S` finite over `R`);
* since `S` is finite free over `R`, `I` is a finitely generated `R`-submodule of a finite free
  `R`-module, hence finitely presented over `R` (Chase's lemma, `chase_free` / the companion file
  `submodule_finitePresentation_of_fg`);
* writing `S^k ↠ I` for the `S`-linear surjection from the chosen generators, its kernel is
  `R`-finitely generated (a surjection from the finitely generated `R`-module `S^k` onto the
  finitely presented `R`-module `I` has finitely generated kernel,
  `Module.FinitePresentation.fg_ker`), and being an `S`-submodule of `S^k` it is then finitely
  generated over `S` (`Submodule.FG.of_restrictScalars`);
* a surjection with finitely generated kernel onto a finitely generated module exhibits it as
  finitely presented (`Module.finitePresentation_of_surjective`).
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open Work.ORReductions.Coherent

namespace Work.ORFinal.FiniteFree

/-- **Chase's lemma, free-module form.**  Over a coherent ring `R`, every finitely generated
submodule of an arbitrary finite free `R`-module is finitely presented.

This upgrades `submodule_finitePresentation_of_fg`, which is stated only for `Fin q → R`, to a
general finite free module `M` by choosing a basis indexed by `Fin (card ι)` and transporting along
the resulting linear equivalence. -/
theorem submodule_finitePresentation_of_fg_of_free {R : Type*} [Ring R] (hR : Ring.Coherent R)
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
    (N : Submodule R M) (hN : N.FG) : Module.FinitePresentation R N := by
  classical
  let n := Fintype.card (Module.Free.ChooseBasisIndex R M)
  let b : Module.Basis (Fin n) R M := (Module.Free.chooseBasis R M).reindex (Fintype.equivFin _)
  let e : M ≃ₗ[R] (Fin n → R) := b.equivFun
  have hN' : (N.map (e : M →ₗ[R] (Fin n → R))).FG := hN.map (e : M →ₗ[R] (Fin n → R))
  have hfp : Module.FinitePresentation R (N.map (e : M →ₗ[R] (Fin n → R))) :=
    submodule_finitePresentation_of_fg hR _ hN'
  haveI := hfp
  exact Module.FinitePresentation.of_equiv
    (Submodule.equivMapOfInjective (e : M →ₗ[R] (Fin n → R)) e.injective N).symm

/-- Coherence is inherited by a finite free ring extension: if `S` is a ring which is a finite free
left `R`-module with `r • s = f r * s` for a ring homomorphism `f : R →+* S`, and `R` is coherent,
then `S` is coherent. -/
theorem ringCoherent_of_finite_free (R : Type*) [Ring R] (S : Type*) [Ring S] (f : R →+* S)
    [Module R S] (hsmul : ∀ (r : R) (s : S), r • s = f r * s)
    [Module.Free R S] [Module.Finite R S] (h : Ring.Coherent R) : Ring.Coherent S := by
  -- The `R`-action on `S` is compatible with the `S`-action, giving a scalar tower.
  haveI hST : IsScalarTower R S S :=
    ⟨fun r s t => by simp only [hsmul, smul_eq_mul]; rw [mul_assoc]⟩
  intro I hI
  -- Choose `S`-module generators of `I`, giving a surjection `S^k ↠ I`.
  obtain ⟨k, φ, hφ⟩ := (Submodule.fg_iff_exists_fin_linearMap S S).mp hI
  let ψ : (Fin k → S) →ₗ[S] I := φ.codRestrict I (fun x => hφ ▸ LinearMap.mem_range_self φ x)
  have hψ : Function.Surjective ψ := by
    rintro ⟨y, hy⟩
    rw [← hφ] at hy
    obtain ⟨x, rfl⟩ := hy
    exact ⟨x, rfl⟩
  -- `I` is finitely generated over `R`, hence finitely presented over `R` (Chase).
  have hIR : (I.restrictScalars R).FG := Submodule.FG.restrictScalars hI
  haveI hfpR : Module.FinitePresentation R (I.restrictScalars R) :=
    submodule_finitePresentation_of_fg_of_free h _ hIR
  -- The two `R`-module structures on the underlying type of `I` (the one coming from `S` via the
  -- scalar tower and the restricted one) agree, so transfer finite presentation across.
  haveI hfpI : Module.FinitePresentation R ↥I :=
    Module.FinitePresentation.of_equiv
      ({ toFun := fun x => ⟨x.1, x.2⟩
         invFun := fun x => ⟨x.1, x.2⟩
         left_inv := fun x => rfl
         right_inv := fun x => rfl
         map_add' := fun x y => rfl
         map_smul' := fun r x => rfl } : ↥(I.restrictScalars R) ≃ₗ[R] ↥I)
  -- `ψ` is also `R`-linear; its kernel is a finitely generated `R`-module.
  have hsurj : Function.Surjective (LinearMap.restrictScalars R ψ) := hψ
  have hkerR : (Submodule.restrictScalars R (LinearMap.ker ψ)).FG := by
    have hker := Module.FinitePresentation.fg_ker (LinearMap.restrictScalars R ψ) hsurj
    rwa [show LinearMap.ker (LinearMap.restrictScalars R ψ)
          = Submodule.restrictScalars R (LinearMap.ker ψ) from rfl] at hker
  -- Being an `S`-submodule, the kernel is then finitely generated over `S`.
  have hkerS : (LinearMap.ker ψ).FG := Submodule.FG.of_restrictScalars R hkerR
  exact Module.finitePresentation_of_surjective ψ hψ hkerS

end Work.ORFinal.FiniteFree
