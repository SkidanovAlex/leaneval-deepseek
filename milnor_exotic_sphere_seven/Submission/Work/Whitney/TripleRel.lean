import Mathlib
import Submission.Work.Whitney.TCMDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# The three-fold intersection complex `C^*(X, A+B+C)` and the inclusion `C^*(X,A∪B∪C) → C^*(X,A+B+C)`

This module isolates the *only* new homological input of the associativity of the canonical
relative–relative cup `Work.Whitney.tcmRelCup` (`Work.Whitney.tcmRelCupAssoc`): the three-fold
analogue of the two-fold quasi-isomorphism `Work.Whitney.pdABInclRelR_quasiIso`.

For open `A B C ⊆ X` the `A+B+C` cochain complex is the degreewise intersection of the three
relative kernels, and the inclusion of the relative complex of the union is

`pd3InclRelR : C^*(X, A∪B∪C) ⟶ C^*(X, A+B+C)`.

The two-fold statement (`pdABInclRelR_quasiIso`) says that for **two** open sets the `A+B` complex
computes the relative cohomology of the union (`H^*(X,A∪B) ≅ H^*(X,A+B)`, i.e. the small cochains
of the open cover `(A,B)` of `A∪B` compute relative cohomology).  The content of this file is the
same statement for three sets.

## Why it is needed, and the *proved reduction* to the two-fold statement

In `Work.Whitney.tcmRelCupAssoc` one has to compare the two bracketings of the triple product; the
only point at which the two *gauges* used in the definition of `tcmRelCup` (`pdABInclRelR` for the
pairs `(A∪B, C)` and `(A, B∪C)`) can be compared is inside the common `A+B+C` complex: the two
bracketed products have the same image in `H^*(X, A+B+C)`, and the comparison becomes an equality
as soon as the map

`H^*(X, A∪B∪C) ⟶ H^*(X, A+B+C)`

is **injective** (equivalently, is a quasi-isomorphism, which is the statement below).

The injectivity is equivalent – by the long exact sequence of the short exact sequence of
complexes `0 → C^*(X,A∪B∪C) → C^*(X,A+B+C) → Q → 0` – to the acyclicity of the quotient, which is
the ℤ-dual of the acyclicity of the *chain-level* quotient

`M = (C_*(A∪B) + C_*(C)) / (C_*(A) + C_*(B) + C_*(C))`.

Here is the reduction of `M`-acyclicity to the **two-fold** theorem, which is the plan of proof
(only `Work.Whitney.pdABInclRelR_quasiIso` in the (A,B) case and its two-fold cousins are used):

* write `N := C_*(A∪B)`, `N' := C_*(A) + C_*(B)`, `K := C_*(C)`, so that
  `M = (N+K)/(N'+K)`, and `N' → N` is a quasi-isomorphism (the two-fold statement for `(A,B)`,
  the dual of `pdABInclRelR_quasiIso` for `(A,B)`);
* the 5-lemma applied to the map of short exact sequences
  `0 → N' → N'+K → K/(N'∩K) → 0`  and  `0 → N → N+K → K/(N∩K) → 0`
  shows that `N'+K → N+K` is a quasi-isomorphism **iff** `K/(N'∩K) → K/(N∩K)` is one, i.e. iff
  `N'∩K → N∩K` is one (the middle vertical map `K → K` being the identity);
* finally the two intersections have an elementary description.  The chain modules of `X` are free
  on the singular simplices and the subcomplex `C_*(S)` is spanned by the simplices *lying in* `S`,
  so a chain lies in `C_*(S) ∩ C_*(T)` iff it is a combination of simplices lying in `S ∩ T`:
  `C_*(S) ∩ C_*(T) = C_*(S ∩ T)`.  Hence
  `N ∩ K = C_*((A∪B) ∩ C)` and `N' ∩ K = C_*(A)∩C_*(C) + C_*(B)∩C_*(C) = C_*(A∩C) + C_*(B∩C)`,
  and the map `N'∩K → N∩K` becomes

  `C_*(A∩C) + C_*(B∩C) ⟶ C_*((A∪B)∩C)`,

  which is **exactly the two-fold theorem applied to the open cover `(A∩C, B∩C)` of the subspace
  `(A∪B)∩C`** (their union is `(A∪B)∩C`).
-/

namespace Work.Whitney

open Work.Cohomology
open CategoryTheory AlgebraicTopology CategoryTheory.Limits

noncomputable section

/-- The degree-`n` part of the `A+B+C` complex: the intersection of the three relative kernels. -/
def pd3KernR (X : TopCat) (A B C : Set X) (n : ℕ) :
    Submodule ℤ ((singularCochainComplex ℤ X).X n) :=
  relKern ℤ X A n ⊓ relKern ℤ X B n ⊓ relKern ℤ X C n

/-- The differential of the `A+B+C` complex. -/
def pd3DiffLMR (X : TopCat) (A B C : Set X) (n : ℕ) :
    (pd3KernR X A B C n) →ₗ[ℤ] (pd3KernR X A B C (n+1)) :=
  (((singularCochainComplex ℤ X).d n (n+1)).hom.comp
      (Submodule.subtype (pd3KernR X A B C n))).codRestrict
    (pd3KernR X A B C (n+1))
    (fun x => Submodule.mem_inf.mpr ⟨
      Submodule.mem_inf.mpr
        ⟨relKern_d_memR X A n x.1 (Submodule.mem_inf.mp (Submodule.mem_inf.mp x.2).1).1,
         relKern_d_memR X B n x.1 (Submodule.mem_inf.mp (Submodule.mem_inf.mp x.2).1).2⟩,
      relKern_d_memR X C n x.1 (Submodule.mem_inf.mp x.2).2⟩)

@[simp] theorem pd3DiffLMR_coe (X : TopCat) (A B C : Set X) (n : ℕ)
    (x : pd3KernR X A B C n) :
    (pd3DiffLMR X A B C n x).1 = ((singularCochainComplex ℤ X).d n (n+1)).hom x.1 := rfl

/-- The differential as a morphism of modules. -/
def pd3DiffR (X : TopCat) (A B C : Set X) (n : ℕ) :
    ModuleCat.of ℤ (pd3KernR X A B C n) ⟶ ModuleCat.of ℤ (pd3KernR X A B C (n+1)) :=
  ModuleCat.ofHom (pd3DiffLMR X A B C n)

/-- **The `A+B+C` cochain complex** `C^*(X, A+B+C) = C^*(X,A) ∩ C^*(X,B) ∩ C^*(X,C)`. -/
def pd3CohR (X : TopCat) (A B C : Set X) : CochainComplex (ModuleCat ℤ) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of ℤ (pd3KernR X A B C n)) (fun n => pd3DiffR X A B C n)
    (fun n => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      rw [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply,
        Submodule.coe_zero]
      show ((pd3DiffLMR X A B C (n+1)) ((pd3DiffLMR X A B C n) x)).1 = 0
      rw [pd3DiffLMR_coe, pd3DiffLMR_coe]
      have h := congrArg ModuleCat.Hom.hom
        (HomologicalComplex.d_comp_d (singularCochainComplex ℤ X) n (n+1) (n+2))
      rw [ModuleCat.hom_comp, ModuleCat.hom_zero] at h
      have h2 := LinearMap.congr_fun h x.1
      simp only [LinearMap.comp_apply, LinearMap.zero_apply] at h2
      exact h2)

@[simp] theorem pd3CohR_d (X : TopCat) (A B C : Set X) (n : ℕ) :
    (pd3CohR X A B C).d n (n+1) = pd3DiffR X A B C n :=
  CochainComplex.of_d (fun n => ModuleCat.of ℤ (pd3KernR X A B C n))
    (fun n => pd3DiffR X A B C n) n

/-- **The inclusion `C^*(X, A∪B∪C) ⟶ C^*(X, A+B+C)`.** -/
def pd3InclRelR (X : TopCat) (A B C : Set X) :
    relComplex ℤ X (A ∪ B ∪ C) ⟶ pd3CohR X A B C :=
  CochainComplex.ofHom
    (fun n => ModuleCat.ofHom (Submodule.inclusion
      (le_inf
        (le_inf (relKern_mono (by intro x hx; simp [hx] : A ⊆ A ∪ B ∪ C))
          (relKern_mono (by intro x hx; simp [hx] : B ⊆ A ∪ B ∪ C)))
        (relKern_mono (by intro x hx; simp [hx] : C ⊆ A ∪ B ∪ C)))))
    (fun n => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      rw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply,
        relComplex_d, pd3CohR_d]
      rfl)


/-- The inclusion `C^*(X, (A∪B)+C) ⟶ C^*(X, A+B+C)`. -/
def pdABCOhR_to_pd3CohR_left (X : TopCat) (A B C : Set X) :
    pdABCohR (R := ℤ) X (A ∪ B) C ⟶ pd3CohR X A B C :=
  CochainComplex.ofHom
    (fun n => ModuleCat.ofHom (Submodule.inclusion (by
      intro x hx
      rw [pdABKernR, Submodule.mem_inf] at hx
      rw [pd3KernR, Submodule.mem_inf, Submodule.mem_inf]
      exact ⟨⟨relKern_mono (by intro y hy; simp [hy] : A ⊆ A ∪ B) hx.1,
        relKern_mono (by intro y hy; simp [hy] : B ⊆ A ∪ B) hx.1⟩, hx.2⟩)))
    (fun n => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      rw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply,
        pdABCohR_d, pd3CohR_d]
      rfl)

/-- The inclusion `C^*(X, A+(B∪C)) ⟶ C^*(X, A+B+C)`. -/
def pdABCOhR_to_pd3CohR_right (X : TopCat) (A B C : Set X) :
    pdABCohR (R := ℤ) X A (B ∪ C) ⟶ pd3CohR X A B C :=
  CochainComplex.ofHom
    (fun n => ModuleCat.ofHom (Submodule.inclusion (by
      intro x hx
      rw [pdABKernR, Submodule.mem_inf] at hx
      rw [pd3KernR, Submodule.mem_inf, Submodule.mem_inf]
      exact ⟨⟨hx.1, relKern_mono (by intro y hy; simp [hy] : B ⊆ B ∪ C) hx.2⟩,
        relKern_mono (by intro y hy; simp [hy] : C ⊆ B ∪ C) hx.2⟩)))
    (fun n => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      rw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply,
        pdABCohR_d, pd3CohR_d]
      rfl)

end

end Work.Whitney
