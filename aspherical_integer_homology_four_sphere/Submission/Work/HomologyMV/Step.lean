import Mathlib
import Submission.Work.HomologyMV.Basic
import Submission.Work.HomologyMV.Model
import Submission.Work.HomologyMV.LinAlg

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `HomologyMV/`: one degree of the Mayer–Vietoris computation

This file turns the linear-algebra lemmas into the single step that the assembly iterates.

The data of the computation is

* a Mayer–Vietoris long exact sequence `L : MVLES` (see `Basic.lean`), whose `(k,0)`, `(k,1)`,
  `(k,2)` slots are `H_k(A ∩ B)`, `H_k(A) ⊞ H_k(B)`, `H_k(M̂)`;
* isomorphisms `eM k : ModelM k ≅ L.H (k,0)` and `eN k : ModelN k ≅ L.H (k,1)` identifying the
  first two slots with the free models of `Model.lean` (this is where the SDR/`HS2`/`HS3`
  identifications enter);
* model maps `w k : ModelM k ⟶ ModelN k` (the concrete matrices `φ_k` of `Data.lean`) whose
  composite with the identifications *is* the Mayer–Vietoris map:
  `(eM k).hom ≫ L.d (k,0) = w k ≫ (eN k).hom`.

The hypotheses of `step_iso` are the surjectivity of `φ_k` (for `k ≥ 1`) and the transport of the
commutative square; the conclusion is that the `X`-slot in degree `k` is the kernel of `φ_{k-1}`,
which is where the answer `ℤ` in degree `4` and `0` elsewhere comes from.

## Main results

* `Work.HomologyMV.kerIso_of_square`, `Work.HomologyMV.rangeTop_of_square` — transport of kernels
  and of surjectivity along a commutative square of `ModuleCat ℤ`;
* `Work.HomologyMV.step_iso` — `L.H (k,2) ≅ ker (w (k-1))` for `k ≥ 1`.
-/

namespace Work.HomologyMV

open CategoryTheory

noncomputable section

variable {A B A' B' : ModuleCat ℤ}

/-- Kernels are unchanged by linear equivalences in a commutative square: if
`d (eM x) = eN (w x)` for all `x`, with `eM`, `eN` linear equivalences, then `ker d ≃ ker w`.
(This is the underlying-types form of the transport; the `ModuleCat` form is
`kerIso_of_square` below.) -/
theorem kerIso_of_commSquare_aux {M N M' N' : Type*} [AddCommGroup M] [AddCommGroup N]
    [AddCommGroup M'] [AddCommGroup N'] [Module ℤ M] [Module ℤ N] [Module ℤ M'] [Module ℤ N']
    (eM : M ≃ₗ[ℤ] M') (eN : N ≃ₗ[ℤ] N') (d : M' →ₗ[ℤ] N') (w : M →ₗ[ℤ] N)
    (hsq : ∀ x, d (eM x) = eN (w x)) : Nonempty (d.ker ≃ₗ[ℤ] w.ker) := by
  let φ := (eM.toLinearMap.comp w.ker.subtype).codRestrict d.ker (fun x => by
    show d (eM x.1) = 0
    rw [hsq x.1, x.2, map_zero])
  have hφval : ∀ z : w.ker, (φ z : M') = eM z.1 := fun z => rfl
  have hφinj : Function.Injective φ := fun x y hxy => by
    have h : eM x.1 = eM y.1 := by
      rw [← hφval x, ← hφval y]
      exact congrArg (fun z : d.ker => (z : M')) hxy
    exact Subtype.ext (eM.injective h)
  have hφsurj : Function.Surjective φ := fun y => by
    refine ⟨⟨eM.symm y.1, ?_⟩, Subtype.ext ?_⟩
    · show w (eM.symm y.1) = 0
      have h1 : d (eM (eM.symm y.1)) = 0 := by rw [eM.apply_symm_apply]; exact y.2
      have h2 : eN (w (eM.symm y.1)) = 0 := by rw [← hsq]; exact h1
      exact eN.injective (by rw [h2, map_zero])
    · show eM (eM.symm y.1) = y.1
      rw [eM.apply_symm_apply]
  exact ⟨(LinearEquiv.ofBijective φ ⟨hφinj, hφsurj⟩).symm⟩

/-- Surjectivity is unchanged by linear equivalences in a commutative square. -/
theorem rangeTop_of_commSquare_aux {M N M' N' : Type*} [AddCommGroup M] [AddCommGroup N]
    [AddCommGroup M'] [AddCommGroup N'] [Module ℤ M] [Module ℤ N] [Module ℤ M'] [Module ℤ N']
    (eM : M ≃ₗ[ℤ] M') (eN : N ≃ₗ[ℤ] N') (d : M' →ₗ[ℤ] N') (w : M →ₗ[ℤ] N)
    (hsq : ∀ x, d (eM x) = eN (w x)) (hw : w.range = ⊤) : d.range = ⊤ := by
  rw [LinearMap.range_eq_top] at hw ⊢
  intro y
  obtain ⟨z, hz⟩ := hw (eN.symm y)
  exact ⟨eM z, by rw [hsq, hz, eN.apply_symm_apply]⟩

/-- An isomorphism of the two terms of a commutative square does not change the kernel. -/
theorem kerIso_of_square (eM : A ≅ A') (eN : B ≅ B') (d : A' ⟶ B') (w : A ⟶ B)
    (hsq : eM.hom ≫ d = w ≫ eN.hom) : Nonempty (d.hom.ker ≃ₗ[ℤ] w.hom.ker) := by
  refine kerIso_of_commSquare_aux eM.toLinearEquiv eN.toLinearEquiv d.hom w.hom ?_
  intro x
  have h := congrArg (fun (f : A ⟶ B') => f x) hsq
  simpa using h

/-- An isomorphism of the two terms of a commutative square does not change surjectivity. -/
theorem rangeTop_of_square (eM : A ≅ A') (eN : B ≅ B') (d : A' ⟶ B') (w : A ⟶ B)
    (hsq : eM.hom ≫ d = w ≫ eN.hom) (hw : w.hom.range = ⊤) : d.hom.range = ⊤ := by
  refine rangeTop_of_commSquare_aux eM.toLinearEquiv eN.toLinearEquiv d.hom w.hom ?_ hw
  intro x
  have h := congrArg (fun (f : A ⟶ B') => f x) hsq
  simpa using h

/-- The engine of the Mayer–Vietoris computation, in the form used here (the underlying-types
form of `Submission/Work/HomologyMV/isoKer_of_surjective.lean`): if
`M --f--> N --g--> X --h--> Y --g'--> Z` is exact at `N`, at `X` and at `Y`, and `f` is
surjective, then `X ≅ ker g'`. -/
private theorem isoKer_linearMap {M N X Y Z : Type*} [AddCommGroup M] [AddCommGroup N]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z] [Module ℤ M] [Module ℤ N] [Module ℤ X]
    [Module ℤ Y] [Module ℤ Z] (f : M →ₗ[ℤ] N) (g : N →ₗ[ℤ] X) (h : X →ₗ[ℤ] Y)
    (g' : Y →ₗ[ℤ] Z) (hf : Function.Exact f g) (hg : Function.Exact g h)
    (hh : Function.Exact h g') (hsurj : f.range = ⊤) : Nonempty (X ≃ₗ[ℤ] g'.ker) := by
  have hgker : g.ker = ⊤ := by rw [LinearMap.exact_iff.mp hf, hsurj]
  have hg0 : g = 0 := LinearMap.ker_eq_top.mp hgker
  have hhker : h.ker = ⊥ := by rw [LinearMap.exact_iff.mp hg, hg0, LinearMap.range_zero]
  have hrange : h.range = g'.ker := (LinearMap.exact_iff.mp hh).symm
  have hinj : Function.Injective h := LinearMap.ker_eq_bot.mp hhker
  let F := h.codRestrict g'.ker (fun x => by rw [← hrange]; exact ⟨x, rfl⟩)
  have hFinj : Function.Injective F := fun x y hxy => hinj (Subtype.ext_iff.mp hxy)
  have hFsurj : Function.Surjective F := fun y => by
    obtain ⟨x, hx⟩ := (show (y : Y) ∈ h.range from by rw [hrange]; exact y.2)
    exact ⟨x, Subtype.ext hx⟩
  exact ⟨LinearEquiv.ofBijective F ⟨hFinj, hFsurj⟩⟩

/-- **One degree of the Mayer–Vietoris computation.**  If the model map `w k = φ_k` is
surjective in degree `k ≥ 1`, then the `X`-slot `L.H (k,2) = H_k(M̂)` is the kernel of
`w (k-1) = φ_{k-1}`. -/
theorem step_iso (L : MVLES) (eM : ∀ k : ℤ, ModelM k ≅ L.H (k, 0))
    (eN : ∀ k : ℤ, ModelN k ≅ L.H (k, 1)) (w : ∀ k : ℤ, ModelM k ⟶ ModelN k)
    (hsq : ∀ k : ℤ, (eM k).hom ≫ L.d (k, 0) = w k ≫ (eN k).hom) (k : ℤ) (hk : 1 ≤ k)
    (hsurj : (w k).hom.range = ⊤) :
    Nonempty (L.H (k, 2) ≅ ModuleCat.of ℤ ↥((w (k - 1)).hom.ker)) := by
  have hsurj' : (L.d (k, 0)).hom.range = ⊤ :=
    rangeTop_of_square (eM k) (eN k) (L.d (k, 0)) (w k) (hsq k) hsurj
  obtain ⟨e1⟩ := isoKer_linearMap (L.d (k, 0)).hom (L.d (k, 1)).hom (L.d (k, 2)).hom
    (L.d (k - 1, 0)).hom (L.exact (k, 0)) (L.exact (k, 1)) (L.exact (k, 2)) hsurj'
  obtain ⟨e2⟩ := kerIso_of_square (eM (k - 1)) (eN (k - 1)) (L.d (k - 1, 0)) (w (k - 1))
    (hsq (k - 1))
  exact ⟨(e1.trans e2).toModuleIso⟩

end

end Work.HomologyMV
