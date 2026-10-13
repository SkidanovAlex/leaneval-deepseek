import Mathlib
import Submission.Work.DSG4a.Criterion
import Submission.Work.DSG4a.Present

/-!
# DSG4a: the explicit presentation of `coker (d⁻¹ : P.X (-1) → P.X 0)`

This file reconciles the two descriptions of the finitely presented module attached to a
model `P` of `RΓ(X, 𝒪)`:

* the *abstract* one `Work.DSG4a.Criterion.modelModule P = P.X 0 ⧸ im (d⁻¹)`, used by the
  chain-level splitting criterion, and
* the *explicit* one `Work.DSG4a.present D = A^m ⧸ im (matMap D)`, where `D` is the matrix
  of the differential `d⁻¹ : P.X (-1) → P.X 0` written in bases
  `b₀ : P.X 0 ≃ A^m`, `b₁ : P.X (-1) ≃ A^n`, used by the algebraic local-to-global theorems
  (`isUnimodular_presentMk_of_forall_maximal`, `solSet_span_eq_baseChange`, ...).

The main theorem `exists_present_modelModule` produces the `A`-linear isomorphism between
the two which carries the class of a vector `b₀ x` to the class of `x`; it is the change of
basis along `b₀`.

The three auxiliary lemmas record the elementary linear algebra behind it:

* `matMap_eq_comp`: the matrix `D i j = b₀ (d⁻¹ (b₁.symm (eⱼ))) i` is the matrix of the
  composite `b₀ ∘ d⁻¹ ∘ b₁.symm`, i.e. for every `z : A^n` the vector `matMap D z` is the
  coordinate vector of `d⁻¹ (b₁.symm z)`;
* `range_matMap_eq`: consequently `im (matMap D) = b₀ '' im (d⁻¹)`;
* `map_symm_range`: and hence `b₀.symm` carries `im (matMap D)` onto `im (d⁻¹)`, which is
  what makes the quotient isomorphism well defined.
-/

namespace Work.DSG4a

open CategoryTheory

universe u

section Aux

variable {A : Type u} [CommRing A] {m n : ℕ}
variable {M N : Type u} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]

/-- **The matrix of a linear map in two bases.**  If `f : N →ₗ[A] M` and `b₀ : M ≃ A^m`,
`b₁ : N ≃ A^n` are bases, then the matrix `D i j = (b₀ (f (b₁.symm (single j 1)))) i`
computes the composite `b₀ ∘ f ∘ b₁.symm`: for every `z : A^n` the vector `matMap D z` is
the coordinate vector of `f (b₁.symm z)`. -/
lemma matMap_eq_comp (f : N →ₗ[A] M) (b₀ : M ≃ₗ[A] (Fin m → A)) (b₁ : N ≃ₗ[A] (Fin n → A)) :
    matMap (fun i j => b₀ (f (b₁.symm (Pi.single j 1))) i)
      = b₀.toLinearMap.comp (f.comp b₁.symm.toLinearMap) := by
  refine LinearMap.ext fun z => funext fun i => ?_
  have h1 : b₁.symm z = ∑ j, z j • b₁.symm (Pi.single j (1 : A)) := by
    conv_lhs => rw [← sum_single_smul z]
    simp only [map_sum, map_smul]
  show (matMap _ z) i = b₀ (f (b₁.symm z)) i
  rw [h1, matMap_apply]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- The image of the matrix `D` of `f` in the bases `b₀`, `b₁` is the image of `f` read in
the basis `b₀`. -/
lemma range_matMap_eq (f : N →ₗ[A] M) (b₀ : M ≃ₗ[A] (Fin m → A)) (b₁ : N ≃ₗ[A] (Fin n → A)) :
    LinearMap.range (matMap (fun i j => b₀ (f (b₁.symm (Pi.single j 1))) i))
      = Submodule.map b₀.toLinearMap (LinearMap.range f) := by
  rw [matMap_eq_comp f b₀ b₁, LinearMap.range_comp, LinearMap.range_comp,
    LinearMap.range_eq_top.mpr b₁.symm.surjective, Submodule.map_top]

/-- The inverse change of basis `b₀.symm` carries the image of the matrix `D` of `f` onto
the image of `f`; equivalently, the two submodules that one quotients out to build
`present D` and `modelModule P` correspond under `b₀.symm`. -/
lemma map_symm_range (f : N →ₗ[A] M) (b₀ : M ≃ₗ[A] (Fin m → A)) (b₁ : N ≃ₗ[A] (Fin n → A)) :
    Submodule.map b₀.symm.toLinearMap
      (LinearMap.range (matMap (fun i j => b₀ (f (b₁.symm (Pi.single j 1))) i)))
      = LinearMap.range f := by
  rw [range_matMap_eq f b₀ b₁, ← Submodule.map_comp,
    show (b₀.symm.toLinearMap.comp b₀.toLinearMap : M →ₗ[A] M) = LinearMap.id from by
      ext y; simp,
    Submodule.map_id]

end Aux

/-- **The explicit presentation of `modelModule P`.**  Given a cochain complex `P` of
`A`-modules together with bases `b₀` of `P.X 0` and `b₁` of `P.X (-1)`, the quotient
`A^m ⧸ im D` by the matrix `D` of the differential `d⁻¹ : P.X (-1) → P.X 0` is `A`-linearly
isomorphic to `modelModule P = P.X 0 ⧸ im d⁻¹`, via the change of basis `b₀`, and the
isomorphism sends the class of `b₀ x` to the class of `x`. -/
theorem exists_present_modelModule {A : Type u} [CommRing A] {m n : ℕ}
    (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (b₀ : P.X 0 ≃ₗ[A] (Fin m → A)) (b₁ : P.X (-1) ≃ₗ[A] (Fin n → A)) :
    ∃ Φ : Work.DSG4a.present
        (fun i j => b₀ ((P.d (-1) 0).hom (b₁.symm (Pi.single j 1))) i) ≃ₗ[A]
        Work.DSG4a.Criterion.modelModule P,
      ∀ x : P.X 0,
        Φ (Work.DSG4a.presentMk
          (fun i j => b₀ ((P.d (-1) 0).hom (b₁.symm (Pi.single j 1))) i)
          (fun i => b₀ x i)) = Submodule.mkQ _ x := by
  let D : Fin m → Fin n → A := fun i j => b₀ ((P.d (-1) 0).hom (b₁.symm (Pi.single j 1))) i
  change ∃ Φ : Work.DSG4a.present D ≃ₗ[A] Work.DSG4a.Criterion.modelModule P,
      ∀ x : P.X 0, Φ (Work.DSG4a.presentMk D (fun i => b₀ x i)) = Submodule.mkQ _ x
  refine ⟨Submodule.Quotient.equiv (LinearMap.range (matMap D))
    (LinearMap.range (P.d (-1) 0).hom) b₀.symm
    (map_symm_range (P.d (-1) 0).hom b₀ b₁), ?_⟩
  intro x
  simp only [Submodule.Quotient.equiv_apply, Submodule.mapQ_apply, Submodule.mkQ_apply]
  exact congrArg (Submodule.Quotient.mk (p := LinearMap.range (P.d (-1) 0).hom))
    (LinearEquiv.symm_apply_apply b₀ x)

end Work.DSG4a
