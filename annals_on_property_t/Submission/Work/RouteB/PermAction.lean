import Submission.Work.RouteB.StarStructure
import Submission.FreeGroupAut
import Submission.Commons.Algebra.MonoidAlgebra.conj_laplacian
import Submission.Commons.GroupTheory.FreeGroup.permAut_conj_mem_SAutGen
import Mathlib

open OnPropertyT Submission.FreeGroupAut
open FreeGroup
open scoped BigOperators

set_option autoImplicit false

/-!
# The action of the symmetric group on `F_n` and on `Aut(F_n)`

The symmetrisation step of the paper (Method I/II) uses the action of the
alternating group `A_n` on the basis `{a_1, …, a_n}` of `F_n` and on the
Nielsen generating set.  This file provides the framework:

* `permHom σ` — the monoid homomorphism `F_n → F_n` sending `a_i ↦ a_{σ i}`;
* `permAut σ` — the induced automorphism of `F_n`;
* `permAut` is multiplicative (`permAut_mul`, `permAut_one`, `permAut_inv`), so
  `σ ↦ permAut σ` is a homomorphism `Equiv.Perm (Fin n) →* Aut(F_n)`;
* the induced conjugation action on `Aut(F_n)`
  (`conjPermAut σ α := permAut σ * α * (permAut σ)⁻¹`), needed to symmetrise
  elements of the group ring `ℝ Aut(F_n)` (see
  `Commons.Algebra.MonoidAlgebra.conj_laplacian`).

The equivariance of the concrete generating set
(`permAut σ * rho i j * (permAut σ)⁻¹ = rho (σ i) (σ j)` etc.) is the finite
computation on top of this framework which the symmetrisation of `Sq_n`, `Adj_n`,
`Op_n` needs.
-/

namespace Submission.RouteB

/-- The monoid homomorphism `F_n → F_n` induced by a permutation of the
generators: `a_i ↦ a_{σ i}`. -/
def permHom {n : ℕ} (σ : Equiv.Perm (Fin n)) : FreeGroup (Fin n) →* FreeGroup (Fin n) :=
  FreeGroup.lift (fun i => FreeGroup.of (σ i))

lemma permHom_of {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    permHom σ (FreeGroup.of i) = FreeGroup.of (σ i) := by
  simp [permHom]

lemma permHom_one {n : ℕ} : permHom (1 : Equiv.Perm (Fin n)) = MonoidHom.id (FreeGroup (Fin n)) := by
  apply FreeGroup.ext_hom
  intro i
  simp [permHom]

lemma permHom_comp {n : ℕ} (σ τ : Equiv.Perm (Fin n)) :
    permHom (σ * τ) = (permHom σ).comp (permHom τ) := by
  apply FreeGroup.ext_hom
  intro i
  simp [permHom]

/-- The automorphism of `F_n` induced by a permutation of the generators. -/
def permAut {n : ℕ} (σ : Equiv.Perm (Fin n)) : MulAut (FreeGroup (Fin n)) where
  toFun := permHom σ
  invFun := permHom σ.symm
  left_inv x := by
    have hs : σ.symm * σ = 1 := by ext x; simp
    have h : (permHom σ.symm).comp (permHom σ) = MonoidHom.id (FreeGroup (Fin n)) := by
      rw [← permHom_comp, hs, permHom_one]
    exact congrFun (congrArg DFunLike.coe h) x
  right_inv x := by
    have hs : σ * σ.symm = 1 := by ext x; simp
    have h : (permHom σ).comp (permHom σ.symm) = MonoidHom.id (FreeGroup (Fin n)) := by
      rw [← permHom_comp, hs, permHom_one]
    exact congrFun (congrArg DFunLike.coe h) x
  map_mul' := (permHom σ).map_mul

lemma permAut_apply {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    permAut σ (FreeGroup.of i) = FreeGroup.of (σ i) :=
  permHom_of σ i

lemma permAut_one {n : ℕ} : permAut (1 : Equiv.Perm (Fin n)) = 1 := by
  ext x
  exact congrFun (congrArg DFunLike.coe (permHom_one (n := n))) x

lemma permAut_mul {n : ℕ} (σ τ : Equiv.Perm (Fin n)) :
    permAut (σ * τ) = permAut σ * permAut τ := by
  ext x
  show permHom (σ * τ) x = permHom σ (permHom τ x)
  rw [permHom_comp]
  rfl

lemma permAut_inv {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (permAut σ)⁻¹ = permAut σ.symm := by
  have hs : σ * σ.symm = 1 := by ext x; simp
  have h : permAut σ * permAut σ.symm = 1 := by
    rw [← permAut_mul, hs, permAut_one]
  exact inv_eq_of_mul_eq_one_right h

/-- The conjugation action of a permutation of the basis on `Aut(F_n)`. -/
def conjPermAut {n : ℕ} (σ : Equiv.Perm (Fin n)) (α : MulAut (FreeGroup (Fin n))) :
    MulAut (FreeGroup (Fin n)) :=
  permAut σ * α * (permAut σ)⁻¹

lemma conjPermAut_one {n : ℕ} (α : MulAut (FreeGroup (Fin n))) : conjPermAut 1 α = α := by
  simp [conjPermAut, permAut_one]

/-- The permutation action is a group action: `conjPermAut (σ * τ) = conjPermAut σ ∘
conjPermAut τ`. -/
lemma conjPermAut_mul {n : ℕ} (σ τ : Equiv.Perm (Fin n)) (α : MulAut (FreeGroup (Fin n))) :
    conjPermAut (σ * τ) α = conjPermAut σ (conjPermAut τ α) := by
  simp only [conjPermAut, permAut_mul, permAut_inv, mul_inv_rev]
  group

/-- The permutation action on the group ring `ℝ Aut(F_n)`, by `mapDomain` along
the conjugation action. -/
noncomputable def permRingHom {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    MonoidAlgebra ℝ (MulAut (FreeGroup (Fin n))) →+*
      MonoidAlgebra ℝ (MulAut (FreeGroup (Fin n))) :=
  MonoidAlgebra.mapDomainRingHom ℝ (MulAut.conj (permAut σ))

/-- `permRingHom σ` is the conjugation by `of (permAut σ)` on the group ring
(restricted to the group ring of the automorphism group). -/
lemma permRingHom_eq_conj {n : ℕ} (σ : Equiv.Perm (Fin n))
    (x : MonoidAlgebra ℝ (MulAut (FreeGroup (Fin n)))) :
    permRingHom σ x
      = MonoidAlgebra.of ℝ (MulAut (FreeGroup (Fin n))) (permAut σ) * x
        * MonoidAlgebra.of ℝ (MulAut (FreeGroup (Fin n))) (permAut σ)⁻¹ :=
  (Commons.Algebra.MonoidAlgebra.of_conj_mul_of x (permAut σ)).symm

/-- **The transvection Laplacian is invariant under the permutation action**,
provided the permutation normalises the transvection generating set (which holds
for all `σ` — see the commons
`Commons.GroupTheory.FreeGroup.permAut_conj_mem_SAutGen`). -/
theorem permRingHom_laplacian (n : ℕ) (σ : Equiv.Perm (Fin n))
    (hconj : ∀ g ∈ SAutGen n, permAut σ * g * (permAut σ)⁻¹ ∈ SAutGen n) :
    permRingHom σ (OnPropertyT.Laplacian (SAutGen n))
      = OnPropertyT.Laplacian (SAutGen n) := by
  classical
  change permRingHom σ (Commons.Algebra.MonoidAlgebra.Laplacian (SAutGen n))
      = Commons.Algebra.MonoidAlgebra.Laplacian (SAutGen n)
  rw [permRingHom_eq_conj, Commons.Algebra.MonoidAlgebra.conj_laplacian]
  congr 1
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · rw [Finset.image_subset_iff]
    intro g hg
    exact hconj g hg
  · have hcard : (Finset.image
        (fun s : MulAut (FreeGroup (Fin n)) => (permAut σ * s) * (permAut σ)⁻¹)
        (SAutGen n)).card = (SAutGen n).card :=
      Finset.card_image_of_injOn (fun a _ b _ hab => by
        rw [mul_assoc, mul_assoc] at hab
        exact mul_right_cancel (mul_left_cancel hab))
    rw [hcard]

/-- **The transvection Laplacian is invariant under the permutation action**
(unconditional form; the normalisation of the generating set is the commons
lemma `Commons.GroupTheory.FreeGroup.permAut_conj_mem_SAutGen`). -/
theorem permRingHom_laplacian' (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    permRingHom σ (OnPropertyT.Laplacian (SAutGen n))
      = OnPropertyT.Laplacian (SAutGen n) :=
  permRingHom_laplacian n σ fun g hg =>
    Commons.GroupTheory.FreeGroup.permAut_conj_mem_SAutGen n σ hg

end Submission.RouteB