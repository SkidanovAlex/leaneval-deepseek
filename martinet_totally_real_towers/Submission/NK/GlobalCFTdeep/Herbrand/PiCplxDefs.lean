/-
# The pointwise product complex, and product-compatibility of linear algebra

This file contains the definitions used in the proof that the Tate cohomology of a
pointwise product representation `piRep M` is the product of the Tate cohomologies of
the factors `M i`.

The main definition is `piCplx C`: the cochain complex whose degree `n` part is the
*Pi type* `∀ i, ↥((C i).X n)` and whose differential is the componentwise product
`LinearMap.piMap` of the differentials of the `C i`.  This is (up to the canonical
isomorphism `ModuleCat.piIsoPi`) the categorical product of the complexes `C i`.

We also provide the two "currying" linear equivalences that identify the terms of the
inhomogeneous (co)chain complexes of `piRep M` with products of those of the `M i`,
and the general linear-algebra lemma that a quotient of a product is the product of
the quotients.

**Note for users of this file.**  Everything here is stated over a *variable* commutative
ring `R`, never over `ℤ` directly.  This is deliberate: for `R = ℤ` the type class search
for the `ℤ`-module structure on a Pi type is ambiguous (`Pi.module` versus the generic
`AddCommGroup.toIntModule`), and the two structures are not syntactically equal, which
makes `rfl`/`simp` fail in confusing ways.  With `R` a variable there is no such
ambiguity.  Lemmas proved here therefore instantiate cleanly at `R = ℤ`.

When working with this file it is recommended to put

```
set_option backward.isDefEq.respectTransparency false
```

at the top of the file: some of the proofs below rely on it (it makes the coercion
`↥(piCplxX R C n)` and the Pi type `∀ i, ↥((C i).X n)` interchangeable for rewriting).
-/
import Mathlib
import Submission.NK.RepresentationTheory.GroupCohomology.piCohomology_injective

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace NK.GlobalCFTdeep.Herbrand

open CategoryTheory CategoryTheory.Limits

noncomputable section

variable {ι : Type}

/-! ## The pointwise product complex -/

/-- The degree `n` part of the pointwise product complex: the product of the `X n`'s. -/
def piCplxX (R : Type) [Ring R] (C : ι → CochainComplex (ModuleCat R) ℤ) (n : ℤ) :
    ModuleCat R :=
  ModuleCat.of R ((i : ι) → ↥((C i).X n))

/-- The differential of the pointwise product complex, componentwise. -/
def piCplxD (R : Type) [Ring R] (C : ι → CochainComplex (ModuleCat R) ℤ) (n m : ℤ) :
    piCplxX R C n ⟶ piCplxX R C m :=
  ModuleCat.ofHom (LinearMap.piMap fun i => ModuleCat.Hom.hom ((C i).d n m))

@[simp]
lemma piCplxD_apply (R : Type) [Ring R] (C : ι → CochainComplex (ModuleCat R) ℤ) (n m : ℤ)
    (x : ↥(piCplxX R C n)) (i : ι) :
    (piCplxD R C n m) x i = ((C i).d n m) (x i) := rfl

/-- The "pointwise product" of a family of cochain complexes of `R`-modules: its degree
`n` part is the product `∀ i, ↥((C i).X n)` and its differential is componentwise. -/
def piCplx (R : Type) [Ring R] (C : ι → CochainComplex (ModuleCat R) ℤ) :
    CochainComplex (ModuleCat R) ℤ where
  X n := piCplxX R C n
  d n m := piCplxD R C n m
  shape n m h := by
    apply ModuleCat.hom_ext
    ext x
    funext i
    show (piCplxD R C n m) x i = 0
    rw [piCplxD_apply]
    have h' : ((C i).d n m) = 0 := HomologicalComplex.shape (C i) n m h
    rw [h']
    simp
  d_comp_d' n m p hnm hmp := by
    apply ModuleCat.hom_ext
    ext x
    funext i
    show (piCplxD R C m p) ((piCplxD R C n m) x) i = 0
    rw [piCplxD_apply, piCplxD_apply]
    have h'' : ((C i).d m p) (((C i).d n m) (x i)) = 0 := by
      have h' : ((C i).d n m) ≫ ((C i).d m p) = 0 := HomologicalComplex.d_comp_d (C i) n m p
      have h2 := congrArg ModuleCat.Hom.hom h'
      simp only [ModuleCat.hom_comp, ModuleCat.hom_zero, LinearMap.comp_apply,
        LinearMap.zero_apply] at h2
      exact congrArg (fun g => g (x i)) h2
    exact h''

@[simp]
lemma piCplx_X (R : Type) [Ring R] (C : ι → CochainComplex (ModuleCat R) ℤ) (n : ℤ) :
    (piCplx R C).X n = piCplxX R C n := rfl

@[simp]
lemma piCplx_d (R : Type) [Ring R] (C : ι → CochainComplex (ModuleCat R) ℤ) (n m : ℤ) :
    (piCplx R C).d n m = piCplxD R C n m := rfl

/-- Evaluation of the differential of `piCplx` at a family of components. -/
@[simp]
lemma piCplx_d_apply (R : Type) [Ring R] (C : ι → CochainComplex (ModuleCat R) ℤ) (n m : ℤ)
    (x : ↥((piCplx R C).X n)) (i : ι) :
    ((piCplx R C).d n m) x i = ((C i).d n m) (x i) := rfl

/-- The degreewise projection `piCplxX R C n ⟶ (C i).X n`. -/
def piCplxProj (R : Type) [Ring R] (C : ι → CochainComplex (ModuleCat R) ℤ) (i : ι) (n : ℤ) :
    piCplxX R C n ⟶ (C i).X n :=
  ModuleCat.ofHom
    { toFun := fun x => x i
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

@[simp]
lemma piCplxProj_apply (R : Type) [Ring R] (C : ι → CochainComplex (ModuleCat R) ℤ) (i : ι) (n : ℤ)
    (x : ↥(piCplxX R C n)) :
    (piCplxProj R C i n) x = x i := rfl

/-- The projection `piCplx R C ⟶ C i`, as a morphism of complexes. -/
def piCplxπ (R : Type) [Ring R] (C : ι → CochainComplex (ModuleCat R) ℤ) (i : ι) :
    piCplx R C ⟶ C i where
  f n := piCplxProj R C i n
  comm' n m hnm := by
    apply ModuleCat.hom_ext
    ext x
    show (piCplxProj R C i n ≫ (C i).d n m) x = (piCplxD R C n m ≫ piCplxProj R C i m) x
    rw [ModuleCat.comp_apply, ModuleCat.comp_apply, piCplxProj_apply, piCplxProj_apply,
      piCplxD_apply]

@[simp]
lemma piCplxπ_f_apply (R : Type) [Ring R] (C : ι → CochainComplex (ModuleCat R) ℤ) (i : ι) (n : ℤ)
    (x : ↥((piCplx R C).X n)) :
    ((piCplxπ R C i).f n) x = x i := rfl

/-! ## Swapping two Pi-types -/

/-- The linear equivalence swapping the two Pi-types: `(α → ∀ i, M i) ≃ₗ (∀ i, α → M i)`. -/
def piSwap (R : Type*) [Semiring R] (α : Type*) {M : ι → Type*}
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] :
    (α → (i : ι) → M i) ≃ₗ[R] ((i : ι) → α → M i) where
  toFun f := fun i a => f a i
  invFun g := fun a i => g i a
  map_add' f g := by ext i a; rfl
  map_smul' c f := by ext i a; rfl
  left_inv f := rfl
  right_inv g := rfl

@[simp]
lemma piSwap_apply (R : Type*) [Semiring R] (α : Type*) {M : ι → Type*}
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
    (f : α → (i : ι) → M i) (i : ι) (a : α) :
    (piSwap R α (M := M) f) i a = f a i := rfl

/-! ## `Finsupp` into a product is a product of `Finsupp`s -/

/-- For a *finite* index type `α`, a finitely supported function into a product is the same
as a family of finitely supported functions: `(α →₀ ∀ i, M i) ≃ₗ (∀ i, α →₀ M i)`. -/
def finsuppPiEquiv (R : Type*) [Semiring R] (α : Type*) [Finite α] {M : ι → Type*}
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] :
    (α →₀ (i : ι) → M i) ≃ₗ[R] ((i : ι) → α →₀ M i) :=
  (Finsupp.linearEquivFunOnFinite R ((i : ι) → M i) α) ≪≫ₗ
    piSwap R α ≪≫ₗ
      LinearEquiv.piCongrRight (fun i => (Finsupp.linearEquivFunOnFinite R (M i) α).symm)

@[simp]
lemma finsuppPiEquiv_apply (R : Type*) [Semiring R] (α : Type*) [Finite α] {M : ι → Type*}
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
    (f : α →₀ (i : ι) → M i) (i : ι) (a : α) :
    (finsuppPiEquiv R α (M := M) f) i a = f a i := by
  simp only [finsuppPiEquiv, LinearEquiv.trans_apply, LinearEquiv.piCongrRight_apply,
    Finsupp.linearEquivFunOnFinite_symm_apply, Finsupp.linearEquivFunOnFinite_apply]
  rfl

/-! ## Quotients of products -/

/-- A quotient of a product by a product of submodules is the product of the quotients. -/
def piQuotEquiv (R : Type*) [Ring R] {M : ι → Type*} [∀ i, AddCommGroup (M i)]
    [∀ i, Module R (M i)] (N : (i : ι) → Submodule R (M i)) :
    (((i : ι) → M i) ⧸ Submodule.pi Set.univ N) ≃ₗ[R] ((i : ι) → M i ⧸ N i) :=
  LinearEquiv.ofBijective
    (Submodule.liftQ _ (LinearMap.piMap fun i => (N i).mkQ)
      (fun x hx => by
        rw [LinearMap.mem_ker]
        funext i
        simp only [LinearMap.coe_piMap, Pi.map_apply, Submodule.mkQ_apply, Pi.zero_apply,
          Submodule.Quotient.mk_eq_zero]
        exact (Submodule.mem_pi (I := Set.univ) (p := N)).mp hx i (Set.mem_univ i)))
    ⟨fun x y hxy => by
      obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective (Submodule.pi Set.univ N) x
      obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective (Submodule.pi Set.univ N) y
      have hxy' : (LinearMap.piMap fun i => (N i).mkQ) u =
          (LinearMap.piMap fun i => (N i).mkQ) v := by
        simpa only [Submodule.liftQ_apply] using hxy
      rw [Submodule.Quotient.eq]
      rw [Submodule.mem_pi]
      intro i _
      have h2 : (N i).mkQ (u i) = (N i).mkQ (v i) := congrFun hxy' i
      have h3 : (N i).mkQ (u i - v i) = 0 := by
        rw [map_sub, h2, sub_self]
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h3
      exact h3,
    by
      intro y
      choose x hx using fun i => (N i).mkQ_surjective (y i)
      refine ⟨Submodule.Quotient.mk fun i => x i, ?_⟩
      rw [Submodule.liftQ_apply]
      funext i
      rw [LinearMap.coe_piMap, Pi.map_apply, hx i]⟩

@[simp]
lemma piQuotEquiv_apply (R : Type*) [Ring R] {M : ι → Type*} [∀ i, AddCommGroup (M i)]
    [∀ i, Module R (M i)] (N : (i : ι) → Submodule R (M i)) (x : (i : ι) → M i) :
    piQuotEquiv R N (Submodule.Quotient.mk x) = fun i => Submodule.Quotient.mk (x i) := by
  funext i
  simp only [piQuotEquiv, LinearEquiv.ofBijective_apply, Submodule.liftQ_apply,
    LinearMap.coe_piMap, Pi.map_apply, Submodule.mkQ_apply]

end

end NK.GlobalCFTdeep.Herbrand
