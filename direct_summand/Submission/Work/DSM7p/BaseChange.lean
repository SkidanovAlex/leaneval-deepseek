import Mathlib

/-!
# DSM7p — base change of the splitting-functionals module

General (context-free) linear-algebra lemmas underlying the base-change computation for
`Work.DSM7p.valIdeal`:

* `rTensor_ker_eq_range_subtype` — for a flat `A`-algebra `B`, tensoring a kernel with `B` is
  the kernel of the tensor;
* `quotSMulEquiv` — `(A ⧸ I) ⊗[A] B ≃ₗ[A] B ⧸ (I · B)`;
* `homBaseChange` — `(W →ₗ[A] A ⧸ I) ⊗[A] B ≃ₗ[A] W →ₗ[A] B ⧸ (I · B)` for `W` finite projective,
  together with its computation rule and its compatibility with precomposition.
-/

open CategoryTheory
open scoped TensorProduct

namespace Work.DSM7p

universe a

section BaseChange

variable {A B : Type a} [CommRing A] [CommRing B] [Algebra A B]

/-- **Base change of a kernel along a flat algebra.**  If `B` is a flat `A`-algebra then tensoring
the short exact sequence `0 → ker f → M → N` with `B` stays exact, so the kernel of `f ⊗ id`
is the image of `ker f ⊗ B`. -/
lemma rTensor_ker_eq_range_subtype [Module.Flat A B]
    {M N : Type a} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (f : M →ₗ[A] N) :
    LinearMap.ker (f.rTensor B) =
      LinearMap.range ((LinearMap.ker f).subtype.rTensor B) := by
  have h : Function.Exact (LinearMap.ker f).subtype f := by
    rw [LinearMap.exact_iff]
    exact (Submodule.range_subtype _).symm
  have h2 := Module.Flat.rTensor_exact (M := B) h
  rw [LinearMap.exact_iff] at h2
  exact h2

/-- **`(A ⧸ I) ⊗[A] B ≃ₗ[A] B ⧸ (I · B)`**, the base change of the quotient `A ⧸ I`. -/
noncomputable def quotSMulEquiv (I : Ideal A) :
    (A ⧸ I) ⊗[A] B ≃ₗ[A] B ⧸ (I.map (algebraMap A B)) :=
  (TensorProduct.comm A (A ⧸ I) B).trans
    ((Ideal.qoutMapEquivTensorQout (R := A) (S := B) (I := I)).symm.restrictScalars A)

lemma quotSMulEquiv_mk_tmul (I : Ideal A) (r : A) (b : B) :
    quotSMulEquiv (A := A) (B := B) I (Ideal.Quotient.mk I r ⊗ₜ[A] b)
      = Ideal.Quotient.mk (I.map (algebraMap A B)) (r • b) := by
  simp only [quotSMulEquiv, LinearEquiv.trans_apply, TensorProduct.comm_tmul,
    LinearEquiv.restrictScalars_apply]
  unfold Ideal.qoutMapEquivTensorQout
  simp only [LinearEquiv.trans_apply, LinearEquiv.symm_trans_apply, LinearEquiv.symm_symm,
    Submodule.quotEquivOfEq_mk, Submodule.restrictScalarsEquiv_apply,
    TensorProduct.quotTensorEquivQuotSMul_symm_mk]
  exact (Submodule.Quotient.mk_smul _ r b).symm

/-- **`(W →ₗ[A] A ⧸ I) ⊗[A] B ≃ₗ[A] W →ₗ[A] B ⧸ (I · B)`** for `W` finite projective. -/
noncomputable def homBaseChange (I : Ideal A) (W : Type a) [AddCommGroup W] [Module A W]
    [Module.Finite A W] [Module.Projective A W] :
    (W →ₗ[A] A ⧸ I) ⊗[A] B ≃ₗ[A] (W →ₗ[A] B ⧸ (I.map (algebraMap A B))) :=
  (rTensorHomEquivHomRTensor A W (A ⧸ I) B).trans
    ((LinearEquiv.refl A W).arrowCongr (quotSMulEquiv (A := A) (B := B) I))

lemma homBaseChange_tmul_apply (I : Ideal A) {W : Type a} [AddCommGroup W] [Module A W]
    [Module.Finite A W] [Module.Projective A W]
    (t : W →ₗ[A] A ⧸ I) (b : B) (w : W) :
    homBaseChange (A := A) (B := B) I W (t ⊗ₜ[A] b) w
      = quotSMulEquiv (A := A) (B := B) I (t w ⊗ₜ[A] b) := by
  simp [homBaseChange, LinearEquiv.arrowCongr_apply]

/-- **Naturality of the evaluation functional** under `homBaseChange`: evaluating a base-changed
functional at `e` is the base change of evaluating at `e`. -/
lemma eval_homBaseChange (I : Ideal A) {W : Type a} [AddCommGroup W] [Module A W]
    [Module.Finite A W] [Module.Projective A W] (e : W) :
    (LinearMap.applyₗ (M := W) (M₂ := B ⧸ (I.map (algebraMap A B))) e) ∘ₗ
        (homBaseChange (A := A) (B := B) I W).toLinearMap =
      (quotSMulEquiv (A := A) (B := B) I).toLinearMap ∘ₗ
        ((LinearMap.applyₗ (M := W) (M₂ := A ⧸ I) e).rTensor B) := by
  apply TensorProduct.ext'
  intro t b
  simp [homBaseChange_tmul_apply]

/-- **Compatibility of `homBaseChange` with precomposition** by a linear map `d : W' →ₗ[A] W`. -/
lemma homBaseChange_lcomp (I : Ideal A) {W W' : Type a} [AddCommGroup W] [Module A W]
    [Module.Finite A W] [Module.Projective A W] [AddCommGroup W'] [Module A W']
    [Module.Finite A W'] [Module.Projective A W']
    (d : W' →ₗ[A] W) :
    (LinearMap.lcomp A (B ⧸ (I.map (algebraMap A B))) d) ∘ₗ
        (homBaseChange (A := A) (B := B) I W).toLinearMap =
      (homBaseChange (A := A) (B := B) I W').toLinearMap ∘ₗ
        (LinearMap.lcomp A (A ⧸ I) d).rTensor B := by
  apply TensorProduct.ext'
  intro t b
  ext w'
  change (homBaseChange (A := A) (B := B) I W (t ⊗ₜ[A] b)) (d w')
      = (homBaseChange (A := A) (B := B) I W'
          ((LinearMap.lcomp A (A ⧸ I) d) t ⊗ₜ[A] b)) w'
  rw [homBaseChange_tmul_apply, homBaseChange_tmul_apply, LinearMap.lcomp_apply]

/-- **General linear algebra.**  If `h ∘ e = e' ∘ g` where `e`, `e'` are linear equivalences, then
`e` carries the kernel of `g` onto the kernel of `h`. -/
lemma map_ker_of_comp_eq {R : Type*} [Semiring R] {M N M' N' : Type*}
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    [AddCommMonoid M'] [Module R M'] [AddCommMonoid N'] [Module R N']
    (e : M ≃ₗ[R] N) (e' : M' ≃ₗ[R] N') (g : M →ₗ[R] M') (h : N →ₗ[R] N')
    (hcomm : h ∘ₗ e.toLinearMap = e'.toLinearMap ∘ₗ g) :
    Submodule.map e.toLinearMap (LinearMap.ker g) = LinearMap.ker h := by
  have key : ∀ x : M, h (e x) = e' (g x) := fun x => by
    simpa using LinearMap.congr_fun hcomm x
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : g x = 0 := hx
    show h (e x) = 0
    rw [key x, hx', map_zero]
  · intro hy
    have hy' : h y = 0 := hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    show g (e.symm y) = 0
    have h1 : e' (g (e.symm y)) = 0 := by
      rw [← key (e.symm y), LinearEquiv.apply_symm_apply, hy']
    exact e'.injective (by rw [h1, map_zero])

/-- **Base change of the module of splitting functionals** (see `homBaseChange`). -/
lemma homBaseChange_map_ker [Module.Flat A B] {W W' : Type a} [AddCommGroup W] [Module A W]
    [Module.Finite A W] [Module.Projective A W] [AddCommGroup W'] [Module A W']
    [Module.Finite A W'] [Module.Projective A W'] (I : Ideal A) (d : W' →ₗ[A] W) :
    Submodule.map (homBaseChange (A := A) (B := B) I W).toLinearMap
        (Submodule.map
          ((LinearMap.ker (LinearMap.lcomp A (A ⧸ I) d)).subtype.rTensor B) ⊤)
      = LinearMap.ker (LinearMap.lcomp A (B ⧸ (I.map (algebraMap A B))) d) := by
  rw [Submodule.map_top, ← rTensor_ker_eq_range_subtype (A := A) (B := B)
    (f := LinearMap.lcomp A (A ⧸ I) d)]
  exact map_ker_of_comp_eq (homBaseChange (A := A) (B := B) I W)
    (homBaseChange (A := A) (B := B) I W')
    ((LinearMap.lcomp A (A ⧸ I) d).rTensor B)
    (LinearMap.lcomp A (B ⧸ (I.map (algebraMap A B))) d)
    (homBaseChange_lcomp (A := A) (B := B) I d)

end BaseChange

end Work.DSM7p
