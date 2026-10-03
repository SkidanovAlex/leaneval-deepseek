/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Conjugation action on `N_ab ⊗ k` and the fibre sums of `k[F]`

For a surjection `φ : FreeGroup (Fin n) →* G` with kernel `N = ker φ` this file provides

* `conjHom φ y`, `actAb φ y`, `act φ y` : the action on `N_ab ⊗ k` induced by conjugation
  with `y : FreeGroup (Fin n)` (an action of `F` which factors through `G`);
* `fibSum k φ hφ c` : the `k`-linear map `k[F] → N_ab ⊗ k` which sums, over the support in the
  coset `φ ⁻¹' {c}`, the coefficients multiplied by the class of `nw`;
* `mu k φ c` : the scalar map summing the coefficients over the coset `φ ⁻¹' {c}`;
* `delta` and `cls_nw_mul` : the cocycle identity for `nw (z * w)`, in the form needed below.
-/
import Mathlib
import Submission.Work.ORFP2.ExtSetup

set_option autoImplicit false

namespace Work.ORFP2.Ext

open MonoidAlgebra

variable (k : Type*) [CommRing k] {n : ℕ} {G : Type*} [Group G]

lemma toIntLinearMap_apply {M M₂ : Type*} [AddCommGroup M] [AddCommGroup M₂] (f : M →+ M₂)
    (x : M) : f.toIntLinearMap x = f x := rfl

lemma conj_mem_ker (φ : FreeGroup (Fin n) →* G) (y : FreeGroup (Fin n)) (x : ↥(φ.ker)) :
    y * (x : FreeGroup (Fin n)) * y⁻¹ ∈ φ.ker :=
  (inferInstance : (φ.ker).Normal).conj_mem x x.2 y

/-- Conjugation by `y` as an automorphism of `↥(φ.ker)`. -/
noncomputable def conjHom (φ : FreeGroup (Fin n) →* G) (y : FreeGroup (Fin n)) :
    ↥(φ.ker) →* ↥(φ.ker) where
  toFun x := ⟨y * (x : FreeGroup (Fin n)) * y⁻¹, conj_mem_ker φ y x⟩
  map_one' := by ext; simp
  map_mul' x x' := by ext; simp [mul_assoc]

/-- Conjugation by `y` on the abelianization of `↥(φ.ker)`, as an additive map. -/
noncomputable def actAb (φ : FreeGroup (Fin n) →* G) (y : FreeGroup (Fin n)) :
    Additive (Abelianization ↥(φ.ker)) →+ Additive (Abelianization ↥(φ.ker)) :=
  (Abelianization.map (conjHom φ y)).toAdditive

lemma actAb_ofMul (φ : FreeGroup (Fin n) →* G) (y : FreeGroup (Fin n))
    (a : Abelianization ↥(φ.ker)) :
    actAb φ y (Additive.ofMul a) = Additive.ofMul (Abelianization.map (conjHom φ y) a) := rfl

lemma conjHom_one (φ : FreeGroup (Fin n) →* G) :
    conjHom φ 1 = MonoidHom.id ↥(φ.ker) := by ext x; simp [conjHom]

lemma conjHom_mul (φ : FreeGroup (Fin n) →* G) (y y' : FreeGroup (Fin n)) :
    conjHom φ (y * y') = (conjHom φ y).comp (conjHom φ y') := by
  ext x; simp [conjHom, mul_assoc]

lemma actAb_one (φ : FreeGroup (Fin n) →* G) (a : Additive (Abelianization ↥(φ.ker))) :
    actAb φ 1 a = a := by
  obtain ⟨a', rfl⟩ := Additive.ofMul.surjective a
  rw [actAb_ofMul, conjHom_one, Abelianization.map_id]
  rfl

lemma actAb_comp (φ : FreeGroup (Fin n) →* G) (y y' : FreeGroup (Fin n))
    (a : Additive (Abelianization ↥(φ.ker))) :
    actAb φ y (actAb φ y' a) = actAb φ (y * y') a := by
  obtain ⟨a', rfl⟩ := Additive.ofMul.surjective a
  rw [actAb_ofMul, actAb_ofMul, actAb_ofMul, conjHom_mul, ← Abelianization.map_comp]
  rfl

lemma actAb_mem_ker (φ : FreeGroup (Fin n) →* G) (y : FreeGroup (Fin n)) (hy : y ∈ φ.ker)
    (a : Additive (Abelianization ↥(φ.ker))) : actAb φ y a = a := by
  obtain ⟨a', rfl⟩ := Additive.ofMul.surjective a
  induction a' using QuotientGroup.induction_on with
  | H z =>
    change actAb φ y (Additive.ofMul (Abelianization.of z)) = Additive.ofMul (Abelianization.of z)
    rw [actAb_ofMul, Abelianization.map_of]
    congr 1
    show Abelianization.of (⟨y * (z : FreeGroup (Fin n)) * y⁻¹, _⟩ : ↥(φ.ker)) = Abelianization.of z
    rw [show (⟨y * (z : FreeGroup (Fin n)) * y⁻¹, _⟩ : ↥(φ.ker)) =
      (⟨y, hy⟩ : ↥(φ.ker)) * z * (⟨y, hy⟩ : ↥(φ.ker))⁻¹ from rfl]
    simp only [map_mul, map_inv]
    rw [mul_right_comm, mul_inv_cancel, one_mul]

/-- The conjugation action of `FreeGroup (Fin n)` on `N_ab ⊗ k`, where `N = ker φ`. -/
noncomputable def act (φ : FreeGroup (Fin n) →* G) (y : FreeGroup (Fin n)) :
    KerMod k φ →ₗ[k] KerMod k φ where
  toFun u := TensorProduct.map ((actAb φ y).toIntLinearMap) (LinearMap.id : k →ₗ[ℤ] k) u
  map_add' u v := by simp only [map_add]
  map_smul' t u := by
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul a d => simp [TensorProduct.map_tmul, smul_tmul_int]
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]

lemma act_tmul (φ : FreeGroup (Fin n) →* G) (y : FreeGroup (Fin n))
    (a : Additive (Abelianization ↥(φ.ker))) (d : k) :
    act k φ y (a ⊗ₜ[ℤ] d) = (actAb φ y a) ⊗ₜ[ℤ] d := rfl

lemma act_cls (φ : FreeGroup (Fin n) →* G) (y : FreeGroup (Fin n)) (x : ↥(φ.ker)) :
    act k φ y (cls k φ x) = cls k φ ⟨y * (x : FreeGroup (Fin n)) * y⁻¹, conj_mem_ker φ y x⟩ := by
  show TensorProduct.map ((actAb φ y).toIntLinearMap) (LinearMap.id : k →ₗ[ℤ] k)
      (Additive.ofMul (Abelianization.of x) ⊗ₜ[ℤ] (1 : k)) = _
  rw [TensorProduct.map_tmul]
  rw [show (actAb φ y).toIntLinearMap (Additive.ofMul (Abelianization.of x)) =
      Additive.ofMul (Abelianization.map (conjHom φ y) (Abelianization.of x)) from rfl]
  rw [Abelianization.map_of]
  rw [show (conjHom φ y) x = ⟨y * (x : FreeGroup (Fin n)) * y⁻¹, conj_mem_ker φ y x⟩ from rfl]
  rfl

lemma act_zero (φ : FreeGroup (Fin n) →* G) (y : FreeGroup (Fin n)) :
    act k φ y (0 : KerMod k φ) = 0 := map_zero _

lemma act_add (φ : FreeGroup (Fin n) →* G) (y : FreeGroup (Fin n)) (u v : KerMod k φ) :
    act k φ y (u + v) = act k φ y u + act k φ y v := map_add _ _ _

lemma act_smul (φ : FreeGroup (Fin n) →* G) (y : FreeGroup (Fin n)) (t : k) (u : KerMod k φ) :
    act k φ y (t • u) = t • act k φ y u := map_smul _ _ _

lemma act_one (φ : FreeGroup (Fin n) →* G) (u : KerMod k φ) : act k φ 1 u = u := by
  induction u using TensorProduct.induction_on with
  | zero => rw [map_zero]
  | tmul a d => rw [act_tmul, actAb_one]
  | add x y hx hy => rw [map_add, hx, hy]

lemma act_comp (φ : FreeGroup (Fin n) →* G) (y y' : FreeGroup (Fin n)) (u : KerMod k φ) :
    act k φ y (act k φ y' u) = act k φ (y * y') u := by
  induction u using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a d => rw [act_tmul, act_tmul, act_tmul, actAb_comp]
  | add x y hx hy => simp only [map_add, hx, hy]

lemma act_mem_ker (φ : FreeGroup (Fin n) →* G) (y : FreeGroup (Fin n)) (hy : y ∈ φ.ker)
    (u : KerMod k φ) : act k φ y u = u := by
  induction u using TensorProduct.induction_on with
  | zero => rw [map_zero]
  | tmul a d => rw [act_tmul, actAb_mem_ker φ y hy]
  | add x y hx hy => rw [map_add, hx, hy]

/-- The element `sec (φ z φ w)⁻¹ * sec (φ z) * sec (φ w)` of `N = ker φ`. -/
noncomputable def delta (φ : FreeGroup (Fin n) →* G) (hφ : Function.Surjective φ)
    (z w : FreeGroup (Fin n)) : ↥(φ.ker) :=
  ⟨(sec φ hφ (φ (z * w)))⁻¹ * sec φ hφ (φ z) * sec φ hφ (φ w),
    MonoidHom.mem_ker.mpr (by simp [map_mul, map_inv, phi_sec])⟩

lemma nw_mul_decomp (φ : FreeGroup (Fin n) →* G) (hφ : Function.Surjective φ)
    (z w : FreeGroup (Fin n)) :
    (nw φ hφ (z * w) : FreeGroup (Fin n))
      = (delta φ hφ z w : FreeGroup (Fin n)) * (sec φ hφ (φ w))⁻¹
        * (nw φ hφ z : FreeGroup (Fin n)) * (sec φ hφ (φ w)) * (nw φ hφ w : FreeGroup (Fin n)) := by
  simp only [delta, nw]; group

/-- The cocycle identity for `nw`, expressed in `N_ab ⊗ k`. -/
lemma cls_nw_mul (φ : FreeGroup (Fin n) →* G) (hφ : Function.Surjective φ)
    (z w : FreeGroup (Fin n)) :
    cls k φ ⟨nw φ hφ (z * w), nw_mem φ hφ (z * w)⟩
      = cls k φ (delta φ hφ z w)
        + act k φ ((sec φ hφ (φ w))⁻¹) (cls k φ ⟨nw φ hφ z, nw_mem φ hφ z⟩)
        + cls k φ ⟨nw φ hφ w, nw_mem φ hφ w⟩ := by
  have h1 : (⟨nw φ hφ (z * w), nw_mem φ hφ (z * w)⟩ : ↥(φ.ker))
      = delta φ hφ z w
        * ⟨(sec φ hφ (φ w))⁻¹ * (nw φ hφ z : FreeGroup (Fin n)) * ((sec φ hφ (φ w))⁻¹)⁻¹,
            conj_mem_ker φ ((sec φ hφ (φ w))⁻¹) ⟨nw φ hφ z, nw_mem φ hφ z⟩⟩
        * ⟨nw φ hφ w, nw_mem φ hφ w⟩ := by
    apply Subtype.ext
    show (nw φ hφ (z * w) : FreeGroup (Fin n)) = _
    rw [nw_mul_decomp]
    push_cast
    group
  rw [h1, cls_mul, cls_mul]
  rw [← act_cls k φ ((sec φ hφ (φ w))⁻¹) ⟨nw φ hφ z, nw_mem φ hφ z⟩]

/-- The weight function `F → N_ab ⊗ k` which is the class of `nw w` when `φ w = c`. -/
noncomputable def fibWeight (φ : FreeGroup (Fin n) →* G) (hφ : Function.Surjective φ) (c : G) :
    FreeGroup (Fin n) → KerMod k φ := by
  classical
  exact fun w => if φ w = c then cls k φ ⟨nw φ hφ w, nw_mem φ hφ w⟩ else 0

lemma fibWeight_of_eq (φ : FreeGroup (Fin n) →* G) (hφ : Function.Surjective φ) {c : G}
    {w : FreeGroup (Fin n)} (h : φ w = c) :
    fibWeight k φ hφ c w = cls k φ ⟨nw φ hφ w, nw_mem φ hφ w⟩ := by
  classical
  rw [fibWeight, if_pos h]

lemma fibWeight_of_ne (φ : FreeGroup (Fin n) →* G) (hφ : Function.Surjective φ) {c : G}
    {w : FreeGroup (Fin n)} (h : φ w ≠ c) : fibWeight k φ hφ c w = 0 := by
  classical
  rw [fibWeight, if_neg h]

/-- The part of `a : k[F]` supported on the coset `φ ⁻¹' {c}`, mapped to `N_ab ⊗ k` by the
class of `nw`. -/
noncomputable def fibSum (φ : FreeGroup (Fin n) →* G) (hφ : Function.Surjective φ) (c : G) :
    MonoidAlgebra k (FreeGroup (Fin n)) →ₗ[k] KerMod k φ where
  toFun a := (Finsupp.linearCombination k (fibWeight k φ hφ c)) a.coeff
  map_add' a b := by rw [MonoidAlgebra.coeff_add, map_add]
  map_smul' t a := by rw [MonoidAlgebra.coeff_smul]; exact map_smul _ t _

lemma fibSum_apply (φ : FreeGroup (Fin n) →* G) (hφ : Function.Surjective φ) (c : G)
    (a : MonoidAlgebra k (FreeGroup (Fin n))) :
    fibSum k φ hφ c a = ∑ w ∈ a.coeff.support, a.coeff w • fibWeight k φ hφ c w := by
  rw [fibSum]
  change (Finsupp.linearCombination k _) a.coeff = _
  rw [Finsupp.linearCombination_apply, Finsupp.sum]

lemma fibSum_single (φ : FreeGroup (Fin n) →* G) (hφ : Function.Surjective φ) (c : G)
    (w : FreeGroup (Fin n)) (t : k) :
    fibSum k φ hφ c (MonoidAlgebra.single w t) = t • fibWeight k φ hφ c w := by
  rw [fibSum]
  change (Finsupp.linearCombination k _) (MonoidAlgebra.coeff (MonoidAlgebra.single w t)) = _
  rw [MonoidAlgebra.coeff_single, Finsupp.linearCombination_single]

lemma fibSum_eq_zero_of_ne (φ : FreeGroup (Fin n) →* G) (hφ : Function.Surjective φ) (c : G)
    (a : MonoidAlgebra k (FreeGroup (Fin n)))
    (ha : ∀ w ∈ a.coeff.support, φ w ≠ c) : fibSum k φ hφ c a = 0 := by
  rw [fibSum_apply]
  apply Finset.sum_eq_zero
  intro w hw
  rw [fibWeight_of_ne k φ hφ (ha w hw), smul_zero]

/-- The weight function `F → k` which is `1` when `φ w = c`. -/
noncomputable def muWeight (φ : FreeGroup (Fin n) →* G) (c : G) : FreeGroup (Fin n) → k := by
  classical
  exact fun w => if φ w = c then (1 : k) else 0

lemma muWeight_of_eq (φ : FreeGroup (Fin n) →* G) {c : G} {w : FreeGroup (Fin n)}
    (h : φ w = c) : muWeight k φ c w = 1 := by
  classical
  rw [muWeight, if_pos h]

lemma muWeight_of_ne (φ : FreeGroup (Fin n) →* G) {c : G} {w : FreeGroup (Fin n)}
    (h : φ w ≠ c) : muWeight k φ c w = 0 := by
  classical
  rw [muWeight, if_neg h]

/-- The scalar map `k[F] → k` summing the coefficients over the coset `φ ⁻¹' {c}`. -/
noncomputable def mu (φ : FreeGroup (Fin n) →* G) (c : G) :
    MonoidAlgebra k (FreeGroup (Fin n)) →ₗ[k] k where
  toFun a := (Finsupp.linearCombination k (muWeight k φ c)) a.coeff
  map_add' a b := by rw [MonoidAlgebra.coeff_add, map_add]
  map_smul' t a := by rw [MonoidAlgebra.coeff_smul]; exact map_smul _ t _

lemma mu_apply (φ : FreeGroup (Fin n) →* G) (c : G)
    (a : MonoidAlgebra k (FreeGroup (Fin n))) :
    mu k φ c a = ∑ w ∈ a.coeff.support, a.coeff w * muWeight k φ c w := by
  rw [mu]
  change (Finsupp.linearCombination k _) a.coeff = _
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  exact Finset.sum_congr rfl (fun w _ => by rw [smul_eq_mul])

lemma mu_single' (φ : FreeGroup (Fin n) →* G) (c : G)
    (w : FreeGroup (Fin n)) (t : k) :
    mu k φ c (MonoidAlgebra.single w t) = t * muWeight k φ c w := by
  rw [mu]
  change (Finsupp.linearCombination k _) (MonoidAlgebra.coeff (MonoidAlgebra.single w t)) = _
  rw [MonoidAlgebra.coeff_single, Finsupp.linearCombination_single, smul_eq_mul]

lemma mu_single (φ : FreeGroup (Fin n) →* G) {c : G}
    {w : FreeGroup (Fin n)} (h : φ w = c) (t : k) :
    mu k φ c (MonoidAlgebra.single w t) = t := by
  rw [mu_single', muWeight_of_eq k φ h, mul_one]

lemma mu_single_of_ne (φ : FreeGroup (Fin n) →* G) {c : G}
    {w : FreeGroup (Fin n)} (h : φ w ≠ c) (t : k) :
    mu k φ c (MonoidAlgebra.single w t) = 0 := by
  rw [mu_single', muWeight_of_ne k φ h, mul_zero]

/-- `mu` is invariant under right multiplication by an element of the kernel. -/
lemma mu_mul_single_mem_ker (φ : FreeGroup (Fin n) →* G) (c : G)
    (x : MonoidAlgebra k (FreeGroup (Fin n))) (r : ↥(φ.ker)) :
    mu k φ c (x * MonoidAlgebra.single (r : FreeGroup (Fin n)) 1) = mu k φ c x := by
  classical
  have key : ∀ v : FreeGroup (Fin n) →₀ k,
      mu k φ c (MonoidAlgebra.ofCoeff v * MonoidAlgebra.single (r : FreeGroup (Fin n)) 1)
        = mu k φ c (MonoidAlgebra.ofCoeff v) := by
    intro v
    induction v using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg => rw [MonoidAlgebra.ofCoeff_add, add_mul, map_add, map_add, hf, hg]
    | single t a =>
        rw [MonoidAlgebra.ofCoeff_single, MonoidAlgebra.single_mul_single, mul_one]
        by_cases h : φ t = c
        · rw [mu_single k φ h a, mu_single k φ (by rw [map_mul, MonoidHom.mem_ker.mp r.2,
            mul_one, h]) a]
        · rw [mu_single_of_ne k φ h a, mu_single_of_ne k φ
            (by rw [map_mul, MonoidHom.mem_ker.mp r.2, mul_one]; exact h) a]
  have hx := key x.coeff
  rwa [MonoidAlgebra.ofCoeff_coeff] at hx

lemma act_same_coset (φ : FreeGroup (Fin n) →* G) {y y' : FreeGroup (Fin n)}
    (h : y⁻¹ * y' ∈ φ.ker) (u : KerMod k φ) : act k φ y u = act k φ y' u := by
  have hy : y' = y * (y⁻¹ * y') := by group
  rw [hy, ← act_comp]
  rw [act_mem_ker k φ (y⁻¹ * y') h u]

/-- `mu` vanishes on the ideal `Jspan` generated by the elements `r - 1`, `r ∈ ker φ`. -/
theorem mu_eq_zero_of_mem_Jspan (φ : FreeGroup (Fin n) →* G)
    {a : MonoidAlgebra k (FreeGroup (Fin n))} (ha : a ∈ Jspan k φ) (c : G) :
    mu k φ c a = 0 := by
  classical
  let S : Submodule (MonoidAlgebra k (FreeGroup (Fin n)))
      (MonoidAlgebra k (FreeGroup (Fin n))) :=
    { carrier := {x | ∀ (j : MonoidAlgebra k (FreeGroup (Fin n))) (c : G), mu k φ c (j * x) = 0}
      zero_mem' := by intro j c; rw [mul_zero, map_zero]
      add_mem' := by intro x y hx hy j c; rw [mul_add, map_add, hx j c, hy j c, add_zero]
      smul_mem' := by
        intro a' x hx j c
        rw [show j * (a' • x) = (j * a') * x from by rw [smul_eq_mul, mul_assoc]]
        exact hx (j * a') c }
  have hle : Jspan k φ ≤ S := by
    rw [Jspan]
    exact Submodule.span_le.mpr (by
      rintro x ⟨r, rfl⟩ j c
      rw [mul_sub, mul_one, map_sub, mu_mul_single_mem_ker k φ c j r, sub_self])
  simpa using (show mu k φ c (1 * a) = 0 from hle ha 1 c)

end Work.ORFP2.Ext
