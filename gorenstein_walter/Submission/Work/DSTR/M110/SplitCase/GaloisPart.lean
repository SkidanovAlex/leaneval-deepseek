/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Galois projection `PΓL(2,F) →* (F ≃+* F)`

For a field `F`, `PΓL(2,F) = pglImage F ⊔ galSub F` is the semidirect product of `PGL(2,F)`
(the normal subgroup `pglImage F`) with the Galois group `galSub F ≅ Aut F`.  We record the
resulting *Galois part* of an element of `PΓL(2,F)` as a ring automorphism of `F`:

* `galEquiv F`    : `(F ≃+* F) ≃* ↥(galSub F)`;
* `galSubPart F x`: the `galSub F`-component of `x ∈ PΓL(2,F)`;
* `galPart F`     : `PΓL(2,F) →* (F ≃+* F)`, the projection with kernel `pglImage F`.

The projection is used in the split case of DS10a: an odd `r`-subgroup `N ≤ Q`, normal in
`C_Q(t)`, cannot contain an element with a non-trivial Galois part, since conjugating it by the
(twisted) torus would produce more conjugates than the `r`-part of `|T|` allows.
-/
import Mathlib
import Submission.Work.DSTR.M110.SplitCase.Basic

open scoped MatrixGroups LinearAlgebra.Projectivization
open OnePoint

namespace Work.DSTR.M110.SplitAux

open Work.AUTL2

variable (F : Type*) [Field F] [DecidableEq F]

/-! ## `galHom` and `negPerm` -/

/-- Field automorphisms commute with the standard split involution `x ↦ -x`. -/
lemma galHom_mul_negPerm (σ : F ≃+* F) :
    galHom F σ * negPerm F = negPerm F * galHom F σ := by
  rw [Equiv.ext_iff, OnePoint.forall]
  refine ⟨?_, fun x => ?_⟩
  · simp only [Equiv.Perm.mul_apply, negPerm_infty, Normalizer.galHom_apply_infty]
  · simp only [Equiv.Perm.mul_apply, negPerm_some, Normalizer.galHom_apply_coe, map_neg]

/-! ## The isomorphism `Aut F ≃* ↥(galSub F)` -/

/-- `Aut F ≃* ↥(galSub F)`, via `galHom F`. -/
noncomputable def galEquiv : (F ≃+* F) ≃* ↥(galSub F) :=
  MulEquiv.ofBijective ((galHom F).rangeRestrict)
    ⟨fun a b h => Galois.galHom_injective F (congrArg Subtype.val h),
     MonoidHom.rangeRestrict_surjective _⟩

@[simp] lemma galEquiv_apply (σ : F ≃+* F) :
    ((galEquiv F σ : ↥(galSub F)) : Equiv.Perm (P1 F)) = galHom F σ := rfl

lemma galEquiv_symm_coe (τ : ↥(galSub F)) :
    galHom F ((galEquiv F).symm τ) = (τ : Equiv.Perm (P1 F)) := by
  have h := galEquiv_apply F ((galEquiv F).symm τ)
  rw [MulEquiv.apply_symm_apply] at h
  exact h.symm

lemma galSub_mem_galHom (σ : F ≃+* F) : galHom F σ ∈ galSub F := ⟨σ, rfl⟩

/-! ## The Galois part of an element of `PΓL(2,F)` -/

/-- A decomposition of `x ∈ PΓL(2,F)` as `PGL`-part times Galois part. -/
theorem exists_gal_decomp (x : ↥(pgammaL F)) :
    ∃ τ ∈ galSub F, ∃ c ∈ pglImage F, (x : Equiv.Perm (P1 F)) = c * τ := by
  obtain ⟨c, hc, τ, hτ, h⟩ := (Galois.decomposition F).1 x x.2
  exact ⟨τ, hτ, c, hc, h⟩

/-- The `galSub F`-component of an element of `PΓL(2,F)`. -/
noncomputable def galSubPart (x : ↥(pgammaL F)) : ↥(galSub F) :=
  ⟨Classical.choose (exists_gal_decomp F x),
    (Classical.choose_spec (exists_gal_decomp F x)).1⟩

lemma galSubPart_spec (x : ↥(pgammaL F)) :
    ∃ c ∈ pglImage F,
      (x : Equiv.Perm (P1 F)) = c * (galSubPart F x : Equiv.Perm (P1 F)) :=
  (Classical.choose_spec (exists_gal_decomp F x)).2

/-- The **Galois part** of an element of `PΓL(2,F)`: the projection
`PΓL(2,F) →* Aut F` with kernel `pglImage F`. -/
noncomputable def galPart (x : ↥(pgammaL F)) : F ≃+* F :=
  (galEquiv F).symm (galSubPart F x)

@[simp] lemma galEquiv_galPart (x : ↥(pgammaL F)) :
    galEquiv F (galPart F x) = galSubPart F x :=
  MulEquiv.apply_symm_apply _ _

lemma galPart_spec (x : ↥(pgammaL F)) :
    ∃ c ∈ pglImage F, (x : Equiv.Perm (P1 F)) = c * galHom F (galPart F x) := by
  obtain ⟨c, hc, h⟩ := galSubPart_spec F x
  refine ⟨c, hc, ?_⟩
  rw [h]
  congr 2
  exact (galEquiv_symm_coe F (galSubPart F x)).symm

/-- Uniqueness of the decomposition `x = c · galHom σ`. -/
lemma galPart_unique (x : ↥(pgammaL F)) {c : Equiv.Perm (P1 F)} {τ : Equiv.Perm (P1 F)}
    (hc : c ∈ pglImage F) (hτ : τ ∈ galSub F)
    (h : (x : Equiv.Perm (P1 F)) = c * τ) :
    galHom F (galPart F x) = τ := by
  obtain ⟨c', hc', h'⟩ := galPart_spec F x
  have h2 : c' * galHom F (galPart F x) = c * τ := by rw [← h', h]
  have h3 : c⁻¹ * c' = τ * (galHom F (galPart F x))⁻¹ := by
    have key : c⁻¹ * (c' * galHom F (galPart F x)) * (galHom F (galPart F x))⁻¹ =
        c⁻¹ * (c * τ) * (galHom F (galPart F x))⁻¹ := by rw [h2]
    rw [show c⁻¹ * (c' * galHom F (galPart F x)) * (galHom F (galPart F x))⁻¹ = c⁻¹ * c' by
          group,
        show c⁻¹ * (c * τ) * (galHom F (galPart F x))⁻¹ =
          τ * (galHom F (galPart F x))⁻¹ by group] at key
    exact key
  have h4 : c⁻¹ * c' ∈ pglImage F := Subgroup.mul_mem _ (Subgroup.inv_mem _ hc) hc'
  have h5 : τ * (galHom F (galPart F x))⁻¹ ∈ galSub F :=
    Subgroup.mul_mem _ hτ (Subgroup.inv_mem _ (galSub_mem_galHom F _))
  have h6 : τ * (galHom F (galPart F x))⁻¹ = 1 := by
    have hmem : τ * (galHom F (galPart F x))⁻¹ ∈ pglImage F ⊓ galSub F :=
      ⟨by rw [← h3]; exact h4, h5⟩
    rwa [Galois.pglImage_inf_galSub, Subgroup.mem_bot] at hmem
  exact (mul_inv_eq_one.mp h6).symm

lemma galPart_mul (x y : ↥(pgammaL F)) :
    galPart F (x * y) = galPart F x * galPart F y := by
  obtain ⟨c₁, hc₁, h₁⟩ := galPart_spec F x
  obtain ⟨c₂, hc₂, h₂⟩ := galPart_spec F y
  have hnorm : galHom F (galPart F x) * c₂ * (galHom F (galPart F x))⁻¹ ∈ pglImage F :=
    Subgroup.le_normalizer_iff.mp (Galois.galSub_le_normalizer_pglImage F)
      _ (galSub_mem_galHom F _) c₂ hc₂
  have hd : ((x * y : ↥(pgammaL F)) : Equiv.Perm (P1 F)) =
      (c₁ * (galHom F (galPart F x) * c₂ * (galHom F (galPart F x))⁻¹)) *
        galHom F (galPart F x * galPart F y) := by
    rw [Subgroup.coe_mul, h₁, h₂, map_mul]
    group
  have h := galPart_unique F (x * y)
    (Subgroup.mul_mem _ hc₁ hnorm)
    (galSub_mem_galHom F _) hd
  exact Galois.galHom_injective F h

lemma galPart_one : galPart F 1 = 1 := by
  have h := galPart_unique F (1 : ↥(pgammaL F)) (c := 1) (τ := 1)
    (Subgroup.one_mem _) (Subgroup.one_mem _) (by rw [mul_one, Subgroup.coe_one])
  exact Galois.galHom_injective F (by rw [h, map_one])

/-- The Galois projection, as a monoid homomorphism. -/
noncomputable def galMap : ↥(pgammaL F) →* (F ≃+* F) where
  toFun := galPart F
  map_one' := galPart_one F
  map_mul' := galPart_mul F

@[simp] lemma galMap_apply (x : ↥(pgammaL F)) : galMap F x = galPart F x := rfl

/-- An element of `PΓL(2,F)` has trivial Galois part exactly when it lies in `PGL(2,F)`. -/
lemma galPart_eq_one_iff (x : ↥(pgammaL F)) :
    galPart F x = 1 ↔ (x : Equiv.Perm (P1 F)) ∈ pglImage F := by
  constructor
  · intro h
    obtain ⟨c, hc, hspec⟩ := galPart_spec F x
    rw [h, map_one, mul_one] at hspec
    rw [hspec]; exact hc
  · intro hx
    have h := galPart_unique F x (c := (x : Equiv.Perm (P1 F))) (τ := 1) hx
      (Subgroup.one_mem _) (by rw [mul_one])
    exact Galois.galHom_injective F (by rw [h, map_one])

lemma galPart_of_mem (x : ↥(pgammaL F)) (hx : (x : Equiv.Perm (P1 F)) ∈ pglImage F) :
    galPart F x = 1 :=
  (galPart_eq_one_iff F x).mpr hx

end Work.DSTR.M110.SplitAux
