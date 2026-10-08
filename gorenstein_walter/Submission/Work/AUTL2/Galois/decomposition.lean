/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Galois decomposition of `PΓL(2,F) = PGL(2,F) · PΣL(2,F)`

For a field `F` (with `DecidableEq F`), with `P1 F = ℙ¹(F)`:

* `galHom F` is injective: a field automorphism is determined by its action on `ℙ¹(F)`;
* `pglImage F ⊓ galSub F = ⊥`;
* `galSub F` normalizes `pglImage F`;
* every element of `pglImage F ⊔ galSub F = PΓL(2,F)` is a product `x * τ` with
  `x ∈ pglImage F` and `τ ∈ galSub F`;
* `PΓL(2,F)` normalizes `pslImage F`.

The two computational ingredients are the compatibility lemma
`OnePoint.map_smul` (a field automorphism conjugates the Möbius action of a matrix into the
Möbius action of the image matrix) and the fact that `toPGL` has range the `SL`-part of `PGL`.
-/
import Mathlib
import Submission.Work.AUTL2.Defs
import Submission.Work.AUTL2.Mobius
import Submission.Work.AUTL2.Stabilizer

open scoped MatrixGroups LinearAlgebra.Projectivization
open OnePoint
open Pointwise

namespace Work.AUTL2.Galois

open Work.AUTL2

/-- If `K` normalizes `H`, then every element of `H ⊔ K` is of the form `x * τ` with `x ∈ H`
and `τ ∈ K`. -/
private lemma exists_mul_of_mem_sup {G : Type*} [Group G] (H K : Subgroup G)
    (h : K ≤ Subgroup.normalizer H) {π : G} (hπ : π ∈ H ⊔ K) :
    ∃ x ∈ H, ∃ τ ∈ K, π = x * τ := by
  classical
  have hconj : ∀ k ∈ K, ∀ y ∈ H, k * y * k⁻¹ ∈ H := Subgroup.le_normalizer_iff.mp h
  set S : Subgroup G :=
    { carrier := (H : Set G) * (K : Set G)
      mul_mem' := by
        rintro a b ⟨h1, h1H, k1, k1K, rfl⟩ ⟨h2, h2H, k2, k2K, rfl⟩
        refine ⟨h1 * (k1 * h2 * k1⁻¹), mul_mem h1H (hconj k1 k1K h2 h2H), k1 * k2,
          mul_mem k1K k2K, ?_⟩
        group
      one_mem' := ⟨1, one_mem H, 1, one_mem K, mul_one 1⟩
      inv_mem' := by
        rintro a ⟨h1, h1H, k1, k1K, rfl⟩
        have hmem' : k1⁻¹ * h1⁻¹ * k1 ∈ H := by
          simpa using hconj k1⁻¹ (inv_mem k1K) h1⁻¹ (inv_mem h1H)
        refine ⟨k1⁻¹ * h1⁻¹ * k1, hmem', k1⁻¹, inv_mem k1K, ?_⟩
        group } with hSdef
  have hHS : H ≤ S := fun x hx => ⟨x, hx, 1, one_mem K, mul_one x⟩
  have hKS : K ≤ S := fun x hx => ⟨1, one_mem H, x, hx, one_mul x⟩
  have hsub : H ⊔ K ≤ S := sup_le hHS hKS
  obtain ⟨x, hxH, τ, hτK, hxτ⟩ := hsub hπ
  exact ⟨x, hxH, τ, hτK, hxτ.symm⟩

variable (F : Type*) [Field F] [DecidableEq F]

/-! ## Matrix-level computations -/

/-- The Möbius action of a matrix: `pglHom F (mk A) c = A • c`. -/
lemma pglHom_mk_apply (A : GL (Fin 2) F) (c : P1 F) :
    pglHom F (Matrix.ProjGenLinGroup.mk A) c = A • c := by
  rw [pglHom, MulAction.toPermHom_apply, MulAction.toPerm_apply]
  exact Matrix.ProjGenLinGroup.mk_smul _ A c

/-- A field automorphism commutes with the action of `GL(2,F)` on `ℙ¹(F)`: it conjugates the
action of a matrix into the action of its image. -/
lemma map_smul_fieldAut (σ : F ≃+* F) (A : GL (Fin 2) F) (c : P1 F) :
    OnePoint.map (σ : F → F) (A • (OnePoint.map (σ.symm : F → F) c)) =
      (Matrix.GeneralLinearGroup.map (σ : F →+* F) A) • c := by
  refine (OnePoint.map_smul (σ : F →+* F) A (OnePoint.map (σ.symm : F → F) c)).trans ?_
  congr 1
  change OnePoint.map (σ : F → F) (OnePoint.map (σ.symm : F → F) c) = c
  rw [show OnePoint.map (σ : F → F) (OnePoint.map (σ.symm : F → F) c) =
      OnePoint.map ((σ : F → F) ∘ (σ.symm : F → F)) c from
    (congrFun (OnePoint.map_comp (σ : F → F) (σ.symm : F → F)).symm c)]
  rw [show ((σ : F → F) ∘ (σ.symm : F → F)) = id from funext fun x => σ.apply_symm_apply x]
  rw [OnePoint.map_id]
  rfl

/-- Conjugation of a `PGL`-element by a field automorphism is again `PGL`. -/
lemma fieldAut_conj_pgl (σ : F ≃+* F) (A : GL (Fin 2) F) :
    galHom F σ * pglHom F (Matrix.ProjGenLinGroup.mk A) * (galHom F σ)⁻¹ =
      pglHom F (Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map (σ : F →+* F) A)) := by
  ext c
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
  rw [show ((galHom F σ)⁻¹ : Equiv.Perm (P1 F)) = galHom F σ.symm from by
    rw [← map_inv]; rfl]
  rw [show ⇑(galHom F σ.symm) = OnePoint.map (σ.symm : F → F) from rfl,
    show ⇑(galHom F σ) = OnePoint.map (σ : F → F) from rfl,
    pglHom_mk_apply, pglHom_mk_apply]
  exact map_smul_fieldAut F σ A c

/-- The map `GL(2,F) → GL(2,F)` induced by a ring homomorphism is compatible with `toGL`. -/
lemma toGL_map (σ : F ≃+* F) (u : Matrix.SpecialLinearGroup (Fin 2) F) :
    Matrix.GeneralLinearGroup.map (σ : F →+* F) (Matrix.SpecialLinearGroup.toGL u) =
      Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map (σ : F →+* F) u) := by
  ext i j
  rfl

/-- Conjugation of a `PSL`-element by a field automorphism is again `PSL`. -/
lemma fieldAut_conj_psl (σ : F ≃+* F) (u : Matrix.SpecialLinearGroup (Fin 2) F) :
    galHom F σ * pslHom F (QuotientGroup.mk u) * (galHom F σ)⁻¹ =
      pslHom F (QuotientGroup.mk (Matrix.SpecialLinearGroup.map (σ : F →+* F) u)) := by
  ext c
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
  rw [show ((galHom F σ)⁻¹ : Equiv.Perm (P1 F)) = galHom F σ.symm from by
    rw [← map_inv]; rfl]
  rw [show ⇑(galHom F σ.symm) = OnePoint.map (σ.symm : F → F) from rfl,
    pslHom_toGL,
    show ⇑(galHom F σ) = OnePoint.map (σ : F → F) from rfl,
    pslHom_toGL]
  rw [show OnePoint.map (σ : F → F)
        ((Matrix.SpecialLinearGroup.toGL u) • OnePoint.map (σ.symm : F → F) c) =
      (Matrix.GeneralLinearGroup.map (σ : F →+* F)
        (Matrix.SpecialLinearGroup.toGL u)) • c from
    map_smul_fieldAut F σ (Matrix.SpecialLinearGroup.toGL u) c]
  rw [toGL_map]

/-- The `PSL`-element `QuotientGroup.mk u` of `PSL` is the `PGL`-element `mk (toGL u)`. -/
lemma pslHom_eq_pglHom (u : Matrix.SpecialLinearGroup (Fin 2) F) :
    pslHom F (QuotientGroup.mk u) =
      pglHom F (Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL u)) := rfl

/-- Inside `PGL(2,F)`, the conjugate of an `SL`-element by an arbitrary element is again an
`SL`-element. -/
lemma pglHom_mk_conj (B C : GL (Fin 2) F) :
    pglHom F (Matrix.ProjGenLinGroup.mk B) * pglHom F (Matrix.ProjGenLinGroup.mk C) *
        (pglHom F (Matrix.ProjGenLinGroup.mk B))⁻¹ =
      pglHom F (Matrix.ProjGenLinGroup.mk (B * C * B⁻¹)) := by
  rw [show Matrix.ProjGenLinGroup.mk (B * C * B⁻¹) =
      Matrix.ProjGenLinGroup.mk B * Matrix.ProjGenLinGroup.mk C *
        (Matrix.ProjGenLinGroup.mk B)⁻¹ from by rw [map_mul, map_mul, map_inv]]
  rw [map_mul, map_mul, map_inv]

/-- A matrix of determinant `1` conjugate to an `SL`-element is the image of an `SL`-element. -/
lemma exists_sl_conj (B : GL (Fin 2) F) (u : Matrix.SpecialLinearGroup (Fin 2) F) :
    ∃ u' : Matrix.SpecialLinearGroup (Fin 2) F,
      Matrix.SpecialLinearGroup.toGL u' = B * Matrix.SpecialLinearGroup.toGL u * B⁻¹ := by
  have hmem : B * Matrix.SpecialLinearGroup.toGL u * B⁻¹ ∈
      (Matrix.SpecialLinearGroup.toGL).range := by
    rw [Matrix.SpecialLinearGroup.range_toGL_eq_ker_det, MonoidHom.mem_ker]
    rw [map_mul, map_mul, map_inv, Matrix.SpecialLinearGroup.coeToGL_det]
    simp
  obtain ⟨u', hu'⟩ := hmem
  exact ⟨u', hu'⟩

/-! ## The five assertions -/

/-- `galHom F` is injective. -/
lemma galHom_injective : Function.Injective (galHom F) := by
  intro σ τ h
  ext x
  have h1 := congrFun (congrArg DFunLike.coe h) ((x : F) : P1 F)
  exact OnePoint.coe_eq_coe.mp h1

/-- A permutation of `ℙ¹(F)` which is both Möbius and a field automorphism is the identity. -/
lemma pglImage_inf_galSub : pglImage F ⊓ galSub F = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hx1, hx2⟩
  obtain ⟨A, rfl⟩ := hx1
  obtain ⟨σ, hσ⟩ := hx2
  obtain ⟨Am, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective A
  simp only [Subgroup.mem_bot]
  -- From `galHom σ = pglHom (mk Am)` we read off that `Am` acts affinely and `σ = id`.
  have hσc : ∀ c : P1 F, galHom F σ c =
      pglHom F (Matrix.ProjGenLinGroup.mk Am) c := fun c =>
    congrFun (congrArg DFunLike.coe hσ) c
  have hinf : Am • (∞ : P1 F) = ∞ := by
    have h := hσc (∞ : P1 F)
    rw [pglHom_mk_apply] at h
    rw [show galHom F σ (∞ : P1 F) = ∞ from rfl] at h
    exact h.symm
  have h10 : (Am : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 :=
    OnePoint.smul_infty_eq_self_iff.mp hinf
  have h11 : (Am : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ 0 := by
    intro h
    have hd : Matrix.det (Am : Matrix (Fin 2) (Fin 2) F) ≠ 0 :=
      Matrix.GeneralLinearGroup.det_ne_zero Am
    rw [Matrix.det_fin_two, h10, mul_zero, h, mul_zero, sub_zero] at hd
    exact hd rfl
  have hform : ∀ y : F, σ y = ((Am : Matrix (Fin 2) (Fin 2) F) 0 0 * y +
      (Am : Matrix (Fin 2) (Fin 2) F) 0 1) / (Am : Matrix (Fin 2) (Fin 2) F) 1 1 := by
    intro y
    have h := hσc ((y : F) : P1 F)
    rw [pglHom_mk_apply, OnePoint.smul_some_eq_ite, h10, zero_mul, zero_add,
      if_neg h11] at h
    exact OnePoint.coe_eq_coe.mp h
  have h01 : (Am : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by
    have h := hform 0
    rw [map_zero] at h
    simp only [mul_zero, zero_add] at h
    rcases div_eq_zero_iff.mp h.symm with h' | h'
    · exact h'
    · exact absurd h' h11
  have h00 : (Am : Matrix (Fin 2) (Fin 2) F) 0 0 =
      (Am : Matrix (Fin 2) (Fin 2) F) 1 1 := by
    have h := hform 1
    rw [map_one, h01, add_zero, mul_one] at h
    have h' : (Am : Matrix (Fin 2) (Fin 2) F) 0 0 =
        1 * (Am : Matrix (Fin 2) (Fin 2) F) 1 1 := (div_eq_iff h11).mp h.symm
    simpa using h'
  have hσone : σ = 1 := by
    ext y
    rw [hform y, h01, add_zero, h00]
    exact mul_div_cancel_left₀ y h11
  rw [← hσ, hσone, map_one]

/-- The Galois part normalizes `PGL(2,F)`. -/
lemma galSub_le_normalizer_pglImage :
    galSub F ≤ Subgroup.normalizer (pglImage F : Set (Equiv.Perm (P1 F))) := by
  rw [Subgroup.le_normalizer_iff]
  rintro τ ⟨σ, rfl⟩ k ⟨A, rfl⟩
  obtain ⟨Am, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective A
  exact ⟨Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map (σ : F →+* F) Am),
    (fieldAut_conj_pgl F σ Am).symm⟩

/-- The Möbius group normalizes `PSL(2,F)`. -/
lemma pglImage_le_normalizer_pslImage :
    pglImage F ≤ Subgroup.normalizer (pslImage F : Set (Equiv.Perm (P1 F))) := by
  rw [Subgroup.le_normalizer_iff]
  rintro k ⟨A, rfl⟩ p ⟨u, rfl⟩
  obtain ⟨Am, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective A
  obtain ⟨u0, rfl⟩ := QuotientGroup.mk_surjective u
  rw [pslHom_eq_pglHom, pglHom_mk_conj]
  obtain ⟨u1, hu1⟩ := exists_sl_conj F Am u0
  rw [← hu1]
  exact ⟨QuotientGroup.mk u1, (pslHom_eq_pglHom F u1).symm⟩

/-- The Galois part normalizes `PSL(2,F)`. -/
lemma galSub_le_normalizer_pslImage :
    galSub F ≤ Subgroup.normalizer (pslImage F : Set (Equiv.Perm (P1 F))) := by
  rw [Subgroup.le_normalizer_iff]
  rintro τ ⟨σ, rfl⟩ p ⟨u, rfl⟩
  obtain ⟨u0, rfl⟩ := QuotientGroup.mk_surjective u
  exact ⟨QuotientGroup.mk (Matrix.SpecialLinearGroup.map (σ : F →+* F) u0),
    (fieldAut_conj_psl F σ u0).symm⟩

/-- `PΓL(2,F)` normalizes `PSL(2,F)`. -/
lemma pgammaL_le_normalizer_pslImage :
    pgammaL F ≤ Subgroup.normalizer (pslImage F : Set (Equiv.Perm (P1 F))) := by
  rw [pgammaL]
  exact sup_le (pglImage_le_normalizer_pslImage F) (galSub_le_normalizer_pslImage F)

theorem decomposition (F : Type*) [Field F] [DecidableEq F] :
    (∀ π ∈ Work.AUTL2.pgammaL F, ∃ x ∈ Work.AUTL2.pglImage F, ∃ τ ∈ Work.AUTL2.galSub F,
        π = x * τ) ∧
      (Work.AUTL2.pglImage F ⊓ Work.AUTL2.galSub F = ⊥) ∧
      (Work.AUTL2.galSub F ≤ Subgroup.normalizer (Work.AUTL2.pglImage F : Set (Equiv.Perm (Work.AUTL2.P1 F)))) ∧
      Function.Injective (Work.AUTL2.galHom F) ∧
      Work.AUTL2.pgammaL F ≤ Subgroup.normalizer (Work.AUTL2.pslImage F : Set (Equiv.Perm (Work.AUTL2.P1 F))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro π hπ
    exact exists_mul_of_mem_sup (pglImage F) (galSub F) (galSub_le_normalizer_pglImage F) hπ
  · exact pglImage_inf_galSub F
  · exact galSub_le_normalizer_pglImage F
  · exact galHom_injective F
  · exact pgammaL_le_normalizer_pslImage F

end Work.AUTL2.Galois
