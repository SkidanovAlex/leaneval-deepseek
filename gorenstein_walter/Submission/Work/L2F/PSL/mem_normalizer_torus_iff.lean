/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The normalizer of the split (diagonal) torus in `SL(2,F)`

Main result (`mem_normalizer_torus_iff`): for a finite field `F` with `5 ≤ |F|`, an element
`x ∈ SL(2,F)` normalizes the diagonal torus `T = torus F = {diag(a,a⁻¹)}` if and only if
`x ∈ T` or `x = z * t` with `t ∈ T`, where `z = !![0,1;-1,0]` is the Weyl element.

Proof.  `N(T) ⊇ T ∪ zT` is clear since `z diag(a,a⁻¹) z⁻¹ = diag(a⁻¹,a)` (`z_mul_diag`).
Conversely let `x ∈ N(T)` and pick `a ∈ Fˣ` with `a ≠ a⁻¹` (this exists as soon as `|F| ≥ 4`,
see `exists_unit_ne_inv`).  Then `x diag(a,a⁻¹) x⁻¹ = diag(b,b⁻¹)` for some `b ∈ Fˣ`, i.e.
`diag b · x = x · diag a` at the level of `2 × 2` matrices.  Writing `X = !![u,u';v,v']` for
the matrix of `x`, this is the four scalar relations

* `b·u = u·a`, `b·u' = u'·a⁻¹`, `b⁻¹·v = v·a`, `b⁻¹·v' = v'·a⁻¹`,

and `det X = 1` reads `u·v' - u'·v = 1`.  If `u ≠ 0` then `b = a`, whence `u' = 0 = v` (using
`a ≠ a⁻¹`) and `u·v' = 1`, so `X` is diagonal and `x ∈ T`; if `u = 0` then `u'·v = -1` and,
again using `a ≠ a⁻¹`, `b = a⁻¹` and `v' = 0`, so `X` is anti-diagonal and `x = z · diag(-v)`.
This dichotomy is `diag_conj_dichotomy`.
-/
import Mathlib
import Submission.Work.L2F.Defs
import Submission.Work.L2F.Mat2.z_mul_diag

open scoped MatrixGroups
open Matrix

namespace Work.L2F.PSL

/-! ## Auxiliary lemmas -/

/-- A finite field with at least five elements has a unit `a` with `a ≠ a⁻¹`: the units fixed by
inversion are the roots of `X² - 1`, namely `1` and `-1` — at most two elements — whereas
`|Fˣ| = |F| - 1 ≥ 4`. -/
lemma exists_unit_ne_inv (F : Type*) [Field F] [Fintype F] (h5 : 5 ≤ Nat.card F) :
    ∃ a : Fˣ, a ≠ a⁻¹ := by
  classical
  have h5' : 5 ≤ Fintype.card F := by rwa [Nat.card_eq_fintype_card] at h5
  have hcard : ({0, 1, -1} : Finset F).card < (Finset.univ : Finset F).card := by
    have h3 : ({0, 1, -1} : Finset F).card ≤ 3 := Finset.card_le_three
    simp only [Finset.card_univ]
    omega
  obtain ⟨a, -, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  simp only [Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
    not_or, not_false_eq_true] at ha
  refine ⟨Units.mk0 a ha.1, ?_⟩
  intro h
  have hval : a = a⁻¹ := by
    have h' := congrArg (fun u : Fˣ => (u : F)) h
    simpa only [Units.val_mk0, Units.val_inv_eq_inv_val] using h'
  have haa : a * a = 1 := by
    have h1 : a⁻¹ * a = 1 := inv_mul_cancel₀ ha.1
    rwa [← hval] at h1
  have hz : (a - 1) * (a + 1) = 0 := by linear_combination haa
  rcases mul_eq_zero.mp hz with h1 | h1
  · exact ha.2.1 (sub_eq_zero.mp h1)
  · exact ha.2.2 (by linear_combination h1)

/-- Computational core of `N_{SL(2,F)}(T) = T ∪ zT`: if `X` has determinant one and
`diag b · X = X · diag a` with `a ≠ a⁻¹`, then `X` is diagonal or anti-diagonal.

Indeed, writing `X = !![u,u';v,v']` the hypothesis is the four scalar relations
`b·u = u·a`, `b·u' = u'·a⁻¹`, `b⁻¹·v = v·a`, `b⁻¹·v' = v'·a⁻¹`, and `det X = 1` is
`u·v' - u'·v = 1`.  If `u ≠ 0` then `b = a`, whence `u' = v = 0` and `u·v' = 1`; if `u = 0`
then `u'·v = -1`, `b = a⁻¹` and `v' = 0`. -/
lemma diag_conj_dichotomy (F : Type*) [Field F] (X : Matrix (Fin 2) (Fin 2) F) {a b : F}
    (ha : a ≠ a⁻¹) (hdet : X.det = 1)
    (h : !![b, 0; 0, b⁻¹] * X = X * !![a, 0; 0, a⁻¹]) :
    (X 0 1 = 0 ∧ X 1 0 = 0 ∧ X 0 0 * X 1 1 = 1) ∨
      (X 0 0 = 0 ∧ X 1 1 = 0 ∧ X 0 1 * X 1 0 = -1) := by
  simp only [Matrix.det_fin_two] at hdet
  have h00 : b * X 0 0 = X 0 0 * a := by
    have h' := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 0 0) h
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using h'
  have h01 : b * X 0 1 = X 0 1 * a⁻¹ := by
    have h' := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 0 1) h
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using h'
  have h10 : b⁻¹ * X 1 0 = X 1 0 * a := by
    have h' := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 1 0) h
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using h'
  have h11 : b⁻¹ * X 1 1 = X 1 1 * a⁻¹ := by
    have h' := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 1 1) h
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using h'
  by_cases hu : X 0 0 = 0
  · -- anti-diagonal case
    right
    have hanti : X 0 1 * X 1 0 = -1 := by
      simp only [hu, zero_mul, zero_sub] at hdet
      linear_combination -hdet
    have hne : X 0 1 ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hanti
      exact (neg_ne_zero.mpr one_ne_zero) hanti.symm
    have hb : b = a⁻¹ := by
      have h' : b * X 0 1 - a⁻¹ * X 0 1 = 0 :=
        sub_eq_zero.mpr (by rw [h01, mul_comm (X 0 1) a⁻¹])
      rw [← sub_mul] at h'
      exact sub_eq_zero.mp ((mul_eq_zero.mp h').resolve_right hne)
    have h1 : X 1 1 = 0 := by
      have h' : a * X 1 1 = X 1 1 * a⁻¹ := by simpa only [hb, inv_inv] using h11
      have h2 : (a - a⁻¹) * X 1 1 = 0 := by rw [sub_mul, h']; ring
      exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr ha)
    exact ⟨hu, h1, hanti⟩
  · -- diagonal case
    left
    have hb : b = a := by
      have h' : X 0 0 * b - X 0 0 * a = 0 :=
        sub_eq_zero.mpr (by rw [mul_comm (X 0 0) b, h00])
      rw [← mul_sub] at h'
      exact sub_eq_zero.mp ((mul_eq_zero.mp h').resolve_left hu)
    have hz : X 1 0 = 0 := by
      have h' : a⁻¹ * X 1 0 = X 1 0 * a := by simpa only [hb] using h10
      have h2 : (a⁻¹ - a) * X 1 0 = 0 := by rw [sub_mul, h']; ring
      exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr (Ne.symm ha))
    have ho : X 0 1 = 0 := by
      have h' : a * X 0 1 = X 0 1 * a⁻¹ := by simpa only [hb] using h01
      have h2 : (a - a⁻¹) * X 0 1 = 0 := by rw [sub_mul, h']; ring
      exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr ha)
    have hprod : X 0 0 * X 1 1 = 1 := by
      rw [ho, hz] at hdet
      simpa using hdet
    exact ⟨ho, hz, hprod⟩

/-- The Weyl element `z = !![0,1;-1,0]` normalizes the split torus:
`z · diag(a,a⁻¹) · z⁻¹ = diag(a⁻¹,a)`. -/
lemma weyl_mem_normalizer_torus (F : Type*) [Field F] :
    Work.L2F.z F ∈ Subgroup.normalizer
      (Work.L2F.torus F : Set (Matrix.SpecialLinearGroup (Fin 2) F)) := by
  have hconj : ∀ a : Fˣ,
      Work.L2F.z F * Work.PSL2.diag F a * (Work.L2F.z F)⁻¹ = Work.PSL2.diag F a⁻¹ := by
    intro a
    rw [Work.L2F.Mat2.z_mul_diag F a, mul_assoc, mul_inv_cancel, mul_one]
  have hconj' : ∀ a : Fˣ,
      (Work.L2F.z F)⁻¹ * Work.PSL2.diag F a * Work.L2F.z F = Work.PSL2.diag F a⁻¹ := by
    intro a
    have h := Work.L2F.Mat2.z_mul_diag F a⁻¹
    simp only [inv_inv] at h
    calc (Work.L2F.z F)⁻¹ * Work.PSL2.diag F a * Work.L2F.z F
        = (Work.L2F.z F)⁻¹ * (Work.PSL2.diag F a * Work.L2F.z F) := by rw [mul_assoc]
      _ = (Work.L2F.z F)⁻¹ * (Work.L2F.z F * Work.PSL2.diag F a⁻¹) := by rw [← h]
      _ = Work.PSL2.diag F a⁻¹ := by rw [← mul_assoc, inv_mul_cancel, one_mul]
  rw [Subgroup.mem_normalizer_iff]
  intro t
  constructor
  · intro ht
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp ht
    exact MonoidHom.mem_range.mpr ⟨a⁻¹, by
      change Work.PSL2.diag F a⁻¹ = Work.L2F.z F * Work.PSL2.diag F a * (Work.L2F.z F)⁻¹
      rw [hconj a]⟩
  · intro ht
    obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp ht
    have htb : t = (Work.L2F.z F)⁻¹ * Work.PSL2.diag F b * Work.L2F.z F := by
      have hb' : Work.PSL2.diag F b = Work.L2F.z F * t * (Work.L2F.z F)⁻¹ := hb
      rw [hb']; group
    exact MonoidHom.mem_range.mpr ⟨b⁻¹, by
      change Work.PSL2.diag F b⁻¹ = t
      rw [htb, hconj' b]⟩

/-! ## The normalizer of the split torus -/

theorem mem_normalizer_torus_iff (F : Type*) [Field F] [Fintype F] (h2 : (2 : F) ≠ 0)
    (h5 : 5 ≤ Nat.card F) (x : Matrix.SpecialLinearGroup (Fin 2) F) :
    x ∈ Subgroup.normalizer (Work.L2F.torus F : Set (Matrix.SpecialLinearGroup (Fin 2) F)) ↔
      x ∈ Work.L2F.torus F ∨ ∃ t ∈ Work.L2F.torus F, x = Work.L2F.z F * t := by
  classical
  constructor
  · intro hx
    rw [Subgroup.mem_normalizer_iff] at hx
    obtain ⟨a, ha⟩ := exists_unit_ne_inv F h5
    have hda : Work.PSL2.diag F a ∈ Work.L2F.torus F := MonoidHom.mem_range.mpr ⟨a, rfl⟩
    have hy : x * Work.PSL2.diag F a * x⁻¹ ∈ Work.L2F.torus F :=
      (hx (Work.PSL2.diag F a)).mp hda
    obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp hy
    have hgrp : Work.PSL2.diag F b * x = x * Work.PSL2.diag F a := by
      have hb' : Work.PSL2.diag F b = x * Work.PSL2.diag F a * x⁻¹ := hb
      rw [hb']; group
    have hmat := congrArg (fun g : SL(2, F) => ((g : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)) hgrp
    simp only [Matrix.SpecialLinearGroup.coe_mul, Work.PSL2.coe_diag,
      Units.val_inv_eq_inv_val] at hmat
    have ha' : (↑a : F) ≠ (↑a)⁻¹ := fun h =>
      ha (Units.ext (by rw [Units.val_inv_eq_inv_val]; exact h))
    have hXdet : (((x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)).det = 1 :=
      Matrix.SpecialLinearGroup.det_coe x
    rcases diag_conj_dichotomy F ((x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) ha' hXdet hmat
      with ⟨h01, h10, hprod⟩ | ⟨h00, h11, hanti⟩
    · -- `X` is diagonal: `x = diag (X 0 0)`
      left
      rw [Work.L2F.torus, MonoidHom.mem_range]
      let u : Fˣ := ⟨((x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 0,
        ((x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 1, hprod,
        by rw [mul_comm]; exact hprod⟩
      refine ⟨u, ?_⟩
      apply Subtype.ext
      change ((Work.PSL2.diag F u : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
        ((x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)
      rw [Work.PSL2.coe_diag]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [h01, h10, u]
    · -- `X` is anti-diagonal: `x = z * diag (-(X 1 0))`
      right
      let t : Fˣ := ⟨-(((x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 0),
        ((x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 1,
        by linear_combination -hanti, by linear_combination -hanti⟩
      refine ⟨Work.PSL2.diag F t, MonoidHom.mem_range.mpr ⟨t, rfl⟩, ?_⟩
      apply Subtype.ext
      change ((x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
        ((Work.L2F.z F * Work.PSL2.diag F t : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)
      rw [Matrix.SpecialLinearGroup.coe_mul, Work.PSL2.coe_diag]
      simp only [Work.L2F.z, Work.PSL2.coe_weyl, Matrix.mul_fin_two]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [h00, h11, t]
  · rintro (hxT | ⟨t, ht, rfl⟩)
    · exact Subgroup.le_normalizer hxT
    · exact Subgroup.mul_mem _ (weyl_mem_normalizer_torus F) (Subgroup.le_normalizer ht)

end Work.L2F.PSL
