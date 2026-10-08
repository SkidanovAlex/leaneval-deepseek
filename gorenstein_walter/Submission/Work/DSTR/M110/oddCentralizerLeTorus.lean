/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Odd-order elements centralizing a non-split involution lie in the torus

Let `F = GF(p^k)` be a finite field and `B ∈ GL(2,F)` a *non-split* involution, i.e.
`B * B = c • 1` with `c` a non-square of `F` and `B` not a scalar matrix.  Write
`t = pglHom F (mk B) ∈ PGL(2,F) ⊆ Sym(ℙ¹(F))` for its image, an involution without fixed points,
and let `T = theTorus B c hB` be the image of the non-split torus
`(F[X]/(X²-c))ˣ → GL(2,F) → PGL(2,F)`.

The theorem proved here is the "centralizer" statement needed for the non-split case of
Bender's Theorem 1.10(ii) in the `ℙ¹` model (`Work.DSTR.M110.nonsplitCase`):

**an element `y ∈ PGL(2,F)` of odd order commuting with `t` lies in `T`.**

The mathematical content is the classical computation `C_{GL(2,F)}(B) = F[B]^×`:

1. `y = pglHom (mk A)` for some `A ∈ GL(2,F)`; the commutation of `y` and `t` in `Sym(ℙ¹(F))`
   and the faithfulness of the `PGL(2,F)`-action give `mk A · mk B = mk B · mk A`, whence
   `A * B = u • (B * A)` for some `u ∈ Fˣ` (the matrices commute up to a scalar —
   `Work.DSTR.M110.mul_eq_smul_mul_of_mk_mul_eq`);
2. taking determinants gives `u ^ 2 = 1`, hence `A * A` commutes with `B`
   (`Work.DSTR.M110.sq_mul_eq_mul_sq_of_smul_twist`);
3. the commutant of the non-scalar matrix `B` is the two-dimensional algebra `F·1 + F·B`
   (`Work.L2F.Mat2.commutant_sq_scalar`), and `B * B = c • 1` with `c` a non-square identifies
   that algebra with `F[X]/(X²-c)`; hence `A * A` is in the range of the torus map
   (`Work.DSTR.M110.exists_torusGL_eq_of_eq_smul_add`), so `y ^ 2 ∈ T`;
4. an element of odd order is a power of its square, so `y ∈ T`.

The oddness hypothesis is what excludes the "reflection" coset of the normalizer `N(T)`: an
element of `C(t)` outside `T` squares into `T`, hence has even order.

Everything is stated over an arbitrary field; the primality of `p` and `k ≠ 0` are not used.
-/
import Mathlib
import Submission.Work.DSTR.M110.nonsplitAux
import Submission.Work.L2F.Mat2.commutant_sq_scalar
import Submission.Work.DSTR.M110.mul_eq_smul_mul_of_mk_mul_eq
import Submission.Work.DSTR.M110.sq_mul_eq_mul_sq_of_smul_twist
import Submission.Work.DSTR.M110.exists_torusGL_eq_of_eq_smul_add

open scoped MatrixGroups LinearAlgebra.Projectivization
open OnePoint Polynomial

namespace Work.DSTR.M110

section Aux

variable {F : Type*} [Field F]

/-- An element of odd order is a power of its own square. -/
lemma eq_sq_pow_of_odd_order {G : Type*} [Group G] (z : G) (hz : Odd (orderOf z)) :
    z = (z * z) ^ ((orderOf z + 1) / 2) := by
  obtain ⟨t, ht⟩ := hz
  have h2 : 2 * ((orderOf z + 1) / 2) = orderOf z + 1 := by omega
  calc z = z ^ (orderOf z + 1) := by rw [pow_succ, pow_orderOf_eq_one, one_mul]
    _ = z ^ (2 * ((orderOf z + 1) / 2)) := by rw [h2]
    _ = (z * z) ^ ((orderOf z + 1) / 2) := by rw [pow_mul, pow_two]

/-- A non-square of a field is non-zero, since `0 = 0 * 0`. -/
lemma ne_zero_of_not_isSquare_aux {c : F} (hc : ¬ IsSquare c) : c ≠ 0 :=
  fun h => hc (h ▸ ⟨0, by ring⟩)

end Aux

open Work.AUTL2

/-- **The centralizer of a non-split involution inside `PGL(2,q)`, odd part.**  An odd-order
element of `PGL(2,F)` commuting with the image of the non-split involution `B` lies in the
non-split torus `T = theTorus B c hB`. -/
theorem oddCentralizerLeTorus (p k : ℕ) [Fact p.Prime] (hk : k ≠ 0)
    [DecidableEq (GaloisField p k)]
    (B : GL (Fin 2) (GaloisField p k)) (c : GaloisField p k)
    (hB : (B : Matrix (Fin 2) (Fin 2) (GaloisField p k)) * B = c • 1)
    (hc : ¬ IsSquare c)
    (hBns : ∀ s : GaloisField p k,
      (B : Matrix (Fin 2) (Fin 2) (GaloisField p k)) ≠ s • 1)
    (y : Equiv.Perm (Work.AUTL2.P1 (GaloisField p k)))
    (hy : y ∈ Work.AUTL2.pglImage (GaloisField p k))
    (hyt : y ∈ Subgroup.centralizer ({(Work.AUTL2.pglHom (GaloisField p k)
      (Matrix.ProjGenLinGroup.mk B))} : Set (Equiv.Perm (Work.AUTL2.P1 (GaloisField p k)))))
    (hodd : Odd (orderOf y)) :
    y ∈ Work.DSTR.M110.theTorus B c hB := by
  -- lift `y` to a matrix
  obtain ⟨g, rfl⟩ := hy
  obtain ⟨A, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
  -- the corresponding elements of `PGL(2,F)` commute
  have hcomm : Matrix.ProjGenLinGroup.mk B * Matrix.ProjGenLinGroup.mk A =
      Matrix.ProjGenLinGroup.mk A * Matrix.ProjGenLinGroup.mk B := by
    apply Work.AUTL2.Aut.pglHomInjective (GaloisField p k)
    rw [map_mul, map_mul]
    exact Subgroup.mem_centralizer_iff.mp hyt _ (Set.mem_singleton _)
  -- therefore `A * B = u • (B * A)` for some unit `u`, and `A * A` commutes with `B`
  obtain ⟨u, hu⟩ := mul_eq_smul_mul_of_mk_mul_eq A B hcomm
  have hsq := sq_mul_eq_mul_sq_of_smul_twist A B u hu
  -- the commutant of the non-scalar matrix `B` is `F·1 + F·B`
  obtain ⟨a, b, hab⟩ := Work.L2F.Mat2.commutant_sq_scalar (GaloisField p k)
    (B : Matrix (Fin 2) (Fin 2) (GaloisField p k))
    ((A * A : GL (Fin 2) (GaloisField p k)) : Matrix (Fin 2) (Fin 2) (GaloisField p k))
    c hB (ne_zero_of_not_isSquare_aux hc) hBns hsq
  -- hence `A * A` is in the range of the torus map, i.e. `y ^ 2 ∈ T`
  obtain ⟨v, hv⟩ := exists_torusGL_eq_of_eq_smul_add B c hB hc (A * A) b a
    (by rw [hab, add_comm])
  have hy2 : Work.AUTL2.pglHom (GaloisField p k) (Matrix.ProjGenLinGroup.mk A) *
        Work.AUTL2.pglHom (GaloisField p k) (Matrix.ProjGenLinGroup.mk A) ∈
      Work.DSTR.M110.theTorus B c hB := by
    have h1 : Work.AUTL2.pglHom (GaloisField p k) (Matrix.ProjGenLinGroup.mk A) *
        Work.AUTL2.pglHom (GaloisField p k) (Matrix.ProjGenLinGroup.mk A) =
        Work.AUTL2.pglHom (GaloisField p k) (Matrix.ProjGenLinGroup.mk (A * A)) := by
      rw [← map_mul, ← map_mul]
    rw [h1]
    exact ⟨v, by rw [torusPerm_apply, hv]⟩
  -- an element of odd order is a power of its square
  rw [eq_sq_pow_of_odd_order _ hodd]
  exact Subgroup.pow_mem _ hy2 _

end Work.DSTR.M110
