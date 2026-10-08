import Mathlib
import Submission.Work.DSTR.M110.nonsplitAux
import Submission.Work.DSTR.M110.kerTorusPerm
import Submission.Work.DSTR.M110.torusGLCommute
import Submission.Work.DSTR.M110.quadAlgUnitsCard
import Submission.Work.DSTR.M110.ofUnitsRangeCard

open Polynomial

namespace Work.DSTR.M110

/-!
# The non-split torus of `PGL(2,F)`: cyclic of order `q + 1`, centralizing `B`

`theTorus B c hB` is the image inside `Sym(ℙ¹(F))` of the unit group of the quadratic algebra
`A = F[X]/(X²-c)`, acting through the Möbius action of `PGL(2,F)` on the image of
`B ∈ GL(2,F)`, where `B * B = c • 1` and `c` is a non-square (so that `A` is a field).

This file assembles the three facts needed in the non-split case of Bender 1.10(ii):

* `theTorus_isCyclic` : `theTorus B c hB` is cyclic (a quotient of `Aˣ`);
* `theTorus_card` : `|theTorus B c hB| = |F| + 1`;
* `theTorus_le_centralizer` : it centralizes the image of `B` in `PGL(2,F)`.

The ingredients, proved separately, are `kerTorusPerm` (the kernel of the permutation
representation is the image of `Fˣ`, of order `|F| - 1`), `quadAlgUnitsCard`
(`|Aˣ| = |F|² - 1`), `ofUnitsRangeCard` and `torusGLCommute`.
-/

/-! ## Auxiliary facts -/

/-- A finite field has at least two elements. -/
lemma two_le_natCard (F : Type*) [Field F] [Fintype F] : 2 ≤ Nat.card F := by
  rw [Nat.card_eq_fintype_card]
  exact Fintype.one_lt_card

section Aux

variable {F : Type*} [Field F] [DecidableEq F]

/-- `X ^ 2 - C c` has degree `2 ≠ 0`, so that `AdjoinRoot.of` is injective. -/
lemma degree_X_sq_sub_C_ne_zero (c : F) : (X ^ 2 - C c : F[X]).degree ≠ 0 := by
  rw [degree_X_pow_sub_C (by norm_num)]
  norm_num

/-- The unit group of `F[X]/(X²-c)` has `|F|² - 1` elements, for `c` a non-square. -/
lemma natCard_quadAlg_units [Fintype F] (c : F) (hc : ¬ IsSquare c) :
    Nat.card (AdjoinRoot (X ^ 2 - C c : F[X]))ˣ = Nat.card F ^ 2 - 1 := by
  rw [quadAlgUnitsCard F (X ^ 2 - C c : F[X]) (monic_X_pow_sub_C c (by norm_num))
    (irreducible_X_sq_sub_C hc), natDegree_X_pow_sub_C]

end Aux

/-- Arithmetic core of `theTorus_card`: a solution of `n * (q - 1) = q ^ 2 - 1` with `2 ≤ q`
is `q + 1`. -/
lemma arith_pred (n q : ℕ) (hq : 2 ≤ q) (h : n * (q - 1) = q ^ 2 - 1) : n = q + 1 := by
  have h1 : q - 1 + 1 = q := Nat.sub_add_cancel (by omega)
  have h2 : (q + 1) * (q - 1) = q ^ 2 - 1 := by
    have h3 : q ^ 2 = (q + 1) * (q - 1) + 1 := by nlinarith [h1]
    exact ((Nat.sub_eq_iff_eq_add (by omega)).mpr h3).symm
  have h4 : n * (q - 1) = (q + 1) * (q - 1) := by rw [h, h2]
  exact Nat.eq_of_mul_eq_mul_right (by omega) h4

/-! ## The three facts about the torus -/

section Main

variable {F : Type*} [Field F] [DecidableEq F] [Fintype F]

/-- **The non-split torus is cyclic**: it is the image of the unit group of the quadratic
algebra `F[X]/(X²-c) ≅ F[B]`, which is a finite subgroup of the units of a field. -/
theorem theTorus_isCyclic (B : GL (Fin 2) F) (c : F)
    (hB : (B : Matrix (Fin 2) (Fin 2) F) * B = c • 1) (hc : ¬ IsSquare c) :
    IsCyclic ↥(theTorus B c hB) := by
  haveI : Fact (Irreducible (X ^ 2 - C c : F[X])) := ⟨irreducible_X_sq_sub_C hc⟩
  have hcard := natCard_quadAlg_units (F := F) c hc
  haveI : Finite (AdjoinRoot (X ^ 2 - C c : F[X]))ˣ :=
    Nat.finite_of_card_ne_zero (by
      rw [hcard]
      have h : 2 ≤ Nat.card F ^ 2 := by nlinarith [two_le_natCard F]
      omega)
  haveI : IsCyclic (AdjoinRoot (X ^ 2 - C c : F[X]))ˣ := inferInstance
  change IsCyclic ↥((torusPerm B c hB).range)
  exact isCyclic_of_surjective (torusPerm B c hB).rangeRestrict
    (MonoidHom.rangeRestrict_surjective _)

/-- **The order of the non-split torus**: `|T| = (|F|² - 1)/(|F| - 1) = |F| + 1`. -/
theorem theTorus_card (B : GL (Fin 2) F) (c : F)
    (hB : (B : Matrix (Fin 2) (Fin 2) F) * B = c • 1) (hc : ¬ IsSquare c) :
    Nat.card ↥(theTorus B c hB) = Nat.card F + 1 := by
  have hq := two_le_natCard F
  have hker := kerTorusPerm F B c hB hc
  have hcardKer : Nat.card ↥((torusPerm B c hB).ker) = Nat.card F - 1 := by
    rw [hker]
    exact ofUnitsRangeCard F (X ^ 2 - C c : F[X]) (degree_X_sq_sub_C_ne_zero c)
  have hcardRunits := natCard_quadAlg_units (F := F) c hc
  have hquot : Nat.card ((AdjoinRoot (X ^ 2 - C c : F[X]))ˣ ⧸ (torusPerm B c hB).ker)
      = Nat.card ↥(theTorus B c hB) := by
    simpa [theTorus] using
      Nat.card_congr (QuotientGroup.quotientKerEquivRange (torusPerm B c hB)).toEquiv
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (torusPerm B c hB).ker
  rw [hcardRunits, hcardKer, hquot] at h1
  exact arith_pred _ _ hq h1.symm

/-- **The non-split torus centralizes `B`**: every element of `theTorus B c hB` is the image
of a polynomial in `B` under the Möbius action, hence commutes with the image of `B`. -/
theorem theTorus_le_centralizer (B : GL (Fin 2) F) (c : F)
    (hB : (B : Matrix (Fin 2) (Fin 2) F) * B = c • 1) (hc : ¬ IsSquare c) :
    theTorus B c hB ≤ Subgroup.centralizer
      ({(Work.AUTL2.pglHom F (Matrix.ProjGenLinGroup.mk B))} :
        Set (Equiv.Perm (Work.AUTL2.P1 F))) := by
  have key : ∀ u : (AdjoinRoot (X ^ 2 - C c : F[X]))ˣ,
      Work.AUTL2.pglHom F (Matrix.ProjGenLinGroup.mk B) * torusPerm B c hB u
        = torusPerm B c hB u * Work.AUTL2.pglHom F (Matrix.ProjGenLinGroup.mk B) := by
    intro u
    have hcomm : Matrix.ProjGenLinGroup.mk B * Matrix.ProjGenLinGroup.mk (torusGL B c hB u)
        = Matrix.ProjGenLinGroup.mk (torusGL B c hB u) * Matrix.ProjGenLinGroup.mk B := by
      calc Matrix.ProjGenLinGroup.mk B * Matrix.ProjGenLinGroup.mk (torusGL B c hB u)
          = Matrix.ProjGenLinGroup.mk (B * torusGL B c hB u) := by rw [map_mul]
        _ = Matrix.ProjGenLinGroup.mk (torusGL B c hB u * B) := by
              rw [torusGLCommute F B c hB u]
        _ = Matrix.ProjGenLinGroup.mk (torusGL B c hB u) * Matrix.ProjGenLinGroup.mk B := by
              rw [map_mul]
    rw [torusPerm_apply]
    calc Work.AUTL2.pglHom F (Matrix.ProjGenLinGroup.mk B)
            * Work.AUTL2.pglHom F (Matrix.ProjGenLinGroup.mk (torusGL B c hB u))
        = Work.AUTL2.pglHom F (Matrix.ProjGenLinGroup.mk B
            * Matrix.ProjGenLinGroup.mk (torusGL B c hB u)) := by rw [map_mul]
      _ = Work.AUTL2.pglHom F (Matrix.ProjGenLinGroup.mk (torusGL B c hB u)
            * Matrix.ProjGenLinGroup.mk B) := by rw [hcomm]
      _ = Work.AUTL2.pglHom F (Matrix.ProjGenLinGroup.mk (torusGL B c hB u))
            * Work.AUTL2.pglHom F (Matrix.ProjGenLinGroup.mk B) := by rw [map_mul]
  rintro x ⟨u, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  exact key u

end Main

theorem theTorusFacts (p k : ℕ) [Fact p.Prime] (hp : Odd p) (hk : k ≠ 0) [DecidableEq (GaloisField p k)]
    (B : GL (Fin 2) (GaloisField p k)) (c : GaloisField p k)
    (hB : (B : Matrix (Fin 2) (Fin 2) (GaloisField p k)) * B = c • 1)
    (hc : ¬ IsSquare c) :
    IsCyclic ↥(Work.DSTR.M110.theTorus B c hB) ∧
      Nat.card ↥(Work.DSTR.M110.theTorus B c hB) = p ^ k + 1 ∧
      (Work.DSTR.M110.theTorus B c hB ≤
        Subgroup.centralizer ({(Work.AUTL2.pglHom (GaloisField p k) (Matrix.ProjGenLinGroup.mk B))} :
          Set (Equiv.Perm (Work.AUTL2.P1 (GaloisField p k))))) := by
  haveI : Fintype (GaloisField p k) := Fintype.ofFinite _
  refine ⟨theTorus_isCyclic B c hB hc, ?_, theTorus_le_centralizer B c hB hc⟩
  rw [theTorus_card B c hB hc, GaloisField.card p k hk]

end Work.DSTR.M110
