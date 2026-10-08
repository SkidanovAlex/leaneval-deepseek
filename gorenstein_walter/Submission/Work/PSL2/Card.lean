/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Orders of `SL(2,q)` and `PSL(2,q)`

Main results (all `q = Nat.card F` for a finite field `F`):

* `card_SL2`            : `Nat.card SL(2,F) = q (q²-1)`.
* `card_PSL2_of_odd`    : `2 * Nat.card PSL(2,F) = q (q²-1)` for `q` of odd characteristic.
* `card_PSL2_galoisField`: `2 * Nat.card PSL(2, GF(p^k)) = p^k (p^(2k) - 1)`.

The abstract input is
* `card_GL_eq_card_SL_mul_card_units`: `|GL(2,q)| = |SL(2,q)| · |Fˣ|`, from the determinant
  `GL(2,F) →* Fˣ`, which is surjective with kernel isomorphic to `SL(2,F)`; and
* `card_center_SL2`: `|Z(SL(2,F))| = 2` for `ringChar F ≠ 2`, from Mathlib's
  `Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity` and `card_rootsOfUnity_two`.
-/
import Mathlib

open scoped MatrixGroups
open Matrix

namespace Work.PSL2

open Matrix.SpecialLinearGroup

/-! ## `|GL(2,F)| = |SL(2,F)| · |Fˣ|` -/

/-- The determinant `GL(2,F) →* Fˣ` has range `⊤` and kernel isomorphic to `SL(2,F)`. -/
theorem card_GL_eq_card_SL_mul_card_units (F : Type*) [Field F] [Fintype F] :
    Nat.card (GL (Fin 2) F) = Nat.card (SL(2, F)) * Nat.card Fˣ := by
  have h1 : Nat.card (GL (Fin 2) F) =
      Nat.card (Matrix.GeneralLinearGroup.det (n := Fin 2) (R := F)).ker *
        ((Matrix.GeneralLinearGroup.det (n := Fin 2) (R := F)).ker).index :=
    (Subgroup.card_mul_index _).symm
  have hker : Nat.card (Matrix.GeneralLinearGroup.det (n := Fin 2) (R := F)).ker =
      Nat.card (SL(2, F)) :=
    Nat.card_congr (Matrix.SpecialLinearGroup.toGLKerEquiv (n := Fin 2) (R := F)).toEquiv.symm
  have htop : Nat.card (⊤ : Subgroup Fˣ) = Nat.card Fˣ :=
    Nat.card_congr (Subgroup.topEquiv (G := Fˣ)).toEquiv
  have h2 : (Matrix.GeneralLinearGroup.det (n := Fin 2) (R := F)).range = ⊤ :=
    MonoidHom.range_eq_top_of_surjective _
      (Matrix.GeneralLinearGroup.det_surjective (n := Fin 2) (R := F))
  rw [h1, Subgroup.index_ker, h2, hker, htop]

/-- Mathlib's `Matrix.card_GL_field` made explicit in the case `n = 2`. -/
theorem card_GL_two (F : Type*) [Field F] [Fintype F] :
    Nat.card (GL (Fin 2) F) =
      (Fintype.card F ^ 2 - 1) * (Fintype.card F ^ 2 - Fintype.card F) := by
  rw [Matrix.card_GL_field (𝔽 := F) 2, Fin.prod_univ_two]
  simp

/-! ## The centre of `SL(2,F)` -/

/-- For a field of characteristic `≠ 2` there are exactly two square roots of `1`. -/
theorem card_rootsOfUnity_two (F : Type*) [Field F] [Fintype F] (hF : ringChar F ≠ 2) :
    Nat.card (rootsOfUnity 2 F) = 2 := by
  refine le_antisymm (card_rootsOfUnity F 2) ?_
  have hmem : (-1 : Fˣ) ∈ rootsOfUnity 2 F := by
    rw [mem_rootsOfUnity]
    ext
    simp
  have hne : (-1 : Fˣ) ≠ 1 := by
    intro h
    exact Ring.neg_one_ne_one_of_char_ne_two hF
      (by simpa using congrArg (fun u : Fˣ => (u : F)) h)
  let f : Fin 2 → rootsOfUnity 2 F := fun i => if i = 0 then 1 else ⟨-1, hmem⟩
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · simp only [f, Fin.isValue] at hij
      exact absurd (Subtype.ext_iff.mp hij).symm hne
    · simp only [f, Fin.isValue] at hij
      exact absurd (Subtype.ext_iff.mp hij) hne
    · rfl
  have := Nat.card_le_card_of_injective f hf
  simpa using this

/-- The centre of `SL(2,F)` has order `2` in odd characteristic. -/
theorem card_center_SL2 (F : Type*) [Field F] [Fintype F] (hF : ringChar F ≠ 2) :
    Nat.card (Subgroup.center (SL(2, F))) = 2 := by
  have h := Nat.card_congr (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity
    (n := Fin 2) (R := F)).toEquiv
  rw [h]
  have : max (Fintype.card (Fin 2)) 1 = 2 := by simp
  rw [this]
  exact card_rootsOfUnity_two F hF

/-! ## The main cardinals -/

/-- `|SL(2,q)| = q (q²-1)`. -/
theorem card_SL2 (F : Type*) [Field F] [Fintype F] :
    Nat.card (SL(2, F)) = Fintype.card F * (Fintype.card F ^ 2 - 1) := by
  set q := Fintype.card F with hq
  have hmain := card_GL_eq_card_SL_mul_card_units F
  rw [card_GL_two F] at hmain
  have hunits : Nat.card Fˣ = q - 1 := by
    rw [Nat.card_units, Nat.card_eq_fintype_card]
  rw [hunits] at hmain
  have hsub : q ^ 2 - q = q * (q - 1) := by
    rw [pow_two, Nat.mul_sub_left_distrib, mul_one]
  rw [hsub] at hmain
  have : Nat.card (SL(2, F)) * (q - 1) = (q * (q ^ 2 - 1)) * (q - 1) := by
    rw [← hmain]; ring
  exact Nat.eq_of_mul_eq_mul_right (by have := Fintype.one_lt_card (α := F); omega) this

/-- `|PSL(2,q)| = q(q²-1)/2`, stated without division, for `q` of odd characteristic. -/
theorem card_PSL2_of_odd (F : Type*) [Field F] [Fintype F] (hF : ringChar F ≠ 2) :
    2 * Nat.card (PSL(2, F)) = Fintype.card F * (Fintype.card F ^ 2 - 1) := by
  have hcard : 2 * Nat.card (PSL(2, F)) = Nat.card (SL(2, F)) := by
    have h := Subgroup.card_mul_index (Subgroup.center (SL(2, F)))
    rw [Subgroup.index_eq_card] at h
    rw [card_center_SL2 F hF] at h
    exact h
  rw [hcard, card_SL2]

/-- `2 * |PSL(2, GF(p^k))| = p^k (p^(2k) - 1)` for odd `p` and `k ≠ 0`. -/
theorem card_PSL2_galoisField (p k : ℕ) [Fact p.Prime] (hp : Odd p) (hk : k ≠ 0) :
    2 * Nat.card (PSL(2, GaloisField p k)) = p ^ k * (p ^ (2 * k) - 1) := by
  letI : Fintype (GaloisField p k) := Fintype.ofFinite _
  letI : CharP (GaloisField p k) p := inferInstance
  have hq : Fintype.card (GaloisField p k) = p ^ k := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card p k hk]
  have hchar : ringChar (GaloisField p k) ≠ 2 := by
    rw [ringChar.eq (GaloisField p k) p]
    intro h
    obtain ⟨m, hm⟩ := hp
    omega
  have h := card_PSL2_of_odd (GaloisField p k) hchar
  rw [hq] at h
  have h2 : (p ^ k) ^ 2 = p ^ (2 * k) := by
    rw [← pow_mul, Nat.mul_comm k 2]
  rwa [h2] at h

end Work.PSL2
