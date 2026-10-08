/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `|PGL(2,q)| = 2 |PSL(2,q)|` for `q` of odd characteristic

The projective general linear group is the quotient of `GL(2,F)` by its centre, which is
the group of scalar matrices; hence `|PGL(2,F)| = |GL(2,F)| / |Fˣ|`.  Since `GL(2,F) → Fˣ`
by the determinant is surjective with kernel `SL(2,F)`, we get
`|GL(2,F)| = |SL(2,F)| · |Fˣ|`, so `|PGL(2,F)| = |SL(2,F)|`.  Finally, for `F` of odd
characteristic, `Z(SL(2,F))` has order `2`, so `|SL(2,F)| = 2 |PSL(2,F)|`
(lemma `Work.PSL2.card_PSL2_of_odd`).  Combining the two gives the claimed formula.

The particular case needed in the Gorenstein–Walter development is `F = GF(p^k)` with
`p` an odd prime and `k ≠ 0`.
-/
import Mathlib
import Submission.Work.PSL2.Card

namespace Work.CORE2A

open scoped MatrixGroups
open Matrix

/-- The scalar matrices give an injective map `Fˣ → GL(2,F)`. -/
theorem scalar_GL2_injective (F : Type*) [Field F] [Fintype F] :
    Function.Injective (Matrix.GeneralLinearGroup.scalar (Fin 2) (R := F)) := by
  intro u v huv
  ext
  have h := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F) 0 0) huv
  simpa using h

/-- The centre of `GL(2,F)` is the image of the scalar matrices, hence has order `|Fˣ|`. -/
theorem card_center_GL2 (F : Type*) [Field F] [Fintype F] :
    Nat.card (Subgroup.center (GL (Fin 2) F)) = Nat.card Fˣ := by
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
  exact (Nat.card_congr (Equiv.ofInjective
    (Matrix.GeneralLinearGroup.scalar (Fin 2) (R := F)) (scalar_GL2_injective F))).symm

/-- `|PGL(2,F)| = |SL(2,F)|`: the quotient of `GL(2,F)` by the scalars cancels the
factor `|Fˣ|` in `|GL(2,F)| = |SL(2,F)| · |Fˣ|`. -/
theorem card_PGL2_eq_card_SL2 (F : Type*) [Field F] [Fintype F] :
    Nat.card (Matrix.ProjGenLinGroup (Fin 2) F) = Nat.card (SL(2, F)) := by
  have h1 : Nat.card Fˣ * Nat.card (Matrix.ProjGenLinGroup (Fin 2) F) =
      Nat.card (GL (Fin 2) F) := by
    have h := Subgroup.card_mul_index (Subgroup.center (GL (Fin 2) F))
    rw [Subgroup.index_eq_card] at h
    rw [card_center_GL2 F] at h
    exact h
  have h2 := Work.PSL2.card_GL_eq_card_SL_mul_card_units F
  have h3 : Nat.card Fˣ * Nat.card (Matrix.ProjGenLinGroup (Fin 2) F) =
      Nat.card Fˣ * Nat.card (SL(2, F)) := by
    rw [h1, h2, mul_comm]
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h3

/-- `|SL(2,F)| = 2 |PSL(2,F)|` for a finite field `F` of odd characteristic. -/
theorem card_SL2_eq_two_mul_card_PSL2 (F : Type*) [Field F] [Fintype F]
    (hF : ringChar F ≠ 2) :
    Nat.card (SL(2, F)) = 2 * Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) := by
  rw [Work.PSL2.card_SL2 F, ← Work.PSL2.card_PSL2_of_odd F hF]

/-- `|PGL(2, GF(p^k))| = 2 |PSL(2, GF(p^k))|` for `p` an odd prime and `k ≠ 0`. -/
theorem card_PGL2_eq_two_mul_card_PSL2 {p k : ℕ} [Fact p.Prime] (hp : Odd p) (hk : k ≠ 0) :
    Nat.card (Matrix.ProjGenLinGroup (Fin 2) (GaloisField p k)) =
      2 * Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)) := by
  letI : Fintype (GaloisField p k) := Fintype.ofFinite _
  letI : CharP (GaloisField p k) p := inferInstance
  have hchar : ringChar (GaloisField p k) ≠ 2 := by
    rw [ringChar.eq (GaloisField p k) p]
    intro h
    obtain ⟨m, hm⟩ := hp
    omega
  rw [card_PGL2_eq_card_SL2 (GaloisField p k),
    card_SL2_eq_two_mul_card_PSL2 _ hchar]

end Work.CORE2A
