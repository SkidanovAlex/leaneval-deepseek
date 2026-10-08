import Mathlib
import Submission.Work.L2F.Defs
import Submission.Work.L2F.Mat2.pslMap_eq_one_iff

open scoped MatrixGroups
open Matrix

namespace Work.L2F.PSL

/-- `diag a = 1` if and only if `a = 1`.  The forward direction reads off the `(0,0)` entry. -/
lemma diag_eq_one_iff (F : Type*) [Field F] (a : Fˣ) :
    Work.PSL2.diag F a = 1 ↔ a = 1 := by
  constructor
  · intro h
    have h' : ((Work.PSL2.diag F a : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
        ((1 : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) := by rw [h]
    rw [Work.PSL2.coe_diag, Matrix.SpecialLinearGroup.coe_one] at h'
    have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 0 0) h'
    simpa using h00
  · intro h
    subst h
    show Work.PSL2.diagHom F 1 = 1
    exact map_one _

/-- `diag a = -1` if and only if `a = -1`.  The forward direction reads off the `(0,0)` entry;
the reverse direction is a direct entry check. -/
lemma diag_eq_negOne_iff (F : Type*) [Field F] (a : Fˣ) :
    Work.PSL2.diag F a = Work.L2F.negOne F ↔ a = -1 := by
  constructor
  · intro h
    have h' : ((Work.PSL2.diag F a : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
        ((Work.L2F.negOne F : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) := by rw [h]
    rw [Work.PSL2.coe_diag] at h'
    have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 0 0) h'
    simp [Work.L2F.negOne] at h00
    simpa using h00
  · intro h
    rw [h]
    apply Subtype.ext
    change ((Work.PSL2.diag F (-1) : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
      ((Work.L2F.negOne F : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)
    rw [Work.PSL2.coe_diag]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Work.L2F.negOne]

/-- The kernel of `pslDiagHom : Fˣ →* PSL(2,F)` is `{±1}`: `pslMap x = 1` iff `x = ±1`
(`pslMap_eq_one_iff`), and `diag a = ±1` iff `a = ±1`. -/
lemma pslDiagHom_eq_one_iff (F : Type*) [Field F] (h2 : (2 : F) ≠ 0) (a : Fˣ) :
    Work.PSL2.pslDiagHom F a = 1 ↔ a = 1 ∨ a = -1 := by
  rw [show Work.PSL2.pslDiagHom F a = Work.PSL2.pslMap F (Work.PSL2.diag F a) from rfl]
  rw [Work.L2F.Mat2.pslMap_eq_one_iff F h2]
  constructor
  · rintro (h | h)
    · exact Or.inl ((diag_eq_one_iff F a).mp h)
    · exact Or.inr ((diag_eq_negOne_iff F a).mp h)
  · rintro (h | h)
    · exact Or.inl ((diag_eq_one_iff F a).mpr h)
    · exact Or.inr ((diag_eq_negOne_iff F a).mpr h)

/-- The image in `PSL(2,F)` of the diagonal torus has `(q-1)/2` elements, i.e.
`2 * Nat.card (pslSplitTorus F) = Nat.card F - 1`.  Proof: `diagHom` is injective and its range
`torus F` is cyclic of order `q - 1` (`Nat.card Fˣ = q - 1`); the kernel of `pslMap` on it is
`{±1}` (`pslMap_eq_one_iff`), and `-1 = diag (-1)` lies in it. -/
theorem pslSplitTorus_card (F : Type*) [Field F] [Fintype F] (h2 : (2 : F) ≠ 0) :
    2 * Nat.card (Work.L2F.pslSplitTorus F) = Nat.card F - 1 := by
  classical
  -- The kernel of `pslDiagHom` is `{±1}`, i.e. `zpowers (-1)`.
  have hK : (Work.PSL2.pslDiagHom F).ker = Subgroup.zpowers (-1 : Fˣ) := by
    apply le_antisymm
    · intro a ha
      rw [MonoidHom.mem_ker] at ha
      rcases (pslDiagHom_eq_one_iff F h2 a).mp ha with h | h
      · rw [h]; exact Subgroup.one_mem _
      · rw [h]; exact Subgroup.mem_zpowers _
    · have hmem : (-1 : Fˣ) ∈ (Work.PSL2.pslDiagHom F).ker := by
        rw [MonoidHom.mem_ker]
        exact (pslDiagHom_eq_one_iff F h2 (-1)).mpr (Or.inr rfl)
      exact Subgroup.zpowers_le.mpr hmem
  -- hence the kernel has two elements.
  have hneg : (-1 : Fˣ) ≠ 1 := by
    intro h
    have hv : ((-1 : Fˣ) : F) = ((1 : Fˣ) : F) := congrArg Units.val h
    simp only [Units.val_neg, Units.val_one] at hv
    have h' : (1 : F) + 1 = 0 := neg_eq_iff_add_eq_zero.mp hv
    exact h2 (by rwa [one_add_one_eq_two] at h')
  have hKcard : Nat.card ((Work.PSL2.pslDiagHom F).ker) = 2 := by
    rw [hK, Nat.card_zpowers]
    exact orderOf_eq_prime (neg_one_sq) hneg
  -- the split torus is exactly the range of `pslDiagHom`.
  have hrange : Work.L2F.pslSplitTorus F = (Work.PSL2.pslDiagHom F).range := by
    simp only [Work.L2F.pslSplitTorus, Work.L2F.torus, Work.PSL2.pslDiagHom]
    exact MonoidHom.map_range (Work.PSL2.pslMap F) (Work.PSL2.diagHom F)
  -- first isomorphism theorem: `|Fˣ| = |range| * |ker|`.
  have hmain : Nat.card Fˣ = Nat.card ((Work.PSL2.pslDiagHom F).range) * 2 := by
    have hq := Subgroup.card_eq_card_quotient_mul_card_subgroup (Work.PSL2.pslDiagHom F).ker
    have heq : Nat.card (Fˣ ⧸ (Work.PSL2.pslDiagHom F).ker) =
        Nat.card ((Work.PSL2.pslDiagHom F).range) :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange (Work.PSL2.pslDiagHom F)).toEquiv
    rw [heq, hKcard] at hq
    exact hq
  have hunits : Nat.card Fˣ = Nat.card F - 1 := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_units]
  rw [hrange]
  rw [show 2 * Nat.card ((Work.PSL2.pslDiagHom F).range) = Nat.card F - 1 from by
    rw [mul_comm, ← hmain, hunits]]

end Work.L2F.PSL
