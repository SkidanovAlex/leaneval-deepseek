import Mathlib
import Submission.Work.L2F.Defs
import Submission.Work.L2F.Props.PGL2CommutatorTorusDefs

open scoped MatrixGroups
open Matrix

namespace Work.L2F.Props

/-! ## The kernel of `SL(2,F) → PGL(2,F)`

The image `L₂(F) ⊆ PGL₂(F)` of `SL(2,F)` is the quotient of `SL(2,F)` by its centre; in odd
characteristic the centre consists of `±1`, i.e. of the identity and the element
`Work.L2F.negOne F` (the matrix `-1`).  Consequently, for any subgroup `H ≤ SL(2,F)` containing
`-1` — in particular for the centralizer `cmtK0 F S`, in which `-1` is central — the restriction
of `SL(2,F) → PGL(2,F)` to `H` has kernel exactly `{1, -1}`, of cardinality `2`.

The helper lemmas below are stated for the concrete group `SL(2,F)`; they are the published
facts "the centre of `SL(2,F)` is `{±1}`" and "`-1` lies in every centralizer". -/

/-- The central element `-1` of `SL(2,F)` is the image of `negOneGL F` under
`SpecialLinearGroup.toGL`. -/
theorem cmtK0_ker_toGL_negOne (F : Type*) [Field F] :
    Matrix.SpecialLinearGroup.toGL (Work.L2F.negOne F) = Work.L2F.Props.negOneGL F := by
  apply Units.ext
  rfl

/-- The matrix `-1` squares to `1` in `SL(2,F)`. -/
theorem cmtK0_ker_negOne_mul_self (F : Type*) [Field F] :
    Work.L2F.negOne F * Work.L2F.negOne F = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  show (-1 : Matrix (Fin 2) (Fin 2) F) * (-1) = 1
  rw [Matrix.neg_mul, Matrix.one_mul, neg_neg]

/-- In odd characteristic the element `-1` of `SL(2,F)` is nontrivial: its underlying matrix has
entry `-1` in position `(0,0)` while the identity has entry `1` there, so `-1 = 1` would force
`2 = 0` in `F`. -/
theorem cmtK0_ker_negOne_ne_one (F : Type*) [Field F] (h2 : (2 : F) ≠ 0) :
    Work.L2F.negOne F ≠ 1 := by
  intro h
  have h' : ((Work.L2F.negOne F : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = 1 := by
    rw [h, Matrix.SpecialLinearGroup.coe_one]
  have hmm : ((Work.L2F.negOne F : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
      (-1 : Matrix (Fin 2) (Fin 2) F) := rfl
  rw [hmm] at h'
  have h00 : (-1 : F) = 1 := by simpa using congrFun (congrFun h' 0) 0
  have h2zero : (2 : F) = 0 := by
    have hsum : (1 : F) + 1 = 0 := by
      nth_rewrite 1 [← h00]
      ring
    rw [show (2 : F) = (1 : F) + 1 by norm_num]
    exact hsum
  exact h2 h2zero

/-- The matrix `-1` lies in the centralizer `cmtK0 F S` of every `S ∈ GL(2,F)`: it is central in
`SL(2,F)`, hence commutes with `S`. -/
theorem cmtK0_ker_negOne_mem (F : Type*) [Field F] (S : Matrix.GeneralLinearGroup (Fin 2) F) :
    Work.L2F.negOne F ∈ Work.L2F.Props.cmtK0 F S := by
  rw [Work.L2F.Props.mem_cmtK0_iff_comm, cmtK0_ker_toGL_negOne]
  exact Work.L2F.Props.negOneGL_mul_comm F S

/-- **The centre of `SL(2,F)`.** A central element `x` is a scalar matrix
(`Matrix.SpecialLinearGroup.mem_center_iff`), say `x` has diagonal entries `r`; its determinant is
`1`, i.e. `r ^ 2 = 1`, and a field has no zero divisors, so `r = ±1` and correspondingly `x` is the
identity or the matrix `-1`. Conversely both the identity and `-1` are central. -/
theorem mem_center_SL_two (F : Type*) [Field F] (x : Matrix.SpecialLinearGroup (Fin 2) F) :
    x ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) ↔
      x = 1 ∨ x = Work.L2F.negOne F := by
  have hmm : ((Work.L2F.negOne F : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
      (-1 : Matrix (Fin 2) (Fin 2) F) := rfl
  constructor
  · intro hx
    obtain ⟨r, hr, hsc⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hx
    simp only [Fintype.card_fin] at hr
    rcases sq_eq_one_iff.mp hr with hr1 | hrm
    · left
      apply Subtype.ext
      rw [← hsc, hr1, Matrix.scalar_apply, Matrix.diagonal_one,
        Matrix.SpecialLinearGroup.coe_one]
    · right
      apply Subtype.ext
      rw [← hsc, hrm, Matrix.scalar_apply, hmm, ← Matrix.diagonal_one (n := Fin 2) (α := F),
        ← Matrix.diagonal_neg]
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hmm]
      rw [Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul, Matrix.one_mul]

/-- The restriction of `SL(2,F) → PGL(2,F)` to the centralizer `cmtK0 F S` of any `S ∈ GL(2,F)`
(odd characteristic) still has kernel `{±1}`: `-1` centralizes `S`, and the kernel of `toPGL` is
`{±1}`.  Hence the map `cmtK0 F S → (cmtK0 F S).map toPGL` is exactly `2`-to-`1`. -/
theorem card_ker_cmtK0_toPGL (F : Type*) [Field F] (h2 : (2 : F) ≠ 0)
    (S : Matrix.GeneralLinearGroup (Fin 2) F) :
    Nat.card (MonoidHom.ker
      ((Matrix.SpecialLinearGroup.toPGL (n := Fin 2) (R := F)).comp
        (Work.L2F.Props.cmtK0 F S).subtype)) = 2 := by
  have hmem : Work.L2F.negOne F ∈ Work.L2F.Props.cmtK0 F S := cmtK0_ker_negOne_mem F S
  let n : Work.L2F.Props.cmtK0 F S := ⟨Work.L2F.negOne F, hmem⟩
  -- The kernel is the image of the centre of `SL(2,F)`, i.e. `{1, -1} = ⟨n⟩`.
  have hker : MonoidHom.ker ((Matrix.SpecialLinearGroup.toPGL (n := Fin 2) (R := F)).comp
        (Work.L2F.Props.cmtK0 F S).subtype) = Subgroup.zpowers n := by
    ext x
    rw [Subgroup.mem_zpowers_iff]
    constructor
    · intro hx
      rw [MonoidHom.mem_ker] at hx
      have hx' : ((x : Work.L2F.Props.cmtK0 F S) : SL(2, F)) ∈
          Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
        rw [← Matrix.SpecialLinearGroup.toPGL_ker, MonoidHom.mem_ker]
        exact hx
      rcases (mem_center_SL_two F _).mp hx' with h1 | h1
      · exact ⟨0, by rw [zpow_zero]; exact (Subtype.ext h1).symm⟩
      · exact ⟨1, by rw [zpow_one]; exact (Subtype.ext h1).symm⟩
    · rintro ⟨k, hk⟩
      have hnker : n ∈ MonoidHom.ker ((Matrix.SpecialLinearGroup.toPGL (n := Fin 2) (R := F)).comp
          (Work.L2F.Props.cmtK0 F S).subtype) := by
        rw [MonoidHom.mem_ker]
        show Matrix.SpecialLinearGroup.toPGL ((n : Work.L2F.Props.cmtK0 F S) : SL(2, F)) = 1
        rw [← MonoidHom.mem_ker, Matrix.SpecialLinearGroup.toPGL_ker]
        exact (mem_center_SL_two F _).mpr (Or.inr rfl)
      exact Subgroup.zpowers_le.mpr hnker ⟨k, hk⟩
  rw [hker, Nat.card_zpowers]
  -- `n` has order `2`: it is nontrivial but squares to `1`.
  refine orderOf_eq_prime ?_ ?_
  · apply Subtype.ext
    show ((Work.L2F.negOne F) ^ 2 : SL(2, F)) = 1
    rw [pow_two]
    exact cmtK0_ker_negOne_mul_self F
  · intro hn1
    exact cmtK0_ker_negOne_ne_one F h2
      (congrArg (fun t : Work.L2F.Props.cmtK0 F S => (t : SL(2, F))) hn1)

end Work.L2F.Props
