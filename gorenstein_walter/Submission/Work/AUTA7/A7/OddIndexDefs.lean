/-
Area AUTA7/A7: concrete elements of `A₇` used in the odd-index case.

The route for the odd-index case (`Submission/Work/AUTA7/A7/OddIndex.lean`) needs three
`3`-cycles of `A₇` which are the "fixed-point `3`-cycles" of three involutions of the model
Sylow `2`-subgroup `dihToA7.range = ⟨(0 1 2 3)(4 5), (0 2)(4 5)⟩` of `A₇`, namely

* `(4 5 6) = Work.A7.a7ThreeCycle`, the fixed-point `3`-cycle of `(0 1)(2 3) = dihToA7 (sr 1)`,
* `(0 2 6) = c026`, the fixed-point `3`-cycle of `(1 3)(4 5) = dihToA7 (sr 2)`,
* `(1 3 6) = c136`, the fixed-point `3`-cycle of `(0 2)(4 5) = a7S = dihToA7 (sr 0)`.

This file collects the definitions and the concrete verifications (orders, centralizing
relations, membership in the model Sylow subgroup) which are used both here and in the
assembly file.
-/
import Mathlib
import Submission.Work.AUTA7.Defs
import Submission.Work.AUTA7.A7.SylowTwoSubgroup
import Submission.Work.AUTA7.A7.CentralizerInvolution

open scoped MatrixGroups

set_option maxRecDepth 10000

namespace Work.AUTA7.A7

open Subgroup

/-! ## The concrete elements -/

/-- The `3`-cycle `(0 2 6)` of `A₇`, as a permutation. -/
def cyc026Perm : Equiv.Perm (Fin 7) := Equiv.swap 0 2 * Equiv.swap 2 6

@[simp]
theorem coe_cyc026Perm : cyc026Perm = Equiv.swap 0 2 * Equiv.swap 2 6 := rfl

/-- The `3`-cycle `(0 2 6)` of `A₇`. -/
def c026 : alternatingGroup (Fin 7) :=
  ⟨cyc026Perm, by
    rw [Equiv.Perm.mem_alternatingGroup, cyc026Perm, Equiv.Perm.sign_mul,
      Equiv.Perm.sign_swap (by decide), Equiv.Perm.sign_swap (by decide)]
    decide⟩

/-- The `3`-cycle `(1 3 6)` of `A₇`, as a permutation. -/
def cyc136Perm : Equiv.Perm (Fin 7) := Equiv.swap 1 3 * Equiv.swap 3 6

@[simp]
theorem coe_cyc136Perm : cyc136Perm = Equiv.swap 1 3 * Equiv.swap 3 6 := rfl

/-- The `3`-cycle `(1 3 6)` of `A₇`. -/
def c136 : alternatingGroup (Fin 7) :=
  ⟨cyc136Perm, by
    rw [Equiv.Perm.mem_alternatingGroup, cyc136Perm, Equiv.Perm.sign_mul,
      Equiv.Perm.sign_swap (by decide), Equiv.Perm.sign_swap (by decide)]
    decide⟩

/-- The involution `(1 3)(4 5)` of the model Sylow `2`-subgroup of `A₇`. -/
def zB : alternatingGroup (Fin 7) := Work.A7.a7Dswap 1 3 4 5 (by decide) (by decide)

/-- The permutation `(0 1 3 4)(2 5)`, which conjugates the model pair
`((0 1)(2 3), (4 5 6))` to `((1 3)(4 5), (0 2 6))`. -/
def gBPerm : Equiv.Perm (Fin 7) :=
  Equiv.swap 0 1 * Equiv.swap 1 3 * Equiv.swap 3 4 * Equiv.swap 2 5

/-- The even permutation `(0 1 3 4)(2 5)` of `A₇`. -/
def gB : alternatingGroup (Fin 7) :=
  ⟨gBPerm, by
    rw [Equiv.Perm.mem_alternatingGroup, gBPerm, Equiv.Perm.sign_mul, Equiv.Perm.sign_mul,
      Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide), Equiv.Perm.sign_swap (by decide),
      Equiv.Perm.sign_swap (by decide), Equiv.Perm.sign_swap (by decide)]
    decide⟩

/-- The permutation `(1 2 5 3 4)`, which conjugates the model pair
`((0 1)(2 3), (4 5 6))` to `((0 2)(4 5), (1 3 6))`. -/
def gCPerm : Equiv.Perm (Fin 7) :=
  Equiv.swap 1 2 * Equiv.swap 2 5 * Equiv.swap 5 3 * Equiv.swap 3 4

/-- The even permutation `(1 2 5 3 4)` of `A₇`. -/
def gC : alternatingGroup (Fin 7) :=
  ⟨gCPerm, by
    rw [Equiv.Perm.mem_alternatingGroup, gCPerm, Equiv.Perm.sign_mul, Equiv.Perm.sign_mul,
      Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide), Equiv.Perm.sign_swap (by decide),
      Equiv.Perm.sign_swap (by decide), Equiv.Perm.sign_swap (by decide)]
    decide⟩

/-- `(0 1 3 4)(2 5)` conjugates `(0 1)(2 3)` to `(1 3)(4 5)`. -/
theorem gB_conj_invol : gB * Work.A7.a7Invol * gB⁻¹ = zB := by decide

/-- `(0 1 3 4)(2 5)` conjugates `(4 5 6)` to `(0 2 6)`. -/
theorem gB_conj_threeCycle : gB * Work.A7.a7ThreeCycle * gB⁻¹ = c026 := by decide

/-- `(1 2 5 3 4)` conjugates `(0 1)(2 3)` to `(0 2)(4 5)`. -/
theorem gC_conj_invol : gC * Work.A7.a7Invol * gC⁻¹ = a7S := by decide

/-- `(1 2 5 3 4)` conjugates `(4 5 6)` to `(1 3 6)`. -/
theorem gC_conj_threeCycle : gC * Work.A7.a7ThreeCycle * gC⁻¹ = c136 := by decide

/-! ## Identification of the elements as values of `dihToA7` -/

/-- `(0 1)(2 3)` is `dihToA7 (sr 1)`. -/
theorem a7Invol_eq_dihToA7 : dihToA7 (DihedralGroup.sr 1) = Work.A7.a7Invol := by decide

/-- `(1 3)(4 5)` is `dihToA7 (sr 2)`. -/
theorem zB_eq_dihToA7 : dihToA7 (DihedralGroup.sr 2) = zB := by decide

/-- `(0 2)(4 5) = a7S` is `dihToA7 (sr 0)`. -/
theorem a7S_eq_dihToA7 : dihToA7 (DihedralGroup.sr 0) = a7S := by decide

/-- `(0 1 2 3)(4 5) = a7R` is `dihToA7 (r 1)`. -/
theorem a7R_eq_dihToA7 : dihToA7 (DihedralGroup.r 1) = a7R := by decide

/-! ## Orders -/

/-- The model `4`-cycle `(0 1 2 3)(4 5)` has order `4`. -/
theorem orderOf_a7R : orderOf a7R = 4 := by
  rw [orderOf_eq_iff (by norm_num)]
  exact ⟨by decide, fun m _ _ => by interval_cases m <;> decide⟩

/-- `(0 2 6)` has order `3`. -/
theorem orderOf_c026 : orderOf c026 = 3 := by
  rw [orderOf_eq_iff (by norm_num)]
  exact ⟨by decide, fun m _ _ => by interval_cases m <;> decide⟩

/-- `(1 3 6)` has order `3`. -/
theorem orderOf_c136 : orderOf c136 = 3 := by
  rw [orderOf_eq_iff (by norm_num)]
  exact ⟨by decide, fun m _ _ => by interval_cases m <;> decide⟩

/-- `(4 5 6) * (0 2 6)` has order `5`. -/
theorem orderOf_a7ThreeCycle_mul_c026 : orderOf (Work.A7.a7ThreeCycle * c026) = 5 := by
  rw [orderOf_eq_iff (by norm_num)]
  exact ⟨by decide, fun m _ _ => by interval_cases m <;> decide⟩

/-- `(4 5 6) * (0 2 6) * (1 3 6)` has order `7`. -/
theorem orderOf_a7ThreeCycle_mul_c026_mul_c136 :
    orderOf (Work.A7.a7ThreeCycle * c026 * c136) = 7 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨?_, fun m _ _ => by interval_cases m <;> decide⟩
  apply Subtype.ext
  decide

/-! ## Centralizing relations -/

/-- `(0 1)(2 3)` centralizes `(4 5 6)`. -/
theorem a7Invol_mul_a7ThreeCycle :
    Work.A7.a7Invol * Work.A7.a7ThreeCycle = Work.A7.a7ThreeCycle * Work.A7.a7Invol := by
  decide

/-- `(1 3)(4 5)` centralizes `(0 2 6)`. -/
theorem zB_mul_c026 : zB * c026 = c026 * zB := by decide

/-- `(0 2)(4 5) = a7S` centralizes `(1 3 6)`. -/
theorem a7S_mul_c136 : a7S * c136 = c136 * a7S := by decide

/-! ## Basic facts about the elements -/

theorem a7Invol_mul_self' : Work.A7.a7Invol * Work.A7.a7Invol = 1 := by decide

theorem zB_mul_self : zB * zB = 1 := by decide

theorem zB_ne_one : zB ≠ 1 := by decide

theorem a7S_ne_one : a7S ≠ 1 := by decide

theorem a7ThreeCycle_ne_one : Work.A7.a7ThreeCycle ≠ 1 := by decide

theorem c026_ne_one : c026 ≠ 1 := by decide

theorem c136_ne_one : c136 ≠ 1 := by decide

/-! ## Membership in the model Sylow `2`-subgroup -/

/-- Every element of `⟨(0 1 2 3)(4 5), (0 2)(4 5)⟩` is in the range of `dihToA7`. -/
theorem closure_RS_le_range :
    Subgroup.closure ({a7R, a7S} : Set (alternatingGroup (Fin 7))) ≤ dihToA7.range := by
  rw [Subgroup.closure_le]
  rintro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact MonoidHom.mem_range.mpr ⟨DihedralGroup.r 1, by simp [a7R_eq_dihToA7]⟩
  · exact MonoidHom.mem_range.mpr ⟨DihedralGroup.sr 0, by simp [a7S_eq_dihToA7]⟩

/-- Every value of `dihToA7` lies in `⟨(0 1 2 3)(4 5), (0 2)(4 5)⟩`. -/
theorem range_le_closure_RS :
    dihToA7.range ≤ Subgroup.closure ({a7R, a7S} : Set (alternatingGroup (Fin 7))) := by
  rintro x ⟨g, rfl⟩
  rcases g with i | i
  · -- `dihToA7 (r i) = a7R ^ (i.val : ℤ)`
    have h : dihToA7 (DihedralGroup.r i) = a7R ^ ((i.val : ℕ) : ℤ) := by
      apply Subtype.ext
      rw [coe_dihToA7, dihToPerm_apply]
      rfl
    rw [h]
    exact Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp)) _
  · have h : dihToA7 (DihedralGroup.sr i) = a7S * a7R ^ ((i.val : ℕ) : ℤ) := by
      apply Subtype.ext
      rw [coe_dihToA7, dihToPerm_apply]
      rfl
    rw [h]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
      (Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp)) _)

/-- The model Sylow `2`-subgroup is `⟨(0 1 2 3)(4 5), (0 2)(4 5)⟩`. -/
theorem range_eq_closure_RS :
    dihToA7.range = Subgroup.closure ({a7R, a7S} : Set (alternatingGroup (Fin 7))) :=
  le_antisymm range_le_closure_RS closure_RS_le_range

theorem zB_mem_range : zB ∈ dihToA7.range := by
  rw [← zB_eq_dihToA7]
  exact MonoidHom.mem_range.mpr ⟨_, rfl⟩

theorem a7Invol_mem_range : Work.A7.a7Invol ∈ dihToA7.range := by
  rw [← a7Invol_eq_dihToA7]
  exact MonoidHom.mem_range.mpr ⟨_, rfl⟩

theorem a7S_mem_range : a7S ∈ dihToA7.range := by
  rw [← a7S_eq_dihToA7]
  exact MonoidHom.mem_range.mpr ⟨_, rfl⟩

end Work.AUTA7.A7
