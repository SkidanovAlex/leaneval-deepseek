import Mathlib
import Submission.Work.L2F.Defs

/-!
# The normalizer of `⟨x⟩` for `x ∈ SL(2,F)` with `x² = -1`

Let `x ∈ SL(2,F)` satisfy `x * x = -1` (as matrices), so that `x ^ 2 = negOne F` in `SL(2,F)`
and `x ^ 4 = 1`; thus `⟨x⟩ = {1, x, -1, -x}` (with the obvious coincidences).

The main result is that the normalizer of `⟨x⟩` consists exactly of the `y` with
`y * x * y⁻¹ = x` or `y * x * y⁻¹ = -x`; both directions are pure group theory around the
cyclic group `⟨x⟩`, whose order divides `4`.

The group-theoretic content is isolated in the two lemmas `zpowers_of_pow_four` and
`mem_normalizer_zpowers_of` (no matrix theory), together with the elementary facts
`negOne_mul_comm` / `negOne_mul_self` about the matrix `-1` of `SL(2,F)`.
-/

namespace Work.L2F.Involution

open scoped MatrixGroups
open Matrix

section Generic

variable {G : Type*} [Group G]

/-- If `x ^ 4 = 1` then every element of `⟨x⟩` is one of `1`, `x`, `x ^ 2`, `x ^ 3`: writing the
element as `x ^ n` with `n : ℤ` and reducing the exponent modulo `4`. -/
theorem zpowers_of_pow_four {x u : G} (hx : x ^ 4 = 1) (hu : u ∈ Subgroup.zpowers x) :
    u = 1 ∨ u = x ∨ u = x ^ 2 ∨ u = x ^ 3 := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
  have h4 : x ^ (4 : ℤ) = 1 := by simpa using hx
  rw [zpow_eq_zpow_emod n h4]
  have h0 : 0 ≤ n % 4 := Int.emod_nonneg n (by norm_num)
  have h1 : n % 4 < 4 := Int.emod_lt_of_pos n (by norm_num)
  rcases (by omega : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3) with h | h | h | h
  · simp [h]
  · simp [h]
  · rw [h]; norm_num
  · rw [h]; norm_num

/-- If `y` conjugates both `x` and `x`'s inverse conjugate into `⟨x⟩`, then `y` normalizes
`⟨x⟩`: for `h = x ^ n` in `⟨x⟩` we have `y * h * y⁻¹ = (y * x * y⁻¹) ^ n`, and conversely
`h = y⁻¹ * (y * h * y⁻¹) * y = (y⁻¹ * x * y) ^ n`. -/
theorem mem_normalizer_zpowers_of {x y : G} (hu : y * x * y⁻¹ ∈ Subgroup.zpowers x)
    (hv : y⁻¹ * x * y ∈ Subgroup.zpowers x) : y ∈ Subgroup.normalizer (Subgroup.zpowers x) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    rw [← conj_zpow]
    exact Subgroup.zpow_mem (Subgroup.zpowers x) hu n
  · intro hh
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hh
    have hconj : h = (y⁻¹ * x * y) ^ n := by
      have h1 : y⁻¹ * (y * h * y⁻¹) * y = h := by group
      rw [← h1, ← hn]
      exact (show (y⁻¹ * x * y) ^ n = y⁻¹ * x ^ n * y from by
        simpa using conj_zpow (a := y⁻¹) (b := x) (i := n)).symm
    rw [hconj]
    exact Subgroup.zpow_mem (Subgroup.zpowers x) hv n

end Generic

/-! ## Elementary facts about the matrix `-1` of `SL(2,F)` -/

/-- `-1` is central in `SL(2,F)`: it is the scalar matrix `(-1) • 1`. -/
theorem negOne_mul_comm (F : Type*) [Field F] (g : Matrix.SpecialLinearGroup (Fin 2) F) :
    Work.L2F.negOne F * g = g * Work.L2F.negOne F := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    show ((Work.L2F.negOne F : Matrix.SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) = -1 from rfl]
  simp

/-- `(-1) * (-1) = 1` in `SL(2,F)`. -/
theorem negOne_mul_self (F : Type*) [Field F] : Work.L2F.negOne F * Work.L2F.negOne F = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul,
    show ((Work.L2F.negOne F : Matrix.SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) = -1 from rfl]
  simp

/-- `(-1) ^ 2 = 1` in `SL(2,F)`. -/
theorem negOne_pow_two (F : Type*) [Field F] : Work.L2F.negOne F ^ 2 = 1 := by
  rw [pow_two, negOne_mul_self]

/-- For `x ∈ SL(2,F)` with `x² = -1`, the normalizer of `⟨x⟩ = {1, x, -1, -x}` is the set of
`y` with `y x y⁻¹ = x` or `y x y⁻¹ = -x`.  (Conjugation preserves the order, and the elements of
order `4` in `⟨x⟩` are exactly `x` and `x³ = -x`.) -/
theorem mem_normalizer_zpowers (F : Type*) [Field F] (x : Matrix.SpecialLinearGroup (Fin 2) F)
    (hx : (x : Matrix (Fin 2) (Fin 2) F) * (x : Matrix (Fin 2) (Fin 2) F) = -1)
    (y : Matrix.SpecialLinearGroup (Fin 2) F) :
    y ∈ Subgroup.normalizer (Subgroup.zpowers x) ↔
      y * x * y⁻¹ = x ∨ y * x * y⁻¹ = Work.L2F.negOne F * x := by
  have hz2 : Work.L2F.negOne F ^ 2 = 1 := negOne_pow_two F
  -- `x ^ 2 = -1` as elements of `SL(2,F)`, then `x ^ 4 = 1`.
  have hx2 : x ^ 2 = Work.L2F.negOne F := by
    rw [pow_two]
    apply Subtype.ext
    change (((x * x) : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      ((Work.L2F.negOne F : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
    rw [Matrix.SpecialLinearGroup.coe_mul]
    change (x : Matrix (Fin 2) (Fin 2) F) * (x : Matrix (Fin 2) (Fin 2) F) = -1
    exact hx
  have hx4 : x ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hx2, hz2]
  constructor
  · -- Forward: `y x y⁻¹ ∈ ⟨x⟩` and `y x y⁻¹` has the same square `-1` as `x`, so it is one of
    -- `1`, `x`, `x² = -1`, `x³ = -x`; only `x` and `-x` survive (`y x y⁻¹ = 1` would give
    -- `x = 1`, and `y x y⁻¹ = -1` would force `-1 = 1`).
    intro hy
    have hmem : y * x * y⁻¹ ∈ Subgroup.zpowers x :=
      ((Subgroup.mem_normalizer_iff.mp hy) x).mp (Subgroup.mem_zpowers x)
    by_cases hx1 : x = 1
    · subst hx1
      left
      simp
    · have hu_ne : y * x * y⁻¹ ≠ 1 := by
        intro h
        refine hx1 ?_
        have h2 : y⁻¹ * (y * x * y⁻¹) * y = x := by group
        rw [h] at h2
        simpa using h2.symm
      have hu2 : (y * x * y⁻¹) ^ 2 = Work.L2F.negOne F := by
        rw [conj_pow, hx2, ← negOne_mul_comm F y, mul_assoc, mul_inv_cancel, mul_one]
      rcases zpowers_of_pow_four hx4 hmem with h1 | h1 | h1 | h1
      · exact absurd h1 hu_ne
      · left; exact h1
      · -- `y x y⁻¹ = x ^ 2 = -1` contradicts `(y x y⁻¹) ^ 2 = -1` together with `(-1) ^ 2 = 1`.
        exfalso
        rw [hx2] at h1
        rw [h1] at hu2
        exact hu_ne (by rw [h1, hu2.symm.trans hz2])
      · -- `y x y⁻¹ = x ^ 3 = x ^ 2 * x = -x`
        right
        rw [h1, ← hx2]
        rw [show x ^ 3 = x ^ 2 * x from by rw [pow_succ]]
  · -- Backward: it suffices that both `y x y⁻¹` and `y⁻¹ x y` lie in `⟨x⟩`; note that
    -- `-x = x ^ 3 ∈ ⟨x⟩` and that `y⁻¹ x y = y x y⁻¹` in either case (`y x y⁻¹ = -x` gives
    -- `x = y⁻¹ (-x) y = -1 · (y⁻¹ x y)` since `-1` is central with `(-1)² = 1`).
    rintro (hy | hy)
    · have hx_mem : x ∈ Subgroup.zpowers x := Subgroup.mem_zpowers x
      refine mem_normalizer_zpowers_of ?_ ?_
      · rw [hy]; exact hx_mem
      · have hv : y⁻¹ * x * y = x := by
          calc y⁻¹ * x * y = y⁻¹ * (y * x * y⁻¹) * y := by rw [hy]
            _ = x := by group
        rw [hv]; exact hx_mem
    · have hz_mem : Work.L2F.negOne F ∈ Subgroup.zpowers x := by
        rw [← hx2]
        exact Subgroup.pow_mem (Subgroup.zpowers x) (Subgroup.mem_zpowers x) 2
      have hzx : Work.L2F.negOne F * x ∈ Subgroup.zpowers x :=
        Subgroup.mul_mem (Subgroup.zpowers x) hz_mem (Subgroup.mem_zpowers x)
      refine mem_normalizer_zpowers_of ?_ ?_
      · rw [hy]; exact hzx
      · have hv : y⁻¹ * x * y = Work.L2F.negOne F * x := by
          have h2 : x = Work.L2F.negOne F * (y⁻¹ * x * y) := by
            calc x = y⁻¹ * (y * x * y⁻¹) * y := by group
              _ = y⁻¹ * (Work.L2F.negOne F * x) * y := by rw [hy]
              _ = Work.L2F.negOne F * (y⁻¹ * x * y) := by
                    rw [← mul_assoc y⁻¹ (Work.L2F.negOne F) x, ← negOne_mul_comm F y⁻¹]
                    group
          have h4 := congrArg (fun t => Work.L2F.negOne F * t) h2
          rw [← mul_assoc, negOne_mul_self, one_mul] at h4
          exact h4.symm
        rw [hv]; exact hzx

end Work.L2F.Involution
