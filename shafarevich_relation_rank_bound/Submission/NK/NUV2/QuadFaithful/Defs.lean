import Mathlib

/-!
# Vocabulary for the quadratic Hasse-norm argument

This file collects the small definitions shared by the files in
`Submission/Work/NUV2/QuadFaithful/`, which together prove
`NK.NUV2.normGroup_quadratic_faithful_odd`.
-/

namespace NK.NUV2.QuadFaithful

noncomputable section

/-- The subgroup `(Fˣ)²` of squares of the unit group of a field `F`. -/
abbrev sq (F : Type*) [Field F] : Subgroup Fˣ := (powMonoidHom 2 : Fˣ →* Fˣ).range

@[simp]
theorem mem_sq_iff {F : Type*} [Field F] {x : Fˣ} :
    x ∈ sq F ↔ ∃ y : Fˣ, y ^ 2 = x :=
  MonoidHom.mem_range

theorem sq_le_iff {F : Type*} [Field F] {H : Subgroup Fˣ} :
    sq F ≤ H ↔ ∀ x : Fˣ, x ^ 2 ∈ H := by
  constructor
  · intro h x
    exact h (by rw [mem_sq_iff]; exact ⟨x, rfl⟩)
  · intro h x hx
    rw [mem_sq_iff] at hx
    obtain ⟨y, hy⟩ := hx
    rw [← hy]
    exact h y

/-- A nonzero element of a field is a square in the field exactly when the corresponding unit is
a square in the unit group. -/
theorem isSquare_iff_units_mem_sq {F : Type*} [Field F] {a : F} (ha : a ≠ 0) :
    IsSquare a ↔ Units.mk0 a ha ∈ sq F := by
  rw [isSquare_iff_exists_sq, mem_sq_iff]
  constructor
  · rintro ⟨b, hb⟩
    have hb0 : b ≠ 0 := by
      rintro rfl
      exact ha (by simpa using hb)
    refine ⟨Units.mk0 b hb0, ?_⟩
    ext
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_mk0]
    exact hb.symm
  · rintro ⟨y, hy⟩
    refine ⟨(y : F), ?_⟩
    have := congrArg (fun u : Fˣ => (u : F)) hy
    rw [Units.val_pow_eq_pow_val, Units.val_mk0] at this
    exact this.symm

end

end NK.NUV2.QuadFaithful
