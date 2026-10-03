import Mathlib

/-!
# Right-regularity from left-regularity in a semisimple ring

In a semisimple ring (`IsSemisimpleRing R`), the regular module is Artinian, and in an
Artinian ring every element that is regular on one side is a unit. Consequently an element
`x` with `x * y = 0 → y = 0` also satisfies `y * x = 0 → y = 0`.

This is the ring-theoretic input used in the proof that group algebras of one-relator
groups over certain coefficient rings are coherent.
-/

namespace Work.ORLyndon

/-- In a semisimple ring, if left multiplication by `x` has trivial kernel then so does
right multiplication by `x`. -/
theorem rightRegular_of_leftRegular_isSemisimple {R : Type*} [Ring R] [IsSemisimpleRing R] {x : R}
    (h : ∀ y : R, x * y = 0 → y = 0) : ∀ y : R, y * x = 0 → y = 0 := by
  -- The hypothesis says precisely that left multiplication by `x` is injective.
  have hleft : IsLeftRegular x := fun a b hab => by
    have hab' : x * a = x * b := hab
    have h0 : x * (a - b) = 0 := by rw [mul_sub, hab', sub_self]
    exact sub_eq_zero.mp (h (a - b) h0)
  -- A semisimple ring is Artinian, and in an Artinian ring a one-sidedly regular element
  -- is a unit.
  have hunit : IsUnit x := (IsArtinianRing.isUnit_iff_isLeftRegular (R := R)).mpr hleft
  obtain ⟨u, rfl⟩ := hunit
  -- A unit is right-regular.
  intro y hy
  calc y = y * (u : R) * (↑u⁻¹ : R) := by rw [mul_assoc, Units.mul_inv, mul_one]
    _ = 0 := by rw [hy, zero_mul]

end Work.ORLyndon
