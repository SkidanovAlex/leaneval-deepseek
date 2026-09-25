import Mathlib

namespace NK.ResidueFrob

/-- If `φ : R →+* ResidueField R` kills the maximal ideal (i.e. factors through
the residue field), `ζ` reduces to a primitive `d`-th root of unity and `φ ζ` is
the `q`-th power of `residue ζ`, then `φ` acts by the `q`-th power map on every
element whose residue is a `d`-th root of unity. -/
theorem map_eq_pow_of_primitiveRoot {R : Type*} [CommRing R] [IsLocalRing R]
    (φ : R →+* IsLocalRing.ResidueField R)
    (hφ : ∀ a : R, IsLocalRing.residue R a = 0 → φ a = 0)
    {d q : ℕ} [NeZero d] {ζ : R} (hζ : IsPrimitiveRoot (IsLocalRing.residue R ζ) d)
    (hφζ : φ ζ = (IsLocalRing.residue R ζ) ^ q)
    {a : R} (ha : (IsLocalRing.residue R a) ^ d = 1) :
    φ a = (IsLocalRing.residue R a) ^ q := by
  -- `residue a` is a `d`-th root of unity, hence a power of the primitive root
  -- `residue ζ`.
  obtain ⟨i, _, hζi⟩ := hζ.eq_pow_of_pow_eq_one ha
  -- `a` and `ζ ^ i` have the same residue, so their difference lies in the
  -- maximal ideal and is killed by `φ`.
  have hmem : IsLocalRing.residue R (a - ζ ^ i) = 0 := by
    rw [map_sub, map_pow, hζi, sub_self]
  have hzero : φ (a - ζ ^ i) = 0 := hφ _ hmem
  have h1 : φ a = φ (ζ ^ i) := by
    rw [map_sub] at hzero
    exact sub_eq_zero.mp hzero
  rw [h1, map_pow, hφζ]
  rw [← hζi, ← pow_mul, ← pow_mul, Nat.mul_comm]

end NK.ResidueFrob
