import Mathlib

namespace NK.TameStructureDeep.Tame

/-- If `x` is an `N`-th root of unity in a local ring whose residue is `1`, and `N` is a unit,
then `x = 1`.  The point is that `x ≡ 1` and `x ^ N = 1` force `x` to lie in `1 + 𝔪` with
`N (x - 1) ∈ 𝔪 ⋅ (x - 1)`; the geometric sum `∑_{i<N} x ^ i` is congruent to `N` modulo the
maximal ideal, hence a unit, and `(x - 1) * ∑_{i<N} x ^ i = x ^ N - 1 = 0`. -/
theorem eq_one_of_residue_eq_one {R : Type*} [CommRing R] [IsLocalRing R]
    {N : ℕ} (hN : IsUnit (N : R)) {x : R} (hxpow : x ^ N = 1)
    (hx : IsLocalRing.residue R x = 1) : x = 1 := by
  set S : R := ∑ i ∈ Finset.range N, x ^ i with hSdef
  have hmul : (x - 1) * S = 0 := by
    rw [hSdef, mul_geom_sum, hxpow, sub_self]
  have hSunit : IsUnit S := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
    have hres : IsLocalRing.residue R S = (N : IsLocalRing.ResidueField R) := by
      rw [hSdef, map_sum]
      simp only [map_pow, hx, one_pow]
      simp
    rw [hres]
    have hNu : IsUnit (N : IsLocalRing.ResidueField R) := by
      simpa using RingHom.isUnit_map (IsLocalRing.residue R) hN
    exact hNu.ne_zero
  have : x - 1 = 0 := (IsUnit.mul_left_eq_zero hSunit).mp hmul
  exact sub_eq_zero.mp this

theorem isPrimitiveRoot_residue {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
    {N : ℕ} (hN : IsUnit (N : R)) {ζ : R} (hζ : IsPrimitiveRoot ζ N) :
    IsPrimitiveRoot (IsLocalRing.residue R ζ) N := by
  refine ⟨?_, ?_⟩
  · rw [← map_pow, hζ.pow_eq_one, map_one]
  · intro l hl
    have h1 : IsLocalRing.residue R (ζ ^ l) = 1 := by rw [map_pow, hl]
    have h2 : (ζ ^ l) ^ N = 1 := by
      rw [← pow_mul, mul_comm l N, pow_mul, hζ.pow_eq_one, one_pow]
    exact hζ.dvd_of_pow_eq_one l (eq_one_of_residue_eq_one hN h2 h1)

end NK.TameStructureDeep.Tame
