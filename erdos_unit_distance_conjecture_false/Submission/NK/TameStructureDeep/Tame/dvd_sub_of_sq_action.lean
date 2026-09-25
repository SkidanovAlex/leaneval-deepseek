import Mathlib

set_option linter.style.haveILetI false

namespace NK.TameStructureDeep.Tame

/-- Powers of an element commute in their exponents: `(x ^ p) ^ q = (x ^ q) ^ p`. -/
private theorem pow_pow_comm' {M : Type*} [Monoid M] (x : M) (p q : ℕ) :
    (x ^ p) ^ q = (x ^ q) ^ p := by
  rw [← pow_mul, ← pow_mul, Nat.mul_comm]

/-- **Compatibility of the cyclotomic characters in degrees `m` and `m ^ 2`.**

If `ζ₀` is a primitive `m`-th root of unity and `ζ` a primitive `m ^ 2`-th root of unity, and a
`κ`-automorphism `σ` of `K'` acts on them by `ζ₀ ↦ ζ₀ ^ a` and `ζ ↦ ζ ^ b`, then the exponents
`a` and `b` are congruent modulo `m`.

Indeed `ζ ^ m` is a primitive `m`-th root of unity, so `ζ₀ = (ζ ^ m) ^ c` for some `c` coprime to
`m`; from `σ (ζ ^ m) = (ζ ^ m) ^ b` it follows that `σ` acts on `ζ₀` by the `b`-th power map,
whence `ζ₀ ^ b = ζ₀ ^ a` and `b ≡ a` modulo the order `m` of `ζ₀`. -/
theorem dvd_sub_of_sq_action {κ K' : Type*} [Field κ] [Field K'] [Algebra κ K']
    {σ : Gal(K'/κ)} {m a b : ℕ} (hm : m ≠ 0) {ζ₀ ζ : K'}
    (hζ₀ : IsPrimitiveRoot ζ₀ m) (hζ : IsPrimitiveRoot ζ (m ^ 2))
    (ha : σ ζ₀ = ζ₀ ^ a) (hb : σ ζ = ζ ^ b) :
    (m : ℤ) ∣ (b : ℤ) - (a : ℤ) := by
  haveI : NeZero m := ⟨hm⟩
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm
  -- `η := ζ ^ m` is a primitive `m`-th root of unity, on which `σ` acts by the `b`-th power map.
  have hη : IsPrimitiveRoot (ζ ^ m) m := hζ.pow (pow_pos hmpos 2) (pow_two m)
  have hησ : σ (ζ ^ m) = (ζ ^ m) ^ b := by
    rw [map_pow, hb, pow_pow_comm']
  -- `ζ₀` is a power of `η`, say `ζ₀ = η ^ c`.
  obtain ⟨c, -, -, hc_eq⟩ := (hη.isPrimitiveRoot_iff).mp hζ₀
  -- hence `σ` acts on `ζ₀` by the `b`-th power map as well.
  have hsb : σ ζ₀ = ζ₀ ^ b := by
    rw [← hc_eq, map_pow, hησ, pow_pow_comm']
  have hbaeq : ζ₀ ^ b = ζ₀ ^ a := by rw [← hsb, ha]
  -- compare the two actions in the group of units, where powers distinguish exponents.
  obtain ⟨u, hu⟩ : ∃ u : K'ˣ, (u : K') = ζ₀ :=
    ⟨(hζ₀.isUnit hm).unit, (hζ₀.isUnit hm).unit_spec⟩
  have huζ : IsPrimitiveRoot u m := IsPrimitiveRoot.coe_units_iff.mp (hu.symm ▸ hζ₀)
  have hpow : u ^ b = u ^ a := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hu, hbaeq]
  have hmod : b ≡ a [MOD m] := by
    have h := (pow_eq_pow_iff_modEq (x := u) (n := b) (m := a)).mp hpow
    rwa [← huζ.eq_orderOf] at h
  exact Nat.ModEq.dvd hmod.symm

end NK.TameStructureDeep.Tame
