import Mathlib

namespace NK.RankTheoryDeep

/-- For `ζ` a primitive `N`-th root of unity, `m ∣ N` and `σ` a `ℚ`-algebra automorphism of `Ω`,
the action of `σ` on the primitive `m`-th root of unity `ζ ^ (N / m)` is given by exponentiation
by the image of `hζ.autToPow ℚ σ` under the reduction `(ZMod N)ˣ → (ZMod m)ˣ`. -/
theorem autToPow_castHom_pow {Ω : Type*} [Field Ω] [Algebra ℚ Ω] {m N : ℕ} [NeZero N]
    {ζ : Ω} (hζ : IsPrimitiveRoot ζ N) (hdiv : m ∣ N) (σ : Ω ≃ₐ[ℚ] Ω) :
    (ζ ^ (N / m)) ^
        ((Units.map (ZMod.castHom hdiv (ZMod m)).toMonoidHom (hζ.autToPow ℚ σ) : (ZMod m)ˣ) : ZMod m).val
      = σ (ζ ^ (N / m)) := by
  have hm0 : m ≠ 0 := fun h => (NeZero.ne N) (zero_dvd_iff.mp (h ▸ hdiv))
  haveI : NeZero m := ⟨hm0⟩
  set u : (ZMod N)ˣ := hζ.autToPow ℚ σ with hu
  have hspec : ζ ^ (u : ZMod N).val = σ ζ := by rw [hu]; exact hζ.autToPow_spec ℚ σ
  have hval : ((Units.map (ZMod.castHom hdiv (ZMod m)).toMonoidHom u : (ZMod m)ˣ) : ZMod m).val
      = (u : ZMod N).val % m := by
    rw [Units.coe_map]
    change (ZMod.cast (u : ZMod N) : ZMod m).val = (u : ZMod N).val % m
    rw [ZMod.cast_eq_val, ZMod.val_natCast]
  have hpow : (ζ ^ (N / m)) ^ m = 1 := by
    rw [← pow_mul, Nat.div_mul_cancel hdiv, hζ.pow_eq_one]
  rw [hval, pow_eq_pow_of_modEq (Nat.mod_modEq _ _) hpow]
  rw [map_pow, ← hspec, ← pow_mul, mul_comm, pow_mul]

end NK.RankTheoryDeep
