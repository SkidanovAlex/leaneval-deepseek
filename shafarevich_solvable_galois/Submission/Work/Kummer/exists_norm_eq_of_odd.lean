import Mathlib
import Submission.Work.Kummer.norm_eq_primRoot_pow_mul_of_kummer_generator
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

universe u v

namespace Work.Kummer

/-- For an odd `n`, the correction factor `ζ ^ (n * (n - 1) / 2)` appearing in the norm of a
Kummer generator is trivial: writing `n = 2 * k + 1` we have `n * (n - 1) / 2 = n * k`, so it is a
power of `ζ ^ n = 1`. -/
theorem primRoot_pow_half_mul_self_sub_one_eq_one {K : Type u} [Field K] {n : ℕ} {ζ : K}
    (hζ : IsPrimitiveRoot ζ n) (hodd : Odd n) : ζ ^ (n * (n - 1) / 2) = 1 := by
  obtain ⟨k, hk⟩ := hodd
  subst hk
  have hexp : (2 * k + 1) * (2 * k + 1 - 1) / 2 = (2 * k + 1) * k := by
    rw [show 2 * k + 1 - 1 = 2 * k by omega]
    rw [Nat.mul_div_assoc (2 * k + 1) (by exact ⟨k, by ring⟩),
      Nat.mul_div_right k (by norm_num)]
  rw [hexp, pow_mul, hζ.pow_eq_one, one_pow]

/-- If `L/K` is a finite Galois extension of degree `n`, with `n` odd, `ζ ∈ K` a primitive `n`-th
root of unity and `α ∈ L` a Kummer generator (`α ^ n = a` and `σα = ζ α` for a generator `σ` of the
Galois group), then `a` is a norm from `L`: `a = N_{L/K}(η)` for some unit `η` of `L`. -/
theorem exists_norm_eq_of_odd {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] {n : ℕ} [NeZero n] {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    (hn : Module.finrank K L = n) (hodd : Odd n) {α : L} {a : K} (ha0 : a ≠ 0)
    (ha : α ^ n = algebraMap K L a) {σ : Gal(L/K)} (hσ : ∀ x : Gal(L/K), x ∈ Subgroup.zpowers σ)
    (hlt : (σ : L ≃ₐ[K] L) α = algebraMap K L ζ * α) :
    ∃ η : Lˣ, Algebra.norm K (η : L) = a := by
  have hmap : algebraMap K L a ≠ 0 := fun h => ha0 ((algebraMap K L).injective (by simpa using h))
  have hα : α ≠ 0 := by
    intro h
    apply hmap
    rw [← ha, h, zero_pow NeZero.out]
  refine ⟨Units.mk0 α hα, ?_⟩
  rw [Units.val_mk0, norm_eq_primRoot_pow_mul_of_kummer_generator hζ hn ha hσ hlt,
    primRoot_pow_half_mul_self_sub_one_eq_one hζ hodd, one_mul]

end Work.Kummer
