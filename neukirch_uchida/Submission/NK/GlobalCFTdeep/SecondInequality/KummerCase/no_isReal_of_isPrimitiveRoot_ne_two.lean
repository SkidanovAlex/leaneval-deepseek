import Mathlib

/-!
# No real place contains a primitive `p`-th root of unity for odd `p`

If `K` is a number field containing a primitive `p`-th root of unity `ζ` with `p` an odd prime,
then `K` admits no real place: a real place would send `ζ` to a real primitive `p`-th root of
unity, and the only roots of unity of `ℝ` are `±1`, of order at most `2`.
-/

namespace NK.GlobalCFTdeep.SecondInequality.KummerCase

theorem no_isReal_of_isPrimitiveRoot_ne_two {K : Type} [Field K] [NumberField K] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (w : NumberField.InfinitePlace K) : ¬ w.IsReal := by
  intro hw
  -- A real place is given by a real embedding `ρ : K →+* ℝ`.
  have hreal : NumberField.ComplexEmbedding.IsReal w.embedding :=
    NumberField.InfinitePlace.isReal_iff.mp hw
  let ρ : K →+* ℝ := hreal.embedding
  -- `ρ ζ` is a root of unity and a real number, hence equal to `1` because `p` is odd.
  have hρζ : ρ ζ = 1 := by
    have hp' : Odd p := hp.odd_of_ne_two hp2
    have hpow : (ρ ζ) ^ p = 1 := by
      rw [← map_pow, hζ.pow_eq_one, map_one]
    exact hp'.strictMono_pow.injective (by rw [hpow, one_pow])
  -- But `ζ ≠ 1`, and `ρ` is injective.
  have : ζ = 1 := by
    apply RingHom.injective ρ
    rw [hρζ, map_one]
  exact hζ.ne_one hp.one_lt this

end NK.GlobalCFTdeep.SecondInequality.KummerCase
