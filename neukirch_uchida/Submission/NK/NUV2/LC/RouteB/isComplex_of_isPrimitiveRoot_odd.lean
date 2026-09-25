import Mathlib

namespace NK.NUV2.LC.RouteB

/-- If a number field `F` contains a primitive `p`-th root of unity `ζ` for an odd prime `p`,
then `F` has no real infinite place: a real place would give a real `p`-th root of unity
`φ ζ`, which for odd `p` can only be `1`, forcing `ζ = 1`, a contradiction. -/
theorem isComplex_of_isPrimitiveRoot_odd {F : Type} [Field F] [NumberField F]
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (ζ : F) (hζ : IsPrimitiveRoot ζ p) :
    ∀ v : NumberField.InfinitePlace F, v.IsComplex := by
  intro v
  rw [← NumberField.InfinitePlace.not_isReal_iff_isComplex]
  intro hv
  -- `v` is real, so `ζ` has a real image under the associated real embedding.
  have hpow : (NumberField.InfinitePlace.embedding_of_isReal hv ζ) ^ p = 1 := by
    rw [← map_pow, hζ.pow_eq_one, map_one]
  have hodd : Odd p := hp.odd_of_ne_two hp2
  rw [pow_eq_one_iff_of_ne_zero hp.ne_zero] at hpow
  obtain h | ⟨h, heven⟩ := hpow
  · -- the real image of `ζ` is `1`, hence `ζ = 1`
    have h1 : NumberField.InfinitePlace.embedding v ζ = 1 := by
      have h2 := NumberField.InfinitePlace.embedding_of_isReal_apply hv ζ
      rw [h] at h2
      simpa using h2.symm
    exact hζ.ne_one hp.one_lt
      ((NumberField.InfinitePlace.embedding v).injective (by rw [h1, map_one]))
  · exact (Nat.not_even_iff_odd.mpr hodd) heven

end NK.NUV2.LC.RouteB
