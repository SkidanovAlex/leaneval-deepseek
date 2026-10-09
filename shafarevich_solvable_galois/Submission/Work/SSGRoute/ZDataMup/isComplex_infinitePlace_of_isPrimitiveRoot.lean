import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ZDataMup

open NumberField

/-- **A real complex embedding sends an odd-order root of unity to `1`.**

If `φ : K →+* ℂ` is a real embedding (fixed by complex conjugation, equivalently taking values in
`ℝ`) and `ζ` is a primitive `p`-th root of unity with `p` odd, then `φ ζ = 1`: the image
`φ ζ ∈ ℝ` satisfies `(φ ζ) ^ p = 1`, and the odd power map is injective on `ℝ`, so `φ ζ = 1`. -/
lemma isReal_apply_isPrimitiveRoot_eq_one {K : Type} [Field K] {p : ℕ} (hpodd : Odd p)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) {φ : K →+* ℂ}
    (hφ : ComplexEmbedding.IsReal φ) : φ ζ = 1 := by
  have hpow : (hφ.embedding ζ) ^ p = 1 := by
    have h : hφ.embedding (ζ ^ p) = hφ.embedding 1 := by rw [hζ.pow_eq_one, map_one]
    rwa [map_pow, map_one] at h
  have h1 : hφ.embedding ζ = 1 := hpodd.pow_injective (by simpa using hpow)
  have hcoe := ComplexEmbedding.IsReal.coe_embedding_apply hφ ζ
  rw [h1] at hcoe
  simpa using hcoe.symm

/-- **A number field containing a primitive `p`-th root of unity for an odd prime `p` has no real
infinite place.**

If `w` were real, the associated real embedding `K →+* ℂ` would send the primitive `p`-th root of
unity `ζ` to a real `p`-th root of unity, necessarily `1` since `p` is odd; injectivity of the
embedding then forces `ζ = 1`, contradicting primitivity. -/
theorem isComplex_infinitePlace_of_isPrimitiveRoot {K : Type} [Field K] [NumberField K]
    {p : ℕ} (hpprime : p.Prime) (hp2 : p ≠ 2) {ζ : K} (hζ : IsPrimitiveRoot ζ p) :
    ∀ w : NumberField.InfinitePlace K, NumberField.InfinitePlace.IsComplex w := by
  intro w
  rw [NumberField.InfinitePlace.isComplex_iff]
  intro hφ
  have hodd : Odd p := hpprime.odd_of_ne_two hp2
  have h1 : NumberField.InfinitePlace.embedding w ζ = 1 :=
    isReal_apply_isPrimitiveRoot_eq_one hodd hζ hφ
  have hζeq1 : ζ = 1 :=
    (RingHom.injective (NumberField.InfinitePlace.embedding w)) (by rw [h1, map_one])
  exact hζ.ne_one hpprime.one_lt hζeq1

end Work.SSGRoute.ZDataMup
