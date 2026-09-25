import Mathlib

/-!
# Values of a rank-one valuation are bounded by powers

A rank-one valuation takes values in an archimedean ordered group (this is exactly the
`MulArchimedean` content of `Valuation.RankOne`): the value group embeds strictly
monotonically into `ℝ≥0`.  Consequently, if `1 < v b` then every value `v a` is dominated
by some power of `v b`.

This is the element-level form of the fact that the value group of a rank-one valuation is
archimedean; it is the input that lets one construct, for any `a`, an integer `N` with
`v a ≤ v b ^ N`.
-/

namespace NK.NeukirchUchida

open MonoidWithZeroHom

/-- In a field `k` with a rank-one valuation `v` (values in `Γ`), if `1 < v b` then every value
`v a` is bounded above by a power of `v b`.  This is the element-level form of the fact that the
value group of a rank-one valuation is archimedean. -/
theorem exists_valuation_le_pow_of_rankOne {k Γ : Type*} [Field k]
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation k Γ) [v.RankOne] {a b : k}
    (hb : 1 < v b) : ∃ N : ℕ, v a ≤ (v b) ^ N := by
  -- The value group of `v` is archimedean, because `RankOne` provides the strict monotone
  -- monoid-with-zero homomorphism `RankOne.hom v : ValueGroup₀ v →*₀ ℝ≥0`.
  have hMA : MulArchimedean (ValueGroup₀ (MonoidWithZeroHom.ofClass v)) :=
    MulArchimedean.comap (Valuation.RankOne.hom v).toMonoidHom (Valuation.RankOne.strictMono v)
  -- `1 < v b` transported to the value group along the (strictly monotone) embedding.
  have hy : 1 < ValueGroup₀.restrict₀ (MonoidWithZeroHom.ofClass v) b := by
    rw [← (ValueGroup₀.embedding_strictMono (f := MonoidWithZeroHom.ofClass v)).lt_iff_lt]
    simpa using hb
  obtain ⟨N, hN⟩ := hMA.arch (ValueGroup₀.restrict₀ (MonoidWithZeroHom.ofClass v) a) hy
  refine ⟨N, ?_⟩
  -- Push the inequality back from the value group to `Γ`.
  have h := (ValueGroup₀.embedding_strictMono (f := MonoidWithZeroHom.ofClass v)).monotone hN
  simpa using h

end NK.NeukirchUchida
