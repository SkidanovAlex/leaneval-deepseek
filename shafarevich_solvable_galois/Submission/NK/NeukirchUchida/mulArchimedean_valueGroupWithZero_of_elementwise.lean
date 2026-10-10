import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Algebra.Order.Archimedean.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.NeukirchUchida

open MonoidWithZeroHom

/-- If the valuation of a valuation subring `A` of a field `L` satisfies the element-level
archimedean property (every value is bounded above by a power of any value `> 1`), then the value
group of `A.valuation` is mul-archimedean: for all `x` and `1 < y` in
`(MonoidWithZeroHom.ofClass A.valuation).ValueGroup₀` there is `n` with `x ≤ y ^ n`. -/
theorem mulArchimedean_valueGroupWithZero_of_elementwise {L : Type*} [Field L]
    (A : ValuationSubring L)
    (h : ∀ u z : L, z ≠ 0 → 1 < A.valuation z → ∃ N : ℕ, A.valuation u < A.valuation z ^ N) :
    MulArchimedean (MonoidWithZeroHom.ofClass A.valuation).ValueGroup₀ := by
  -- The valuation `A.valuation : L → A.ValueGroup` is surjective, so the element-level
  -- archimedean property upgrades to the archimedean property of `A.ValueGroup` itself.
  have hMA : MulArchimedean A.ValueGroup := ⟨fun x y hy => by
    obtain ⟨u, hu⟩ := A.valuation_surjective x
    obtain ⟨z, hz⟩ := A.valuation_surjective y
    subst hu
    subst hz
    have hz0 : z ≠ 0 := by
      rintro rfl
      exact absurd hy (not_lt_of_ge zero_le_one)
    obtain ⟨N, hN⟩ := h u z hz0 hy
    exact ⟨N, hN.le⟩⟩
  -- The value group with zero embeds strictly monotonically into `A.ValueGroup`.
  exact MulArchimedean.comap
    (MonoidWithZeroHom.toMonoidHom
      (MonoidWithZeroHom.ValueGroup₀.embedding (f := MonoidWithZeroHom.ofClass A.valuation)))
    (MonoidWithZeroHom.ValueGroup₀.embedding_strictMono
      (f := MonoidWithZeroHom.ofClass A.valuation))

end NK.NeukirchUchida
