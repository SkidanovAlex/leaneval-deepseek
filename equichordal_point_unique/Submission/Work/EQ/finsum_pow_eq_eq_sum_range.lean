import Mathlib

set_option linter.style.haveILetI false

namespace Work.EQ

/-- For `c ≠ 0` and `0 < k`, the `k`-th roots of `c` are exactly `η ^ j * t` (`j < k`), where `η`
is a primitive `k`-th root of unity and `t` is any `k`-th root of `c`. Consequently, summing any
function over all `k`-th roots of `c` is the same as summing it over `η ^ j * t`, `j < k`. -/
theorem finsum_pow_eq_eq_sum_range {k : ℕ} (hk : 0 < k) {η : ℂ} (hη : IsPrimitiveRoot η k)
    {c : ℂ} (hc : c ≠ 0) {t : ℂ} (ht : t ^ k = c) {M : Type*} [AddCommMonoid M] (A : ℂ → M) :
    ∑ᶠ ζ ∈ {ζ : ℂ | ζ ^ k = c}, A ζ = ∑ j ∈ Finset.range k, A (η ^ j * t) := by
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [zero_pow hk.ne'] at ht
    exact hc ht.symm
  haveI : NeZero k := ⟨hk.ne'⟩
  have hinj : Set.InjOn (fun j => η ^ j * t) ↑(Finset.range k) := by
    intro i hi j hj hij
    simp only [Finset.mem_coe, Finset.mem_range] at hi hj
    exact hη.pow_inj hi hj (mul_right_cancel₀ ht0 hij)
  have hsub : ({ζ : ℂ | ζ ^ k = c} ∩ Function.support A) ⊆
      ↑((Finset.range k).image (fun j => η ^ j * t)) := by
    intro x hx
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Function.mem_support] at hx
    obtain ⟨hxroot, _⟩ := hx
    have hx1 : (x * t⁻¹) ^ k = 1 := by
      rw [mul_pow, inv_pow, hxroot, ht, mul_inv_cancel₀ hc]
    obtain ⟨j, hj, hje⟩ := hη.eq_pow_of_pow_eq_one hx1
    refine Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj, ?_⟩
    rw [hje, mul_assoc, inv_mul_cancel₀ ht0, mul_one]
  have hsub2 : (↑((Finset.range k).image (fun j => η ^ j * t)) : Set ℂ) ⊆
      {ζ : ℂ | ζ ^ k = c} := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    rw [Finset.mem_range] at hj
    simp only [Set.mem_ofPred_eq]
    rw [mul_pow, ← pow_mul, mul_comm j k, pow_mul, hη.pow_eq_one, one_pow, one_mul, ht]
  rw [finsum_mem_eq_sum_of_subset A hsub hsub2, Finset.sum_image hinj]

end Work.EQ
