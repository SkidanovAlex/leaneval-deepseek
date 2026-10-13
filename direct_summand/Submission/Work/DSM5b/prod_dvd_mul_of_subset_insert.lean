import Mathlib

namespace Work.DSM5b

universe a

/-- **A product over `T` divides a product over `S` times `t k`, when `S ⊆ T ⊆ insert k S`.**
For `t : ι → M` in a commutative monoid and finsets `S ⊆ T` with `T ⊆ insert k S`
(so `T = S` or `T = S ∪ {k}`), the product `∏_{i ∈ T} t i` divides `(∏_{i ∈ S} t i) * t k`.

Proof route: `∏_{i ∈ T} t i ∣ ∏_{i ∈ insert k S} t i` by `Finset.prod_dvd_prod_of_subset`;
if `k ∈ S` then `insert k S = S` and `∏_{i ∈ S} t i ∣ (∏_{i ∈ S} t i) * t k`; if `k ∉ S` then
`∏_{i ∈ insert k S} t i = t k * ∏_{i ∈ S} t i` by `Finset.prod_insert`.-/
theorem prod_dvd_mul_of_subset_insert {ι M : Type a} [DecidableEq ι] [CommMonoid M]
    (t : ι → M) {S T : Finset ι} (hST : S ⊆ T) {k : ι} (hT : T ⊆ insert k S) :
    (∏ i ∈ T, t i) ∣ (∏ i ∈ S, t i) * t k := by
  have h1 : (∏ i ∈ T, t i) ∣ (∏ i ∈ insert k S, t i) :=
    Finset.prod_dvd_prod_of_subset T (insert k S) t hT
  refine h1.trans ?_
  by_cases hk : k ∈ S
  · rw [Finset.insert_eq_of_mem hk]
    exact dvd_mul_right _ _
  · have h : (∏ i ∈ insert k S, t i) = (∏ i ∈ S, t i) * t k := by
      rw [Finset.prod_insert hk, mul_comm (t k) (∏ i ∈ S, t i)]
    rw [h]

end Work.DSM5b
