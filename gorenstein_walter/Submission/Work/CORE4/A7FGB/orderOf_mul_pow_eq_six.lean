import Mathlib

namespace Work.CORE4.A7FGB

/-- If `V` is a subgroup all of whose elements are involutions, `x` has order `3`, and `x`
commutes with every element of `V`, then for every `v ∈ V`, `v ≠ 1`, and `k : Fin 2` the
element `v * x ^ (k.val + 1)` has order `6`.

Indeed `k.val + 1 ∈ {1, 2}` is coprime to `3`, so `x ^ (k.val + 1)` still has order `3`
(`Nat.Coprime.orderOf_pow`); `v` has order `2`; and `v` commutes with `x ^ (k.val + 1)`, so
the commuting-product formula for coprime orders gives `2 * 3 = 6`. -/
theorem orderOf_mul_pow_eq_six {G : Type*} [Group G] (V : Subgroup G) (x : G)
    (hV2 : ∀ v ∈ V, v * v = 1) (hx3 : orderOf x = 3) (hcomm : ∀ v ∈ V, v * x = x * v)
    {v : G} (hv : v ∈ V) (hv1 : v ≠ 1) (k : Fin 2) :
    orderOf (v * x ^ (k.val + 1)) = 6 := by
  -- `v` is an involution different from `1`, hence has order `2`.
  have hv2 : orderOf v = 2 := by
    rw [orderOf_eq_prime_iff]
    exact ⟨by simpa [pow_two] using hV2 v hv, hv1⟩
  -- `k.val + 1 ∈ {1, 2}` is coprime to `3`, so the exponent stays coprime to `orderOf x = 3`.
  have hcop3 : (orderOf x).Coprime (k.val + 1) := by
    have hk : k.val = 0 ∨ k.val = 1 := by omega
    rw [hx3]
    rcases hk with hk | hk <;> rw [hk] <;> norm_num
  -- hence `x ^ (k.val + 1)` still has order `3`.
  have hw3 : orderOf (x ^ (k.val + 1)) = 3 := by
    rw [Nat.Coprime.orderOf_pow hcop3, hx3]
  -- `v` and `x ^ (k.val + 1)` commute (both are powers/products of commuting elements).
  have hcomm' : Commute v (x ^ (k.val + 1)) := Commute.pow_right (hcomm v hv) _
  have hcop : (orderOf v).Coprime (orderOf (x ^ (k.val + 1))) := by rw [hv2, hw3]; norm_num
  -- the product of commuting elements of coprime orders `2` and `3` has order `2 * 3 = 6`.
  rw [hcomm'.orderOf_mul_eq_mul_orderOf_of_coprime hcop, hv2, hw3]

end Work.CORE4.A7FGB
