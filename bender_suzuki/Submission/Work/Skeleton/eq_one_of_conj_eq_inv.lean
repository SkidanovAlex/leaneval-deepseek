import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Skeleton

/-- If `g` conjugates `x` to `x⁻¹` and both `g` and `x` have odd order, then `x = 1`.

Conjugation by `g` inverts `x`, so by induction `g ^ k * x * (g ^ k)⁻¹ = x ^ ((-1) ^ k)`.
With `k = orderOf g`, using `g ^ orderOf g = 1` and oddness of `orderOf g`, this reads
`x = x⁻¹`, hence `x * x = 1`, so `orderOf x ∣ 2`. Since `orderOf x` is odd this forces
`orderOf x = 1`, i.e. `x = 1`. -/
theorem eq_one_of_conj_eq_inv {G : Type*} [Group G] {x g : G} (h : g * x * g⁻¹ = x⁻¹)
    (hg : Odd (orderOf g)) (hx : Odd (orderOf x)) : x = 1 := by
  have key : ∀ k : ℕ, g ^ k * x * (g ^ k)⁻¹ = x ^ ((-1 : ℤ) ^ k) := by
    intro k
    induction k with
    | zero => simp
    | succ n ih =>
      rw [pow_succ]
      have h1 : g ^ n * g * x * (g ^ n * g)⁻¹ = g ^ n * (g * x * g⁻¹) * (g ^ n)⁻¹ := by
        rw [mul_inv_rev]; group
      rw [h1, h]
      have h2 : g ^ n * x⁻¹ * (g ^ n)⁻¹ = (g ^ n * x * (g ^ n)⁻¹)⁻¹ := by
        group
      rw [h2, ih, ← zpow_neg]
      congr 1
      rw [pow_succ]
      ring
  have hxinv : x = x⁻¹ := by
    have hkey := key (orderOf g)
    rw [pow_orderOf_eq_one g, one_mul, inv_one, mul_one] at hkey
    rw [Odd.neg_one_pow hg, zpow_neg_one] at hkey
    exact hkey
  have hsq : x * x = 1 := by
    nth_rewrite 1 [hxinv]
    exact inv_mul_cancel x
  have hdvd : orderOf x ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact hsq)
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
  · exact orderOf_eq_one_iff.mp h1
  · rw [h2] at hx
    exact absurd hx (by decide)

end Work.Skeleton
