import Mathlib

namespace Work.CORE3.A7V18

/-- If `s` lies in `N` and inverts every element of a subgroup `P` of odd order, while `P`
normalizes `N` (through `M ≤ N_G(N)`), then `P ≤ N`.

The point is that `p * s * p = s` for every `p ∈ P`, whence `p * s * p⁻¹ = s * (p⁻¹)^2`
belongs to `N` (as `p` normalizes `N`), so `p ^ 2 ∈ N`. Since `P` has odd order every
element of `P` is a square, giving `P ≤ N`. -/
theorem le_of_inverts_of_odd {G : Type*} [Group G] {M N P : Subgroup G} {s : G}
    (hNM : M ≤ Subgroup.normalizer (N : Set G)) (hPM : P ≤ M) (hs : s ∈ N)
    (hinv : ∀ x ∈ P, s * x * s⁻¹ = x⁻¹) (hodd : Odd (Nat.card P)) : P ≤ N := by
  -- Every element of `P` has its square in `N`.
  have hsq : ∀ p ∈ P, p ^ 2 ∈ N := by
    intro p hp
    have hpN : p ∈ Subgroup.normalizer (N : Set G) := hNM (hPM hp)
    rw [Subgroup.mem_normalizer_iff] at hpN
    have hpconj : p * s * p⁻¹ ∈ N := (hpN s).1 hs
    -- From `s * p * s⁻¹ = p⁻¹` we get `p * s * p = s`.
    have hpsp : p * s * p = s := by
      have h1 : s * p = p⁻¹ * s := by
        calc s * p = s * p * s⁻¹ * s := by group
          _ = p⁻¹ * s := by rw [hinv p hp]
      calc p * s * p = p * (s * p) := by group
        _ = p * (p⁻¹ * s) := by rw [h1]
        _ = s := by group
    have hconj2 : p * s * p⁻¹ = s * (p⁻¹)^2 := by
      have h2 : p * s = s * p⁻¹ := by
        have hc := congrArg (· * p⁻¹) hpsp
        simpa [mul_assoc] using hc
      calc p * s * p⁻¹ = (s * p⁻¹) * p⁻¹ := by rw [h2]
        _ = s * (p⁻¹)^2 := by group
    rw [hconj2] at hpconj
    have hmem : (p⁻¹)^2 ∈ N := by
      have := N.mul_mem (N.inv_mem hs) hpconj
      simpa using this
    have := N.inv_mem hmem
    rwa [show ((p⁻¹)^2)⁻¹ = p ^ 2 by group] at this
  -- `P` is finite because `Nat.card P` is odd, so its cardinality may be used as an exponent.
  have hnz : Nat.card P ≠ 0 := by
    intro h0
    rw [h0] at hodd
    exact Nat.not_odd_zero hodd
  haveI : Finite P := (Nat.card_ne_zero.mp hnz).2
  haveI : Fintype P := Fintype.ofFinite P
  obtain ⟨k, hk⟩ := hodd
  -- Since `|P|` is odd, every element of `P` is a square of an element of `P`.
  intro x hx
  have hpow : x ^ Nat.card P = 1 := by
    have h1 : (⟨x, hx⟩ : P) ^ Fintype.card P = 1 := pow_card_eq_one
    have h2 : x ^ Fintype.card P = 1 := by
      have hh := congrArg (fun y : P => (y : G)) h1
      simp only [Subgroup.coe_pow, Subgroup.coe_one] at hh
      exact hh
    rw [Nat.card_eq_fintype_card]
    exact h2
  have hxp : (x ^ (k + 1)) ^ 2 = x := by
    have h2 : 2 * (k + 1) = Nat.card P + 1 := by omega
    rw [← pow_mul, Nat.mul_comm (k + 1) 2, h2, pow_succ, hpow, one_mul]
  have hmem := hsq (x ^ (k + 1)) (P.pow_mem hx (k + 1))
  rwa [hxp] at hmem

end Work.CORE3.A7V18
