import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.HallHigman

/-- If a faithful representation in characteristic `p` satisfies `(ρ x - 1) ^ 2 = 0`, then `x`
has `p`-power order: this is what allows an element given by its minimal polynomial `(X - 1) ^ 2`
in Feit--Thompson's Lemma 7.1 to be fed into Hall--Higman Theorem B. -/
theorem orderOf_eq_prime_pow_of_sq_sub_one_eq_zero {p : ℕ} [Fact p.Prime] {G V : Type*}
    [Group G] [Finite G] [AddCommGroup V] [Module (ZMod p) V] (ρ : Representation (ZMod p) G V)
    (hfaith : Function.Injective ρ) {x : G} (h : (ρ x - 1) ^ 2 = 0) :
    ∃ n : ℕ, orderOf x = p ^ n := by
  -- In characteristic `p`, the natural number `p` is zero in the endomorphism ring.
  have hp0 : (p : Module.End (ZMod p) V) = 0 := by
    have : (p : ZMod p) • (1 : Module.End (ZMod p) V) = (p : Module.End (ZMod p) V) := by
      rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul, mul_one]
    rw [← this, CharP.cast_eq_zero (ZMod p) p, zero_smul]
  -- `ρ x` is unipotent of index `2`, hence `(ρ x - 1)` is nilpotent, of nilpotency index
  -- dividing `p` because `p ≥ 2`.
  have hap : (ρ x - 1) ^ p = 0 := by
    have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
    exact pow_eq_zero_of_le hp2 h
  -- Freshman's dream: `(ρ x) ^ p = ((ρ x - 1) + 1) ^ p = (ρ x - 1) ^ p + 1 ^ p + p * (...) = 1`.
  have hxpow : ρ x ^ p = 1 := by
    have hc := Commute.add_pow_prime_eq' (p := p) (Fact.out : p.Prime)
      (x := ρ x - 1) (y := 1) (Commute.one_right _)
    rw [sub_add_cancel, hap, one_pow] at hc
    rw [hp0, zero_mul] at hc
    simpa using hc
  -- Faithfulness transfers the relation to `G`.
  have hxp : x ^ p = 1 := by
    apply hfaith
    rw [map_pow, hxpow, map_one]
  -- Therefore `orderOf x` divides the prime `p`.
  have hdvd : orderOf x ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hxp
  rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp hdvd with h1 | hp
  · exact ⟨0, by rw [h1, pow_zero]⟩
  · exact ⟨1, by rw [hp, pow_one]⟩

end Work.HallHigman
