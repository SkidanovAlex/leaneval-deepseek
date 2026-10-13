import Mathlib

namespace Work.DSM2p

theorem N4d_expand_F_sub {C : Type*} [CommRing C] (p : ℕ) [Fact p.Prime]
    (ϖ₁ s0 s1 q0 q1 : C) (hp : (p : C) ∈ Ideal.span {ϖ₁ ^ p})
    (hs : s1 ^ p = s0) (hq : q1 ^ p - q0 ∈ Ideal.span {s0 * ϖ₁ ^ p}) :
    (Polynomial.expand C p) (Polynomial.C s0 * Polynomial.X - Polynomial.C q0) -
      (Polynomial.C s1 * Polynomial.X - Polynomial.C q1) ^ p ∈
        Ideal.span {Polynomial.C (ϖ₁ ^ p)} := by
  have hp' : p.Prime := Fact.out
  -- The key observation: `Polynomial.C` of a multiple of `ϖ₁^p` is a multiple of `C (ϖ₁^p)`.
  have key : ∀ x : C, x ∈ Ideal.span {ϖ₁ ^ p} →
      Polynomial.C x ∈ Ideal.span {Polynomial.C (ϖ₁ ^ p)} := by
    intro x hx
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton.mp hx
    rw [Ideal.mem_span_singleton]
    exact ⟨Polynomial.C y, map_mul Polynomial.C _ _⟩
  have hm : s0 * ϖ₁ ^ p ∈ Ideal.span {ϖ₁ ^ p} :=
    Ideal.mul_mem_left _ s0 (Ideal.subset_span (by simp))
  have hq' : q1 ^ p - q0 ∈ Ideal.span {ϖ₁ ^ p} :=
    (Ideal.span_singleton_le_iff_mem (Ideal.span {ϖ₁ ^ p})).mpr hm hq
  have hpexpand : (Polynomial.expand C p) (Polynomial.C s0 * Polynomial.X - Polynomial.C q0)
      = Polynomial.C s0 * Polynomial.X ^ p - Polynomial.C q0 := by
    simp only [map_sub, map_mul, Polynomial.expand_C, Polynomial.expand_X]
  -- Frobenius defect: `(x + y)^p - x^p - y^p` is a multiple of `p`.
  obtain ⟨r, hr⟩ :=
    exists_add_pow_prime_eq hp' (Polynomial.C s1 * Polynomial.X - Polynomial.C q1) (Polynomial.C q1)
  rw [sub_add_cancel] at hr
  have hA : (Polynomial.C s1 * Polynomial.X - Polynomial.C q1) ^ p
      = (Polynomial.C s1 * Polynomial.X) ^ p - (Polynomial.C q1) ^ p
        - (↑p : Polynomial C) * (Polynomial.C s1 * Polynomial.X - Polynomial.C q1)
            * Polynomial.C q1 * r := by
    rw [hr]; ring
  have hpow : (Polynomial.C s1 * Polynomial.X : Polynomial C) ^ p
      = Polynomial.C s0 * Polynomial.X ^ p := by
    rw [mul_pow, ← map_pow, hs]
  have hCq : (Polynomial.C q1 : Polynomial C) ^ p = Polynomial.C (q1 ^ p) :=
    (map_pow Polynomial.C q1 p).symm
  have hD : (Polynomial.expand C p) (Polynomial.C s0 * Polynomial.X - Polynomial.C q0) -
        (Polynomial.C s1 * Polynomial.X - Polynomial.C q1) ^ p
      = Polynomial.C (q1 ^ p - q0)
        + (↑p : Polynomial C) * (Polynomial.C s1 * Polynomial.X - Polynomial.C q1)
            * Polynomial.C q1 * r := by
    rw [hpexpand, hA, hpow, hCq, map_sub]
    ring
  rw [hD]
  apply Ideal.add_mem
  · exact key _ hq'
  · have hY : (↑p : Polynomial C) ∈ Ideal.span {Polynomial.C (ϖ₁ ^ p)} := by
      rw [← map_natCast Polynomial.C p]
      exact key _ hp
    exact Ideal.mul_mem_right r _
      (Ideal.mul_mem_right (Polynomial.C q1) _
        (Ideal.mul_mem_right (Polynomial.C s1 * Polynomial.X - Polynomial.C q1) _ hY))

end Work.DSM2p
