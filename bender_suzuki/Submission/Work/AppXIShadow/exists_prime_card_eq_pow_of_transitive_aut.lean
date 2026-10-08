import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.AppXIShadow

/-- An abelian finite group whose non-identity elements form a single orbit under a group of
automorphisms is elementary abelian: all of its non-identity elements have one and the same
prime order `f`, and its cardinality is a power of `f`.

Proof: if `A` is trivial take `f = 2`, `m = 0`.  Otherwise fix `1 ≠ a₀`, set `f = orderOf a₀`;
every `b ≠ 1` is `φ g a₀` with `orderOf b = orderOf a₀ = f`; `f` is prime because for `p ∣ f`
prime, `a₀^(f/p) ≠ 1` has order `f / gcd f (f/p) = p`, so `p = f`; then `A` has exponent the
prime `f`, so by Cauchy `Nat.card A = f ^ m`. -/
theorem exists_prime_card_eq_pow_of_transitive_aut {A B : Type} [Group A] [Finite A] [Group B]
    (hcomm : ∀ a b : A, a * b = b * a) (φ : B →* MulAut A)
    (htr : ∀ a : A, a ≠ 1 → ∀ b : A, b ≠ 1 → ∃ g : B, φ g a = b) :
    ∃ (f m : ℕ), f.Prime ∧ (∀ a : A, a ≠ 1 → orderOf a = f) ∧ Nat.card A = f ^ m := by
  by_cases hA : Nat.card A = 1
  · -- trivial group: take `f = 2`, `m = 0`
    refine ⟨2, 0, Nat.prime_two, ?_, by simp [hA]⟩
    intro a ha
    have hs : Subsingleton A := (Nat.card_eq_one_iff_unique.mp hA).1
    exact absurd (hs.elim a 1) ha
  · -- nontrivial group
    haveI : Nontrivial A := by
      rw [← not_subsingleton_iff_nontrivial]
      intro hs
      exact hA (Nat.card_eq_one_iff_unique.mpr ⟨hs, ⟨1⟩⟩)
    obtain ⟨a₀, ha₀⟩ := exists_ne (1 : A)
    have hfpos : 0 < orderOf a₀ := orderOf_pos a₀
    -- every non-identity element has the same order as `a₀`
    have hord : ∀ b : A, b ≠ 1 → orderOf b = orderOf a₀ := by
      intro b hb
      obtain ⟨g, hg⟩ := htr a₀ ha₀ b hb
      rw [← hg]
      exact MulEquiv.orderOf_eq (φ g) a₀
    -- that common order is prime
    have hprime : (orderOf a₀).Prime := by
      have hf1 : orderOf a₀ ≠ 1 := fun h => ha₀ (orderOf_eq_one_iff.mp h)
      rw [Nat.prime_def_lt]
      refine ⟨by omega, ?_⟩
      intro m hmlt hmdvd
      rcases eq_or_ne m 1 with h1 | h1
      · exact h1
      · exfalso
        have hmpos : 0 < m := by
          rcases Nat.eq_zero_or_pos m with h0 | hpos
          · subst h0
            rw [Nat.zero_dvd] at hmdvd
            omega
          · exact hpos
        obtain ⟨p, hpprime, hpm⟩ := Nat.exists_prime_and_dvd h1
        have hpf : p ∣ orderOf a₀ := hpm.trans hmdvd
        -- any prime dividing `orderOf a₀` equals `orderOf a₀`
        have hp_eq : p = orderOf a₀ := by
          have hnpos : 0 < orderOf a₀ / p :=
            Nat.div_pos (Nat.le_of_dvd hfpos hpf) hpprime.pos
          have hx : orderOf (a₀ ^ (orderOf a₀ / p)) = p := by
            rw [orderOf_pow a₀, Nat.gcd_eq_right (Nat.div_dvd_of_dvd hpf)]
            exact Nat.div_eq_of_eq_mul_right hnpos (Nat.div_mul_cancel hpf).symm
          have hxne : a₀ ^ (orderOf a₀ / p) ≠ 1 := by
            intro h
            rw [h, orderOf_one] at hx
            exact hpprime.ne_one hx.symm
          have h2 := hord (a₀ ^ (orderOf a₀ / p)) hxne
          rw [hx] at h2
          exact h2
        have hple : p ≤ m := Nat.le_of_dvd hmpos hpm
        omega
    -- hence `A` is an `f`-group, so its cardinality is a power of `f`
    have hisP : IsPGroup (orderOf a₀) A := by
      intro g
      by_cases hg : g = 1
      · exact ⟨0, by simp [hg]⟩
      · exact ⟨1, by rw [pow_one, ← hord g hg, pow_orderOf_eq_one]⟩
    haveI : Fact (orderOf a₀).Prime := ⟨hprime⟩
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card (p := orderOf a₀)).mp hisP
    exact ⟨orderOf a₀, m, hprime, hord, hm⟩

end Work.AppXIShadow
