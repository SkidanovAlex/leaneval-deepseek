import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.StageB

theorem pow_eq_forces_pow_two {F : Type*} [Field F] [CharP F 2]
    (c : F) (hc : c ≠ 0) {m : ℕ} (hm : 1 ≤ m)
    (h : (Polynomial.X + Polynomial.C c : Polynomial F) ^ m
        = Polynomial.X ^ m + Polynomial.C (c ^ m)) :
    ∃ s : ℕ, m = 2 ^ s := by
  -- The coefficient of `X ^ k` in `(X + c) ^ m` is `c ^ (m - k) * (m.choose k)`; for
  -- `1 ≤ k ≤ m - 1` the right-hand side has coefficient `0`, so `2 ∣ m.choose k`.
  have key : ∀ k, 1 ≤ k → k ≤ m - 1 → (2 : ℕ) ∣ m.choose k := by
    intro k hk1 hk2
    have hcoeff := congrArg (fun p : Polynomial F => p.coeff k) h
    rw [Polynomial.coeff_X_add_C_pow] at hcoeff
    have hkne_m : k ≠ m := by omega
    have hkne_0 : k ≠ 0 := by omega
    simp only [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_C,
      hkne_0, hkne_m, ite_false, add_zero] at hcoeff
    have hcpow : c ^ (m - k) ≠ 0 := pow_ne_zero _ hc
    have hzero : ((m.choose k : F)) = 0 := by
      rcases mul_eq_zero.mp hcoeff with h1 | h2
      · exact absurd h1 hcpow
      · exact h2
    exact (CharP.cast_eq_zero_iff F 2 (m.choose k)).mp hzero
  -- Every intermediate binomial coefficient of `m` is even, hence `m` is a power of `2`.
  have hmod : ∀ i ∈ Finset.Icc 1 (m - 1), m.choose i ≡ 0 [MOD 2] := by
    intro i hi
    rw [Finset.mem_Icc] at hi
    exact Nat.modEq_zero_iff_dvd.mpr (key i hi.1 hi.2)
  exact ⟨_, Choose.eq_pow_multiplicity_of_choose_modEq_zero_nat (n := m) (p := 2)
    (by omega) hmod⟩

end Work.PSU3.StageB
