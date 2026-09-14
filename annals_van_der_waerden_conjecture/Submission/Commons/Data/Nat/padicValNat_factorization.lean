import Mathlib.NumberTheory.Padics.PadicVal.Basic

namespace Commons.Data.Nat

theorem padicValNat_factorization {p d : ℕ} [Fact p.Prime] (hd : d ≠ 0) :
    d = p ^ padicValNat p d * (d / p ^ padicValNat p d) ∧
    ¬ p ∣ (d / p ^ padicValNat p d) := by
  have hdvd : p ^ padicValNat p d ∣ d := pow_padicValNat_dvd
  constructor
  · rw [Nat.mul_comm, Nat.div_mul_cancel hdvd]
  · intro hdiv
    rcases hdiv with ⟨t, ht⟩
    have h2dvd : p ^ (padicValNat p d + 1) ∣ d := by
      refine ⟨t, ?_⟩
      calc
        d = p ^ padicValNat p d * (d / p ^ padicValNat p d) := by
          rw [Nat.mul_comm, Nat.div_mul_cancel hdvd]
        _ = p ^ padicValNat p d * (p * t) := by
          rw [ht]
        _ = p ^ padicValNat p d * p * t := by
          rw [← mul_assoc]
        _ = p ^ (padicValNat p d + 1) * t := by
          rw [Nat.pow_succ]
    exact (pow_succ_padicValNat_not_dvd (p := p) (n := d) hd) h2dvd

end Commons.Data.Nat