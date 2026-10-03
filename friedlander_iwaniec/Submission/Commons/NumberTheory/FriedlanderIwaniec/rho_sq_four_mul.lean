import Mathlib
import Submission.Commons.NumberTheory.FriedlanderIwaniec.X2Y4_sieve_remainder_le
import Submission.Commons.NumberTheory.FriedlanderIwaniec.rho_mul_of_coprime

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.NumberTheory.FriedlanderIwaniec

/-- `ρ(b; d)` depends only on `b` modulo `d`. -/
lemma rho_eq_of_cast_eq (b b' d : ℕ) (h : (b : ZMod d) = (b' : ZMod d)) :
    Submission.rho b d = Submission.rho b' d := by
  unfold Submission.rho
  congr 1
  ext α
  simp only [Set.mem_ofPred_eq]
  rw [h]

/-- Scaling `b` by a unit modulo `m` does not change `ρ(b; m)`: the number of
roots of `α² + b² = 0` is invariant under `α ↦ u α` when `u` is a unit. -/
lemma rho_unit_mul (u x m : ℕ) (h : Nat.Coprime u m) :
    Submission.rho (u * x) m = Submission.rho x m := by
  obtain ⟨wu, hwu⟩ := (ZMod.isUnit_iff_coprime u m).mpr h
  have hcx : ((u * x : ℕ) : ZMod m) = (wu : ZMod m) * (x : ZMod m) := by
    push_cast
    rw [← hwu]
  set w : ZMod m := ((wu⁻¹ : (ZMod m)ˣ) : ZMod m) with hwdef
  have hw1 : (wu : ZMod m) * w = 1 := by
    rw [hwdef]
    exact Units.mul_inv wu
  have h1w : w * (wu : ZMod m) = 1 := by
    rw [hwdef]
    exact Units.inv_mul wu
  have hkey : ∀ α : ZMod m, (α * w) ^ 2 + (x : ZMod m) ^ 2
      = (α ^ 2 + ((u * x : ℕ) : ZMod m) ^ 2) * w ^ 2 := by
    intro α
    have hcw : (wu : ZMod m) ^ 2 * w ^ 2 = 1 := by rw [← mul_pow, hw1, one_pow]
    rw [hcx]
    calc (α * w) ^ 2 + (x : ZMod m) ^ 2
        = α ^ 2 * w ^ 2 + (x : ZMod m) ^ 2 := by ring
      _ = α ^ 2 * w ^ 2 + (x : ZMod m) ^ 2 * ((wu : ZMod m) ^ 2 * w ^ 2) := by
            rw [hcw, mul_one]
      _ = (α ^ 2 + ((wu : ZMod m) * (x : ZMod m)) ^ 2) * w ^ 2 := by ring
  refine Set.ncard_congr (fun α _ => α * w) ?_ ?_ ?_
  · intro α hα
    simp only [Set.mem_ofPred_eq] at hα ⊢
    rw [hkey α, hα, zero_mul]
  · intro α γ _ _ h
    have h' : α * w * (wu : ZMod m) = γ * w * (wu : ZMod m) := by rw [h]
    rwa [mul_assoc, h1w, mul_one, mul_assoc, h1w, mul_one] at h'
  · intro β hβ
    refine ⟨β * (wu : ZMod m), ?_, ?_⟩
    · simp only [Set.mem_ofPred_eq]
      rw [hcx]
      calc (β * (wu : ZMod m)) ^ 2 + ((wu : ZMod m) * (x : ZMod m)) ^ 2
          = (wu : ZMod m) ^ 2 * (β ^ 2 + (x : ZMod m) ^ 2) := by ring
        _ = 0 := by rw [show β ^ 2 + (x : ZMod m) ^ 2 = 0 from hβ, mul_zero]
    · rw [mul_assoc, hw1, mul_one]

theorem rho_sq_four_mul (c m : ℕ) (hm : ¬ 2 ∣ m) :
    Submission.rho ((2 * c) ^ 2) (4 * m) = 2 * Submission.rho (c ^ 2) m := by
  have h2 : Nat.Coprime 2 m := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hm
  have hcop : Nat.Coprime 4 m := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
    exact Nat.Coprime.pow_left 2 h2
  rw [rho_mul_of_coprime ((2 * c) ^ 2) 4 m hcop]
  have h4 : Submission.rho ((2 * c) ^ 2) 4 = 2 := by
    have hzero : (((2 * c) ^ 2 : ℕ) : ZMod 4) = 0 := by
      rw [show (2 * c) ^ 2 = 4 * c ^ 2 by ring]
      push_cast
      rw [show (4 : ZMod 4) = 0 from ZMod.natCast_self 4]
      ring
    rw [rho_eq_of_cast_eq ((2 * c) ^ 2) 0 4 (by simpa using hzero)]
    rw [Submission.rho_zero_eq 4 (by norm_num)]
    have hfr : Nat.floorRoot 2 (2 ^ 2) = 2 := Nat.floorRoot_pow_self (by norm_num) 2
    simpa using hfr
  have hm' : Submission.rho ((2 * c) ^ 2) m = Submission.rho (c ^ 2) m := by
    rw [show (2 * c) ^ 2 = 2 * (2 * c ^ 2) by ring]
    rw [rho_unit_mul 2 (2 * c ^ 2) m h2, rho_unit_mul 2 (c ^ 2) m h2]
  rw [h4, hm']

end Commons.NumberTheory.FriedlanderIwaniec
