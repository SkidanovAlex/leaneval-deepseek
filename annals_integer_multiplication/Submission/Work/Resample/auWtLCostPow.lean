import Mathlib

namespace Work.Resample

/-- Basic exponential growth fact: for `M ≥ 4`, `2*M + 2 ≤ 2^M`. -/
lemma two_mul_add_two_le_two_pow (M : ℕ) (hM : 4 ≤ M) : 2*M + 2 ≤ 2^M := by
  induction M, hM using Nat.le_induction with
  | base => norm_num
  | succ M hM ih =>
    rw [Nat.pow_succ]
    have h1 : 1 ≤ 2^M := Nat.one_le_two_pow
    nlinarith [ih, h1]

theorem auWtLCostPow {Krep Kenum Kml KE p : ℕ} (hp : 1 ≤ p) :
    (Krep+Kenum+Kml+KE+40) * (p+1)^8 ≤ (p+1)^(2^(Krep+Kenum+Kml+KE+40)) ∧
    KE * (p+1)^(KE+2) ≤ (p+1)^(2^(Krep+Kenum+Kml+KE+40)) := by
  set M := Krep+Kenum+Kml+KE+40
  set N := p+1
  have hNpos : 0 < N := by omega
  have hM40 : 40 ≤ M := by omega
  have hKE : KE ≤ M := by omega
  have hbig : 2*M + 2 ≤ 2^M := two_mul_add_two_le_two_pow M (by omega)
  have hpow : M + 8 ≤ 2^M := by omega
  have hpow2 : 2*KE + 2 ≤ 2^M := by omega
  have hNM : M ≤ N^M := le_of_lt (Nat.lt_pow_self (by omega : 1 < N))
  have hNKE : KE ≤ N^KE := le_of_lt (Nat.lt_pow_self (by omega : 1 < N))
  constructor
  · calc M * N^8 ≤ N^M * N^8 := Nat.mul_le_mul_right _ hNM
      _ = N^(M+8) := (Nat.pow_add N M 8).symm
      _ ≤ N^(2^M) := Nat.pow_le_pow_right hNpos hpow
  · rcases Nat.eq_zero_or_pos KE with hKE0 | hKEpos
    · subst hKE0; simp
    · calc KE * N^(KE+2) ≤ N^KE * N^(KE+2) := Nat.mul_le_mul_right _ hNKE
        _ = N^(KE+2) * N^KE := Nat.mul_comm _ _
        _ = N^((KE+2)+KE) := (Nat.pow_add N (KE+2) KE).symm
        _ = N^(2*KE+2) := by congr 1; omega
        _ ≤ N^(2^M) := Nat.pow_le_pow_right hNpos hpow2

end Work.Resample
