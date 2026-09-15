import Mathlib.NumberTheory.LSeries.PrimesInAP

namespace Commons.NumberTheory.PrimesInAP

/-- Dirichlet's theorem on primes in arithmetic progressions, reformulated as
infinitely many primes of the affine form `W * n + r` for fixed coprime `W`, `r`. -/
theorem infinite_affine_prime_set {W r : ℕ} (hW : 1 ≤ W) (hcop : r.Coprime W) :
    Set.Infinite {n : ℕ | Nat.Prime (W * n + r)} := by
  rw [Set.infinite_iff_exists_gt]
  intro N
  have hW0 : W ≠ 0 := by omega
  have hWpos : 0 < W := by omega
  -- A prime above `W * (N+1) + r` in the residue class `r mod W` (Dirichlet).
  obtain ⟨p, hpgt, hpp, hcong⟩ :=
    Nat.forall_exists_prime_gt_and_modEq (W * (N + 1) + r) hW0 hcop
  -- `p` is representable as `W * t + r` with `t > N`.
  have hrle : r ≤ p := by
    exact le_trans (Nat.le_add_left r (W * (N + 1))) (le_of_lt hpgt)
  have hdvd : W ∣ p - r :=
    (Nat.modEq_iff_dvd' (a := r) (b := p) hrle).1 hcong.symm
  rcases hdvd with ⟨t, hsub⟩
  have hp_eq : W * t + r = p := by
    rw [← hsub]
    exact Nat.sub_add_cancel hrle
  refine ⟨t, ?hmem, ?hgt⟩
  · -- `t` belongs to the set: `W * t + r` is prime.
    dsimp
    rw [hp_eq]
    exact hpp
  · -- `t > N`
    have hgt' : W * (N + 1) + r < W * t + r := by
      rw [← hp_eq] at hpgt
      exact hpgt
    have hlt : W * (N + 1) < W * t :=
      (Nat.add_lt_add_iff_right (k := r)).1 hgt'
    have hN1 : N + 1 < t := (Nat.mul_lt_mul_left hWpos).1 hlt
    omega

end Commons.NumberTheory.PrimesInAP