import Mathlib

namespace Work.FIChain

/-- Any divisor `n₁` of the primorial `Π(Pz) = ∏_{p ≤ Pz} p` of the primes up to `Pz` is squarefree
with all its prime factors `≤ Pz`; hence `n₁ = ∏_{p | n₁} p ≤ Pz ^ ω(n₁)`. -/
theorem le_pow_card_primeFactors_of_dvd_primorial {Pz n₁ : ℕ} (hPz : 2 ≤ Pz)
    (hdvd : n₁ ∣ primorial Pz) : n₁ ≤ Pz ^ n₁.primeFactors.card := by
  rcases eq_or_ne n₁ 0 with h0 | h0
  · rw [h0]; exact Nat.zero_le _
  · have hsq : Squarefree n₁ := (squarefree_primorial Pz).squarefree_of_dvd hdvd
    calc n₁ = ∏ p ∈ n₁.primeFactors, p := (Nat.prod_primeFactors_of_squarefree hsq).symm
      _ ≤ ∏ p ∈ n₁.primeFactors, Pz :=
          Finset.prod_le_prod' (fun p hp =>
            ((Nat.prime_of_mem_primeFactors hp).dvd_primorial_iff).mp
              (Nat.dvd_of_mem_primeFactors hp |>.trans hdvd))
      _ = Pz ^ n₁.primeFactors.card := Finset.prod_const Pz

end Work.FIChain
