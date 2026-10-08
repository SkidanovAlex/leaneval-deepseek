import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.S3

/-- If `ℓ` is a prime not dividing the order of a finite commutative group `K`, then the `ℓ`-th
power map `k ↦ k ^ ℓ` is an automorphism of `K`. -/
theorem powMulAut_of_not_dvd {K : Type} [Group K] [IsMulCommutative K] [Finite K] {ℓ : ℕ} (hℓ : ℓ.Prime)
    (h : ¬ ℓ ∣ Nat.card K) : ∃ Φ : MulAut K, ∀ k : K, Φ k = k ^ ℓ := by
  have hcop : (Nat.card K).Coprime ℓ := (hℓ.coprime_iff_not_dvd.2 h).symm
  refine ⟨{ Equiv.ofBijective (fun k : K => k ^ ℓ) (Nat.Coprime.pow_left_bijective hcop) with
      map_mul' := fun a b => by
        change (a * b) ^ ℓ = a ^ ℓ * b ^ ℓ
        exact Commute.mul_pow (mul_comm' a b) ℓ }, ?_⟩
  intro k
  simp

end Work.S3
