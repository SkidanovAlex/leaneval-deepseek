import Mathlib
import Submission.Work.HP.HP2.ClassCountPrelude
import Submission.Work.HP.HP2.finite_eNorm_ball

namespace Work.ClassCount

/-- The set counted by `mobiusCount` is contained in the coset set `c + W ℤ^{n+1}` intersected
with the cone region of radius `T/k`: `Work.HP.mobiusCount d n a b W k α T` counts the nonzero `z`
with `k z ≡ b (mod W)`, `‖z‖ ≤ T/k` and `z` in the cone, while the right-hand set is
`{v | v ≡ c (mod W), ‖v‖ ≤ T/k, v in the cone}`.  Since `k c ≡ b (mod W)` and `gcd (k, W) = 1`,
we have `k z ≡ k c (mod W) ⟹ z ≡ c (mod W)`, so the first set is contained in the second (the
`z ≠ 0` condition only makes it smaller); both are finite, so `ncard` is monotone. -/
theorem mobiusCount_le_coset_ncard (d n : ℕ) (a : Work.HP.Mon d n → ℤ) (b c : Fin (n + 1) → ℤ)
    (W k : ℕ) (α T : ℝ) (hc : ∀ i, (W : ℤ) ∣ (k : ℤ) * c i - b i)
    (hcop : Nat.Coprime k W) :
    Work.HP.mobiusCount d n a b W k α T
      ≤ ({v : Fin (n + 1) → ℤ | (∀ i, (W : ℤ) ∣ v i - c i) ∧
          Work.HP.toR v ∈ Work.HP.coneRegion d n a α (T / (k : ℝ))} : Set (Fin (n + 1) → ℤ)).ncard := by
  classical
  unfold Work.HP.mobiusCount
  refine Set.ncard_le_ncard ?_ ?_
  · -- Membership: the congruence `k z ≡ b` together with `k c ≡ b` and `gcd k W = 1`
    -- forces `z ≡ c`, and the cone/norm data transfer verbatim.
    rintro z ⟨hzne, hcong, hnorm, hcone⟩
    refine ⟨fun i => ?_, ?_⟩
    · have hdvd : (W : ℤ) ∣ (k : ℤ) * (z i - c i) := by
        have h := dvd_sub (hcong i) (hc i)
        have he : (k : ℤ) * z i - b i - ((k : ℤ) * c i - b i) = (k : ℤ) * (z i - c i) := by ring
        rwa [he] at h
      exact ((hcop.isCoprime : IsCoprime (k : ℤ) (W : ℤ)).symm).dvd_of_dvd_mul_left hdvd
    · rw [Work.HP.HP2.mem_coneRegion_toR]
      exact ⟨hnorm, hcone⟩
  · -- The target coset set is contained in a Euclidean ball of integer vectors, hence finite.
    refine (Work.HP.HP2.finite_eNorm_ball (T / (k : ℝ))).subset ?_
    rintro v ⟨hcong, hcone⟩
    exact ((Work.HP.HP2.mem_coneRegion_toR d n a α (T / (k : ℝ)) v).mp hcone).1

end Work.ClassCount
