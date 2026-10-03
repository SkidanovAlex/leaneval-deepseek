import Mathlib
import Submission.Work.FIArea7.prop232Defs

namespace Work.FIArea7

/-- **The Grössencharacter is multiplicative on primary fibres of coprime norms.**
For `m, n ≥ 1` coprime, `w ∈ primarySet m` and `z ∈ primarySet n` are automatically nonzero and
coprime Gaussian integers: a common divisor `d` satisfies `gnorm d ∣ gnorm w = m` and
`gnorm d ∣ gnorm z = n` (norm is multiplicative), so `gnorm d = 1`.  Hence the multiplicativity
hypothesis on `χ` gives `ψ(w z) = ψ(w) ψ(z)` for `ψ = grossenChar χ k` — exactly
`Work.FIArea7.grossenChar_mul_of_coprime` (already proved in `Submission.Work.FIArea7.prop232Defs`)
applied to nonzero, coprime `w`, `z`.  (`IsCoprime` in `ℤ[i]` is the Bézout condition; a common
divisor of `w` and `z` being a unit gives it via `isRelPrime_iff_isCoprime`, since `ℤ[i]` is a
PID.) -/
lemma grossenChar_mul_primarySet {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (hcop : Nat.Coprime m n)
    (k : ℤ) (chi : GaussianInt → ℂ)
    (hmul : ∀ z1 z2 : GaussianInt, IsCoprime z1 z2 → chi (z1 * z2) = chi z1 * chi z2)
    {w z : GaussianInt} (hw : w ∈ Work.FIArea7.primarySet m)
    (hz : z ∈ Work.FIArea7.primarySet n) :
    Work.FIArea7.grossenChar chi k (w * z)
      = Work.FIArea7.grossenChar chi k w * Work.FIArea7.grossenChar chi k z := by
  -- `w` and `z` are nonzero because their norms are `m`, `n ≥ 1`.
  have hw0 : w ≠ 0 := by
    intro h
    have hg := gnorm_of_mem_primarySet hw
    rw [h] at hg
    simp [Work.FIPlan.gnorm, Zsqrtd.norm] at hg
    omega
  have hz0 : z ≠ 0 := by
    intro h
    have hg := gnorm_of_mem_primarySet hz
    rw [h] at hg
    simp [Work.FIPlan.gnorm, Zsqrtd.norm] at hg
    omega
  -- A common divisor of `w` and `z` has norm dividing both `m` and `n`, hence norm `1`.
  have hdvd : ∀ d : GaussianInt, d ∣ w → d ∣ z → Work.FIPlan.gnorm d = 1 := by
    intro d hdw hdz
    have h1 : Work.FIPlan.gnorm d ∣ m := by
      rw [← gnorm_of_mem_primarySet hw]
      obtain ⟨c, rfl⟩ := hdw
      simp only [Work.FIPlan.gnorm, Zsqrtd.norm_mul, Int.natAbs_mul]
      exact dvd_mul_right _ _
    have h2 : Work.FIPlan.gnorm d ∣ n := by
      rw [← gnorm_of_mem_primarySet hz]
      obtain ⟨c, rfl⟩ := hdz
      simp only [Work.FIPlan.gnorm, Zsqrtd.norm_mul, Int.natAbs_mul]
      exact dvd_mul_right _ _
    have h3 : Work.FIPlan.gnorm d ∣ Nat.gcd m n := Nat.dvd_gcd h1 h2
    rw [hcop.gcd_eq_one] at h3
    exact Nat.dvd_one.mp h3
  -- So `w` and `z` have no common non-unit divisor: `IsRelPrime`, hence Bézout-coprime in `ℤ[i]`.
  have hrel : IsRelPrime w z := fun d hdw hdz =>
    Zsqrtd.norm_eq_one_iff.mp (hdvd d hdw hdz)
  exact grossenChar_mul_of_coprime hmul hw0 hz0 (isRelPrime_iff_isCoprime.mp hrel)

end Work.FIArea7
