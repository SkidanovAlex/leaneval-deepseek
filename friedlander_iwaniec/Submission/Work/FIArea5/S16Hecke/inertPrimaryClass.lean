import Mathlib
import Submission.Work.FIPlan.Interface
import Submission.Work.FIArea5.S16Hecke.primaryAux
import Submission.Commons.NumberTheory.GaussianInt.ncard_assoc_irred_norm_prime

set_option autoImplicit false

namespace Work.FIArea5.S16Hecke

open Work.FIPlan

noncomputable section

/-! ## The inert prime `-p` of `ℤ[i]` and its primary powers -/

/-- The rational prime is fixed by conjugation. -/
theorem star_natCast (p : ℕ) : star (p : GaussianInt) = (p : GaussianInt) := by
  ext <;> simp

/-- `-p` is primary for `p ≡ 3 (mod 4)`. -/
theorem isPrimary_neg_nat_prime (p : ℕ) (hp : p.Prime) (h3 : p % 4 = 3) :
    IsPrimary (-(p : GaussianInt)) := by
  have hp2 : p ≠ 2 := by rintro rfl; omega
  have hodd : Odd (-(p : GaussianInt)).re := by
    rw [show (-(p : GaussianInt)).re = -(p : ℤ) by simp]
    exact ((Int.odd_coe_nat p).mpr (hp.odd_of_ne_two hp2)).neg
  have hev : Even (-(p : GaussianInt)).im := by
    rw [show (-(p : GaussianInt)).im = 0 by simp]; exact ⟨0, rfl⟩
  refine ⟨hodd, hev, ?_⟩
  rw [show (-(p : GaussianInt)).im = 0 by simp,
      show (-(p : GaussianInt)).re = -(p : ℤ) by simp, Int.modEq_iff_dvd]
  have h4 : (4 : ℤ) ∣ ((p : ℤ) + 1) := by
    have hnat : (4 : ℕ) ∣ p + 1 := by omega
    exact_mod_cast hnat
  have hkey : -(p : ℤ) - 1 - 0 = -((p : ℤ) + 1) := by ring
  rw [hkey]
  exact dvd_neg.mpr h4

/-- `gnorm (-p) = p ^ 2`. -/
theorem gnorm_neg_nat_prime (p : ℕ) : gnorm (-(p : GaussianInt)) = p ^ 2 := by
  rw [show gnorm (-(p : GaussianInt)) = (-(p : GaussianInt)).norm.natAbs from rfl,
    Zsqrtd.norm_neg, Zsqrtd.norm_natCast, Int.natAbs_mul, Int.natAbs_natCast, pow_two]

/-- `-p` is irreducible (equivalently prime) in `ℤ[i]` for `p ≡ 3 (mod 4)`. -/
theorem irreducible_neg_nat_prime (p : ℕ) (hp : p.Prime) (h3 : p % 4 = 3) :
    Irreducible (-(p : GaussianInt)) := by
  have hpprime : Prime (p : GaussianInt) :=
    (@GaussianInt.prime_iff_mod_four_eq_three_of_nat_prime p ⟨hp⟩).mpr h3
  exact (UniqueFactorizationMonoid.irreducible_iff_prime).mpr (Prime.neg hpprime)

/-- Powers of a primary element are primary. -/
theorem isPrimary_pow {z : GaussianInt} (hz : IsPrimary z) (n : ℕ) : IsPrimary (z ^ n) := by
  induction n with
  | zero => simpa using isPrimary_one
  | succ k ih => rw [pow_succ]; exact isPrimary_mul ih hz

/-- **Classification of the Gaussian integers of `p`-power norm, `p ≡ 3 (mod 4)`.**

Every Gaussian integer of norm `p ^ ν` is a unit multiple of `p ^ (ν / 2)` (and `ν` is even).
This is the arithmetical content of the fact that `p` is inert in `ℤ[i]`. -/
theorem exists_unit_mul_prime_pow (p : ℕ) (hp : p.Prime) (h3 : p % 4 = 3)
    (ν : ℕ) (z : GaussianInt) (hz : gnorm z = p ^ ν) :
    ∃ μ : ℕ, ν = 2 * μ ∧ ∃ u : GaussianInt, IsUnit u ∧ z = u * (p : GaussianInt) ^ μ := by
  have hp_pos : 0 < p := hp.pos
  have hpprime : Prime (p : GaussianInt) :=
    (@GaussianInt.prime_iff_mod_four_eq_three_of_nat_prime p ⟨hp⟩).mpr h3
  have hgnormp : gnorm (p : GaussianInt) = p ^ 2 := by
    rw [show gnorm (p : GaussianInt) = (p : GaussianInt).norm.natAbs from rfl,
      Zsqrtd.norm_natCast, Int.natAbs_mul, Int.natAbs_natCast, pow_two]
  revert z
  refine Nat.strong_induction_on ν (fun n ih z hz => ?_)
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    have hz1 : gnorm z = 1 := by simpa using hz
    exact ⟨0, rfl, z, Zsqrtd.norm_eq_one_iff.mp hz1, by simp⟩
  · have hz0 : z ≠ 0 := by
      intro h
      rw [h] at hz
      simp only [gnorm, Zsqrtd.norm_zero, Int.natAbs_zero] at hz
      exact pow_ne_zero n hp.ne_zero hz.symm
    -- `p` divides `z`
    have hcast : (p : GaussianInt) ^ n = z * star z := by
      have h := Commons.NumberTheory.GaussianInt.norm_natAbs_cast_eq z
      rw [show z.norm.natAbs = p ^ n from hz, Nat.cast_pow] at h
      exact h
    have hdvd : (p : GaussianInt) ∣ z * star z := by
      rw [← hcast]
      exact dvd_pow_self _ (by omega)
    have hpdvd : (p : GaussianInt) ∣ z := by
      rcases hpprime.dvd_or_dvd hdvd with h | h
      · exact h
      · obtain ⟨w, hw⟩ := h
        refine ⟨star w, ?_⟩
        have hstar : star (p : GaussianInt) = (p : GaussianInt) := star_natCast p
        have hthis : z = star w * (p : GaussianInt) := by
          have h2 := congrArg star hw
          rw [star_mul, star_star, hstar] at h2
          exact h2
        rw [hthis, mul_comm]
    obtain ⟨z1, hz1⟩ := hpdvd
    -- norm of `z1`
    have hpow : p ^ n = p ^ 2 * gnorm z1 := by
      rw [← hz, hz1, gnorm_mul, hgnormp]
    have hz1ne : z1 ≠ 0 := by
      intro h; rw [h, mul_zero] at hz1; exact hz0 hz1
    have hpos1 : 0 < gnorm z1 := by
      rw [show gnorm z1 = z1.norm.natAbs from rfl]
      exact Int.natAbs_pos.mpr (ne_of_gt ((GaussianInt.norm_pos).mpr hz1ne))
    have hn2 : 2 ≤ n := by
      by_contra hlt
      have hn1 : n = 1 := by omega
      have hp1 : p = p ^ 2 * gnorm z1 := by simpa [hn1] using hpow
      have hle : p ^ 2 ≤ p := by
        calc p ^ 2 = p ^ 2 * 1 := (mul_one _).symm
          _ ≤ p ^ 2 * gnorm z1 := Nat.mul_le_mul_left (p ^ 2) (by omega)
          _ = p := hp1.symm
      have h2 : p ≤ 1 := Nat.le_of_mul_le_mul_left (by simpa [pow_two] using hle) hp_pos
      omega
    have hgn1 : gnorm z1 = p ^ (n - 2) := by
      have h3' : p ^ 2 * p ^ (n - 2) = p ^ 2 * gnorm z1 := by
        rw [mul_comm (p ^ 2), Nat.pow_sub_mul_pow p hn2]; exact hpow
      exact (Nat.mul_left_cancel (pow_pos hp_pos 2) h3').symm
    obtain ⟨μ, hμ, u, hu, hzu⟩ := ih (n - 2) (by omega) z1 hgn1
    refine ⟨μ + 1, by omega, u, hu, ?_⟩
    rw [hz1, hzu, pow_succ]
    ring


theorem inertPrimaryClass (p : ℕ) (hp : p.Prime) (h3 : p % 4 = 3) :
    Work.FIPlan.IsPrimary (-(p : GaussianInt)) ∧ Irreducible (-(p : GaussianInt)) ∧
    Work.FIPlan.gnorm (-(p : GaussianInt)) = p ^ 2 ∧
    (∀ ν : ℕ, ∀ z : GaussianInt, Work.FIPlan.IsPrimary z → Work.FIPlan.gnorm z = p ^ ν →
        ∃! μ : ℕ, ν = 2 * μ ∧ z = (-(p : GaussianInt)) ^ μ) := by
  have hpri : IsPrimary (-(p : GaussianInt)) := isPrimary_neg_nat_prime p hp h3
  refine ⟨hpri, irreducible_neg_nat_prime p hp h3, gnorm_neg_nat_prime p, ?_⟩
  intro ν z hzp hz
  obtain ⟨μ, hν, u, hu, hzu⟩ := exists_unit_mul_prime_pow p hp h3 ν z hz
  have hdec : (p : GaussianInt) ^ μ = (-1 : GaussianInt) ^ μ * (-(p : GaussianInt)) ^ μ := by
    have h1 : (-(p : GaussianInt)) = (-1 : GaussianInt) * (p : GaussianInt) := by
      rw [neg_eq_neg_one_mul]
    have hsq : (-1 : GaussianInt) ^ μ * (-1 : GaussianInt) ^ μ = 1 := by
      rw [← mul_pow, show (-1 : GaussianInt) * (-1) = 1 by ring, one_pow]
    rw [h1, mul_pow, ← mul_assoc, hsq, one_mul]
  have hz2 : z = (u * (-1 : GaussianInt) ^ μ) * (-(p : GaussianInt)) ^ μ := by
    rw [hzu, hdec, mul_assoc]
  have hwu : IsUnit (u * (-1 : GaussianInt) ^ μ) := IsUnit.mul hu (IsUnit.pow μ isUnit_neg_one)
  have hprod : (-(p : GaussianInt)) ^ μ * (u * (-1 : GaussianInt) ^ μ) = z := by
    rw [mul_comm, ← hz2]
  have hwp : IsPrimary (u * (-1 : GaussianInt) ^ μ) :=
    isPrimary_of_isPrimary_mul_right (a := (-(p : GaussianInt)) ^ μ)
      (isPrimary_pow hpri μ) (hprod.symm ▸ hzp)
  have hw1 : u * (-1 : GaussianInt) ^ μ = 1 := isPrimary_unit hwp hwu
  have hzfin : z = (-(p : GaussianInt)) ^ μ := by
    rw [hz2, hw1, one_mul]
  exact ⟨μ, ⟨hν, hzfin⟩, fun μ' h' => by obtain ⟨h1', -⟩ := h'; omega⟩

end

end Work.FIArea5.S16Hecke
