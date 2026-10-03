import Mathlib
import Submission.Work.FIPlan.Interface
import Submission.Work.FIArea5.S16Hecke.primaryAux

namespace Work.FIArea5.S16Hecke

open Work.FIPlan

/-! ## Auxiliary facts about primary Gaussian integers and conjugation -/

/-- Conjugation preserves the primary condition: `star z` has real part `z.re` and imaginary
part `-z.im`, and `-z.im ≡ z.re - 1 (mod 4)` because `z.im ≡ z.re - 1` and `z.im` is even. -/
theorem isPrimary_star {z : GaussianInt} (hz : IsPrimary z) : IsPrimary (star z) := by
  obtain ⟨ho, he, hc⟩ := hz
  refine ⟨by simpa using ho, by simpa using he.neg, ?_⟩
  have hre : (star z).re = z.re := by simp
  have him : (star z).im = -z.im := by simp
  rw [him, hre]
  obtain ⟨k, hk⟩ := Int.modEq_iff_dvd.mp hc
  obtain ⟨j, hj⟩ := he
  rw [Int.modEq_iff_dvd]
  use k + j
  omega

/-- `|z|²` is invariant under conjugation. -/
theorem gnorm_star (z : GaussianInt) : gnorm (star z) = gnorm z := by
  simp only [gnorm]
  rw [Zsqrtd.norm_conj]

/-- `z * z̄ = |z|²` as a Gaussian integer. -/
theorem mul_star_eq_gnorm (z : GaussianInt) : z * star z = (gnorm z : GaussianInt) := by
  have h1 : ((gnorm z : ℕ) : ℤ) = z.re ^ 2 + z.im ^ 2 := by
    rw [gnorm, Int.natAbs_of_nonneg (Zsqrtd.norm_nonneg (by norm_num : (-1:ℤ) ≤ 0) z),
      Zsqrtd.norm_def]
    ring
  ext
  · simp only [Zsqrtd.re_mul, Zsqrtd.re_natCast]
    simp
    rw [h1]
    ring
  · simp only [Zsqrtd.im_mul, Zsqrtd.im_natCast]
    simp
    ring_nf

/-! ## The classification -/

/-- **The primary Gaussian integers of `p`-power norm are the products `π ^ a * π̄ ^ (ν - a)`.**

Let `π` be a primary irreducible Gaussian integer of norm `p`.  Then every primary `z` with
`|z|² = p ^ ν` is of the shape `π ^ a * π̄ ^ (ν - a)` for some `a ≤ ν`.

The proof is a descent on `ν`.  Since `π * π̄ = p` and `z * z̄ = p ^ ν`, the prime `π` divides
`z * z̄`, so (by primality of `π`) it divides `z` or `z̄`; in the latter case `π̄` divides `z`.
Cancelling the primary factor (primary elements form a submonoid in which the only unit is `1`)
reduces `ν` by one, and the induction hypothesis finishes. -/
theorem primaryPowClassify (p : ℕ) (π : GaussianInt) (hp : 0 < p)
    (hπprim : Work.FIPlan.IsPrimary π) (hπgn : Work.FIPlan.gnorm π = p)
    (hπirr : Irreducible π) :
    ∀ ν : ℕ, ∀ z : GaussianInt, Work.FIPlan.IsPrimary z → Work.FIPlan.gnorm z = p ^ ν →
      ∃ a : ℕ, a ≤ ν ∧ z = π ^ a * (star π) ^ (ν - a) := by
  have hπprime : Prime π := (UniqueFactorizationMonoid.irreducible_iff_prime).mp hπirr
  have hstπprim : IsPrimary (star π) := isPrimary_star hπprim
  have hgnstπ : gnorm (star π) = p := by rw [gnorm_star, hπgn]
  have hππ : π * star π = (p : GaussianInt) := by rw [mul_star_eq_gnorm, hπgn]
  intro ν
  induction ν using Nat.strong_induction_on with
  | _ ν ih =>
    intro z hzp hzg
    rcases Nat.eq_zero_or_pos ν with h0 | hpos
    · -- `ν = 0`: `z` has norm `1`, hence is the primary unit `1`
      subst h0
      refine ⟨0, le_refl 0, ?_⟩
      simp only [pow_zero, tsub_zero, mul_one]
      have hz1 : z.norm.natAbs = 1 := by
        change gnorm z = 1
        rw [hzg, pow_zero]
      exact isPrimary_unit hzp (Zsqrtd.norm_eq_one_iff.mp hz1)
    · -- `ν ≥ 1`
      have hzprod : z * star z = (p : GaussianInt) ^ ν := by
        rw [mul_star_eq_gnorm, hzg, Nat.cast_pow]
      have hdvd : π ∣ z * star z := by
        rw [hzprod]
        exact dvd_trans ⟨star π, hππ.symm⟩ (dvd_pow_self (p : GaussianInt) (by omega))
      -- dividing an equal-norm factor by a norm-`p` factor drops the exponent by one
      have step : ∀ d w : GaussianInt, gnorm d = p → z = d * w → gnorm w = p ^ (ν - 1) := by
        intro d w hd hz
        have h1 : p * gnorm w = p ^ ν := by rw [← hzg, hz, gnorm_mul, hd]
        have h2 : p ^ (ν - 1) * p = p ^ ν := by
          have := Nat.pow_sub_mul_pow p (m := 1) (n := ν) (by omega)
          simpa using this
        have h3 : gnorm w * p = p ^ (ν - 1) * p := by rw [mul_comm (gnorm w) p, h1, h2]
        exact Nat.mul_right_cancel hp h3
      rcases hπprime.dvd_or_dvd hdvd with h | h
      · -- `π ∣ z`
        obtain ⟨w, hw⟩ := h
        have hwp : IsPrimary w :=
          isPrimary_of_isPrimary_mul_right hπprim (by rw [← hw]; exact hzp)
        have hgw : gnorm w = p ^ (ν - 1) := step π w hπgn hw
        obtain ⟨a, ha, hwa⟩ := ih (ν - 1) (by omega) w hwp hgw
        refine ⟨a + 1, by omega, ?_⟩
        rw [hw, hwa, ← mul_assoc, ← pow_succ', show ν - (a + 1) = ν - 1 - a by omega]
      · -- `π ∣ z̄`, hence `π̄ ∣ z`
        obtain ⟨t, ht⟩ := h
        have hz_eq : z = star π * star t := by
          have h2 : z = star t * star π := by
            have hh := congrArg star ht
            rwa [star_star, star_mul] at hh
          rw [h2, mul_comm (star t) (star π)]
        have hwp : IsPrimary (star t) :=
          isPrimary_of_isPrimary_mul_right hstπprim (by rw [← hz_eq]; exact hzp)
        have hgw : gnorm (star t) = p ^ (ν - 1) := step (star π) (star t) hgnstπ hz_eq
        obtain ⟨a, ha, hwa⟩ := ih (ν - 1) (by omega) (star t) hwp hgw
        refine ⟨a, by omega, ?_⟩
        rw [hz_eq, hwa, show ν - a = ν - 1 - a + 1 by omega, pow_succ', mul_left_comm]

end Work.FIArea5.S16Hecke
