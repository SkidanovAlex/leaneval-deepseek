import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Int.Star
import Mathlib.NumberTheory.Zsqrtd.GaussianInt

namespace Commons.NumberTheory.GaussianInt

open Zsqrtd

private lemma irreducible_star_of {z : GaussianInt} (h : Irreducible (star z)) :
    Irreducible z := by
  refine ⟨fun hu => h.1 hu.star, fun a b hab => ?_⟩
  have h2 : star z = star b * star a := by rw [hab, star_mul]
  rcases h.2 h2 with hb | ha
  · exact Or.inr (isUnit_star.mp hb)
  · exact Or.inl (isUnit_star.mp ha)

private lemma irreducible_star_iff {z : GaussianInt} :
    Irreducible (star z) ↔ Irreducible z :=
  ⟨irreducible_star_of, fun h => irreducible_star_of (z := star z) (by rwa [star_star])⟩

theorem irreducible_norm_prime_pow {z : GaussianInt} (hz : Irreducible z) :
    ∃ p k : ℕ, p.Prime ∧ 1 ≤ k ∧ z.norm.natAbs = p ^ k := by
  -- basic facts about z
  have hz0 : z ≠ 0 := hz.ne_zero
  have hzu : ¬ IsUnit z := hz.1
  have hzpos : 0 < z.norm := (GaussianInt.norm_pos).mpr hz0
  have hz_ne_one : z.norm ≠ 1 := fun h =>
    hzu ((Zsqrtd.norm_eq_one_iff' (d := -1) (by norm_num) z).mp h)
  -- n := natAbs(norm z) ≥ 2
  set n : ℕ := z.norm.natAbs with hn
  have hn_int : (n : ℤ) = z.norm := by
    rw [hn]
    exact Int.natAbs_of_nonneg (le_of_lt hzpos)
  have hn_ge2 : 2 ≤ n := by omega
  -- choose a prime p dividing n
  obtain ⟨p, hpprime, hpdvdn⟩ := Nat.exists_prime_and_dvd (by omega : n ≠ 1)
  -- facts about (p : ℤ[i])
  have hp0 : (p : GaussianInt) ≠ 0 := by
    exact_mod_cast hpprime.ne_zero
  have hpu : ¬ IsUnit (p : GaussianInt) := by
    intro h
    have h1 := (Zsqrtd.norm_eq_one_iff' (d := -1) (by norm_num) (p : GaussianInt)).mpr h
    rw [Zsqrtd.norm_natCast] at h1
    have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast hpprime.two_le
    nlinarith
  -- (p : ℤ[i]) ∣ z * star z
  have hpdvd_prod : (p : GaussianInt) ∣ z * star z := by
    have hn_cast : (n : GaussianInt) = z * star z := by
      rw [← Zsqrtd.norm_eq_mul_conj z, ← hn_int]
      push_cast
      ring
    rw [← hn_cast]
    exact Nat.cast_dvd_cast hpdvdn
  -- choose a Gaussian prime π dividing (p : ℤ[i])
  obtain ⟨π, hπirr, hπdvdp⟩ := WfDvdMonoid.exists_irreducible_factor hpu hp0
  have hπdvd_prod : π ∣ z * star z := dvd_trans hπdvdp hpdvd_prod
  have hszirr : Irreducible (star z) := irreducible_star_iff.mpr hz
  have hπprime : Prime π := (UniqueFactorizationMonoid.irreducible_iff_prime).mp hπirr
  -- norm π = norm z
  have hnorm_pi : π.norm = z.norm := by
    have key : ∀ m : GaussianInt, z = π * m → IsUnit m := by
      intro m hm
      rcases hz.isUnit_or_isUnit hm with hu | hu
      · exact absurd hu hπirr.1
      · exact hu
    have key' : ∀ m : GaussianInt, star z = π * m → IsUnit m := by
      intro m hm
      rcases hszirr.isUnit_or_isUnit hm with hu | hu
      · exact absurd hu hπirr.1
      · exact hu
    rcases hπprime.dvd_or_dvd hπdvd_prod with h | h
    · obtain ⟨m, hm⟩ := h
      have hy := key m hm
      have hmn : m.norm = 1 := (Zsqrtd.norm_eq_one_iff' (d := -1) (by norm_num) m).mpr hy
      calc π.norm = π.norm * 1 := (mul_one _).symm
        _ = π.norm * m.norm := by rw [hmn]
        _ = (π * m).norm := (Zsqrtd.norm_mul π m).symm
        _ = z.norm := by rw [← hm]
    · obtain ⟨m, hm⟩ := h
      have hy := key' m hm
      have hmn : m.norm = 1 := (Zsqrtd.norm_eq_one_iff' (d := -1) (by norm_num) m).mpr hy
      calc π.norm = π.norm * 1 := (mul_one _).symm
        _ = π.norm * m.norm := by rw [hmn]
        _ = (π * m).norm := (Zsqrtd.norm_mul π m).symm
        _ = (star z).norm := by rw [← hm]
        _ = z.norm := Zsqrtd.norm_conj z
  -- n ∣ p ^ 2
  have hdiv : z.norm ∣ (p : ℤ) * (p : ℤ) := by
    obtain ⟨m, hm⟩ := hπdvdp
    have h := congrArg Zsqrtd.norm hm
    rw [Zsqrtd.norm_natCast, Zsqrtd.norm_mul, hnorm_pi] at h
    exact ⟨m.norm, h⟩
  have hdiv_nat : n ∣ p ^ 2 := by
    have h1 : (n : ℤ) ∣ (p : ℤ) ^ 2 := by
      rw [sq, hn_int]
      exact hdiv
    have h2 : (n : ℤ) ∣ ((p ^ 2 : ℕ) : ℤ) := by simpa [Nat.cast_pow] using h1
    exact Int.ofNat_dvd.mp h2
  -- conclude
  obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow hpprime (m := 2)).mp hdiv_nat
  refine ⟨p, k, hpprime, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · exfalso
      rw [hk0] at hk
      simp at hk
      omega
    · exact hkpos
  · exact hk

end Commons.NumberTheory.GaussianInt