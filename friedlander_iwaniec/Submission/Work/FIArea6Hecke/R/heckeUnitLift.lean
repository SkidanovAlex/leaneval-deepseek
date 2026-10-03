import Mathlib
import Submission.Work.FIArea6Hecke.R.StrictConductorDefs

namespace Work.FIArea6Hecke.R

open scoped BigOperators

/-- `IsUnitMod M z` is exactly `IsCoprime z M`: `M ∣ z*w - 1` is the same data as
`w * z + (-k) * M = 1`. -/
private lemma isUnitMod_iff_isCoprime' (M z : GaussianInt) :
    IsUnitMod M z ↔ IsCoprime z M := by
  constructor
  · rintro ⟨w, k, hk⟩
    exact ⟨w, -k, by linear_combination hk⟩
  · rintro ⟨a, b, hab⟩
    exact ⟨a, -b, by linear_combination hab⟩

/-- **Prime avoidance.**  If `z` is coprime to `M` and `g ≠ 0`, then `z` can be shifted by a
multiple of `M` so as to avoid every prime divisor of `g`.  Explicitly one may take `t` to be the
product of the prime factors of `g` which do not divide `z`. -/
private lemma exists_forall_prime_not_dvd' (M z g : GaussianInt) (hg : g ≠ 0)
    (hz : IsCoprime z M) :
    ∃ t : GaussianInt, ∀ p : GaussianInt, Prime p → p ∣ g → ¬ p ∣ (z + M * t) := by
  classical
  set S : Multiset GaussianInt :=
    (UniqueFactorizationMonoid.factors g).filter (fun q => ¬ q ∣ z) with hS
  refine ⟨S.prod, ?_⟩
  have hmem : ∀ q, q ∈ S ↔ q ∈ UniqueFactorizationMonoid.factors g ∧ ¬ q ∣ z := by
    intro q
    rw [hS, Multiset.mem_filter]
  intro p hp hpg hpu
  have hzrel : IsRelPrime z M := hz.isRelPrime
  have hfac : ∀ r ∈ UniqueFactorizationMonoid.factors g, Prime r := fun r hr =>
    UniqueFactorizationMonoid.irreducible_iff_prime.mp
      (UniqueFactorizationMonoid.irreducible_of_factor r hr)
  obtain ⟨q, hq_mem, hpq⟩ : ∃ q ∈ UniqueFactorizationMonoid.factors g, Associated p q := by
    refine exists_associated_mem_of_dvd_prod hp ?_ ?_
    · exact hfac
    · exact dvd_trans hpg (UniqueFactorizationMonoid.factors_prod hg).dvd'
  by_cases hpz : p ∣ z
  · -- a prime dividing both `z` and `g` cannot divide `M`, hence not `M * t` either
    have hqz : q ∣ z := hpq.dvd'.trans hpz
    have hq_not_prod : ¬ q ∣ S.prod := by
      intro hqt
      obtain ⟨r, hrS, hqr⟩ := exists_associated_mem_of_dvd_prod (hfac q hq_mem)
        (fun r hr => hfac r ((hmem r).mp hr).1) hqt
      exact ((hmem r).mp hrS).2 (hqr.dvd'.trans hqz)
    have hq_not_M : ¬ q ∣ M := fun hqM => (hfac q hq_mem).not_isUnit (hzrel hqz hqM)
    have hq_not_Mt : ¬ q ∣ M * S.prod := by
      rw [Prime.dvd_mul (hfac q hq_mem)]
      exact not_or.mpr ⟨hq_not_M, hq_not_prod⟩
    have hdiv : q ∣ (z + M * S.prod) - z := dvd_sub (hpq.dvd'.trans hpu) hqz
    exact hq_not_Mt (by convert hdiv using 1; ring)
  · -- `q` is one of the primes put into the product, so it divides `M * t`
    have hq_not_z : ¬ q ∣ z := fun h => hpz (hpq.dvd.trans h)
    have hqS : q ∈ S := (hmem q).mpr ⟨hq_mem, hq_not_z⟩
    have hq_prod : q ∣ S.prod := Multiset.dvd_prod hqS
    have hdiv : p ∣ (z + M * S.prod) - M * S.prod :=
      dvd_sub hpu (dvd_mul_of_dvd_right (hpq.dvd.trans hq_prod) M)
    exact hpz (by convert hdiv using 1; ring)

theorem heckeUnitLift (g M z : GaussianInt) (hg : g ≠ 0)
    (hz : Work.FIArea6Hecke.R.IsUnitMod M z) :
    ∃ u : GaussianInt, M ∣ (u - z) ∧ Work.FIArea6Hecke.R.IsUnitMod (M * g) u := by
  classical
  rcases eq_or_ne M 0 with hM0 | hM0
  · -- `M = 0`: `z` is already a unit of `ℤ[i]`, and `u = z` works
    rw [hM0] at hz ⊢
    refine ⟨z, by simp, ?_⟩
    rw [zero_mul]
    exact hz
  · have hzC : IsCoprime z M := (isUnitMod_iff_isCoprime' M z).mp hz
    obtain ⟨t, ht⟩ := exists_forall_prime_not_dvd' M z g hg hzC
    refine ⟨z + M * t, ⟨t, by ring⟩, ?_⟩
    rw [isUnitMod_iff_isCoprime']
    have hMg : M * g ≠ 0 := mul_ne_zero hM0 hg
    -- `z + M*t` is coprime to `M * g`: no prime divides both
    have hrel : IsRelPrime (z + M * t) (M * g) := by
      intro d hdu hdn
      by_contra hdu'
      have hd0 : d ≠ 0 := by
        intro hd
        rw [hd, zero_dvd_iff] at hdn
        exact hMg hdn
      obtain ⟨i, hi_irr, hi_dvd⟩ := WfDvdMonoid.exists_irreducible_factor hdu' hd0
      have hip : Prime i := UniqueFactorizationMonoid.irreducible_iff_prime.mp hi_irr
      have hiu : i ∣ z + M * t := hi_dvd.trans hdu
      have hiMg : i ∣ M * g := hi_dvd.trans hdn
      rcases (Prime.dvd_mul hip).mp hiMg with hiM | hig
      · -- primes of `M` are avoided because `z + M*t ≡ z (mod M)`
        have hz_i : i ∣ z := by
          have h := dvd_sub hiu (dvd_mul_of_dvd_left hiM t)
          rwa [show (z + M * t) - M * t = z by ring] at h
        exact hip.not_isUnit (hzC.isRelPrime hz_i hiM)
      · -- primes of `g` are avoided by construction of `t`
        exact ht i hip hig hiu
    exact hrel.isCoprime

end Work.FIArea6Hecke.R
