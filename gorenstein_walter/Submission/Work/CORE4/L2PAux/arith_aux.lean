import Mathlib

namespace Work.CORE4.L2PAux

theorem arith_aux {d m ρ : ℕ} (hρ : ρ.Prime) (hm : m ≠ 0) (hd : d ∣ m) (hcop : Nat.Coprime d ρ)
    (h : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ ρ → ℓ ^ m.factorization ℓ ∣ d) :
    d * ρ ^ m.factorization ρ = m := by
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact hm (zero_dvd_iff.mp hd)
  have hρ0 : ρ ≠ 0 := hρ.ne_zero
  -- every prime power of `m` at any prime ℓ ≠ ρ divides `d`
  have hge : ∀ ℓ, ℓ ≠ ρ → m.factorization ℓ ≤ d.factorization ℓ := by
    intro ℓ hne
    by_cases hp : ℓ.Prime
    · exact (Nat.Prime.pow_dvd_iff_le_factorization hp hd0).mp (h ℓ hp hne)
    · have : m.factorization ℓ = 0 := (Nat.factorization_eq_zero_iff m ℓ).mpr (Or.inl hp)
      rw [this]
      exact Nat.zero_le _
  -- and `d` divides `m`, so the factorizations agree away from ρ
  have heq : ∀ ℓ, ℓ ≠ ρ → d.factorization ℓ = m.factorization ℓ :=
    fun ℓ hne =>
      le_antisymm
        (Finsupp.le_def.mp ((Nat.factorization_le_iff_dvd hd0 hm).mpr hd) ℓ)
        (hge ℓ hne)
  have hdρ : d.factorization ρ = 0 :=
    Nat.factorization_eq_zero_of_not_dvd ((hρ.coprime_iff_not_dvd).mp hcop.symm)
  have hρfac : ρ.factorization ρ = 1 := hρ.factorization_self
  have hρzero : ∀ ℓ, ℓ ≠ ρ → ρ.factorization ℓ = 0 := by
    intro ℓ hne
    refine (Nat.factorization_eq_zero_iff ρ ℓ).mpr ?_
    by_cases hp : ℓ.Prime
    · right; left
      intro hdvd
      exact hne ((Nat.Prime.dvd_iff_eq hρ hp.ne_one).mp hdvd).symm
    · exact Or.inl hp
  have hpow0 : ρ ^ m.factorization ρ ≠ 0 := pow_ne_zero _ hρ0
  refine Nat.eq_of_factorization_eq (mul_ne_zero hd0 hpow0) hm ?_
  intro ℓ
  rw [Nat.factorization_mul hd0 hpow0, Nat.factorization_pow, Finsupp.add_apply,
    Finsupp.smul_apply, smul_eq_mul]
  by_cases hℓ : ℓ = ρ
  · subst hℓ
    rw [hdρ, hρfac, mul_one, zero_add]
  · rw [heq ℓ hℓ, hρzero ℓ hℓ, mul_zero, add_zero]

end Work.CORE4.L2PAux
