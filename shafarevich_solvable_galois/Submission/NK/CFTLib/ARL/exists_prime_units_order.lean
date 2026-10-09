import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# A prime `q` with `(ZMod q)ˣ` containing an element of order `n`

For every `n > 0` and every bound `B` there is a prime `q > B` such that
`n ∣ q - 1` while, for every prime `ℓ ∣ n`, the `ℓ`-adic valuation of `q - 1` equals
that of `n` (i.e. `ℓ ^ (n.factorization ℓ + 1) ∤ q - 1`).  Consequently the cyclic
group `(ZMod q)ˣ` of order `q - 1` contains an element of order exactly `n`.

The prime is produced by Dirichlet's theorem (`Nat.forall_exists_prime_gt_and_modEq`)
in the residue class `1 + n` modulo `n ^ 2`: since `n ^ 2` is divisible by `n · ℓ` for
every prime `ℓ ∣ n`, the congruence `q ≡ 1 + n (mod n ^ 2)` forces
`q - 1 = n · m` with `m ≡ 1 (mod ℓ)`, whence `v_ℓ (q - 1) = v_ℓ n`.
-/

set_option linter.unnecessarySimpa false
set_option linter.style.haveILetI false

namespace NK.CFTLib.ARL

/-- If `ℓ` is prime then `ℓ ∤ ℓ * k + 1`. -/
private lemma not_dvd_mul_add_one {ℓ k : ℕ} (hℓ : ℓ.Prime) : ¬ ℓ ∣ ℓ * k + 1 := by
  intro h
  have h2 : ℓ ∣ ℓ * k := Nat.dvd_mul_right ℓ k
  exact hℓ.not_dvd_one (by simpa using Nat.dvd_sub h h2)

theorem exists_prime_units_order (n B : ℕ) (hn : 0 < n) :
    ∃ q : ℕ, q.Prime ∧ B < q ∧ n ∣ q - 1 ∧
      (∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ n → ¬ ℓ ^ (n.factorization ℓ + 1) ∣ q - 1) ∧
      ∃ u : (ZMod q)ˣ, orderOf u = n := by
  classical
  have hn0 : n ≠ 0 := Nat.pos_iff_ne_zero.mp hn
  -- `1 + n` is coprime to the modulus `n ^ 2`
  have hcop : (1 + n).Coprime (n ^ 2) :=
    Nat.Coprime.pow_right 2 (Nat.coprime_add_self_left.mpr (Nat.coprime_one_left n))
  -- Dirichlet: a prime `q > max B (n+1)` with `q ≡ 1 + n (mod n ^ 2)`
  obtain ⟨q, hqgt, hqprime, hqmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq (max B (n + 1)) (pow_ne_zero 2 hn0) hcop
  have hBq : B < q := lt_of_le_of_lt (le_max_left _ _) hqgt
  have hn1q : n + 1 < q := lt_of_le_of_lt (le_max_right _ _) hqgt
  have hn1le : 1 + n ≤ q := by omega
  have hn_dvd : n ∣ n ^ 2 := by
    simpa [pow_two] using dvd_mul_right n n
  -- `n ∣ q - 1`
  have hdivn : n ∣ q - (1 + n) :=
    (Nat.modEq_iff_dvd' hn1le).mp (Nat.ModEq.of_dvd hn_dvd hqmod).symm
  have hqn : n ∣ q - 1 := by
    have h : q - 1 = (q - (1 + n)) + n := by omega
    rw [h]
    exact Nat.dvd_add hdivn (dvd_refl n)
  -- the exact valuation of `q - 1` at each prime `ℓ ∣ n`
  have hval : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ n → ¬ ℓ ^ (n.factorization ℓ + 1) ∣ q - 1 := by
    intro ℓ hℓprime hℓdvd
    have hℓ_dvd : n * ℓ ∣ n ^ 2 := by
      obtain ⟨c, hc⟩ := hℓdvd
      refine ⟨c, ?_⟩
      rw [hc]; ring
    have hmodℓ : 1 + n ≡ q [MOD n * ℓ] := (Nat.ModEq.of_dvd hℓ_dvd hqmod).symm
    have hdivℓ : n * ℓ ∣ q - (1 + n) := (Nat.modEq_iff_dvd' hn1le).mp hmodℓ
    obtain ⟨k, hk⟩ := hdivℓ
    -- `q - 1 = n * (ℓ * k + 1)` with `ℓ ∤ ℓ * k + 1`
    have hqeq : q - 1 = n * (ℓ * k + 1) := by
      have h : q - 1 = (q - (1 + n)) + n := by omega
      rw [h, hk]; ring
    have hm1 : ℓ * k + 1 ≠ 0 := by omega
    have hfac : (q - 1).factorization ℓ = n.factorization ℓ := by
      rw [hqeq, Nat.factorization_mul hn0 hm1, Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd (not_dvd_mul_add_one hℓprime), add_zero]
    have hqm1 : q - 1 ≠ 0 := by
      have := hqprime.two_le
      omega
    rw [Nat.Prime.pow_dvd_iff_le_factorization hℓprime hqm1, hfac]
    omega
  refine ⟨q, hqprime, hBq, hqn, hval, ?_⟩
  -- `(ZMod q)ˣ` is cyclic of order `q - 1`, and `n ∣ q - 1`
  haveI : NeZero q := ⟨hqprime.ne_zero⟩
  haveI : IsCyclic (ZMod q)ˣ := ZMod.isCyclic_units_prime hqprime
  have hcard : Fintype.card (ZMod q)ˣ = q - 1 := by
    rw [ZMod.card_units_eq_totient, Nat.totient_prime hqprime]
  have hdvd : n ∣ Fintype.card (ZMod q)ˣ := by rw [hcard]; exact hqn
  have hpos : 0 < ({a : (ZMod q)ˣ | orderOf a = n} : Finset _).card := by
    rw [IsCyclic.card_orderOf_eq_totient hdvd]
    exact Nat.totient_pos.mpr hn
  obtain ⟨u, hu⟩ := Finset.card_pos.mp hpos
  exact ⟨u, (Finset.mem_filter.mp hu).2⟩

end NK.CFTLib.ARL
