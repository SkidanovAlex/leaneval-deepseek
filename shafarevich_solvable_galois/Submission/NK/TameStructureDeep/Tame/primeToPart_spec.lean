import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Submission.NK.TameStructureDeep.Tame.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.TameStructureDeep.Tame

/-- **Auxiliary: `p ^ k` divides `m` and the cofactor is coprime to the prime `p`.**

If `p` is a prime and `k = m.factorization p` with `m ≠ 0`, then `p ^ k ∣ m` and the cofactor
`m / p ^ k` is not divisible by `p` (hence is coprime to `p`): `p ^ (k+1) ∣ m` would force
`k + 1 ≤ k`. -/
theorem pow_factorization_dvd_and_not_dvd {p m : ℕ} (hp : p.Prime) (hm : m ≠ 0) :
    p ^ (m.factorization p) ∣ m ∧ ¬ p ∣ m / p ^ (m.factorization p) := by
  set k := m.factorization p with hkdef
  have hdiv : p ^ k ∣ m := (hp.pow_dvd_iff_le_factorization hm).mpr le_rfl
  refine ⟨hdiv, ?_⟩
  have hmul : p ^ k * (m / p ^ k) = m := Nat.mul_div_cancel' hdiv
  intro h
  have h1 : p ^ (k + 1) ∣ m := by
    rw [pow_succ, ← hmul]
    exact mul_dvd_mul_left _ h
  have h2 := (hp.pow_dvd_iff_le_factorization hm).mp h1
  exact Nat.not_succ_le_self k h2

/-- **The prime-to-`p` part of `m`.**  For a number field `K`, a place `𝔭` with residue
characteristic `p = resCharAt 𝔭` and `m ≠ 0`, the number `d₀ = m / p ^ (m.factorization p)` divides
`m`, is coprime to `p`, and is divisible by every divisor of `m` coprime to `p` (i.e. it is the
largest divisor of `m` prime to `p`). -/
theorem primeToPart_spec {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) (m : ℕ) (hm : m ≠ 0) :
    (m / (resCharAt 𝔭) ^ (m.factorization (resCharAt 𝔭)) ∣ m) ∧
      Nat.Coprime (m / (resCharAt 𝔭) ^ (m.factorization (resCharAt 𝔭))) (resCharAt 𝔭) ∧
      ∀ g : ℕ, g ∣ m → ¬ resCharAt 𝔭 ∣ g →
        g ∣ m / (resCharAt 𝔭) ^ (m.factorization (resCharAt 𝔭)) := by
  set p := resCharAt 𝔭 with hpdef
  -- `p` is the residue characteristic, hence a prime.
  have hp : p.Prime := NK.Mine.prime_ringChar_residueField_adicCompletion 𝔭
  set k := m.factorization p with hkdef
  obtain ⟨hdiv, hnotdvd⟩ := pow_factorization_dvd_and_not_dvd hp hm
  have hmul : p ^ k * (m / p ^ k) = m := Nat.mul_div_cancel' hdiv
  refine ⟨Nat.div_dvd_of_dvd hdiv, ?_, ?_⟩
  · -- the cofactor is coprime to `p` because `p` is a prime not dividing it
    exact Nat.coprime_comm.mp ((hp.coprime_iff_not_dvd).mpr hnotdvd)
  · intro g hg hgp
    -- `g` is coprime to `p ^ k`, and `g ∣ p ^ k * (m / p ^ k) = m`, so `g ∣ m / p ^ k`
    have hcop : g.Coprime (p ^ k) := ((hp.coprime_iff_not_dvd).mpr hgp).symm.pow_right k
    have hg' : g ∣ p ^ k * (m / p ^ k) := by rw [hmul]; exact hg
    exact hcop.dvd_of_dvd_mul_left hg'

end NK.TameStructureDeep.Tame
