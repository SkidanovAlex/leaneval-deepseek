import Mathlib
import Submission.NK.UchidaKummer.Defs
import Submission.NK.ReconstructField.sum_localDeg_primesOver
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.ReconstructField

/-- **Counting the primes above a prime, from the local degrees.**

If every prime `𝔔` of `𝓞 L` above the finite prime `𝔭` of `K` has the same local degree
`[L_𝔔 : K_𝔭] = e(𝔔|𝔭) · f(𝔔|𝔭) = d`, then the number of such primes times `d` is the global
degree `[L : K]`.

This is the counting form of
`NK.ReconstructField.sum_localDeg_primesOver`, which says that
`∑_𝔔 [L_𝔔 : K_𝔭] = [L : K]`. -/
theorem ncard_primesOver_mul_eq_finrank_of_forall_localDeg {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (𝔭 : NK.Chebotarev.PrimeIdeal K) (d : ℕ)
    (h : ∀ Q : NK.Chebotarev.PrimeIdeal L, Q.asIdeal.LiesOver 𝔭.asIdeal →
      NK.UchidaKummer.localDeg Q 𝔭 = d) :
    (𝔭.asIdeal.primesOver (NumberField.RingOfIntegers L)).ncard * d = Module.finrank K L := by
  classical
  have hterm : ∀ Q : 𝔭.asIdeal.primesOver (NumberField.RingOfIntegers L),
      NK.UchidaKummer.localDeg
          ⟨Q.1, Q.2.1, Ideal.ne_bot_of_mem_primesOver 𝔭.ne_bot Q.2⟩ 𝔭 = d :=
    fun Q => h ⟨Q.1, Q.2.1, Ideal.ne_bot_of_mem_primesOver 𝔭.ne_bot Q.2⟩ Q.2.2
  have key : (∑ Q : 𝔭.asIdeal.primesOver (NumberField.RingOfIntegers L),
      NK.UchidaKummer.localDeg
          ⟨Q.1, Q.2.1, Ideal.ne_bot_of_mem_primesOver 𝔭.ne_bot Q.2⟩ 𝔭)
      = (𝔭.asIdeal.primesOver (NumberField.RingOfIntegers L)).ncard * d := by
    rw [Finset.sum_congr rfl (fun Q _ => hterm Q), Finset.sum_const, Finset.card_univ,
      smul_eq_mul, Set.fintypeCard_eq_ncard]
  rw [← key]
  exact sum_localDeg_primesOver 𝔭

end NK.ReconstructField
