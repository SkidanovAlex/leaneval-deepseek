import Mathlib
import Submission.Work.ShafarevichKoch.isCyclic_inertia_of_tame
import Submission.Work.ShafarevichKoch.SupportedSubextensions
import Submission.Commons.NumberTheory.NumberField.ramificationIdx_dvd_two_pow_of_isPGroup

/-!
# `Work.ShafarevichKoch.isCyclic_inertia_of_le_kSupported`

For a finite Galois subextension `L` of the maximal pro-`2` extension `k_S` of a number field `F`
unramified outside a set `S` of odd rational primes, and a prime `P` of `𝒪_L` lying over a
rational prime `q ∈ S`, the inertia subgroup `I_P ≤ Gal(L/F)` is cyclic.

Two inputs:

* `Work.ShafarevichKoch.isCyclic_inertia_of_tame` -- tamely ramified inertia is cyclic;
* the hypothesis `L ⊆ k_S` with `Gal(L/F)` a `2`-group forces `e(P | q)` to be a power of `2`,
  hence prime to the odd `q`: **the ramification is tame**.
-/

open scoped Classical
open NumberField

noncomputable section

namespace Work.ShafarevichKoch

theorem isCyclic_inertia_of_le_kSupported {F : Type} [Field F] [NumberField F] {S : Finset ℕ} (hodd : ∀ q ∈ S, 2 < q) (L : IntermediateField F ↥(Work.ShafarevichKoch.kSupported F 2 S)) [FiniteDimensional F L] [IsGalois F L] [NumberField ↥L] (hpg : IsPGroup 2 (↥L ≃ₐ[F] ↥L)) (P : Ideal (NumberField.RingOfIntegers ↥L)) [P.IsPrime] (hP : ∃ q ∈ S, P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ))) : IsCyclic ↥(Ideal.inertia (↥L ≃ₐ[F] ↥L) P) := by
  classical
  obtain ⟨q, hqS, hqP⟩ := hP
  have hq2 : 2 < q := hodd q hqS
  -- `q` is a (rational) prime, because `(q)` is the prime ideal under `P`
  have hqspan : (Ideal.span ({(q : ℤ)} : Set ℤ)).IsPrime := by
    rw [hqP.over]; exact Ideal.IsPrime.under ℤ P
  have hq0 : (q : ℤ) ≠ 0 := by
    have : (0 : ℤ) < (q : ℤ) := by exact_mod_cast (by omega : 0 < q)
    omega
  have hqprime : Nat.Prime q :=
    Nat.prime_iff_prime_int.mpr ((Ideal.span_singleton_prime hq0).mp hqspan)
  -- `e(P | q)` is a power of `2`, so it is prime to the odd prime `q`: the ramification is tame
  have htame : ¬ (q : ℤ) ∣ (P.ramificationIdx (NumberField.RingOfIntegers F) : ℤ) := by
    obtain ⟨k, hk⟩ :=
      Commons.NumberTheory.NumberField.ramificationIdx_dvd_two_pow_of_isPGroup
        (F := F) (L := ↥L) hpg P
    rw [hk]
    intro h
    have hnat : q ∣ 2 ^ k := (Int.natCast_dvd_natCast).mp h
    have hdiv : q ∣ 2 := hqprime.dvd_of_dvd_pow hnat
    have hle : q ≤ 2 := Nat.le_of_dvd (by norm_num : 0 < 2) hdiv
    omega
  exact isCyclic_inertia_of_tame (F := F) (L := ↥L) P q hqprime hqP.over.symm htame

end Work.ShafarevichKoch
