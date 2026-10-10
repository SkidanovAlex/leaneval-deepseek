import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Submission.NK.FrobeniusBridge.Endgame
import Submission.NK.LocalCFT.Completion.exists_mulEquiv_unitsCompletion
import Submission.NK.LocalCFT.Functoriality.levelMulEquiv_restrict
import Submission.NK.LocalCFT.Instance.artinReciprocity_complex
import Submission.NK.LocalCFT.NormGroup.normGroup_eq_iff
import Submission.NK.LocalCFT.NormGroup.normGroup_le_iff
import Submission.NK.LocalCFT.NormGroup.normGroup_sup_eq_inf
import Submission.NK.LocalCFT.Reduction.nonempty_artinReciprocity_of_reciprocityLaw
import Submission.NK.LocalInputs.PowerQuotient.localFieldInputs_of_prime
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.Reconstruct

/-- **The characteristic of a ring is invariant under a ring isomorphism.** -/
lemma charP_iff_of_ringEquiv {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S]
    (e : R ≃+* S) (n : ℕ) : CharP R n ↔ CharP S n := by
  constructor
  · intro h
    obtain ⟨q, hq⟩ := CharP.exists S
    have h1 : q ∣ n := CharP.dvd_of_ringHom (e : R →+* S) n q
    have h2 : n ∣ q := CharP.dvd_of_ringHom (e.symm : S →+* R) q n
    have heq : n = q := Nat.dvd_antisymm h2 h1
    rwa [← heq] at hq
  · intro h
    obtain ⟨q, hq⟩ := CharP.exists R
    have h1 : q ∣ n := CharP.dvd_of_ringHom (e.symm : S →+* R) n q
    have h2 : n ∣ q := CharP.dvd_of_ringHom (e : R →+* S) q n
    have heq : n = q := Nat.dvd_antisymm h2 h1
    rwa [← heq] at hq

/-- **The characteristic of the residue field at a prime is preserved by transport of primes along
an isomorphism of number fields.**  The isomorphism `ringOfIntegersEquiv e` of rings of integers
sends `P.asIdeal` to `(primeTransport e P).asIdeal`, whence it induces an isomorphism of the
corresponding residue rings; the characteristic is an isomorphism invariant of rings. -/
theorem charP_quotient_primeTransport {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] (e : K ≃+* L) (P : NK.Chebotarev.PrimeIdeal K) (n : ℕ) :
    CharP (NumberField.RingOfIntegers K ⧸ P.asIdeal) n ↔
      CharP (NumberField.RingOfIntegers L ⧸ (NK.Reconstruct.primeTransport e P).asIdeal) n := by
  have hmap : (NK.Reconstruct.primeTransport e P).asIdeal =
      Ideal.map (ringOfIntegersEquiv e) P.asIdeal := rfl
  rw [hmap]
  exact charP_iff_of_ringEquiv
    (Ideal.quotientEquiv P.asIdeal (Ideal.map (ringOfIntegersEquiv e) P.asIdeal)
      (ringOfIntegersEquiv e) rfl) n

end NK.Reconstruct
