import Mathlib
import Submission.NK.Reconstruct.Transport
import Submission.NK.ReconstructField.localDegree_primeTransport
import Submission.NK.LocalInputs.Degree.localDegree_eq_ramificationIdx_mul_inertiaDeg
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Invariance of the local degree `e · f` under a ring equivalence, over the base `ℤ`

The file `Submission.NK.ReconstructField.localDegree_primeTransport` proves that a *relative*
isomorphism `μ : B₁ ≃+* B₂` of two number field extensions (compatible with an isomorphism
`μ₀ : A₁ ≃+* A₂` of the base fields) preserves the ramification index and the inertia degree of a
prime of the ring of integers, measured over the rings of integers `𝓞 A₁`, `𝓞 A₂` of the bases.

For the reconstruction of Neukirch–Uchida one needs the *absolute* statement: an arbitrary ring
equivalence `e : K ≃+* L` of two number fields induces, on rings of integers, a bijection
`primeTransport e` of the finite primes which preserves the local degree `[K_𝔭 : ℚ_p]`, expressed as
`e(𝔭) · f(𝔭)` with the ramification index and the inertia degree computed over `ℤ`.

This is a special case: a ring isomorphism of fields of characteristic zero automatically commutes
with the embeddings of `ℚ`, so it is compatible with the base change `ℚ → ℚ` given by the identity.
Two transports remain, from the base `𝓞 ℚ` (where the relative statement lives) to the base `ℤ`
(where the statement is phrased): these are `NK.LocalInputs.Degree.ramificationIdx_rat_eq` and
`NK.LocalInputs.Degree.inertiaDeg_rat_eq`.  -/

namespace NK.Reconstruct

open IsDedekindDomain.HeightOneSpectrum

/-- **The local degree `e · f` is invariant under a ring equivalence of number fields.**

For any ring equivalence `e : K ≃+* L` of number fields and any finite prime `P` of `K`, the
transported prime `primeTransport e P` of `L` has the same local degree over `ℤ` as `P`:

`f(primeTransport e P) · e(primeTransport e P) = f(P) · e(P)`. -/
theorem localDegree_primeTransport_of_ringEquiv {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] (e : K ≃+* L) (P : NK.Chebotarev.PrimeIdeal K) :
    (NK.Reconstruct.primeTransport e P).asIdeal.inertiaDeg ℤ *
        (NK.Reconstruct.primeTransport e P).asIdeal.ramificationIdx ℤ =
      P.asIdeal.inertiaDeg ℤ * P.asIdeal.ramificationIdx ℤ := by
  -- replace the base `ℤ` by the base `𝓞 ℚ`, where the relative statement applies
  have h1 := NK.LocalInputs.Degree.inertiaDeg_rat_eq (K := L)
    (NK.Reconstruct.primeTransport e P).asIdeal (NK.Reconstruct.primeTransport e P).ne_bot
  have h2 := NK.LocalInputs.Degree.ramificationIdx_rat_eq (K := L)
    (NK.Reconstruct.primeTransport e P).asIdeal (NK.Reconstruct.primeTransport e P).ne_bot
  have h3 := NK.LocalInputs.Degree.inertiaDeg_rat_eq (K := K) P.asIdeal P.ne_bot
  have h4 := NK.LocalInputs.Degree.ramificationIdx_rat_eq (K := K) P.asIdeal P.ne_bot
  rw [← h1, ← h2, ← h3, ← h4]
  -- a ring isomorphism of fields of characteristic zero commutes with the embeddings of `ℚ`
  have hmain := NK.ReconstructField.localDegree_primeTransport (A₁ := ℚ) (A₂ := ℚ)
    (B₁ := K) (B₂ := L) e (RingEquiv.refl ℚ) (fun x => by simp) P
    (NK.LocalInputs.primeBelow K P) (NK.LocalInputs.primeBelow_liesOver K P)
  calc (NK.Reconstruct.primeTransport e P).asIdeal.inertiaDeg (NumberField.RingOfIntegers ℚ)
        * (NK.Reconstruct.primeTransport e P).asIdeal.ramificationIdx (NumberField.RingOfIntegers ℚ)
      = (NK.Reconstruct.primeTransport e P).asIdeal.ramificationIdx (NumberField.RingOfIntegers ℚ)
        * (NK.Reconstruct.primeTransport e P).asIdeal.inertiaDeg (NumberField.RingOfIntegers ℚ) :=
        mul_comm _ _
    _ = P.asIdeal.ramificationIdx (NumberField.RingOfIntegers ℚ)
        * P.asIdeal.inertiaDeg (NumberField.RingOfIntegers ℚ) := hmain.symm
    _ = P.asIdeal.inertiaDeg (NumberField.RingOfIntegers ℚ)
        * P.asIdeal.ramificationIdx (NumberField.RingOfIntegers ℚ) := mul_comm _ _

end NK.Reconstruct
