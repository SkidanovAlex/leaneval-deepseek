import Mathlib
import Submission.NK.ReconstructField.localDegree_primeTransport

set_option linter.style.haveILetI false

/-!
# Invariance of "unramified over `Q`" under a `K`-algebra isomorphism

If `A` and `B` are number fields with a common subfield `K` and `e : A ≃ₐ[K] B` is a `K`-algebra
isomorphism, then the primes of `𝓞 B` over a fixed prime `Q` of `𝓞 K` correspond bijectively to
the primes of `𝓞 A` over `Q`, and the ramification index over `𝓞 K` is preserved.  Consequently, if
every prime of `𝓞 A` over `Q` is unramified over `𝓞 K`, the same holds in `B`.
-/

namespace NK.NUV2.ArtinBridge

/-- Ramification of primes over a fixed prime `Q` is invariant under a `K`-algebra isomorphism of number fields: if every prime of `𝓞 A` over `Q` is unramified, the same holds in a `K`-isomorphic field `B`. -/
theorem ramificationIdx_eq_one_of_algEquiv {K A B : Type*} [Field K] [NumberField K] [Field A]
    [NumberField A] [Field B] [NumberField B] [Algebra K A] [Algebra K B]
    (e : A ≃ₐ[K] B) (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hA : ∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers A),
      q.asIdeal.LiesOver Q.asIdeal → q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1)
    (qB : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers B))
    (hqB : qB.asIdeal.LiesOver Q.asIdeal) :
    qB.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1 := by
  -- The inverse isomorphism of rings of integers `𝓞 B ≃+* 𝓞 A`.
  have hμ : ∀ x : K, e.symm (algebraMap K B x) = algebraMap K A x := fun x => e.symm.commutes x
  have hrefl : ∀ x : NumberField.RingOfIntegers K,
      NK.Reconstruct.ringOfIntegersEquiv (RingEquiv.refl K) x = x := by
    intro x
    apply NumberField.RingOfIntegers.ext
    rw [NK.Reconstruct.ringOfIntegersEquiv_apply]
    rfl
  have hcompat : ∀ x : NumberField.RingOfIntegers K,
      NK.Reconstruct.ringOfIntegersEquiv (e.symm : B ≃+* A)
          (algebraMap (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers B) x) =
        algebraMap (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers A) x := by
    intro x
    have h := NK.ReconstructField.ringOfIntegersEquiv_algebraMap (e.symm : B ≃+* A)
      (RingEquiv.refl K) hμ x
    rw [hrefl x] at h
    exact h
  let Ψ : NumberField.RingOfIntegers B ≃ₐ[NumberField.RingOfIntegers K]
      NumberField.RingOfIntegers A :=
    AlgEquiv.ofRingEquiv (f := NK.Reconstruct.ringOfIntegersEquiv (e.symm : B ≃+* A)) hcompat
  haveI : qB.asIdeal.LiesOver Q.asIdeal := hqB
  have hqLies : (Ideal.map Ψ qB.asIdeal).LiesOver Q.asIdeal :=
    Ideal.map_equiv_liesOver qB.asIdeal Q.asIdeal Ψ
  have hram : (Ideal.map Ψ qB.asIdeal).ramificationIdx (NumberField.RingOfIntegers K) =
      qB.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) :=
    NK.ReconstructField.ramificationIdx_map_ringOfIntegersEquiv (e.symm : B ≃+* A)
      (RingEquiv.refl K) hμ qB.asIdeal qB.ne_bot
  have hne : Ideal.map Ψ qB.asIdeal ≠ ⊥ := fun h =>
    qB.ne_bot ((Ideal.map_eq_bot_iff_of_injective (NK.Reconstruct.ringOfIntegersEquiv
      (e.symm : B ≃+* A)).injective).mp h)
  have hunr := hA ⟨Ideal.map Ψ qB.asIdeal, Ideal.map_isPrime_of_equiv Ψ, hne⟩ hqLies
  rw [← hram]
  exact hunr

end NK.NUV2.ArtinBridge
