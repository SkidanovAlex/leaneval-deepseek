import Mathlib
import Submission.NK.Reconstruct.splitFrobeniusBase
import Submission.NK.Reconstruct.Transport

/-!
# The completely split condition survives the transport of primes

`NK.Reconstruct.SplitsCompletelyOverRat 𝔭` says that the prime `𝔭` of a number field is
unramified over `ℚ` with residue degree one.  The condition is manifestly a property of the pair
`(𝓞 L, 𝔭)` alone, so it is invariant under any automorphism of `L` (over `ℚ`) — but the transport
of primes used by the reconstruction,
`NK.Reconstruct.primeTransport τ 𝔭 = Ideal.map (ringOfIntegersEquiv τ) 𝔭.asIdeal`
(`Submission/Work/Reconstruct/Transport.lean`), is stated through the *ring* automorphism
`ringOfIntegersEquiv τ` of `𝓞 L` obtained from the ring isomorphism underlying `τ`, and
`Ideal.inertiaDeg`/`Ideal.ramificationIdx` are indexed by a *base ring*.

The point of this file is that the two presentations agree: the ring automorphism of `𝓞 L`
induced by `τ : L ≃ₐ[ℚ] L` is an `𝓞 ℚ`-algebra automorphism (`𝓞 ℚ`-linearity of
`ringOfIntegersEquiv τ`, i.e. that `τ` fixes the integers), so that the invariance of the
inertia degree and of the ramification index under an `R`-algebra automorphism
(`Ideal.inertiaDeg_smul` and `Ideal.ramificationIdx_smul`) applies directly.

## Contents

* `inertiaDeg_map_self_algEquiv` — the inertia degree over `R` is unchanged by an `R`-algebra
  automorphism of the ambient ring;
* `ramificationIdx_map_self_algEquiv` — the same for the ramification index;
* `ringOfIntegersEquiv_algebraMap_eq` — `ringOfIntegersEquiv τ` fixes the image of `𝓞 ℚ`;
* `ringOfIntegersAlgEquiv` — the induced `𝓞 ℚ`-algebra automorphism of `𝓞 L`, whose underlying
  ring automorphism *is* the transported prime's defining map;
* `splitsCompletelyOverRat_primeTransport` — `SplitsCompletelyOverRat` is preserved by
  `primeTransport`.

## References

J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, Ch. XII §12.2;
S. Shimizu, *On the Neukirch–Uchida theorem for small sets of primes*, arXiv:2009.10431, §4.
-/

set_option linter.unusedSectionVars false

namespace NK.Reconstruct

open NK.Chebotarev
open scoped Pointwise NumberField

/-! ## Invariance of the inertia degree and the ramification index under an algebra automorphism -/

section AlgEquivTransport

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- **The inertia degree over `R` is unchanged by an `R`-algebra automorphism of the ambient
ring.**  This is `Ideal.inertiaDeg_smul` made explicit for the algebra automorphism group: an
`R`-algebra automorphism acts on ideals by `Ideal.map`, and `Ideal.inertiaDeg_smul` says that the
action does not change the inertia degree. -/
theorem inertiaDeg_map_self_algEquiv (f : S ≃ₐ[R] S) (q : Ideal S) :
    (q.map f).inertiaDeg R = q.inertiaDeg R := by
  have h : q.map f = f • q := by
    rw [Ideal.pointwise_smul_def]
    rfl
  rw [h]
  exact Ideal.inertiaDeg_smul R q f

/-- **The ramification index over `R` is unchanged by an `R`-algebra automorphism of the ambient
ring.**  This is `Ideal.ramificationIdx_smul` made explicit for the algebra automorphism group. -/
theorem ramificationIdx_map_self_algEquiv (f : S ≃ₐ[R] S) (q : Ideal S) :
    (q.map f).ramificationIdx R = q.ramificationIdx R := by
  have h : q.map f = f • q := by
    rw [Ideal.pointwise_smul_def]
    rfl
  rw [h]
  exact Ideal.ramificationIdx_smul R q f

end AlgEquivTransport

/-! ## The ring automorphism of `𝓞 L` induced by an automorphism of `L` over `ℚ` is `𝓞 ℚ`-linear -/

section NumberFieldTransport

variable {Ω : Type*} [Field Ω] [Algebra ℚ Ω]

/-- **`ringOfIntegersEquiv τ` fixes the image of `𝓞 ℚ`.**  An automorphism `τ` of the number field
`L` over `ℚ` fixes the rational integers, hence the ring isomorphism `𝓞 L ≃+* 𝓞 L` it induces is
`𝓞 ℚ`-linear.  Concretely, the image of `r ∈ 𝓞 ℚ` in `𝓞 L` is the image of the rational number
`(r : ℚ)` under `algebraMap ℚ L`, which `τ` fixes. -/
theorem ringOfIntegersEquiv_algebraMap_eq (L : FrobLevel ℚ Ω) (τ : Gal(↥L.L/ℚ)) (r : 𝓞 ℚ) :
    ringOfIntegersEquiv (τ : ↥L.L ≃+* ↥L.L) (algebraMap (𝓞 ℚ) (𝓞 ↥L.L) r)
      = algebraMap (𝓞 ℚ) (𝓞 ↥L.L) r := by
  apply NumberField.RingOfIntegers.ext
  rw [ringOfIntegersEquiv_apply]
  have h1 : ((algebraMap (𝓞 ℚ) (𝓞 ↥L.L) r : 𝓞 ↥L.L) : ↥L.L)
      = algebraMap ℚ ↥L.L (r : ℚ) := by
    change ((NumberField.RingOfIntegers.mapRingHom (algebraMap ℚ ↥L.L) r : 𝓞 ↥L.L) : ↥L.L) = _
    rw [NumberField.RingOfIntegers.mapRingHom_apply]
  rw [h1]
  exact τ.commutes (r : ℚ)

/-- **The `𝓞 ℚ`-algebra automorphism of `𝓞 L` induced by an automorphism `τ` of `L` over `ℚ`.**
Its underlying *ring* automorphism is `ringOfIntegersEquiv τ`, the map through which
`NK.Reconstruct.primeTransport τ` is defined. -/
noncomputable def ringOfIntegersAlgEquiv (L : FrobLevel ℚ Ω) (τ : Gal(↥L.L/ℚ)) :
    𝓞 ↥L.L ≃ₐ[𝓞 ℚ] 𝓞 ↥L.L :=
  AlgEquiv.ofRingEquiv (f := ringOfIntegersEquiv (τ : ↥L.L ≃+* ↥L.L))
    (ringOfIntegersEquiv_algebraMap_eq L τ)

/-- The underlying ring automorphism of `ringOfIntegersAlgEquiv L τ` is `ringOfIntegersEquiv τ`,
which is the map defining `primeTransport τ`. -/
theorem ringOfIntegersAlgEquiv_toRingEquiv (L : FrobLevel ℚ Ω) (τ : Gal(↥L.L/ℚ)) :
    (ringOfIntegersAlgEquiv L τ).toRingEquiv = ringOfIntegersEquiv (τ : ↥L.L ≃+* ↥L.L) := rfl

end NumberFieldTransport

/-! ## The target -/

theorem splitsCompletelyOverRat_primeTransport {Ω : Type*} [Field Ω] [Algebra ℚ Ω]
    (L : NK.Reconstruct.FrobLevel ℚ Ω) (τ : Gal(↥L.L/ℚ))
    (𝔭 : NK.Chebotarev.PrimeIdeal ↥L.L) (h : NK.Reconstruct.SplitsCompletelyOverRat 𝔭) :
    NK.Reconstruct.SplitsCompletelyOverRat
      (NK.Reconstruct.primeTransport (τ : ↥L.L ≃+* ↥L.L) 𝔭) := by
  obtain ⟨h1, h2⟩ := h
  have hmap : (NK.Reconstruct.primeTransport (τ : ↥L.L ≃+* ↥L.L) 𝔭).asIdeal
      = Ideal.map (ringOfIntegersAlgEquiv L τ) 𝔭.asIdeal := rfl
  refine ⟨?_, ?_⟩
  · rw [hmap, inertiaDeg_map_self_algEquiv (ringOfIntegersAlgEquiv L τ) 𝔭.asIdeal]
    exact h1
  · rw [hmap, ramificationIdx_map_self_algEquiv (ringOfIntegersAlgEquiv L τ) 𝔭.asIdeal]
    exact h2

end NK.Reconstruct
