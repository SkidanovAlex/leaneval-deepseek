import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Heights, quotient dimensions and Krull dimension for a finite (integral) extension of domains

Let `C ⊆ S` be an extension of commutative rings such that `S` is a finite `C`-module (hence
integral over `C`), `C → S` is injective (`FaithfulSMul`), `C` and `S` are domains and `C` is
integrally closed.  Then:

* `ht J = ht (J ∩ C)` for every prime `J` of `S`;
* `dim (S ⧸ J) = dim (C ⧸ (J ∩ C))` for every prime `J` of `S`;
* `dim S = dim C`.

The size of the primes is controlled by the two Cohen–Seidenberg properties of the integral
extension `C → S`.  Incomparability (`Ideal.IsIntegral.under_lt_under`) says that
`Spec S → Spec C`, `J ↦ J ∩ C`, is strictly monotone; this immediately gives
`ht J ≤ ht (J ∩ C)`, and (with `Order.krullDim_le_of_strictMono`) half of the dimension formula.
The reverse inequalities come from lying over together with going up (which hold for *every*
integral extension, `Ideal.exists_ltSeries_of_hasGoingUp`) and from going down, which for an
integral extension of domains requires the base to be integrally closed
(`Ideal.exists_ltSeries_of_hasGoingDown`, Matsumura 13.B Th. 19).

The general auxiliary statements are isolated below since they are the reusable content:
`ringKrullDim_eq_of_isIntegral_of_injective` (an injective integral extension preserves the Krull
dimension, no openness/normality assumption), and `Ideal.height_eq_height_under_of_hasGoingDown`
(heights of primes are preserved under an integral extension with going down).
-/

set_option linter.style.haveILetI false

namespace Work.BW.RB

open Order

/-! ### An injective integral extension preserves the Krull dimension

Incomparability gives `dim S ≤ dim C`, while lying over and going up lift any chain of primes of
`C` to a chain of the same length in `S`, giving `dim C ≤ dim S`. -/
theorem ringKrullDim_eq_of_isIntegral_of_injective {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [Algebra.IsIntegral A B] (hinj : Function.Injective (algebraMap A B)) :
    ringKrullDim B = ringKrullDim A := by
  refine le_antisymm ?_ ?_
  · rw [ringKrullDim, ringKrullDim]
    exact Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap A B))
      (fun p q h => Ideal.IsIntegral.under_lt_under h)
  · rw [ringKrullDim, ringKrullDim]
    apply iSup_le
    intro p
    -- lying over: produce a prime of `B` above the first element of the chain
    have hker : Ideal.under A (⊥ : Ideal B) ≤ p.head.asIdeal := by
      show RingHom.ker (algebraMap A B) ≤ _
      rw [(RingHom.injective_iff_ker_eq_bot (algebraMap A B)).mp hinj]
      exact bot_le
    obtain ⟨Q, -, hQprime, hQu⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (R := A) (S := B)
        p.head.asIdeal (⊥ : Ideal B) hker
    haveI : Q.IsPrime := hQprime
    haveI : Q.LiesOver p.head.asIdeal := ⟨hQu.symm⟩
    -- going up lifts the whole chain
    obtain ⟨L, hlen, -, -⟩ := Ideal.exists_ltSeries_of_hasGoingUp p Q
    calc (↑p.length : WithBot ℕ∞) = ↑L.length := by rw [hlen]
      _ ≤ krullDim (PrimeSpectrum B) :=
        le_iSup (fun q : LTSeries (PrimeSpectrum B) => (↑q.length : WithBot ℕ∞)) L

/-! ### Primes have the same height as their contraction

Incomparability gives `ht J ≤ ht (J ∩ C)`; going down lifts a chain of primes below `J ∩ C` to a
chain of primes below `J` of the same length, giving the reverse inequality. -/
theorem Ideal.height_eq_height_under_of_hasGoingDown {C S : Type*} [CommRing C] [CommRing S]
    [Algebra C S] [Algebra.IsIntegral C S] [Algebra.HasGoingDown C S] (J : Ideal S)
    [hJ : J.IsPrime] : J.height = (J.under C).height := by
  have hsm : StrictMono (PrimeSpectrum.comap (algebraMap C S)) :=
    fun p q h => Ideal.IsIntegral.under_lt_under h
  have hJh : J.height = Order.height (⟨J, hJ⟩ : PrimeSpectrum S) :=
    PrimeSpectrum.height_eq_orderHeight (⟨J, hJ⟩ : PrimeSpectrum S)
  have hJuh : (J.under C).height =
      Order.height (PrimeSpectrum.comap (algebraMap C S) ⟨J, hJ⟩) :=
    PrimeSpectrum.height_eq_orderHeight (PrimeSpectrum.comap (algebraMap C S) ⟨J, hJ⟩)
  refine le_antisymm ?_ ?_
  · rw [hJh, hJuh]
    exact Order.height_le_height_apply_of_strictMono _ hsm _
  · rw [hJh, hJuh]
    refine Order.height_le ?_
    intro p hp
    have hlast : p.last.asIdeal = J.under C := congrArg PrimeSpectrum.asIdeal hp
    haveI : J.LiesOver p.last.asIdeal := by rw [hlast]; exact Ideal.over_under J
    obtain ⟨L, hLlen, hLlast, -⟩ := Ideal.exists_ltSeries_of_hasGoingDown p J
    calc (p.length : ℕ∞) = (L.length : ℕ∞) := by rw [hLlen]
      _ ≤ Order.height L.last := Order.length_le_height_last
      _ = Order.height (⟨J, hJ⟩ : PrimeSpectrum S) := by rw [hLlast]

/-! ### The main statement -/
theorem finite_extension_domain_height {C S : Type*} [CommRing C] [CommRing S] [Algebra C S]
    [Module.Finite C S] [FaithfulSMul C S] [IsDomain C] [IsDomain S] [IsIntegrallyClosed C] :
    (∀ (J : Ideal S) [J.IsPrime], J.height = (J.under C).height) ∧
    (∀ (J : Ideal S) [J.IsPrime], ringKrullDim (S ⧸ J) = ringKrullDim (C ⧸ J.under C)) ∧
    ringKrullDim S = ringKrullDim C := by
  -- `S` is a finite, hence integral, `C`-module.
  haveI : Algebra.IsIntegral C S := Algebra.IsIntegral.of_finite C S
  -- `C` integrally closed makes the integral extension `C ⊆ S` satisfy going down.
  haveI : Algebra.HasGoingDown C S := inferInstance
  refine ⟨?_, ?_, ?_⟩
  · -- heights of primes
    intro J hJ
    exact Ideal.height_eq_height_under_of_hasGoingDown (C := C) (S := S) J
  · -- dimensions of the residues: `C ⧸ (J ∩ C) → S ⧸ J` is injective and integral
    intro J hJ
    have hinj : Function.Injective (algebraMap (C ⧸ J.under C) (S ⧸ J)) :=
      FaithfulSMul.algebraMap_injective _ _
    exact ringKrullDim_eq_of_isIntegral_of_injective (A := C ⧸ J.under C) (B := S ⧸ J) hinj
  · -- total dimension
    exact ringKrullDim_eq_of_isIntegral_of_injective (FaithfulSMul.algebraMap_injective C S)

end Work.BW.RB
