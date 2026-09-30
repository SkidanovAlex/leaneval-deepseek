import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW.RB

open Order

/-- The poset of prime ideals of `T ⧸ P` lying below the image of `Q` is order-isomorphic to the
poset of prime ideals `J` of `T` with `P ≤ J ≤ Q`; hence the two posets have the same Krull
dimension.  The order isomorphism is induced by the correspondence theorem for ideals under the
surjective ring homomorphism `T → T ⧸ P` (`Ideal.relIsoOfSurjective`), restricted to primes. -/
private lemma krullDim_Icc_quotient_eq {T : Type*} [CommRing T] (P Q : Ideal T)
    [P.IsPrime] [Q.IsPrime] (h : P ≤ Q) :
    Order.krullDim ↥(Set.Iic (⟨Q.map (Ideal.Quotient.mk P),
        Ideal.map_isPrime_of_surjective (Ideal.Quotient.mk_surjective)
          (by rw [Ideal.mk_ker]; exact h)⟩ : PrimeSpectrum (T ⧸ P)))
      = Order.krullDim {J : Ideal T // J.IsPrime ∧ P ≤ J ∧ J ≤ Q} := by
  let f : T →+* T ⧸ P := Ideal.Quotient.mk P
  have hf : Function.Surjective f := Ideal.Quotient.mk_surjective
  have hker : RingHom.ker f = P := Ideal.mk_ker
  have hbot : Ideal.comap f ⊥ = P := by rw [← RingHom.ker_eq_comap_bot, hker]
  have hQprime : (Q.map f).IsPrime :=
    Ideal.map_isPrime_of_surjective hf (hker.le.trans h)
  let x : PrimeSpectrum (T ⧸ P) := ⟨Q.map f, hQprime⟩
  change Order.krullDim ↥(Set.Iic x) = Order.krullDim {J : Ideal T // J.IsPrime ∧ P ≤ J ∧ J ≤ Q}
  refine Order.krullDim_eq_of_orderIso ?_
  refine
    { toFun := fun y => ⟨y.1.asIdeal.comap f, ?_, ?_, ?_⟩
      invFun := fun J => ⟨⟨J.1.map f, ?_⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_
      map_rel_iff' := ?_ }
  · exact Ideal.comap_isPrime f y.1.asIdeal
  · exact (le_of_eq hbot.symm).trans (Ideal.comap_mono (bot_le : (⊥ : Ideal (T ⧸ P)) ≤ y.1.asIdeal))
  · have hpq : y.1.asIdeal ≤ Q.map f := y.2
    refine (Ideal.comap_mono hpq).trans ?_
    rw [Ideal.comap_map_of_surjective f hf Q, hbot]
    exact sup_le le_rfl h
  · exact Ideal.map_isPrime_of_surjective (f := f) hf (I := J.1) (H := J.2.1)
      (hker.le.trans J.2.2.1)
  · exact Ideal.map_mono J.2.2.2
  · intro y
    apply Subtype.ext
    apply PrimeSpectrum.ext
    exact Ideal.map_comap_of_surjective f hf y.1.asIdeal
  · intro J
    apply Subtype.ext
    exact (Ideal.comap_map_of_surjective f hf J.1).trans
      (by rw [hbot, sup_eq_left.mpr J.2.2.1])
  · intro a b
    show Ideal.comap f a.1.asIdeal ≤ Ideal.comap f b.1.asIdeal ↔ a.1.asIdeal ≤ b.1.asIdeal
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_comap_of_surjective f hf]

/-- For primes `P ≤ Q` in a commutative ring `T`, the height of the image of `Q` in `T ⧸ P`
equals the Krull dimension of the poset of primes `J` of `T` with `P ≤ J ≤ Q`
(this is the "relative height" of `Q` over `P`). -/
theorem height_map_quotient_mk_eq_krullDim_Icc {T : Type*} [CommRing T] (P Q : Ideal T)
    [P.IsPrime] [Q.IsPrime] (h : P ≤ Q) :
    ((Q.map (Ideal.Quotient.mk P)).height : WithBot ℕ∞)
      = Order.krullDim {J : Ideal T // J.IsPrime ∧ P ≤ J ∧ J ≤ Q} := by
  have hQprime : (Q.map (Ideal.Quotient.mk P)).IsPrime :=
    Ideal.map_isPrime_of_surjective (Ideal.Quotient.mk_surjective)
      (by rw [Ideal.mk_ker]; exact h)
  let x : PrimeSpectrum (T ⧸ P) := ⟨Q.map (Ideal.Quotient.mk P), hQprime⟩
  have h1 : (Q.map (Ideal.Quotient.mk P)).height = Order.height x :=
    PrimeSpectrum.height_eq_orderHeight x
  have h2 : ((Q.map (Ideal.Quotient.mk P)).height : WithBot ℕ∞)
      = (↑(Order.height x) : WithBot ℕ∞) :=
    congrArg (fun n : ℕ∞ => (n : WithBot ℕ∞)) h1
  have h3 : (↑(Order.height x) : WithBot ℕ∞)
      = Order.krullDim ↥(Set.Iic x) := Order.height_eq_krullDim_Iic x
  have h4 : Order.krullDim ↥(Set.Iic x)
      = Order.krullDim {J : Ideal T // J.IsPrime ∧ P ≤ J ∧ J ≤ Q} :=
    krullDim_Icc_quotient_eq P Q h
  exact h2.trans (h3.trans h4)

end Work.BW.RB
