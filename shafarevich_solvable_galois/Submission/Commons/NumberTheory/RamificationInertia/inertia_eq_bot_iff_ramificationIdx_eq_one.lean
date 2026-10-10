import Mathlib.NumberTheory.RamificationInertia.Galois
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.NumberTheory.RamificationInertia

open NumberField in
/-- **The inertia group is trivial iff the ramification index is one.**

For a Galois extension `K/F` of number fields, a prime `P` of `𝓞 K` over a prime `p` of `𝓞 F` has
trivial inertia group in `Gal(K/F)` exactly when its ramification index over `p` is `1`.

Proof: `Commons.NumberTheory.RamificationInertia.card_inertia_eq_ramificationIdx` (or the Mathlib
lemma `Ideal.card_inertia_eq_ramificationIdxIn` together with
`Ideal.ramificationIdxIn_eq_ramificationIdx`) gives `Nat.card (Ideal.inertia Gal(K/F) P) =
P.ramificationIdx (𝓞 F)`; a subgroup of cardinality `1` is `⊥`. -/
theorem inertia_eq_bot_iff_ramificationIdx_eq_one {F K : Type*} [Field F] [Field K] [Algebra F K]
    [NumberField F] [NumberField K] [IsGalois F K] [FiniteDimensional F K]
    (p : Ideal (RingOfIntegers F)) (P : Ideal (RingOfIntegers K))
    [P.LiesOver p] [p.IsPrime] [P.IsPrime] :
    Ideal.inertia (K ≃ₐ[F] K) P = ⊥ ↔ P.ramificationIdx (RingOfIntegers F) = 1 := by
  have h := Ideal.card_inertia_eq_ramificationIdxIn (G := K ≃ₐ[F] K) (R := RingOfIntegers F)
    (S := RingOfIntegers K) p P
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx p P (K ≃ₐ[F] K)] at h
  rw [Subgroup.eq_bot_iff_card, h]

end Commons.NumberTheory.RamificationInertia